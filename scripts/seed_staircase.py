#!/usr/bin/env python3
"""Trust: the seed staircase — Trust-from-Trust, with stock Rust nowhere in the loop.

The checksum-pinned seed in ``src/stage0`` is a Trust compiler. Every build that
starts from it, directly or through earlier rungs built from it, descends from
Trust alone. When the pinned seed cannot build the tree in one step, the
staircase builds the newest commit it CAN build, uses that stage2 as the stage0
for a later commit, and repeats until the target builds. Every rung is recorded
(commit, stage0 identity by sha256, log, process census), so the lineage of the
final compiler is a ledger, not a claim. docs/SEED_STAIRCASE.md is the procedure
and the measured record.

Subcommands (each prints JSON on stdout; refusals exit 1, usage errors exit 2):

  admit DIR --repo R [--target C] [--compat-lib D]...
        Admit DIR as a stage0 by CONTENT, not by name or path: native executables
        (a ``#!`` script is refused), nothing under a stock root (rustup, cargo,
        Homebrew, /usr/local, the genesis adapter), ``trustc -vV`` names a commit
        in R's object DB (and, with --target, an ancestor of C), ``-Z help``
        carries the Trust verification switch, ``--print sysroot`` is DIR, and on
        macOS every dylib load command resolves to the OS, inside DIR, or to a
        declared compat library. On native Linux, glibc's actual loader resolves
        each ELF DT_NEEDED closure to bound internal or OS files. Prints the
        identity (sha256 of every driver file); neither observation proves lineage.

  seed-sysroot --payloads DIR --stage0-file F --out DIR
        Verify the pinned seed archives against ``src/stage0`` and install the
        trustc, trust-std and targo components into one sysroot, for admission.

  libgit2-compat --crate FILE --lock Cargo.lock --out DIR
        Build libgit2 as a dylib from the Cargo.lock-pinned ``libgit2-sys`` crate
        with the system C compiler (no Homebrew, no cmake, no Rust). The
        2026-07-13 seed's cargo carries a load command for Homebrew's
        ``libgit2.1.9.dylib`` (it was minted before 8336ef81e9 vendored libgit2);
        this satisfies it without changing one seed byte.

  seed-config --worktree W [--llvm-config P]
        Write W's bootstrap.toml in the recreator's SEED mode (no stage0 keys:
        x.py materializes the pinned archives itself), with W's own
        scripts/recreate_bootstrap.py writer. Rung 0 uses this.

  config --base FILE --stage0 DIR --out FILE
        Write a rung config: ``include`` the base config and point the four
        stage0 tool keys at an admitted earlier rung's stage2.

  run --worktree W --label L --ledger D --stage0-admission F [--compat-lib D]... [--seed-mode]
      [--stop-grace-seconds S] [--offline] [--clean-lean-lib DIR] [--fifo-jobserver] -- <x.py args>
        Run one x.py invocation in a scrubbed environment (PATH of OS dirs plus
        trap shims that refuse and log every stock tool name, RUSTUP_* pointing
        nowhere, a private CARGO_HOME, SOURCE_DATE_EPOCH = the commit's time)
        behind a memory gate, sampling every
        process of the build, then census the build tree and hash the stage0
        the build actually ran (--seed-mode: the one x.py materialized in-tree
        from src/stage0; otherwise the admitted directory the config names) and
        the stage2 it produced. Appends the record to D/rungs.jsonl.
        --offline adds CARGO_NET_OFFLINE=true. --clean-lean-lib DIR hands the
        build the Lean library W's Clean pin names (the two CLEAN_OLEAN_*
        variables), once `mint_seed_support.clean_lean_inputs` accepts DIR, and
        records what that bound before and after the build under `clean_lean`.
        --fifo-jobserver hands x.py a named FIFO jobserver (BOOTSTRAP-JOBSERVER-PROBE-1:
        a pipe jobserver's descriptors do not survive Trust std's spawn, a path does):
        a private FIFO D/tmp/jobserver.fifo preloaded with N-1 tokens for the job count
        N x.py runs with (its -j, else [build] jobs of its configuration; refused when
        neither names one), held open here until x.py exits, advertised as
        MAKEFLAGS="-jN --jobserver-auth=fifo:PATH", then removed. GNU make before
        4.4 stops on that spelling, so D/pathbin/make, first on x.py's PATH, is an
        adapter that hands the make after it the FIFO as two descriptors
        (MAKE_ADAPTER_MARK); refused when no make follows pathbin. The record's
        `jobserver` names the adapter and the make it runs, and says how many tokens
        the FIFO held at the end; a count that is not N-1 is recorded, never judged
        here (see FifoJobserver).
        With none of the three, the environment and the record are what they were.

  scan --build-dir B --repo R
        Census a build tree: every ``.rustc_info.json`` (which compiler cargo
        saw, and its sysroot; since BOOTSTRAP-RUSTC-INFO-1 a tree of a commit
        that carries it has only build/bootstrap's, the stage0 that built
        bootstrap, because x.py's Cargo persists none behind its rustc shim)
        and every ``/rustc/<40-hex>`` std path embedded in
        the produced drivers and tools, each commit classified against R; and,
        for information, the unremapped std source roots each binary embeds.

  lineage --root-admission F --rung F... --final-stage2 S2 --repo R
          [--ddc-manifests STAIRCASE DDC --ddc-seed-admission F [--ddc-run F]]
        Assemble the lineage record promote-toolchain.sh --lineage seals: the
        admitted root seed, every rung in order, the final stage2's identity
        and, with --ddc-manifests, the double-compile verdict over two
        `mint_seed_support.py stage2-manifest` trees (the pack cut's own
        comparator and relation classifier). Rungs chain by commit AND by bytes:
        each rung's stage0 is the compiler the previous rung produced, and the
        final stage2 is the last rung's output. Consecutive records of one
        worktree, commit and stage0 are one rung resumed in place. Refuses a
        rung without clean no-stock evidence; exit 1 unless the compiler and
        std compared identical.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor. config_build_tools reads a bootstrap configuration with tomllib
# (3.11+), and `config` and `run` reach it.
# `python3 seed_staircase.py` on a machine whose python3 is older (3.9 on macOS
# CommandLineTools) re-execs here under the newest >=3.11 on PATH
# (scripts/tests/python_floor_test.py holds every such script to this).
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("seed_staircase.py requires Python 3.11+ (tomllib); none found on PATH")

import argparse
import fnmatch
import functools
import hashlib
import json
import os
import platform
import re
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile
import time
import types
from contextlib import contextmanager, suppress
from pathlib import Path

SCHEMA = "trust-seed-staircase-v1"
HOME = str(Path.home())

# A stage0 whose real path contains one of these is stock or the genesis adapter.
STOCK_ROOT_MARKERS = (
    "/.rustup/",
    "/.cargo/",
    "/opt/homebrew/",
    "/usr/local/",
    "/genesis-stage0/",
    "/rustup/toolchains/",
)
# Load commands that name the operating system itself.
SYSTEM_DYLIB_PREFIXES = ("/usr/lib/", "/System/Library/")
# Names a PATH lookup must never resolve during a rung: the trap shims refuse them.
TRAPPED_NAMES = (
    "rustc", "cargo", "rustup", "rustfmt", "rustdoc", "cargo-clippy", "clippy-driver",
    "cargo-fmt", "rust-analyzer", "cargo-miri", "miri",
)
RUST_TOOL_BASENAMES = frozenset(TRAPPED_NAMES) | {"trustc", "targo", "trustdoc", "trustfmt"}
MACHO_MAGICS = {
    b"\xcf\xfa\xed\xfe", b"\xce\xfa\xed\xfe", b"\xfe\xed\xfa\xcf", b"\xfe\xed\xfa\xce",
    b"\xca\xfe\xba\xbe", b"\xbe\xba\xfe\xca",
}
ELF_MAGIC = b"\x7fELF"
RUSTC_PATH_RE = re.compile(rb"/rustc/([0-9a-f]{40})/")
# A std compiled without remap-debuginfo embeds its builder's absolute source root
# instead (the 2026-07-13 seed's std says library/...): which
# std a binary links is then read off that root.
STD_ROOT_RE = re.compile(rb"(/[A-Za-z0-9._/-]{1,200}?)/library/(?:std|core|alloc)/src/")
# Archive members that are links or name `..` are refused before any extraction; the
# data filter (where this Python has it) also strips setuid/world-write bits.
TAR_FILTER = {"filter": "data"} if hasattr(tarfile, "data_filter") else {}
VERSION_LINE_RE = re.compile(r"^rustc (\S+) \(([0-9a-f]{7,40}) (\d{4}-\d{2}-\d{2})\)")


class Refusal(Exception):
    """A stage0 or input that the staircase refuses; the message says why."""


# ---------------------------------------------------------------------------
# small helpers


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def native_kind(path: Path) -> str:
    """'macho', 'elf', 'script' or 'other' by the file's leading bytes."""
    with open(path, "rb") as handle:
        head = handle.read(4)
    if head in MACHO_MAGICS:
        return "macho"
    if head == ELF_MAGIC:
        return "elf"
    if head.startswith(b"#!"):
        return "script"
    return "other"


def stock_marker(path: Path) -> str | None:
    rendered = "/" + str(path).strip("/") + "/"
    for marker in STOCK_ROOT_MARKERS:
        if marker in rendered:
            return marker
    return None


def git(repo: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-C", str(repo), *args], capture_output=True, text=True, check=False
    )


def commit_in_repo(repo: Path, commit: str) -> str | None:
    """The full hash when ``commit`` names a commit in repo's object DB."""
    if not re.fullmatch(r"[0-9a-f]{7,40}", commit):
        return None
    probe = git(repo, "rev-parse", "--verify", "--quiet", f"{commit}^{{commit}}")
    return probe.stdout.strip() if probe.returncode == 0 else None


def is_ancestor(repo: Path, ancestor: str, descendant: str) -> bool:
    return git(repo, "merge-base", "--is-ancestor", ancestor, descendant).returncode == 0


def run_tool(argv: list[str], env: dict[str, str] | None = None, timeout: int = 240) -> str:
    # A freshly extracted driver can take ~40 s on its first exec (the OS scans it).
    proc = subprocess.run(
        argv, capture_output=True, text=True, env=env, timeout=timeout, check=False
    )
    if proc.returncode != 0:
        raise Refusal(f"`{' '.join(argv)}` exited {proc.returncode}: {proc.stderr.strip()[:400]}")
    return proc.stdout


def compat_env(compat_dirs: list[Path]) -> dict[str, str]:
    env = dict(os.environ)
    if platform.system() == "Linux":
        # Match the loader observation and rung's scrubbed environment. Ambient
        # preloads/search overrides must not select a different dependency set.
        env = {k: v for k, v in env.items() if not k.startswith("LD_") and k != "GLIBC_TUNABLES"}
    if compat_dirs:
        env["DYLD_LIBRARY_PATH"] = ":".join(str(d) for d in compat_dirs)
    return env


_SUPPORT_SOURCE_INPUTS: dict[str, tuple[str, str]] = {}


@functools.lru_cache(maxsize=None)
def staircase_support(name: str):
    """Load captured source, never a pyc or an existing same-name module.

    A live source owner may supply the maintained BoundSourceLoader protocol.
    The standalone path records the exact buffer it compiles so its caller can
    bind those actual inputs rather than hashes from later disk reads.
    """
    if not re.fullmatch(r"[A-Za-z0-9_]+", name):
        raise Refusal("seed support needs a literal adjacent helper name")
    path = Path(__file__).resolve().parent / "lib" / (name + ".py")
    loader = globals().get("__trust_source_loader__")
    if loader is not None:
        module = loader.module("trust_seed_" + name, path)
        captured = module.__source_sha256__
    else:
        descriptor = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
        try:
            before = os.fstat(descriptor)
            if not stat.S_ISREG(before.st_mode) or before.st_size > 4 * 1024 * 1024:
                raise Refusal("seed support must be a bounded regular source file")
            raw = bytearray()
            while len(raw) <= 4 * 1024 * 1024:
                block = os.read(descriptor, min(65536, 4 * 1024 * 1024 + 1 - len(raw)))
                if not block:
                    break
                raw.extend(block)
            if len(raw) != before.st_size:
                raise Refusal("seed support source changed during capture")
        finally:
            os.close(descriptor)
        source = bytes(raw)
        captured = hashlib.sha256(source).hexdigest()
        private_name = "_trust_seed_" + name + "_" + captured
        module = types.ModuleType(private_name)
        module.__file__ = str(path)
        sys.modules[private_name] = module
        try:
            exec(compile(source, str(path), "exec", dont_inherit=True), module.__dict__)
        except BaseException:
            sys.modules.pop(private_name, None)
            raise
    if not isinstance(captured, str) or not re.fullmatch(r"[0-9a-f]{64}", captured):
        raise Refusal("seed support owner supplied no captured source identity")
    _SUPPORT_SOURCE_INPUTS[name] = (str(path), captured)
    return module


def support_source_inputs() -> dict[str, str]:
    """Actual already-loaded support source identities, for the live owner."""
    return dict(_SUPPORT_SOURCE_INPUTS.values())


def linux_seed_support():
    return staircase_support("seed_linux")


def seed_content_identity(root: Path) -> str:
    """Canonical seal-content encoding, excluding the extraction's own receipt.

    Bind all installed std/rustc-private files as well as compiler binaries.
    The existing seal helper supplies entry selection, modes and file hashes.
    """
    digest = hashlib.sha256()
    support = staircase_support("seal_content_identity")
    try:
        entries = support.entries(root)
    except support.SealContentError as error:
        raise Refusal(f"seed content identity refused: {error}") from error
    for path, kind, mode, value in entries:
        if path == b"STAGE0-SEED.json":
            continue
        for field in (kind, mode, value, path):
            digest.update(field)
            digest.update(b"\0")
    return digest.hexdigest()


# ---------------------------------------------------------------------------
# sysroot identity: the bytes a lineage links rung to rung

IDENTITY_FILES = ("bin/trustc", "bin/cargo", "bin/targo", "bin/trustdoc", "bin/trustfmt")
IDENTITY_GLOBS = ("lib/librustc_driver-*", "lib/libstd-*")


def sysroot_files(root: Path) -> dict[str, str]:
    """sha256 of a sysroot's drivers, its librustc_driver and its std dylib."""
    files = {}
    for rel in IDENTITY_FILES:
        if (root / rel).is_file():
            files[rel] = sha256_file(root / rel)
    for pattern in IDENTITY_GLOBS:
        for path in sorted(root.glob(pattern)):
            if path.is_file():
                files[str(path.relative_to(root))] = sha256_file(path)
    return files


def manifest_identity(manifest: dict) -> dict[str, str]:
    """sysroot_files() of the tree a `mint_seed_support.py stage2-manifest`
    describes, read from its records: the same files, by the same rules."""
    return {
        record["path"]: record["sha256"] for record in manifest.get("records", [])
        if record.get("kind") == "file" and (
            record.get("path") in IDENTITY_FILES
            or any(fnmatch.fnmatchcase(record.get("path", ""), glob) for glob in IDENTITY_GLOBS))
    }


def compiler_bytes(files: dict[str, str]) -> dict[str, str]:
    """The part of an identity that makes the next compiler: trustc, the driver
    it loads, and the cargo that drives the build."""
    return {rel: digest for rel, digest in files.items()
            if rel in ("bin/trustc", "bin/cargo") or rel.startswith("lib/librustc_driver-")}


def host_triple() -> str:
    machine = platform.machine().lower()
    arch = {"arm64": "aarch64", "aarch64": "aarch64", "x86_64": "x86_64", "amd64": "x86_64"}.get(machine)
    system = {"Darwin": "apple-darwin", "Linux": "unknown-linux-gnu"}.get(platform.system())
    if not arch or not system:
        raise Refusal(f"no host triple for {platform.system()} {platform.machine()}")
    return f"{arch}-{system}"


# ---------------------------------------------------------------------------
# dylib closure (macOS)


def macho_load_commands(binary: Path) -> list[str]:
    out = run_tool(["otool", "-L", str(binary)], timeout=60)
    libs = []
    for line in out.splitlines()[1:]:
        line = line.strip()
        if line:
            libs.append(line.split(" (compatibility", 1)[0].strip())
    return libs


def macho_files(root: Path) -> list[Path]:
    """Every Mach-O under root's bin/, lib/ (recursively: codegen backends and
    rustlib dylibs load too) and libexec/."""
    found = []
    for sub in ("bin", "lib", "libexec"):
        base = root / sub
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*")):
            if path.is_file() and not path.is_symlink() and native_kind(path) == "macho":
                found.append(path)
    return found


def dylib_closure(root: Path, compat_dirs: list[Path]) -> dict:
    """Classify every load command of every Mach-O under root's bin/lib/libexec.

    ``system``: the OS; ``internal``: resolves inside root; ``compat``: an absolute
    foreign path whose leaf a declared compat directory provides (the runner puts
    those directories on DYLD_LIBRARY_PATH, which dyld searches BEFORE the
    absolute path, so a foreign copy at that path is never loaded); ``unresolved``:
    anything else. An unresolved entry is a refusal.
    """
    if platform.system() == "Linux":
        try:
            return linux_seed_support().closure(root, host_triple(), compat_dirs)
        except (ValueError, OSError, subprocess.TimeoutExpired) as error:
            raise Refusal(f"Linux ELF closure refused: {error}") from error
    if platform.system() != "Darwin":
        raise Refusal(f"native shared-library closure is unsupported on {platform.system()}")
    internal_leaves = {p.name for p in root.rglob("*.dylib")}
    rows = []
    for binary in macho_files(root):
        for lib in macho_load_commands(binary):
            leaf = lib.rsplit("/", 1)[-1]
            if lib.startswith(SYSTEM_DYLIB_PREFIXES):
                continue
            if lib.startswith(("@rpath/", "@loader_path/", "@executable_path/")):
                kind = "internal" if leaf in internal_leaves else "unresolved"
                provider = None
            elif Path(lib).resolve().is_relative_to(root.resolve()):
                kind, provider = "internal", lib
            else:
                hit = next((d / leaf for d in compat_dirs if (d / leaf).is_file()), None)
                kind = "compat" if hit else "unresolved"
                provider = str(hit) if hit else None
            if binary.suffix == ".dylib" and leaf == binary.name:
                continue  # a dylib's own install name
            rows.append({
                "binary": str(binary.relative_to(root)),
                "load": lib,
                "kind": kind,
                "provider": provider,
                "provider_sha256": sha256_file(Path(provider)) if kind == "compat" else None,
            })
    return {
        "checked": True,
        "non_system": rows,
        "unresolved": [r for r in rows if r["kind"] == "unresolved"],
        "compat": [r for r in rows if r["kind"] == "compat"],
    }


# ---------------------------------------------------------------------------
# admission


def parse_vv(text: str) -> dict:
    fields = {}
    lines = text.splitlines()
    if lines:
        fields["version_line"] = lines[0]
    for line in lines[1:]:
        if ":" in line:
            key, value = line.split(":", 1)
            fields[key.strip()] = value.strip()
    return fields


def advertises_trust_switch(help_text: str) -> bool:
    for line in help_text.splitlines():
        rest = line.strip()
        if not rest.startswith("-Z"):
            continue
        rest = rest[2:].lstrip()
        for name in ("trust-verify", "no-trust-verify"):
            if rest == name or (rest.startswith(name) and rest[len(name):len(name) + 1] in ("=", " ", "\t")):
                return True
    return False


def admit(stage0: Path, repo: Path, target: str | None, compat_dirs: list[Path]) -> dict:
    stage0 = stage0.resolve()
    refusals: list[str] = []
    identity: dict = {"schema": SCHEMA, "kind": "stage0-admission", "stage0": str(stage0)}
    trustc = stage0 / "bin" / "trustc"
    cargo = stage0 / "bin" / "cargo"
    for tool in (trustc, cargo):
        if not tool.is_file():
            refusals.append(f"missing {tool.relative_to(stage0)}")
            continue
        real = tool.resolve()
        marker = stock_marker(real)
        if marker:
            refusals.append(f"{tool.name} resolves into a stock root ({marker}): {real}")
        kind = native_kind(real)
        if kind == "script":
            refusals.append(f"{tool.name} is a `#!` script, not a native compiler (the genesis adapter shape): {real}")
        elif kind not in ("macho", "elf"):
            refusals.append(f"{tool.name} is not a native executable: {real}")
    marker = stock_marker(stage0)
    if marker:
        refusals.append(f"stage0 directory lies in a stock root ({marker})")
    if refusals:
        identity["refusals"] = refusals
        return identity

    try:
        closure = dylib_closure(stage0, compat_dirs)
    except Refusal as error:
        identity["refusals"] = [str(error)]
        return identity
    identity["dylib_closure"] = closure
    for row in closure.get("unresolved", []):
        refusals.append(
            f"{row['binary']} loads {row['load']}, which is neither the OS, inside the stage0, "
            "nor a declared compat library (see `libgit2-compat`)"
        )
    env = compat_env(compat_dirs)
    probes: dict[str, str] = {}
    for key, argv in (
        ("vV", [str(trustc), "-vV"]),
        ("Z help", [str(trustc), "-Z", "help"]),
        ("sysroot", [str(trustc), "--print", "sysroot"]),
        ("cargo --version", [str(cargo), "--version"]),
    ):
        try:
            probes[key] = run_tool(argv, env=env)
        except (Refusal, OSError, subprocess.TimeoutExpired) as error:
            refusals.append(f"stage0 probe `{key}` failed: {error}")
    vv = parse_vv(probes.get("vV", ""))
    identity["trustc_vV"] = vv
    if platform.system() == "Linux" and vv.get("host") != host_triple():
        refusals.append(f"trustc reports host {vv.get('host', '<none>')}, not native {host_triple()}")
    identity["cargo_version"] = probes.get("cargo --version", "").strip()
    commit = vv.get("commit-hash", "")
    full = commit_in_repo(repo, commit)
    if "vV" in probes and not full:
        refusals.append(f"trustc reports commit-hash {commit or '<none>'}, which is not a commit in {repo} (a stock or foreign compiler)")
    elif full and target and not is_ancestor(repo, full, target):
        refusals.append(f"stage0 commit {full[:12]} is not an ancestor of the target {target[:12]}: a staircase only goes forward")
    identity["commit"] = full or commit
    # Trust merges upstream, so a stock nightly's commit can be in this history
    # too; a Trust compiler also names itself (the pack cut's lineage rule).
    if "vV" in probes and vv.get("binary") != "trustc":
        refusals.append(f"trustc -vV says `binary: {vv.get('binary', '<none>')}`, not trustc: not a Trust compiler")
    if "Z help" in probes and not advertises_trust_switch(probes["Z help"]):
        refusals.append("`-Z help` advertises no Trust verification switch (trust-verify / no-trust-verify)")
    sysroot = probes.get("sysroot", "").strip()
    if "sysroot" in probes and Path(sysroot).resolve() != stage0:
        refusals.append(f"--print sysroot is {sysroot}, not the stage0 directory")
    identity["sysroot"] = sysroot
    identity["sha256"] = sysroot_files(stage0)
    if platform.system() == "Linux" and (stage0 / "STAGE0-SEED.json").exists():
        try:
            pinned = pinned_seed_record(stage0, repo)
            if pinned["compiler_commit"] != identity["commit"]:
                raise Refusal("extracted seed compiler differs from src/stage0's commit")
            identity["pinned_seed"] = pinned
        except (OSError, ValueError, Refusal) as error:
            refusals.append(str(error))
    if len([rel for rel in identity["sha256"] if rel.startswith("lib/librustc_driver-")]) != 1:
        refusals.append("stage0 does not ship exactly one lib/librustc_driver-*")
    if platform.system() == "Linux":
        try:
            linux_seed_support().unchanged(closure)
        except (ValueError, OSError) as error:
            refusals.append(str(error))
    if refusals:
        identity["refusals"] = refusals
    return identity


# ---------------------------------------------------------------------------
# the pinned seed as a sysroot


def read_stage0_pins(stage0_file: Path) -> dict[str, str]:
    pins = {}
    for line in stage0_file.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        if key in pins:
            raise Refusal(f"{stage0_file} repeats pin {key}")
        pins[key] = value
    return pins


def _seed_archives(payloads: Path, pins: dict[str, str], host: str):
    date, version = pins.get("compiler_date"), pins.get("compiler_version")
    if not date or not version:
        raise Refusal("src/stage0 names no compiler_date/compiler_version")
    for component in ("trustc", "trust-std", "targo"):
        name = f"{component}-{version}-{host}.tar.xz"
        pin = pins.get(f"dist/{date}/{name}")
        if not pin or not re.fullmatch(r"[0-9a-f]{64}", pin):
            raise Refusal(f"src/stage0 pins no canonical SHA-256 for {name}")
        yield name, payloads / name, pin


@contextmanager
def _captured_archive(archive: Path, pin: str):
    """Parse ONLY the private byte snapshot whose digest matched the pin.

    A pre/post hash of a pathname cannot authenticate bytes read between those
    hashes. This private, unlinked spool is both the hash input and tar input.
    Never execute archive content while deriving the expected installation.
    """
    with os.fdopen(os.open(archive, os.O_RDONLY | os.O_NONBLOCK), "rb") as source, tempfile.TemporaryFile() as captured:
        metadata = os.fstat(source.fileno())
        if not stat.S_ISREG(metadata.st_mode):
            raise Refusal(f"seed archive is not a regular file: {archive}")
        remaining = metadata.st_size
        digest = hashlib.sha256()
        while remaining:
            block = source.read(min(1 << 20, remaining))
            if not block:
                raise Refusal(f"seed archive shortened during capture: {archive}")
            digest.update(block)
            captured.write(block)
            remaining -= len(block)
        if source.read(1):
            raise Refusal(f"seed archive grew during capture: {archive}")
        actual = digest.hexdigest()
        if actual != pin:
            raise Refusal(f"seed archive changed: {archive} sha256 {actual} != src/stage0 pin {pin}")
        captured.seek(0)
        yield captured


def _install_seed_components(payloads: Path, pins: dict[str, str], host: str,
                             tmp: Path) -> dict[str, str]:
    """The shared real installation recipe for construction AND authentication."""
    installed = {}
    for name, archive, pin in _seed_archives(payloads, pins, host):
        with _captured_archive(archive, pin) as captured:
            with tarfile.open(fileobj=captured, mode="r:xz") as tar:
                members = tar.getmembers()
                for member in members:
                    if (not (member.isfile() or member.isdir()) or ".." in Path(member.name).parts
                            or not (member.name == name[:-7] or member.name.startswith(f"{name[:-7]}/"))):
                        raise Refusal(f"refusing archive member {member.name} in {name}")
                tar.extractall(tmp, members=members, **TAR_FILTER)
        installed[name] = pin
        comp_root = tmp / name[:-7]
        for sub in comp_root.iterdir():
            if not sub.is_dir():
                continue
            for path in sorted(sub.rglob("*")):
                rel = path.relative_to(sub)
                dest = tmp / "sysroot" / rel
                if path.is_dir():
                    dest.mkdir(parents=True, exist_ok=True)
                elif rel.parts[-1] not in ("manifest.in",):
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    if dest.exists() and sha256_file(dest) != sha256_file(path):
                        raise Refusal(f"seed components disagree on {rel}")
                    shutil.copy2(path, dest)
    for tool in ("trustc", "cargo", "targo"):
        path = tmp / "sysroot" / "bin" / tool
        if not path.is_file():
            raise Refusal(f"pinned seed omitted bin/{tool}")
        if platform.system() == "Linux":
            try:
                linux_seed_support().native_elf(path, host)
            except ValueError as error:
                raise Refusal(str(error)) from error
    return installed


def _seed_archive_entries(root: Path):
    """Complete archive-installed namespace, including ordinary seal record names.

    Directories are created by the installer under its ambient umask. Their
    paths/kinds must match; file modes and bytes come from the archives. The
    existing installed_content_sha256 still binds actual directory modes.
    """
    support = staircase_support("seal_content_identity")
    try:
        rows = support.entries(root, excluded_root_records={"STAGE0-SEED.json"}, mode_mask=0o7777)
    except support.SealContentError as error:
        raise Refusal(f"seed archive identity refused: {error}") from error
    return tuple((path, kind, b"" if kind == b"D" else mode, value)
                 for path, kind, mode, value in rows)


def seed_sysroot(payloads: Path, stage0_file: Path, out: Path) -> dict:
    pins = read_stage0_pins(stage0_file)
    if not re.fullmatch(r"[0-9a-f]{40}", pins.get("compiler_git_commit_hash", "")):
        raise Refusal(f"{stage0_file} names no canonical compiler source commit")
    if out.exists() or out.is_symlink():
        raise Refusal(f"{out} already exists; a seed sysroot is never overwritten")
    host = host_triple()
    record = {"schema": SCHEMA, "kind": "seed-sysroot", "host": host,
              "compiler_commit": pins.get("compiler_git_commit_hash"),
              "stage0_file_sha256": sha256_file(stage0_file)}
    tmp = Path(tempfile.mkdtemp(prefix=".seed-sysroot-", dir=out.parent))
    try:
        record["payloads"] = _install_seed_components(payloads, pins, host, tmp)
        sysroot = tmp / "sysroot"
        if sha256_file(stage0_file) != record["stage0_file_sha256"]:
            raise Refusal("src/stage0 changed during seed extraction")
        record.update(sysroot=str(out.resolve()), payloads_path=str(payloads.resolve()),
                      sha256=sysroot_files(sysroot), installed_content_sha256=seed_content_identity(sysroot))
        (sysroot / "STAGE0-SEED.json").write_text(json.dumps(record, sort_keys=True, indent=2) + "\n")
        sysroot.rename(out)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return record


def pinned_seed_record(stage0: Path, repo: Path) -> dict:
    """Authenticate a Linux root extraction against this repo's actual pin.

    Native content admission alone also admits intermediate Trust compilers;
    those are never a substitute for the archive-pinned root of a lineage.
    """
    path = stage0 / "STAGE0-SEED.json"
    if not path.is_file() or path.is_symlink():
        raise Refusal("Linux root seed needs its checksum-pinned extraction record")
    record = json.loads(path.read_text())
    if not isinstance(record, dict) or not isinstance(record.get("payloads_path"), str):
        raise Refusal("malformed Linux root seed extraction record")
    pin_file = repo / "src/stage0"
    pins = read_stage0_pins(pin_file)
    if (record.get("kind") != "seed-sysroot" or record.get("host") != host_triple()
            or record.get("sysroot") != str(stage0.resolve())
            or record.get("stage0_file_sha256") != sha256_file(pin_file)
            or record.get("compiler_commit") != pins.get("compiler_git_commit_hash")
            or record.get("sha256") != sysroot_files(stage0)
            or record.get("installed_content_sha256") != seed_content_identity(stage0)):
        raise Refusal("Linux root seed extraction differs from its native source/pin/installed bytes")
    # The receipt is only a consistency record. Derive authority independently
    # from the pinned bytes with exactly the fresh constructor's recipe.
    with tempfile.TemporaryDirectory(prefix=".seed-archive-auth-") as temporary:
        tmp = Path(temporary)
        expected = _install_seed_components(Path(record["payloads_path"]), pins, host_triple(), tmp)
        if record.get("payloads") != expected:
            raise Refusal("root seed archive inventory differs from src/stage0")
        if _seed_archive_entries(stage0) != _seed_archive_entries(tmp / "sysroot"):
            raise Refusal("installed root seed differs from the pinned archive installation")
    if sha256_file(pin_file) != record["stage0_file_sha256"]:
        raise Refusal("src/stage0 changed during root seed authentication")
    return record


def require_pinned_root(admission: dict, repo: Path) -> None:
    if platform.system() == "Linux":
        record = pinned_seed_record(Path(admission.get("stage0", "/nonexistent")), repo)
        if admission.get("pinned_seed") != record or admission.get("commit") != record["compiler_commit"]:
            raise Refusal("Linux root admission is not the authenticated pinned extraction")


def seed_host_ledger_module():
    """scripts/seed_host_ledger.py beside this file: the rules that admit a seed
    host record. Loaded by its path (never a same-name importable module) and
    without a bytecode cache, like the sibling validators it loads in turn."""
    path = Path(__file__).resolve().parent / "seed_host_ledger.py"
    loader = globals().get("__trust_source_loader__")
    if loader is not None:
        return loader.module("trust_seed_host_ledger", path)
    import importlib.util

    spec = importlib.util.spec_from_file_location("trust_staircase_seed_host_ledger", path)
    if spec is None or spec.loader is None:
        raise Refusal(f"cannot load the seed host ledger rules: {path}")
    module = importlib.util.module_from_spec(spec)
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = previous
    return module


def pinned_root_admission(repo: Path, host: str) -> dict:
    """Which host record admitted a pinned root seed: the repo's seed ledger's
    table for `host`, passed through seed_host_ledger.select_host_record and
    capture_host_record, which re-derive the record from the tracked proofs and
    src/stage0's pins and refuse one they do not reproduce. Returns {kind,
    root_disclosure}: `kind` is the record's admission_kind (`mint` for a mint
    record, which names none) and root_disclosure its table or None. A ledger
    with no table for `host` is refused: the pin is admitted through its own
    host record or not at all."""
    import tomllib

    seed_root = repo / "bootstrap" / "trust-stage0"
    ledger = seed_root / "seed-ledger.toml"
    try:
        seed_root = seed_root.resolve(strict=True)
        release = tomllib.loads(ledger.read_text(encoding="utf-8")).get("release")
        pins = read_stage0_pins(repo / "src" / "stage0")
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        raise Refusal(f"the pinned root's seed ledger or src/stage0 cannot be read ({ledger}): {error}") from error
    if not isinstance(release, dict):
        raise Refusal(f"the pinned root's seed ledger {ledger} has no [release] table")
    helper = seed_host_ledger_module()
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        record = helper.select_host_record(release, host)
        if record is None:
            raise Refusal(f"the pinned root's seed ledger {ledger} has no [release.hosts.\"{host}\"] table (it is "
                          "in the single-host format): a pinned root is admitted only through its own host record")
        record, _metadata_sha256 = helper.capture_host_record(seed_root, pins, host, record)
    except (OSError, UnicodeError, ValueError, TypeError, KeyError) as error:
        raise Refusal(f"the pinned root's {host} seed host record is not admitted: {error}") from error
    finally:
        sys.dont_write_bytecode = previous
    kind = record.get("admission_kind", "mint" if record.get("schema") == helper.SCHEMA else None)
    disclosure = record.get("root_disclosure")
    if not isinstance(kind, str) or not re.fullmatch(r"[a-z][a-z0-9-]*", kind):
        raise Refusal(f"the pinned root's {host} seed host record names no admission kind")
    if disclosure is not None and not isinstance(disclosure, dict):
        raise Refusal(f"the pinned root's {host} seed host record's root_disclosure is not a table")
    return {"kind": kind, "root_disclosure": disclosure}


# ---------------------------------------------------------------------------
# libgit2 compat library


LIBGIT2_FEATURES_H = """#ifndef INCLUDE_features_h
#define INCLUDE_features_h
#define GIT_THREADS 1
#define GIT_TRACE 1
#define GIT_HTTPPARSER_BUILTIN 1
#define GIT_USE_NSEC 1
#define GIT_IO_POLL 1
#define GIT_IO_SELECT 1
#define GIT_USE_STAT_MTIMESPEC 1
#define GIT_ARCH_64 1
#define GIT_HTTPS 1
#define GIT_SECURE_TRANSPORT 1
#define GIT_SHA1_COLLISIONDETECT 1
#define GIT_SHA256_COMMON_CRYPTO 1
#define GIT_USE_ICONV 1
#endif
"""
PCRE2_SOURCES = (
    "auto_possess chartables chkdint compile compile_cgroup compile_class config context convert "
    "dfa_match error extuni find_bracket maketables match match_data match_next newline ord2utf "
    "pattern_info script_run serialize string_utils study substitute substring tables ucd "
    "valid_utf xclass"
).split()


def lock_checksum(lock: Path, name: str, version: str) -> str | None:
    text = lock.read_text()
    for block in text.split("[[package]]"):
        if f'name = "{name}"' in block and f'version = "{version}"' in block:
            match = re.search(r'checksum = "([0-9a-f]{64})"', block)
            return match.group(1) if match else None
    return None


def libgit2_compat(crate: Path, lock: Path, out: Path, jobs: int = 6) -> dict:
    if platform.system() != "Darwin":
        raise Refusal("libgit2-compat builds the macOS dylib the 2026-07-13 seed loads; nothing else needs it")
    match = re.fullmatch(r"libgit2-sys-(.+)\.crate", crate.name)
    if not match:
        raise Refusal(f"{crate} is not a libgit2-sys-<version>.crate file")
    version = match.group(1)
    pinned = lock_checksum(lock, "libgit2-sys", version)
    actual = sha256_file(crate)
    if pinned is None:
        raise Refusal(f"{lock} pins no libgit2-sys {version}")
    if actual != pinned:
        raise Refusal(f"{crate} sha256 {actual} != Cargo.lock checksum {pinned}")
    if out.exists():
        raise Refusal(f"{out} already exists; a compat library is never overwritten")
    cc = "/usr/bin/clang"
    work = Path(tempfile.mkdtemp(prefix=".libgit2-compat-", dir=out.parent))
    try:
        with tarfile.open(crate, "r:gz") as tar:
            for member in tar.getmembers():
                if member.issym() or member.islnk() or ".." in Path(member.name).parts:
                    raise Refusal(f"refusing crate member {member.name}")
            tar.extractall(work / "src", **TAR_FILTER)
        src = work / "src" / f"libgit2-sys-{version}" / "libgit2"
        header = (src / "include/git2/version.h").read_text()
        full = re.search(r'#define LIBGIT2_VERSION\s+"([^"]+)"', header).group(1)
        so = re.search(r'#define LIBGIT2_SOVERSION\s+"([^"]+)"', header).group(1)
        include = work / "include"
        shutil.copytree(src / "include", include)
        (include / "git2_features.h").write_text(LIBGIT2_FEATURES_H)
        files: list[Path] = []
        for sub in ("src/libgit2", "src/util", "src/libgit2/transports", "src/libgit2/streams",
                    "deps/llhttp", "deps/xdiff", "src/util/unix"):
            files += sorted((src / sub).glob("*.c"))
        files += [src / "deps/pcre2" / f"pcre2_{name}.c" for name in PCRE2_SOURCES]
        files += [src / rel for rel in (
            "src/util/allocators/failalloc.c", "src/util/allocators/stdalloc.c",
            "src/util/hash/collisiondetect.c", "src/util/hash/sha1dc/sha1.c",
            "src/util/hash/sha1dc/ubc_check.c", "src/util/hash/common_crypto.c")]
        flags = [
            # The scratch directory's random name must not reach the bytes (libgit2's
            # asserts embed __FILE__): the same crate gives the same dylib every run.
            f"-ffile-prefix-map={work}=/libgit2-compat",
            "-O2", "-fPIC", "-fvisibility=hidden", "-w", "-arch", "arm64", "-mmacosx-version-min=11.0",
            f"-I{include}", f"-I{src}/src/libgit2", f"-I{src}/src/util", f"-I{src}/deps/llhttp",
            f"-I{src}/deps/xdiff", f"-I{src}/deps/pcre2",
            "-DGIT_REGEX_BUILTIN=1", "-DPCRE2_STATIC", "-DPCRE2_EXPORT=", "-DPCRE2_EXP_DECL=",
            "-DPCRE2_EXP_DEFN=", "-DPCRE2_CODE_UNIT_WIDTH=8", "-DSUPPORT_PCRE2_8=1",
            "-DSUPPORT_UNICODE=1", "-DLINK_SIZE=2", "-DHEAP_LIMIT=20000000",
            "-DMATCH_LIMIT=10000000", "-DMATCH_LIMIT_DEPTH=MATCH_LIMIT", "-DMAX_VARLOOKBEHIND=255",
            "-DNEWLINE_DEFAULT=2", "-DPARENS_NEST_LIMIT=250", "-DMAX_NAME_SIZE=128",
            "-DMAX_NAME_COUNT=10000", "-DSHA1DC_NO_STANDARD_INCLUDES=1",
            '-DSHA1DC_CUSTOM_INCLUDE_SHA1_C="common.h"', '-DSHA1DC_CUSTOM_INCLUDE_UBC_CHECK_C="common.h"',
        ]
        objects = [work / "obj" / f"{i:04d}-{f.stem}.o" for i, f in enumerate(files)]
        (work / "obj").mkdir()
        pending = list(zip(files, objects))
        running: list[subprocess.Popen] = []
        while pending or running:
            while pending and len(running) < jobs:
                source, obj = pending.pop(0)
                running.append(subprocess.Popen([cc, *flags, "-c", str(source), "-o", str(obj)]))
            done = running.pop(0)
            if done.wait() != 0:
                raise Refusal(f"clang failed: {' '.join(done.args[-3:])}")
        lib = work / "lib" / f"libgit2.{so}.dylib"
        lib.parent.mkdir()
        subprocess.run(
            [cc, "-dynamiclib", "-arch", "arm64", "-mmacosx-version-min=11.0", "-o", str(lib),
             *map(str, objects), "-install_name", f"@rpath/libgit2.{so}.dylib",
             "-compatibility_version", f"{so}.0", "-current_version", full,
             "-liconv", "-lz", "-framework", "Security", "-framework", "CoreFoundation"],
            check=True,
        )
        (work / "lib").rename(out)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    dylib = out / f"libgit2.{so}.dylib"
    return {
        "schema": SCHEMA, "kind": "libgit2-compat", "crate": crate.name, "crate_sha256": actual,
        "libgit2_version": full, "compatibility_version": f"{so}.0", "compiler": cc,
        "dylib": str(dylib), "dylib_sha256": sha256_file(dylib),
        "load_commands": macho_load_commands(dylib),
    }


# ---------------------------------------------------------------------------
# rung configuration


def toml_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def write_seed_config(worktree: Path, llvm_config: str | None) -> dict:
    """Rung 0: the recreator's own seed-mode config for this worktree's commit."""
    scripts = worktree / "scripts"
    if not (scripts / "recreate_bootstrap.py").is_file():
        raise Refusal(f"{worktree} has no scripts/recreate_bootstrap.py")
    sys.path.insert(0, str(scripts))
    try:
        import recreate_bootstrap as rb  # the worktree's own writer, not this checkout's
    finally:
        sys.path.pop(0)
    host = rb.host_triple()
    import contextlib
    with contextlib.redirect_stdout(sys.stderr):  # stdout carries only this tool's JSON
        existing, content = rb._existing_bootstrap_config(worktree)
        written = rb.write_config(worktree, host, True, llvm_config=llvm_config, seed_mode=True,
                                  selection=rb.Stage0Selection("seed", existing, content))
    text = Path(written.path).read_text()
    for key in ("rustc", "cargo", "rustdoc", "rustfmt", "cargo-clippy"):
        if re.search(rf"^\s*{re.escape(key)}\s*=", text, re.M):
            raise Refusal(f"seed-mode config sets [build] {key}; the seed must come from src/stage0")
    return {"schema": SCHEMA, "kind": "seed-config", "config": str(written.path), "sha256": written.sha256}


def write_rung_config(base: Path, stage0: Path, out: Path) -> str:
    for rel in ("bin/trustc", "bin/cargo", "bin/trustdoc", "bin/trustfmt"):
        if not (stage0 / rel).is_file():
            raise Refusal(f"stage0 {stage0} has no {rel}")
    marker = stock_marker(stage0.resolve())
    if marker:
        raise Refusal(f"stage0 {stage0} lies in a stock root ({marker})")
    if out.exists():
        raise Refusal(f"{out} already exists; a rung config is never overwritten")
    text = "\n".join((
        f"# seed staircase rung config ({SCHEMA}); stage0 = an admitted earlier rung's stage2.",
        f"include = [{toml_string(str(base.resolve()))}]",
        "",
        "[build]",
        f"rustc = {toml_string(str(stage0 / 'bin' / 'trustc'))}",
        f"cargo = {toml_string(str(stage0 / 'bin' / 'cargo'))}",
        f"rustdoc = {toml_string(str(stage0 / 'bin' / 'trustdoc'))}",
        f"rustfmt = {toml_string(str(stage0 / 'bin' / 'trustfmt'))}",
        "",
    ))
    out.write_text(text)
    return text


# ---------------------------------------------------------------------------
# which stage0 tools an invocation's configuration names

CONFIG_TOOL_KEYS = ("rustc", "cargo", "rustdoc", "rustfmt", "cargo-clippy")
# The keys whose program compiles or drives the build; a `#!` script here is the
# genesis adapter's shape. (A pack-cut DDC config names a refusing script as
# cargo-clippy; it is recorded with its text, not refused.)
CONFIG_COMPILER_KEYS = ("rustc", "cargo", "rustdoc", "rustfmt")


def xpy_config_path(worktree: Path, xpy: list[str]) -> Path | None:
    """The configuration x.py reads, in bootstrap's own order: `--config FILE`,
    else the worktree's bootstrap.toml, else its config.toml (the scrubbed
    environment carries no RUST_BOOTSTRAP_CONFIG)."""
    for i, arg in enumerate(xpy):
        if arg == "--config" and i + 1 < len(xpy):
            return (worktree / xpy[i + 1]).resolve()
        if arg.startswith("--config="):
            return (worktree / arg.split("=", 1)[1]).resolve()
    for name in ("bootstrap.toml", "config.toml"):
        if (worktree / name).is_file():
            return (worktree / name).resolve()
    return None


def config_build_tools(config: Path, xpy: list[str], _seen: frozenset = frozenset()) -> dict[str, str]:
    """The `[build]` tool keys a bootstrap configuration sets, merged the way
    bootstrap merges them (config.rs `postprocess_toml`): every `include` (relative
    to the including file), later includes over earlier ones, the including file
    over all of them, and `--set build.<key>=...` over everything."""
    import tomllib

    config = config.resolve()
    if config in _seen:
        raise Refusal(f"{config} includes itself")
    data = tomllib.loads(config.read_text())
    merged: dict[str, str] = {}
    for include in data.get("include") or []:
        merged.update(config_build_tools(config.parent / include, [], _seen | {config}))
    build = data.get("build") or {}
    merged.update({key: str(build[key]) for key in CONFIG_TOOL_KEYS if key in build})
    for i, arg in enumerate(xpy):
        value = xpy[i + 1] if arg == "--set" and i + 1 < len(xpy) else (
            arg.split("=", 1)[1] if arg.startswith("--set=") else None)
        match = re.fullmatch(r"build\.([a-z-]+)=(.*)", value or "")
        if match and match.group(1) in CONFIG_TOOL_KEYS:
            merged[match.group(1)] = match.group(2).strip().strip('"')
    return merged


def config_tools_record(worktree: Path, xpy: list[str], admission: dict, seed_mode: bool) -> dict:
    """Which stage0 tools this invocation's configuration hands x.py, by real path
    and sha256, and whether that agrees with the admitted stage0: in seed mode the
    configuration names no compiler (x.py materializes the pinned seed in-tree, and
    that extraction is what `stage0_observed` hashes); otherwise its `rustc` is the
    admitted stage0's trustc, byte for byte. The driving cargo is recorded, not
    required to be the admission's: a double compile drives with the staircase's
    own stage0 cargo on purpose."""
    path = xpy_config_path(worktree, xpy)
    record: dict = {"config": str(path) if path else None, "tools": {}, "problems": []}
    if path is None:
        record["problems"].append("no bootstrap configuration found")
        return record
    record["config_sha256"] = sha256_file(path)
    try:
        named = config_build_tools(path, xpy)
    except (OSError, ValueError, Refusal) as error:
        record["problems"].append(f"cannot read the configuration: {error}")
        return record
    for key, value in sorted(named.items()):
        tool = (path.parent / value) if not os.path.isabs(value) else Path(value)
        row: dict = {"named": value}
        if tool.is_file():
            real = tool.resolve()
            row.update({"real": str(real), "kind": native_kind(real), "sha256": sha256_file(real)})
            if row["kind"] == "script" and real.stat().st_size <= 1024:
                row["script_text"] = real.read_text(errors="replace")
            marker = stock_marker(real)
            if marker:
                record["problems"].append(f"[build] {key} resolves into a stock root ({marker}): {real}")
            if key in CONFIG_COMPILER_KEYS and row["kind"] not in ("macho", "elf"):
                record["problems"].append(f"[build] {key} is not a native executable ({row['kind']}): {real}")
        else:
            row["missing"] = True
            record["problems"].append(f"[build] {key} names {value}, which is not a file")
        record["tools"][key] = row
    if seed_mode:
        for key in CONFIG_TOOL_KEYS:
            if key in named:
                record["problems"].append(
                    f"--seed-mode, but the configuration sets [build] {key}: the in-tree seed would not be the stage0")
    else:
        rustc = record["tools"].get("rustc") or {}
        admitted_root = Path(admission.get("stage0", "/nonexistent")).resolve()
        if not rustc.get("sha256"):
            record["problems"].append("the configuration names no [build] rustc, so the admitted stage0 is not what compiles")
        elif rustc["sha256"] != (admission.get("sha256") or {}).get("bin/trustc"):
            record["problems"].append("[build] rustc is not the admitted stage0's bin/trustc (bytes differ)")
        elif not Path(rustc["real"]).is_relative_to(admitted_root):
            record["problems"].append(f"[build] rustc lies outside the admitted stage0 {admitted_root}")
    record["matches_admission"] = not record["problems"]
    return record


# ---------------------------------------------------------------------------
# build-tree census


def classify_commit(repo: Path, commit: str, allowed: set[str] | None) -> str:
    """`rung` for a commit this build may name (its own source, its stage0's),
    `FOREIGN` for anything else. Without an allowed set: `trust` for any commit in
    repo's history — weaker, because Trust merges upstream, so a stock NIGHTLY's
    commit can be in that history too."""
    full = commit_in_repo(repo, commit)
    if allowed is not None:
        return "rung" if full in allowed else "FOREIGN"
    return "trust" if full else "FOREIGN"


def scan_build(build: Path, repo: Path, allowed: set[str] | None = None) -> dict:
    infos = []
    for path in sorted(build.rglob(".rustc_info.json")):
        try:
            data = json.loads(path.read_text())
        except (OSError, ValueError) as error:
            infos.append({"file": str(path), "error": str(error)})
            continue
        versions, sysroots = set(), set()
        for output in (data.get("outputs") or {}).values():
            for line in (output.get("stdout") or "").splitlines():
                match = VERSION_LINE_RE.match(line)
                if match:
                    versions.add((match.group(1), match.group(2)))
                elif line.startswith("/") and "/" in line[1:] and " " not in line:
                    sysroots.add(line)
        row = {"file": str(path.relative_to(build)), "versions": [], "sysroots": sorted(sysroots), "flags": []}
        for release, commit in sorted(versions):
            verdict = classify_commit(repo, commit, allowed)
            row["versions"].append({"release": release, "commit": commit, "class": verdict})
            if verdict == "FOREIGN":
                row["flags"].append(f"compiler commit {commit} is not a commit this build may name")
        for sysroot in sysroots:
            marker = stock_marker(Path(sysroot))
            if marker:
                row["flags"].append(f"sysroot or libdir in a stock root ({marker}): {sysroot}")
        infos.append(row)
    census = {}
    targets = []
    resolved: set[Path] = set()
    for pattern in ("bootstrap/debug/bootstrap", "bootstrap/debug/rustc", "bootstrap/debug/rustdoc",
                    "*/stage1/lib/librustc_driver-*", "*/stage2/lib/librustc_driver-*",
                    "*/stage1/bin/*", "*/stage2/bin/*", "*/bootstrap-tools/*/release/*",
                    "*/bootstrap-seed-tools/*/release/*"):
        for path in sorted(build.glob(pattern)):
            # build/host is a link to build/<host>: census each file once.
            if (path.is_file() and not path.is_symlink() and path.resolve() not in resolved
                    and native_kind(path) in ("macho", "elf")):
                resolved.add(path.resolve())
                targets.append(path)
    std_roots: dict[str, dict[str, int]] = {}
    classes: dict[str, str] = {}
    for path in targets:
        hashes: dict[str, int] = {}
        roots: dict[str, int] = {}
        with open(path, "rb") as handle:
            data = handle.read()
        for match in RUSTC_PATH_RE.finditer(data):
            commit = match.group(1).decode()
            hashes[commit] = hashes.get(commit, 0) + 1
        for match in STD_ROOT_RE.finditer(data):
            root = match.group(1).decode()
            if not root.startswith("/rustc/"):
                roots[root] = roots.get(root, 0) + 1
        rel = str(path.relative_to(build))
        for commit in hashes:
            if commit not in classes:
                classes[commit] = classify_commit(repo, commit, allowed)
        census[rel] = {commit: {"count": count, "class": classes[commit]} for commit, count in sorted(hashes.items())}
        if roots:
            std_roots[rel] = dict(sorted(roots.items()))
    foreign = sorted({
        f"{name}: /rustc/{commit}" for name, rows in census.items()
        for commit, row in rows.items() if row["class"] == "FOREIGN"
    })
    flagged = [row for row in infos if row.get("flags") or row.get("error")]
    # An empty census is not a clean one: say what was actually observed. (Measured
    # 2026-09-30: under a RUSTUP_HOME sentinel cargo wrote no .rustc_info.json at
    # all, and only the std-path census carried weight; scrubbed_env says why.)
    return {
        "schema": SCHEMA, "kind": "build-census", "build": str(build),
        "allowed_commits": sorted(allowed) if allowed is not None else "any commit in the repository's history",
        "rustc_info_files": len(infos), "rustc_path_targets": len(targets),
        "rustc_info": infos, "rustc_path_census": census,
        # Informational: which unremapped std source roots each binary embeds.
        "unremapped_std_roots": std_roots,
        "foreign_rustc_paths": foreign, "flagged_rustc_info": flagged,
        # Clean needs both halves: binaries whose std paths name only allowed
        # commits, and at least one record of the compiler cargo actually saw.
        "clean": bool(targets) and bool(infos) and not foreign and not flagged,
    }


# ---------------------------------------------------------------------------
# the FIFO jobserver (`run --fifo-jobserver`, docs/OPEN_ISSUES.md BOOTSTRAP-JOBSERVER-PROBE-1)
#
# A Cargo without CARGO_JOBSERVER_HANDOFF (29ebb403de and earlier) gives its build
# scripts a pipe jobserver by descriptor number (--jobserver-auth=R,W), and Trust std
# gives a spawned child only fds 0-2, so a build script's compiler probe reaches
# Bootstrap's rustc shim with CARGO_MAKEFLAGS naming closed descriptors and the shim
# refuses it. A named FIFO survives that: every client opens it again by its path.
# Bootstrap forwards MAKEFLAGS to Cargo only when it names a FIFO
# (core/builder/cargo.rs), so the run that starts x.py makes and holds one.

# Under the run's TMPDIR (<ledger>/tmp), by one fixed name: every run of a ledger hands
# x.py the same MAKEFLAGS, so the runs a driver compares do not differ in it.
FIFO_JOBSERVER_NAME = "jobserver.fifo"
# GNU make's token byte (a jobserver client returns whatever byte it read).
FIFO_TOKEN = b"+"
# Every token is preloaded before x.py starts and must fit in the FIFO's buffer; 4096
# keeps N-1 below Linux's PIPE_BUF, so the preload is never a partial write there.
MAX_FIFO_JOBS = 4096
# The OS directories of x.py's PATH, after its trap shims and pathbin (scrubbed_env).
OS_PATH = ("/usr/bin", "/bin", "/usr/sbin", "/sbin", "/Library/Developer/CommandLineTools/usr/bin")


def config_build_jobs(config: Path, _seen: frozenset = frozenset()) -> tuple[object, Path] | None:
    """`[build] jobs` of a bootstrap configuration and the file that set it, merged
    the way bootstrap merges files (config_build_tools): each include, later over
    earlier, and the including file over all of them. None when no file sets it."""
    import tomllib

    config = config.resolve()
    if config in _seen:
        raise Refusal(f"{config} includes itself")
    data = tomllib.loads(config.read_text())
    found = None
    for include in data.get("include") or []:
        found = config_build_jobs(config.parent / include, _seen | {config}) or found
    build = data.get("build") or {}
    if isinstance(build, dict) and "jobs" in build:
        found = (build["jobs"], config)
    return found


def _job_count(value: object, where: str, *, text: bool = False) -> int:
    """A job count a FIFO jobserver can advertise: a whole number from 1 to MAX_FIFO_JOBS.
    A configuration's is a TOML integer (Bootstrap reads a string there as no count);
    a command line's is its digits."""
    digits = text and isinstance(value, str) and re.fullmatch(r"[0-9]+", value) is not None
    if isinstance(value, bool) or not (isinstance(value, int) or digits):
        raise Refusal(f"--fifo-jobserver: {where} is {value!r}, not a whole job count. Nothing was started and "
                      "nothing was written. Name the count x.py runs with as a whole number")
    count = int(value)
    if count < 1:
        raise Refusal(f"--fifo-jobserver: {where} is {count}; Bootstrap reads a count below 1 as this host's "
                      "parallelism, which this tool does not guess, and a FIFO jobserver is made for one count. "
                      "Nothing was started and nothing was written. Name a count of at least 1")
    if count > MAX_FIFO_JOBS:
        raise Refusal(f"--fifo-jobserver: {where} is {count}, over the {MAX_FIFO_JOBS} jobs whose tokens are "
                      "preloaded whole. Nothing was started and nothing was written. Name a smaller count")
    return count


def xpy_jobs(worktree: Path, xpy: list[str]) -> tuple[int, str]:
    """The job count x.py runs with and where it was read, the way Bootstrap reads it
    (config.rs: `flags_jobs.or(build_jobs)`): `-j`/`--jobs` on its command line over
    `[build] jobs` of its configuration (xpy_config_path; includes merged, `--set
    build.jobs=N` over the files). Words after `--` are not x.py's. Refused when
    nothing names a count, when the command line names one twice or in a cluster of
    short flags, or when the count is not a whole number from 1 to MAX_FIFO_JOBS."""
    words = xpy[:xpy.index("--")] if "--" in xpy else list(xpy)
    given: list[str] = []
    setting: str | None = None
    for i, arg in enumerate(words):
        following = words[i + 1] if i + 1 < len(words) else ""
        if arg in ("-j", "--jobs"):
            given.append(following)
        elif arg.startswith("--jobs="):
            given.append(arg.split("=", 1)[1])
        elif arg.startswith("-j") and not arg.startswith("--"):
            given.append(arg[2:].removeprefix("="))
        elif re.fullmatch(r"-[A-Za-z]+j.*", arg):
            raise Refusal(f"--fifo-jobserver: the x.py argument {arg!r} may hold -j among other short flags, and "
                          "this tool does not read clusters. Nothing was started and nothing was written. Give "
                          "-j N on its own")
        value = following if arg == "--set" else (arg.split("=", 1)[1] if arg.startswith("--set=") else None)
        match = re.fullmatch(r"build\.jobs=(.*)", value or "")
        if match:
            setting = match.group(1).strip()
    if len(given) > 1:
        raise Refusal(f"--fifo-jobserver: x.py's arguments name the job count {len(given)} times "
                      f"({', '.join(map(repr, given))}). Nothing was started and nothing was written. Give -j once")
    if given:
        return _job_count(given[0], "x.py's -j", text=True), "x.py -j"
    if setting is not None:
        return _job_count(setting, "x.py's --set build.jobs", text=True), "x.py --set build.jobs"
    config = xpy_config_path(worktree, xpy)
    try:
        found = config_build_jobs(config) if config is not None else None
    except (OSError, ValueError, Refusal) as error:
        raise Refusal(f"--fifo-jobserver: the configuration {config} cannot be read for its [build] jobs: {error}. "
                      "Nothing was started and nothing was written") from error
    if found is None:
        raise Refusal("--fifo-jobserver: the job count x.py runs with is named nowhere: not by -j or --set "
                      f"build.jobs among its arguments, and not by [build] jobs of {config or 'any configuration'} "
                      "or what it includes. A FIFO jobserver advertises -jN and holds N-1 tokens, so it needs N. "
                      "Nothing was started and nothing was written. Give x.py -j N, or set jobs in [build]")
    value, where = found
    return _job_count(value, f"[build] jobs of {where}"), f"[build] jobs of {where}"


def fifo_jobserver_path(ledger: Path) -> Path:
    """Where `run --fifo-jobserver` makes the FIFO for a run of `ledger`."""
    return ledger / "tmp" / FIFO_JOBSERVER_NAME


def fifo_jobserver_makeflags(path: Path, jobs: int) -> str:
    """The MAKEFLAGS x.py is given: GNU make 4.4's spelling of a FIFO jobserver."""
    return f"-j{jobs} --jobserver-auth=fifo:{path}"


# The make adapter `run --fifo-jobserver` puts first on x.py's PATH (<ledger>/pathbin/make).
# GNU make before 4.4 (4.3 on the GB10, 3.81 on macOS) stops on `--jobserver-auth=fifo:PATH`
# ("internal error: invalid --jobserver-auth string", exit 2), and a jobserver client hands
# make the run's FIFO by that spelling: 82bb867edd's openssl-sys build script imports the
# jobserver, and openssl-src runs `make` through jobserver_utils' configure_make, which sets
# MAKEFLAGS and MFLAGS to "-j --jobserver-fds=fifo:P --jobserver-auth=fifo:P". The adapter
# opens P by its path, once to read and once to write, names those two descriptors instead
# (R,W: the form every GNU make reads; the tokens are still the FIFO's), and runs the make
# x.py's PATH reaches after pathbin. A make that is handed no FIFO is run as it was asked.
# Its bytes are make_adapter_text of the python and the make it names, and the run records
# them under the jobserver's `make_adapter`.
MAKE_ADAPTER_MARK = "# seed_staircase.py: the make adapter of run --fifo-jobserver (BOOTSTRAP-JOBSERVER-PROBE-1)"
MAKE_ADAPTER_BODY = r'''import os, re, stat, sys

FIFO = re.compile(r"(--jobserver-(?:auth|fds)=)fifo:(\S+)")
KEYS = ("MAKEFLAGS", "MFLAGS")


def refuse(why):
    sys.stderr.write(f"seed staircase make adapter: {why}; {MAKE} was not run\n")
    sys.exit(2)


named = sorted({found.group(2) for key in KEYS for found in FIFO.finditer(os.environ.get(key, ""))})
if len(named) > 1:
    refuse(f"MAKEFLAGS and MFLAGS name {len(named)} FIFO jobservers ({', '.join(named)})")
if named:
    try:
        read = os.open(named[0], os.O_RDONLY | os.O_NONBLOCK)
        if not stat.S_ISFIFO(os.fstat(read).st_mode):
            refuse(f"the jobserver {named[0]} is not a FIFO")
        write = os.open(named[0], os.O_WRONLY | os.O_NONBLOCK)
    except OSError as error:
        refuse(f"the jobserver FIFO {named[0]} cannot be opened: {error.strerror or error}")
    for fd in (read, write):
        os.set_blocking(fd, True)
        os.set_inheritable(fd, True)
    for key in KEYS:
        if key in os.environ:
            os.environ[key] = FIFO.sub(lambda found: f"{found.group(1)}{read},{write}", os.environ[key])
os.execve(MAKE, [MAKE, *sys.argv[1:]], os.environ)
'''


def make_adapter_path(ledger: Path) -> Path:
    """Where `run --fifo-jobserver` puts the make adapter for a run of `ledger`."""
    return ledger / "pathbin" / "make"


def make_adapter_text(python_bin: str, make: str) -> str:
    """The make adapter's bytes, as text: started by `python_bin`, it runs `make`."""
    return f"#!{python_bin} -I\n{MAKE_ADAPTER_MARK}\nMAKE = {make!r}\n{MAKE_ADAPTER_BODY}"


def real_make(tool_dirs: list[Path]) -> str | None:
    """The make x.py's PATH reaches after its trap shims and pathbin (scrubbed_env)."""
    return shutil.which("make", path=os.pathsep.join([*OS_PATH, *map(str, tool_dirs)]))


def install_make_adapter(ledger: Path, python_bin: str, make: str) -> dict:
    """Write the make adapter (replacing what pathbin held at its name) and say what it is."""
    text = make_adapter_text(python_bin, make).encode()
    adapter = make_adapter_path(ledger)
    partial = adapter.with_name(".make.partial")
    partial.unlink(missing_ok=True)
    partial.write_bytes(text)
    partial.chmod(0o755)
    os.replace(partial, adapter)
    return {"path": str(adapter), "sha256": hashlib.sha256(text).hexdigest(), "make": make,
            "make_sha256": sha256_file(Path(os.path.realpath(make)))}


def remove_make_adapter(ledger: Path) -> None:
    """A run without --fifo-jobserver reaches the make it always reached: an adapter an
    earlier run of this ledger left in pathbin is removed (nothing else is)."""
    adapter = make_adapter_path(ledger)
    try:
        with open(adapter, "rb") as handle:
            head = handle.read(4096)
    except OSError:
        return
    if head.split(b"\n")[1:2] == [MAKE_ADAPTER_MARK.encode()]:
        adapter.unlink()


def fifo_jobserver_preflight(worktree: Path, ledger: Path, xpy: list[str], tool_dirs: list[Path]) -> dict:
    """What `run --fifo-jobserver` needs, judged before anything is written: the job
    count, the FIFO's path (free, without white space), a python whose path a #! line
    can name, and the make the adapter runs."""
    jobs, source = xpy_jobs(worktree, xpy)
    path = fifo_jobserver_path(ledger)
    if re.search(r"\s", str(path)):
        raise Refusal(f"--fifo-jobserver: the FIFO's path {path} holds white space, and a jobserver client "
                      "reads MAKEFLAGS word by word. Nothing was started and nothing was written. Use a ledger "
                      "whose path has none")
    if path.exists() or path.is_symlink():
        raise Refusal(f"--fifo-jobserver: {path} is already there: a run of this ledger that was killed "
                      "before it could remove it left it, or one is using it now. Nothing was started and nothing "
                      "was written or removed. If no run of this ledger is alive, remove it and run again")
    python_bin = python311()
    if re.search(r"\s", python_bin):
        raise Refusal(f"--fifo-jobserver: the python {python_bin} holds white space, and the make adapter's #! "
                      "line names it. Nothing was started and nothing was written. Put a python >= 3.11 without "
                      "white space in its path first on PATH")
    make = real_make(tool_dirs)
    if make is None:
        raise Refusal("--fifo-jobserver: there is no make on x.py's PATH after its pathbin "
                      f"({os.pathsep.join([*OS_PATH, *map(str, tool_dirs)])}). The run puts a make adapter first "
                      "on that PATH, because a jobserver client hands make the FIFO as fifo:PATH and make before "
                      "4.4 stops on it, and the adapter runs this host's make. Nothing was started and nothing was "
                      "written. Install make, or name its directory with --tool-dir")
    return {"jobs": jobs, "source": source, "path": path, "make": make}


class FifoJobserver:
    """A private FIFO (mode 0600) holding `jobs - 1` tokens, open read-write in this
    process from before x.py starts until after it exits: a FIFO discards what it
    holds when no descriptor is open on it, and with one held here a client never
    reads end-of-file nor writes to a FIFO with no reader. The descriptor is
    close-on-exec, so x.py and every process below it reach the jobserver by its
    path only, as a build script's probe under Trust std must.

    `release` counts the tokens the FIFO holds when x.py has exited, closes it and
    removes the path while it still names this FIFO. A count that is not `jobs - 1`
    is recorded and not judged here: fewer means a process ended holding a token (it
    died, or outlived x.py), more means something wrote a token it never took. Either
    way the build's exit status and no-stock evidence say what they said; whoever
    reads the record decides what a build whose jobserver did not balance is worth
    (the first-seed driver and its validator refuse it)."""

    def __init__(self, path: Path, jobs: int, source: str) -> None:
        self.path, self.fd = path, None
        try:
            os.mkfifo(path, 0o600)
        except FileExistsError:
            raise Refusal(f"--fifo-jobserver: {path} is already there: a run of this ledger that was killed before "
                          "it could remove it left it, or one is using it now. x.py was not started and nothing was "
                          "removed. If no run of this ledger is alive, remove it and run again") from None
        except OSError as error:
            raise Refusal(f"--fifo-jobserver: the FIFO {path} could not be made: {error.strerror or error}. x.py was "
                          "not started") from error
        try:
            self.fd = os.open(path, os.O_RDWR | os.O_NONBLOCK | os.O_CLOEXEC | os.O_NOFOLLOW)
            held = os.fstat(self.fd)
            if not stat.S_ISFIFO(held.st_mode) or held.st_uid != os.getuid() or stat.S_IMODE(held.st_mode) != 0o600:
                raise Refusal(f"--fifo-jobserver: {path} is not the private FIFO this run made (mode "
                              f"{stat.S_IMODE(held.st_mode):o}, owner {held.st_uid}). x.py was not started")
            self.identity = (held.st_dev, held.st_ino)
            tokens, remaining = jobs - 1, jobs - 1
            while remaining:
                try:
                    remaining -= os.write(self.fd, FIFO_TOKEN * min(remaining, 512))
                except BlockingIOError:
                    raise Refusal(f"--fifo-jobserver: {path} took {tokens - remaining} of the {tokens} tokens for "
                                  f"-j{jobs} before its buffer was full. x.py was not started; name a smaller "
                                  "count") from None
        except BaseException as error:
            self._discard()
            if isinstance(error, OSError):
                raise Refusal(f"--fifo-jobserver: the FIFO {path} could not be opened and filled: "
                              f"{error.strerror or error}. x.py was not started") from error
            raise
        self.record: dict = {"kind": "fifo", "path": str(path), "jobs": jobs, "jobs_from": source, "tokens": tokens}

    def _discard(self) -> None:
        """Close and remove a FIFO this run made, before x.py starts."""
        if self.fd is not None:
            os.close(self.fd)
            self.fd = None
        with suppress(OSError):
            if stat.S_ISFIFO(os.lstat(self.path).st_mode):
                self.path.unlink()

    def release(self) -> dict:
        """After x.py: the tokens held now, then the FIFO closed and its path removed.
        Adds `tokens_at_end` and `path_unchanged` (the path still named this FIFO, so
        it was removed; otherwise whatever is there is left as it is)."""
        if self.fd is None:
            return self.record
        count = 0
        while True:
            try:
                chunk = os.read(self.fd, 65536)
            except BlockingIOError:
                break
            if not chunk:
                break
            count += len(chunk)
        try:
            now = os.lstat(self.path)
            unchanged = (now.st_dev, now.st_ino) == self.identity
        except OSError:
            unchanged = False
        if unchanged:
            self.path.unlink()
        os.close(self.fd)
        self.fd = None
        self.record.update({"tokens_at_end": count, "path_unchanged": unchanged})
        return self.record


# ---------------------------------------------------------------------------
# running a rung


def available_gib() -> int:
    if platform.system() == "Linux":
        text = Path("/proc/meminfo").read_text()
        match = re.search(r"^MemAvailable:\s+(\d+) kB$", text, re.MULTILINE)
        if not match:
            raise Refusal("Linux /proc/meminfo reports no MemAvailable")
        return int(match.group(1)) * 1024 // (1 << 30)
    out = subprocess.run(["vm_stat"], capture_output=True, text=True, check=False).stdout
    page = 16384
    match = re.search(r"page size of (\d+) bytes", out)
    if match:
        page = int(match.group(1))
    pages = 0
    for key in ("Pages free", "Pages speculative", "Pages inactive", "Pages purgeable"):
        found = re.search(rf"{key}:\s+(\d+)\.", out)
        if found:
            pages += int(found.group(1))
    return pages * page // (1 << 30)


def write_traps(trap_dir: Path, log: Path) -> None:
    trap_dir.mkdir(parents=True, exist_ok=True)
    for name in TRAPPED_NAMES:
        shim = trap_dir / name
        # One line per hit: time, the caller's pid, this shim, its arguments, and the
        # caller's command line, read while the caller still exists (measured
        # 2026-10-01: the first hit came from a build script that lived for
        # milliseconds, and a bare pid named nothing by the time anyone looked).
        shim.write_text(
            "#!/bin/sh\n"
            "# seed staircase trap: a PATH lookup of a stock Rust tool name reached this shim.\n"
            "caller=$(ps -o command= -p \"$PPID\" 2>/dev/null | tr '\\t\\n' '  ')\n"
            f"printf '%s\\t%s\\t%s\\t%s\\t%s\\n' \"$(date '+%Y-%m-%dT%H:%M:%S')\" \"$PPID\" \"$0\" \"$*\" \"$caller\" >> {toml_string(str(log))}\n"
            f"echo 'seed staircase: refused PATH {name} (no stock Rust in a rung)' >&2\n"
            "exit 127\n"
        )
        shim.chmod(0o755)


def python311() -> str:
    for name in ("python3.14", "python3.13", "python3.12", "python3.11"):
        found = shutil.which(name)
        if found:
            return os.path.realpath(found)
    if sys.version_info >= (3, 11):
        return os.path.realpath(sys.executable)
    raise Refusal("x.py's preflight needs Python >= 3.11; none found")


def scrubbed_env(ledger: Path, label: str, compat_dirs: list[Path], python_bin: str,
                 source_date_epoch: str | None = None,
                 tool_dirs: list[Path] = (), offline: bool = False,
                 clean_lean: dict[str, str] | None = None, makeflags: str | None = None) -> dict[str, str]:
    pathbin = ledger / "pathbin"
    pathbin.mkdir(parents=True, exist_ok=True)
    for name in ("python3", Path(python_bin).name):
        link = pathbin / name
        if link.is_symlink() or link.exists():
            link.unlink()
        link.symlink_to(python_bin)
    env = {
        "HOME": HOME, "USER": os.environ.get("USER", "trust"),
        "LOGNAME": os.environ.get("LOGNAME", os.environ.get("USER", "trust")),
        "SHELL": "/bin/sh", "TERM": "dumb", "LANG": "en_US.UTF-8", "LC_ALL": "en_US.UTF-8",
        "TMPDIR": str(ledger / "tmp"),
        # Declared non-Rust tool directories (`run --tool-dir`) come last: the OS
        # copy of a tool wins, and the trap shims still answer every Rust name first.
        "PATH": ":".join((str(ledger / "trap"), str(pathbin), *OS_PATH, *map(str, tool_dirs))),
        "CARGO_HOME": str(ledger / "cargo-home"),
        # The plan's rustup sentinel: any rustup proxy reached by any path fails on
        # a toolchain that does not exist and may not be installed. No RUSTUP_HOME:
        # set beside RUSTUP_TOOLCHAIN, it makes cargo hash the mtime of
        # $RUSTUP_HOME/toolchains/<toolchain>/bin/rustc, fail, and write no
        # .rustc_info.json at all (measured 2026-10-01), emptying the build-tree
        # census of the files that say which compiler cargo saw.
        "RUSTUP_TOOLCHAIN": "__trust_no_rustup__", "RUSTUP_AUTO_INSTALL": "0",
        "TRUST_STAIRCASE_RUNG": label,
    }
    if os.environ.get("SSH_AUTH_SOCK"):
        env["SSH_AUTH_SOCK"] = os.environ["SSH_AUTH_SOCK"]
    if compat_dirs:
        env["DYLD_LIBRARY_PATH"] = ":".join(str(d) for d in compat_dirs)
    # Build-time stamps follow the source commit, not the wall clock (ay's build
    # scripts stamp `build.datetime_utc` from it), so two builds of one commit can
    # be compared byte for byte; nothing else in the build reads it.
    if source_date_epoch:
        env["SOURCE_DATE_EPOCH"] = source_date_epoch
    # `run --offline`, `run --clean-lean-lib` and `run --fifo-jobserver`: additions
    # only, after everything above, so a run given none gets the environment it
    # always got.
    if offline:
        env["CARGO_NET_OFFLINE"] = "true"
    if clean_lean:
        env.update(clean_lean)
    if makeflags is not None:
        env["MAKEFLAGS"] = makeflags
    (ledger / "tmp").mkdir(parents=True, exist_ok=True)
    (ledger / "cargo-home").mkdir(parents=True, exist_ok=True)
    return env


def tool_dir_record(tool_dirs: list[Path]) -> list[dict]:
    """What a declared `--tool-dir` hands a rung, by real path and sha256.

    A rung may need a non-Rust build tool the OS does not ship (on the GB10,
    `ninja` lives in `~/.local/bin`: no root, and the in-tree LLVM build uses
    it). Only a directory made for the purpose is admitted, never a general bin
    directory: every entry must be an executable regular file (or a link to
    one) that is not a Rust tool name and does not resolve into a stock root,
    so the declaration cannot carry a Rust compiler, a cargo or a rustup proxy
    onto PATH. The record is re-taken after the build and must be unchanged."""
    rows = []
    for directory in tool_dirs:
        if not directory.is_dir():
            raise Refusal(f"--tool-dir {directory} is not a directory")
        entries = []
        for entry in sorted(directory.iterdir()):
            name = entry.name
            real = Path(os.path.realpath(entry))
            if name in RUST_TOOL_BASENAMES or real.name in RUST_TOOL_BASENAMES:
                raise Refusal(f"--tool-dir {directory} carries a Rust tool name: {name}")
            marker = stock_marker(real)
            if marker:
                raise Refusal(f"--tool-dir entry {name} resolves into a stock root ({marker}): {real}")
            if not real.is_file() or not os.access(real, os.X_OK):
                raise Refusal(f"--tool-dir entry {name} is not an executable file: {real}")
            entries.append({"name": name, "path": str(entry), "real": str(real),
                            "sha256": sha256_file(real)})
        if not entries:
            raise Refusal(f"--tool-dir {directory} declares no tool")
        rows.append({"dir": str(directory), "entries": entries})
    return rows


def classify_exe(exe: str, allowed_roots: list[str]) -> str:
    if exe.startswith("(") or exe in ("<defunct>", "<exited>"):
        return "ok"
    marker = stock_marker(Path(exe))
    base = os.path.basename(exe)
    if marker in ("/.rustup/", "/.cargo/", "/rustup/toolchains/", "/genesis-stage0/"):
        return "STOCK-RUST"
    if marker in ("/opt/homebrew/", "/usr/local/"):
        return "STOCK-RUST" if base in RUST_TOOL_BASENAMES or "rust" in exe.lower() else "FOREIGN-NONRUST"
    if base in RUST_TOOL_BASENAMES and not any(exe.startswith(root) for root in allowed_roots):
        return "RUST-OUTSIDE-ADMITTED-ROOTS"
    return "ok"


# The longest the process census may go without a completed sample before the
# rung's no-stock evidence is void (a stalled `ps`, a run of failed samples).
MAX_CENSUS_GAP_S = 120.0
# The longest one census subprocess (`ps`, `lsof`) may take. A healthy listing
# takes well under a second; a slower one is abandoned (see census_output) and
# the next tick tries again.
SAMPLE_TIMEOUT_S = 10.0

# What a tick lists: every process's pid, parent and executable, from the kernel's
# process table. No column reads another process's memory (`comm` is the exec
# path; never `command`/`-E`, which read each process's argument and environment
# area), so another workload's paged-out or throttled process cannot stall it.
TICK_LISTING = ("/bin/ps", "-axww", "-o", "pid=,ppid=,lstart=,comm=")
# One row: pid, parent, start time (C locale, fixed width; with the pid it names
# one process, since pids wrap many times in a rung), executable.
TICK_ROW_RE = re.compile(r"\s*(\d+)\s+(\d+)\s+(\w{3} \w{3} [ \d]\d \d\d:\d\d:\d\d \d{4}|ticks:\d+)\s+(.*)")
# Census children run in the C locale (TICK_ROW_RE) with the OS directories only.
CENSUS_CHILD_ENV = {"LC_ALL": "C", "LANG": "C", "PATH": "/usr/bin:/bin:/usr/sbin:/sbin"}
# At most this many pids per environment read (`ps -E -p ...`).
ENV_READ_BATCH = 64
# Census children that outlived their bound: killed, never waited for, reaped
# by poll() on later ticks.
_ABANDONED: list[subprocess.Popen] = []


def census_output(argv: list[str]) -> bytes:
    """One census subprocess, bounded for real. A child that outlives
    SAMPLE_TIMEOUT_S is SIGKILLed and ABANDONED, never waited for: measured
    2026-10-01, a `ps -axE` blocked in the kernel reading another process's
    memory outlived its SIGKILL by about 90 s, and subprocess.run's timeout path
    waits for the killed child, so a "10 s" sample cost 100 s, twice in a row (a
    229.5 s blind spot that voided a five-hour rung)."""
    child = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                             stderr=subprocess.DEVNULL, env=CENSUS_CHILD_ENV)
    try:
        out, _ = child.communicate(timeout=SAMPLE_TIMEOUT_S)
    except subprocess.TimeoutExpired:
        child.kill()
        if child.stdout is not None:
            child.stdout.close()
        _ABANDONED.append(child)
        raise
    return out


def reap_abandoned() -> int:
    """Reap the abandoned census children that have ended (poll, never wait);
    how many remain."""
    _ABANDONED[:] = [child for child in _ABANDONED if child.poll() is None]
    return len(_ABANDONED)


def ps_listing(argv: list[str]) -> str:
    """One `ps` listing as text. A process's arguments and launch environment are
    whatever bytes it was started with (measured 2026-09-30: a 0xff byte in an
    unrelated process's environment killed the census five hours into a rung),
    so a listing is decoded, never trusted to be UTF-8."""
    if platform.system() == "Linux":
        if tuple(argv) == TICK_LISTING:
            return linux_seed_support().tick_listing()
        if argv[:4] == ["/bin/ps", "-Eww", "-o", "pid=,command="]:
            return linux_seed_support().environment_listing([int(pid) for pid in argv[-1].split(",")])
    return census_output(list(argv)).decode("utf-8", errors="replace")


def parse_tick(listing: str) -> dict[int, tuple[int, str, str]]:
    """{pid: (ppid, start time, executable)} from one TICK_LISTING."""
    table: dict[int, tuple[int, str, str]] = {}
    for line in listing.splitlines():
        match = TICK_ROW_RE.fullmatch(line.rstrip())
        if match:
            table[int(match.group(1))] = (int(match.group(2)), match.group(3), match.group(4))
    return table


def rung_members(table: dict[int, tuple[int, str, str]], roots: set[int]) -> set[int]:
    """Every listed process descending from a root (the watched build, members
    from earlier ticks, orphans carrying the rung's marker)."""
    children: dict[int, list[int]] = {}
    for pid, (ppid, _started, _exe) in table.items():
        children.setdefault(ppid, []).append(pid)
    members = {pid for pid in roots if pid in table}
    frontier = list(members)
    while frontier:
        for child in children.get(frontier.pop(), ()):
            if child not in members:
                members.add(child)
                frontier.append(child)
    return members


def read_environments(pids: list[int]) -> dict[int, str]:
    """{pid: argument-and-environment text} for those of `pids` still alive
    (`ps -E` restricted to them: only processes this census needs to read)."""
    rows: dict[int, str] = {}
    listing = ps_listing(["/bin/ps", "-Eww", "-o", "pid=,command=", "-p", ",".join(map(str, pids))])
    for line in listing.splitlines():
        parts = line.strip().split(None, 1)
        if parts and parts[0].isdigit():
            rows[int(parts[0])] = parts[1] if len(parts) == 2 else ""
    return rows


def sample_processes(label: str, watched: int, out: Path, allowed: list[str], interval: float, cap: int,
                     checkpoint_every: int = 60) -> None:
    """The process census of one rung: once per `interval`, every process that
    belongs to the rung, classified by its real executable.

    A process belongs to the rung when it descends from the watched build (x.py),
    or from a process that did when last listed (a member whose parent exits is
    reparented to launchd and stays a member), or when it is a NEW orphan whose
    launch environment carries the rung's marker (a double fork that left the
    tree between two ticks). Descent is read from the kernel's process table
    every tick; environments are read once per new member (the evidence of
    which RUSTUP_*/CARGO*/DYLD_* it ran with) and once per new orphan. Until
    2026-10-01 the census found the rung only by the marker, through a
    machine-wide `ps -E`: a descendant started with a cleared environment was
    invisible to it, and that listing stalled under load (census_output)."""
    marker = f"TRUST_STAIRCASE_RUNG={label}"
    keys = ("RUSTUP_TOOLCHAIN", "RUSTC", "CARGO", "RUSTC_WRAPPER", "RUSTUP_HOME", "CARGO_HOME", "DYLD_LIBRARY_PATH")
    seen: dict[str, list] = {}
    envs: dict[str, int] = {}
    # Which non-OS dylibs each build driver actually mapped (read once per cargo
    # process): the evidence for which libgit2 the seed's cargo loaded.
    dylibs: dict[str, dict[str, int]] = {}
    iterations = failed = env_reads = env_failed = 0
    errors: list[str] = []
    # Every blind spot over 30 s, by when it ended: what explains a census that
    # breaks MAX_CENSUS_GAP_S (a stalled machine, not a stalled sampler).
    long_gaps: list[dict] = []
    ended = "cap"
    started = last_ok = time.monotonic()
    max_gap = 0.0
    # A process is (pid, start time): pids wrap many times in a rung.
    baseline: set[tuple[int, str]] | None = None  # listed before the rung could have made them
    known: set[tuple[int, str]] = set()           # every process listed so far
    member_keys: set[tuple[int, str]] = set()     # members as of the last listing (and marked orphans)
    marked_orphans: set[tuple[int, str]] = set()
    orphan_exes: dict[tuple[int, str], str] = {}
    pending: dict[tuple[int, str], float] = {}    # process -> when its environment was first wanted
    to_probe: list[tuple[int, str]] = []
    member_pids = 0
    unverified: list[dict] = []
    max_env_wait = 0.0

    def count(exe: str) -> None:
        if exe not in seen:
            seen[exe] = [0, time.strftime("%H:%M:%S"), classify_exe(exe, allowed)]
        seen[exe][0] += 1

    # Written atomically at every checkpoint and at the end: a census that is
    # killed with its rung keeps what it saw up to the last checkpoint, and says
    # `ended: running`, which is never read as a complete census.
    def write_census(state: str, gap: float) -> None:
        flagged = sorted(
            {exe for exe, row in seen.items() if row[2] not in ("ok", "FOREIGN-NONRUST")}
            | {row["exe"] for row in unverified if row["class"] not in ("ok", "FOREIGN-NONRUST")})
        tmp = out.with_name(out.name + ".tmp")
        tmp.write_text(json.dumps({
            "schema": SCHEMA, "kind": "process-census", "label": label, "iterations": iterations,
            "membership": "descendants of the watched build (kept while they live) and new orphans "
                          "carrying the rung's marker",
            "hit_cap": state == "cap", "ended": state, "elapsed_s": round(time.monotonic() - started, 1),
            "failed_samples": failed, "errors": errors, "max_gap_s": round(gap, 1),
            "long_gaps": long_gaps, "member_pids": member_pids,
            "environment_reads": env_reads, "environment_read_failures": env_failed,
            "max_environment_wait_s": round(max_env_wait, 1),
            "environments_unread": len(pending), "marked_orphans": len(marked_orphans),
            "unverified_orphans": unverified[:200], "abandoned_children": reap_abandoned(),
            "executables": [{"exe": exe, "samples": row[0], "first_seen": row[1], "class": row[2]}
                            for exe, row in sorted(seen.items(), key=lambda kv: -kv[1][0])],
            "environment": dict(sorted(envs.items())), "flagged": flagged,
            "driver_dylibs": {exe: dict(sorted(libs.items())) for exe, libs in sorted(dylibs.items())},
        }, indent=1) + "\n")
        os.replace(tmp, out)

    def read_pending() -> None:
        nonlocal env_reads, env_failed, max_env_wait
        batch = sorted(pending, key=pending.get)[:ENV_READ_BATCH]
        try:
            rows = read_environments([pid for pid, _started in batch])
        except Exception as error:  # noqa: BLE001 - retried next tick, its wait measured
            env_failed += 1
            if len(errors) < 20:
                errors.append(f"{time.strftime('%H:%M:%S')} environment read {type(error).__name__}: {error}"[:300])
            return
        env_reads += 1
        now = time.monotonic()
        for process in batch:
            max_env_wait = max(max_env_wait, now - pending.pop(process))
            # (A pid reused since it was listed would be read as the wrong process:
            # the next tick's listing re-reads start times, so that is caught there.)
            text = rows.get(process[0])
            if process in orphan_exes:
                exe = orphan_exes.pop(process)
                if text is None:
                    # Gone before it could be read: not shown to be the rung's, not
                    # shown not to be. Kept, classified, and flagged if it is Rust.
                    if len(unverified) < 1000:
                        unverified.append({"pid": process[0], "exe": exe, "at": time.strftime("%H:%M:%S"),
                                           "class": classify_exe(exe, allowed)})
                    continue
                if marker not in text:
                    continue
                marked_orphans.add(process)
                member_keys.add(process)
                count(exe)
            if text is None:
                continue
            for key in keys:
                at = text.find(f" {key}=")
                value = "<unset>" if at < 0 else text[at + len(key) + 2:].split(" ", 1)[0]
                envs[f"{key}={value}"] = envs.get(f"{key}={value}", 0) + 1

    while iterations < cap:
        try:
            os.kill(watched, 0)
        except OSError:
            ended = "watched-exited"
            break
        iterations += 1
        reap_abandoned()
        # A failed sample is a gap in the observation, never the end of it: it is
        # counted, the first errors are kept, and the gap it opens is measured.
        try:
            table = parse_tick(ps_listing(list(TICK_LISTING)))
            if watched not in table:
                raise RuntimeError(f"the watched build {watched} is missing from the listing")
            processes = {(pid, row[1]) for pid, row in table.items()}
            if baseline is None:
                baseline = processes - {(watched, table[watched][1])}
            # Membership: the tree under the build, and under every member (or marked
            # orphan) of the last listing that is still the same process.
            roots = {watched} | {pid for pid, started in member_keys & processes}
            members = rung_members(table, roots)
            member_keys = {(pid, table[pid][1]) for pid in members}
            for process in sorted(processes - known):
                pid = process[0]
                ppid, _started, exe = table[pid]
                if pid in members:
                    member_pids += 1
                    pending.setdefault(process, time.monotonic())
                    if os.path.basename(exe) in ("cargo", "targo"):
                        to_probe.append((pid, exe))
                elif ppid == 1 and process not in baseline:
                    orphan_exes[process] = exe
                    pending.setdefault(process, time.monotonic())
            known |= processes
            for pid in members:
                count(table[pid][2])
            now = time.monotonic()
            if now - last_ok > 30.0 and len(long_gaps) < 50:
                long_gaps.append({"at": time.strftime("%H:%M:%S"), "gap_s": round(now - last_ok, 1)})
            max_gap = max(max_gap, now - last_ok)
            last_ok = now
        except Exception as error:  # noqa: BLE001 - every failure is recorded, none ends the census
            failed += 1
            if len(errors) < 20:
                errors.append(f"{time.strftime('%H:%M:%S')} {type(error).__name__}: {error}"[:300])
            table = None
        # Off the tick's critical path: an environment read or a dylib probe that
        # stalls costs at most its bound, and what it did not read is retried.
        if table is not None and pending:
            read_pending()
        if to_probe:
            pid, exe = to_probe.pop(0)
            for lib in mapped_dylibs(str(pid)):
                dylibs.setdefault(exe, {})
                dylibs[exe][lib] = dylibs[exe].get(lib, 0) + 1
        if iterations % checkpoint_every == 0:
            write_census("running", max(max_gap, time.monotonic() - last_ok))
        time.sleep(interval)
    write_census(ended, max(max_gap, time.monotonic() - last_ok))


def census_is_complete(census: dict) -> bool:
    """The census watched the build to its end without a long blind spot."""
    return (census.get("ended") == "watched-exited"
            and isinstance(census.get("max_gap_s"), (int, float))
            and census["max_gap_s"] <= MAX_CENSUS_GAP_S)


def mapped_dylibs(pid: str) -> list[str]:
    """The non-OS shared libraries a live process has mapped (macOS: lsof)."""
    if platform.system() == "Linux":
        try:
            return linux_seed_support().mapped_libraries(int(pid))
        except (OSError, ValueError):
            return []  # unavailable observation; never a runtime closure receipt
    if platform.system() != "Darwin":
        return []
    try:
        out = census_output(["/usr/sbin/lsof", "-p", pid, "-Fn"]).decode("utf-8", errors="replace")
    except (OSError, subprocess.TimeoutExpired):
        return []
    return sorted({line[1:] for line in out.splitlines()
                   if line.startswith("n") and line.endswith(".dylib")
                   and not line[1:].startswith(SYSTEM_DYLIB_PREFIXES)})


def tool_identity() -> dict:
    """This script, by bytes, and the checkout it ran from: a rung record names the
    tool that wrote it."""
    here = Path(__file__).resolve()
    head = git(here.parent, "rev-parse", "HEAD")
    status = git(here.parent, "status", "--porcelain", "--", here.name)
    return {
        "path": str(here), "sha256": sha256_file(here),
        "checkout_head": head.stdout.strip() if head.returncode == 0 else None,
        "modified_in_checkout": bool(status.stdout.strip()) if status.returncode == 0 else None,
    }


def clean_lean_observation(worktree: Path, library: Path) -> dict:
    """What `run --clean-lean-lib` binds, by the mint's own rule.

    `mint_seed_support.clean_lean_inputs` accepts only the `lib/lean` of the exact
    installation the worktree's Clean pin names, with the Oracle world's olean
    headers, and binds every entry of that installation. `environment` is the two
    variables that function says select it; `manifest_sha256` is the sha256 of the
    file `mint_seed_support.py clean-lean-inputs --output` writes for the same
    arguments (`write_json_exclusive`'s bytes), so a record and a manifest written
    by that command can be joined by digest."""
    support = mint_support()
    if not library.is_absolute():
        raise Refusal(f"--clean-lean-lib {library} must be an absolute path: it is handed to the build as it is given")
    try:
        manifest = support.clean_lean_inputs(worktree, library)
    except (support.WorkflowError, OSError) as error:
        raise Refusal(f"--clean-lean-lib {library} is not the Lean library {worktree}'s Clean pin "
                      f"(first-party/clean/lean-toolchain) names: {error}") from error
    payload = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode("utf-8")
    return {"environment": dict(manifest["environment"]), "fingerprint": manifest["fingerprint"],
            "manifest_sha256": hashlib.sha256(payload).hexdigest()}


def run_rung(args: argparse.Namespace) -> dict:
    worktree = Path(args.worktree).resolve()
    ledger = Path(args.ledger).resolve()
    admission = json.loads(Path(args.stage0_admission).read_text())
    if admission.get("refusals") or admission.get("kind") != "stage0-admission":
        raise Refusal(f"{args.stage0_admission} is not a clean stage0 admission")
    if platform.system() == "Linux":
        try:
            linux_seed_support().unchanged(admission.get("dylib_closure") or {})
        except (ValueError, OSError) as error:
            raise Refusal(f"Linux stage0 runtime admission refused: {error}") from error
    # `--clean-lean-lib`: judged before anything is written or started, so a
    # library the pin does not name costs no build.
    lean_library = Path(args.clean_lean_lib) if getattr(args, "clean_lean_lib", None) else None
    lean_before = clean_lean_observation(worktree, lean_library) if lean_library is not None else None
    # `--fifo-jobserver`: the job count, the path and the make, judged before anything is written.
    fifo = fifo_jobserver_preflight(worktree, ledger, args.xpy,
                                    [Path(d).resolve() for d in getattr(args, "tool_dir", [])]) \
        if getattr(args, "fifo_jobserver", False) else None
    compat = [Path(d).resolve() for d in args.compat_lib]
    ledger.mkdir(parents=True, exist_ok=True)
    logs = ledger / "logs"
    logs.mkdir(exist_ok=True)
    trap_log = ledger / "trap.log"
    trap_log.touch()
    write_traps(ledger / "trap", trap_log)
    for attempt in range(args.memory_wait_minutes * 2 + 1):
        gib = available_gib()
        if gib >= args.min_available_gib:
            break
        if attempt == args.memory_wait_minutes * 2:
            raise Refusal(f"memory gate: {gib} GiB available after {args.memory_wait_minutes} min (< {args.min_available_gib})")
        print(f"memory gate: {gib} GiB available, waiting", file=sys.stderr)
        time.sleep(30)
    python_bin = python311()
    head = git(worktree, "rev-parse", "HEAD").stdout.strip()
    commit_time = git(worktree, "log", "-1", "--format=%ct", "HEAD").stdout.strip()
    tool_dirs = [Path(d).resolve() for d in getattr(args, "tool_dir", [])]
    tool_dirs_before = tool_dir_record(tool_dirs)
    env = scrubbed_env(ledger, args.label, compat, python_bin, source_date_epoch=commit_time,
                       tool_dirs=tool_dirs, offline=bool(getattr(args, "offline", False)),
                       clean_lean=lean_before["environment"] if lean_before else None,
                       makeflags=fifo_jobserver_makeflags(fifo["path"], fifo["jobs"]) if fifo else None)
    # `--fifo-jobserver`'s make adapter goes first on PATH (pathbin); a run without it
    # reaches the make it always reached.
    adapter = install_make_adapter(ledger, python_bin, fifo["make"]) if fifo else remove_make_adapter(ledger)
    record: dict = {
        "schema": SCHEMA, "kind": "rung", "label": args.label, "worktree": str(worktree),
        "tool": tool_identity(),
        "commit": head, "argv": ["x.py", *args.xpy], "available_gib_at_start": gib,
        "python": python_bin, "environment": env, "tool_dirs": tool_dirs_before,
        "stage0_commit": admission.get("commit"), "stage0_sha256": admission.get("sha256"),
        "stage0_compat": (admission.get("dylib_closure") or {}).get("compat", []),
        "start": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
    }
    if lean_before is not None:
        record["clean_lean"] = {"library": str(lean_library),
                                "before": {key: lean_before[key] for key in ("fingerprint", "manifest_sha256")}}
    # Read before x.py starts: what the configuration hands the build as stage0.
    record["config_tools"] = config_tools_record(worktree, args.xpy, admission, args.seed_mode)
    before = len(trap_log.read_text().splitlines())
    log = logs / f"{args.label}.log"

    # x.py runs in its own session (so a terminal's ^C reaches it only through
    # here); a stop request is forwarded to the whole build, which then ends
    # with the process census still running and its record still written. A
    # build that outlives the request by the grace period is killed (measured
    # 2026-10-01: a SIGTERM that reached x.py while its python layer was
    # extracting the seed left it hung tearing down its multiprocessing pool, and
    # the tool waited on it indefinitely). The handlers are in place before the
    # FIFO jobserver is made, so a request from then on never ends this process
    # on the spot with the FIFO left behind: one that comes before x.py is started
    # starts nothing, and one that comes while it is being started reaches it as
    # soon as it is.
    stop: dict = {}
    child = None

    def request_stop(signum: int, reason: str) -> None:
        if not stop:
            stop.update({"signal": signal.Signals(signum).name, "reason": reason,
                         "requested_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
                         "_since": time.monotonic()})
        if child is None:
            return
        try:
            os.killpg(child.pid, signum)
        except ProcessLookupError:
            pass

    for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        signal.signal(signum, lambda signum, _frame: request_stop(signum, "stop request"))
    # `--fifo-jobserver`: made and filled now, held open until x.py and its census
    # have ended, then counted and removed (FifoJobserver); a run without it is
    # what it always was.
    held = FifoJobserver(fifo["path"], fifo["jobs"], fifo["source"]) if fifo else None
    if held is not None:
        held.record["make_adapter"] = adapter
    try:
        if stop:
            raise Refusal(f"a {stop['signal']} reached this run before x.py was started, so x.py was not started "
                          f"and no record was written. The ledger {ledger} keeps what was written before (its trap "
                          "shims, pathbin and logs); run this again to build")
        with open(log, "wb") as handle:
            child = subprocess.Popen([python_bin, "x.py", *args.xpy], cwd=worktree, env=env,
                                     stdout=handle, stderr=subprocess.STDOUT, start_new_session=True)
        if stop:
            try:
                os.killpg(child.pid, signal.Signals[stop["signal"]])
            except ProcessLookupError:
                pass
        census_path = logs / f"{args.label}.processes.json"
        sampler = subprocess.Popen([
            sys.executable, os.path.realpath(__file__), "_sample", args.label, str(child.pid),
            # Rust tools may run from the rung's own tree (stage0 extraction, the stages,
            # build scripts), from the admitted stage0, or be a declared compat library.
            str(census_path), ":".join([str(worktree), str(admission.get("stage0", "")), *map(str, compat)]),
        ])
        started = time.time()

        # A build the census no longer watches produces no evidence, so it is not
        # left running: when the sampler dies first, the build is stopped (and can be
        # resumed under a new label) instead of compiling for hours unobserved.
        sampler_died = None
        while True:
            try:
                rc = child.wait(timeout=5)
                break
            except subprocess.TimeoutExpired:
                pass
            if sampler_died is None and sampler.poll() is not None:
                sampler_died = time.strftime("%Y-%m-%dT%H:%M:%S%z")
                print(f"seed staircase: the process census exited ({sampler.returncode}) while the "
                      "build runs; stopping the build", file=sys.stderr)
                request_stop(signal.SIGTERM, "the process census exited")
            if (stop and "escalated_to_sigkill_at" not in stop
                    and time.monotonic() - stop["_since"] > args.stop_grace_seconds):
                stop["escalated_to_sigkill_at"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
                print(f"seed staircase: the build outlived its {stop['signal']} by "
                      f"{args.stop_grace_seconds:g} s; killing its session", file=sys.stderr)
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        sampler.wait()
    finally:
        if held is not None:
            record["jobserver"] = held.release()
    trap_hits = trap_log.read_text().splitlines()[before:]
    record.update({
        "end": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "rc": rc,
        "elapsed_s": int(time.time() - started), "log": str(log),
        "trap_hits": trap_hits,
    })
    if sampler_died is not None:
        record["sampler_died"] = {"at": sampler_died, "rc": sampler.returncode}
    if stop:
        record["stop"] = {key: value for key, value in stop.items() if not key.startswith("_")}
    try:
        record["process_census"] = json.loads(census_path.read_text())
    except (OSError, ValueError):
        record["process_census"] = {"error": "no census written"}
    build = worktree / "build"
    # The only commits the build may name: its own source and its stage0's.
    record["build_census"] = scan_build(build, worktree, {head, admission.get("commit")})
    # Which stage0 the build actually ran. In seed mode x.py materializes the
    # pinned archives in-tree; otherwise the config names the admitted directory,
    # which must still hold the admitted bytes after the build.
    host = host_triple()
    observed_root = build / host / "stage0" if args.seed_mode else Path(admission["stage0"])
    observed = sysroot_files(observed_root) if observed_root.is_dir() else {}
    record["stage0_observed"] = {"root": str(observed_root), "sha256": observed}
    record["stage0_matches_admission"] = bool(compiler_bytes(observed)) and (
        compiler_bytes(observed) == compiler_bytes(admission.get("sha256") or {}))
    try:
        record["tool_dirs_unchanged"] = tool_dir_record(tool_dirs) == tool_dirs_before
    except Refusal as error:
        record["tool_dirs_unchanged"] = False
        record["tool_dirs_refusal"] = str(error)
    record["stage0_runtime_unchanged"] = True
    if platform.system() == "Linux":
        try:
            linux_seed_support().unchanged(admission["dylib_closure"])
        except (ValueError, OSError) as error:
            record["stage0_runtime_unchanged"] = False
            record["stage0_runtime_refusal"] = str(error)
    stage2 = build / host / "stage2"
    if rc == 0 and stage2.is_dir():
        record["produced"] = {"stage2": str(stage2), "sha256": sysroot_files(stage2)}
    if lean_before is not None:
        # Recorded, and not part of no_stock_evidence, which says what it always
        # said: whoever asked for a pinned library reads `unchanged`.
        try:
            lean_after = clean_lean_observation(worktree, lean_library)
            record["clean_lean"]["after"] = {key: lean_after[key] for key in ("fingerprint", "manifest_sha256")}
        except Refusal as error:
            record["clean_lean"]["after"] = {"refusal": str(error)}
        record["clean_lean"]["unchanged"] = record["clean_lean"]["after"] == record["clean_lean"]["before"]
    record["no_stock_evidence"] = (
        not trap_hits
        and "sampler_died" not in record
        and not record["process_census"].get("flagged")
        and census_is_complete(record["process_census"])
        and record["build_census"]["clean"]
        and record["stage0_matches_admission"]
        and record["stage0_runtime_unchanged"]
        and record["config_tools"]["matches_admission"]
        and record["tool_dirs_unchanged"]
    )
    with open(ledger / "rungs.jsonl", "a") as handle:
        handle.write(json.dumps(record, sort_keys=True) + "\n")
    return record


# ---------------------------------------------------------------------------
# the lineage record (with the pack cut's double-compile comparison)


@functools.lru_cache(maxsize=None)
def mint_support():
    """scripts/mint_seed_support.py: the ONE stage2-tree comparator the pack cut
    (mint_and_prove_seed.sh) also uses, so a staircase DDC and a pack-cut DDC
    can never disagree about what 'identical' means."""
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "mint_seed_support", Path(__file__).resolve().with_name("mint_seed_support.py"))
    module = importlib.util.module_from_spec(spec)
    sys.modules.setdefault("mint_seed_support", module)
    spec.loader.exec_module(module)
    return module


# What a double compile must hold identical (plan W12): the compiler (trustc, its
# driver, the codegen backends it loads) and every library the sysroot ships.
DDC_KEY_RE = re.compile(
    r"bin/(trustc|rustc)"
    r"|lib/librustc_driver-[^/]+"
    r"|lib/rustlib/[^/]+/lib/[^/]+\.(rlib|rmeta|dylib|so)"
    r"|lib/rustlib/[^/]+/codegen-backends/[^/]+"
)


def ddc_record(staircase_manifest: Path, ddc_manifest: Path, ddc_seed: dict, repo: Path) -> dict:
    """Compare two `mint_seed_support.py stage2-manifest` trees of one commit,
    both built at one path with one cargo driving: one from the staircase
    lineage, one with an independent compiler. Byte identity of the compiler and
    std means the staircase ancestry did not steer those bytes (Wheeler's DDC,
    within what the two builds share). Every other difference is listed."""
    if ddc_seed.get("refusals"):
        raise Refusal("the DDC seed admission carries refusals")
    support = mint_support()
    staircase = json.loads(staircase_manifest.read_text())
    independent = json.loads(ddc_manifest.read_text())
    differences = support.ddc_differences(staircase, independent)
    keyed = lambda records: sorted(r["path"] for r in records if DDC_KEY_RE.fullmatch(r["path"]))
    key_paths = keyed(staircase.get("records", []))
    if key_paths != keyed(independent.get("records", [])):
        key_differences = ["the two trees ship different compiler/std entries"]
    else:
        key_differences = [d for d in differences if DDC_KEY_RE.fullmatch(d.split(": ", 1)[1])]
    if not any(p.startswith("bin/trustc") for p in key_paths) or not any(".rlib" in p for p in key_paths):
        key_differences.append("no compiler or no std in the compared trees (a vacuous comparison)")
    if not differences and not key_differences:
        verdict = "identical"
    elif not key_differences:
        verdict = "compiler-and-std-identical"
    else:
        verdict = "different"
    # The pack cut's own classifier (mint_seed_support DDC_RELATIONS) names how the
    # independent compiler relates to the src/stage0 pin.
    relation = support.ddc_seed_identity(repo.resolve(strict=True), Path(ddc_seed["stage0"]))["relation"]
    return {
        "relation": relation,
        "relation_meaning": support.DDC_RELATIONS.get(relation),
        "ddc_seed": {k: ddc_seed.get(k) for k in ("commit", "trustc_vV", "sha256", "stage0")},
        "stage2_tree_sha256_staircase": staircase.get("sha256"),
        # What binds this comparison to the stage2 being sealed, and the other side
        # to the independent compiler's build (`lineage` checks both).
        "staircase_identity": manifest_identity(staircase),
        "ddc_identity": manifest_identity(independent),
        "stage2_tree_sha256_ddc_seed": independent.get("sha256"),
        "compared_records": len(staircase.get("records", [])),
        "compiler_and_std_entries": len(key_paths),
        "differences": differences[:400],
        "difference_count": len(differences),
        "compiler_and_std_differences": key_differences,
        "verdict": verdict,
    }


def stage2_identity(stage2: Path, repo: Path) -> dict:
    drivers = sorted(stage2.glob("lib/librustc_driver-*"))
    if len(drivers) != 1:
        raise Refusal(f"{stage2} ships {len(drivers)} librustc_driver files")
    vv = parse_vv(run_tool([str(stage2 / "bin" / "trustc"), "-vV"]))
    commit = commit_in_repo(repo, vv.get("commit-hash", ""))
    if not commit:
        raise Refusal(f"{stage2}/bin/trustc names no commit of {repo}")
    return {"commit": commit, "version_line": vv.get("version_line"),
            "trustc_sha256": sha256_file(stage2 / "bin" / "trustc"),
            "driver": drivers[0].name, "driver_sha256": sha256_file(drivers[0]),
            "cargo_sha256": sha256_file(stage2 / "bin" / "cargo") if (stage2 / "bin" / "cargo").is_file() else None,
            "sha256": sysroot_files(stage2)}


def fold_invocations(records: list[dict]) -> list[list[dict]]:
    """Group rung records into rungs. Consecutive records of one worktree, commit
    and stage0 (by bytes) are invocations of ONE rung: an interrupted build that
    was resumed in place. Only the last of them has to succeed."""
    rungs: list[list[dict]] = []
    last_key = None
    for record in records:
        key = (record.get("worktree"), record.get("commit"),
               json.dumps(compiler_bytes(record.get("stage0_sha256") or {}), sort_keys=True))
        if rungs and key == last_key:
            rungs[-1].append(record)
        else:
            rungs.append([record])
        last_key = key
    return rungs


def build_lineage(root_admission: dict, records: list[dict], final_stage2: Path, repo: Path,
                  ddc: dict | None) -> dict:
    """Chain the rungs from the admitted root seed to the final stage2, by commit
    AND by bytes: each rung's stage0 must be the exact compiler (trustc, driver,
    driving cargo) the previous rung produced (the root's admitted seed for the
    first), the build must have run that stage0, and the final stage2 must be the
    last rung's output. A same-commit compiler of another lineage cannot stand in."""
    if root_admission.get("refusals"):
        raise Refusal("the root seed admission carries refusals")
    root_commit = root_admission.get("commit", "")
    if not commit_in_repo(repo, root_commit):
        raise Refusal(f"root seed commit {root_commit!r} is not a commit of {repo}")
    require_pinned_root(root_admission, repo)
    # A pinned root (set only on Linux, by `admit`) is admitted by a host record
    # in the seed ledger; the lineage says which kind, and what it discloses.
    pin_admission = (pinned_root_admission(repo, host_triple())
                     if "pinned_seed" in root_admission else None)
    if not records:
        raise Refusal("a lineage needs at least one rung")
    previous_commit, previous_bytes = root_commit, compiler_bytes(root_admission.get("sha256") or {})
    if not previous_bytes:
        raise Refusal("the root seed admission records no compiler bytes")
    rungs = []
    for invocations in fold_invocations(records):
        last = invocations[-1]
        label, commit = last.get("label"), last.get("commit", "")
        if last.get("rc") != 0:
            raise Refusal(f"rung {label} did not succeed (rc {last.get('rc')})")
        for invocation in invocations:
            name = invocation.get("label")
            if invocation.get("stage0_commit") != previous_commit:
                raise Refusal(f"rung {name} was built by {invocation.get('stage0_commit')}, not by the previous rung {previous_commit}")
            if compiler_bytes(invocation.get("stage0_sha256") or {}) != previous_bytes:
                raise Refusal(f"rung {name}'s stage0 is not the compiler the previous rung produced (bytes differ)")
            if not invocation.get("stage0_matches_admission"):
                raise Refusal(f"rung {name} did not run its admitted stage0 (stage0_observed differs or is missing)")
            if not invocation.get("no_stock_evidence"):
                raise Refusal(f"rung {name} carries no clean no-stock evidence")
            require_compiler_record(invocation, f"rung {name}")
            # Records written before `config_tools` existed carry no reading of the
            # configuration; the lineage says so instead of inventing one.
            config = invocation.get("config_tools")
            if config is not None and not config.get("matches_admission"):
                raise Refusal(f"rung {name}'s configuration does not hand x.py its admitted stage0: "
                              + "; ".join(config.get("problems") or ["unknown"]))
        if not is_ancestor(repo, previous_commit, commit):
            raise Refusal(f"rung {label} goes backward ({previous_commit[:10]} is not an ancestor of {commit[:10]})")
        produced = compiler_bytes((last.get("produced") or {}).get("sha256") or {})
        if not produced:
            raise Refusal(f"rung {label} records no produced stage2")
        unread = [i.get("label") for i in invocations if i.get("config_tools") is None]
        rungs.append({"label": label, "commit": commit, "invocations": invocations,
                      "configuration_evidence": (
                          f"not recorded by invocation(s) {', '.join(map(str, unread))} (record predates config_tools); "
                          "the stage0 the build ran is still bound by stage0_observed and the process census"
                          if unread else "recorded for every invocation")})
        previous_commit, previous_bytes = commit, produced
    final = stage2_identity(final_stage2, repo)
    if final["commit"] != previous_commit:
        raise Refusal(f"final stage2 is {final['commit'][:10]}, but the last rung built {previous_commit[:10]}")
    if compiler_bytes(final["sha256"]) != previous_bytes:
        raise Refusal(f"{final_stage2} is not the stage2 the last rung produced (bytes differ)")
    history = git(repo, "log", "--format=%H %cI", "-G^compiler_git_commit_hash=", "--", "src/stage0")
    record = {
        "schema": SCHEMA, "kind": "lineage",
        "root": {
            "commit": root_commit, "admission": root_admission,
            # What git records about how the root itself was made: the commits that
            # changed the src/stage0 pin (the seed chain's claimed history). Claimed,
            # not attested: no receipt says which stage0 built the root.
            "src_stage0_pin_changes": history.stdout.split("\n")[:-1] if history.returncode == 0 else [],
            **({"pin_admission": pin_admission} if pin_admission is not None else {}),
        },
        "rungs": rungs, "final": final,
    }
    if ddc is not None:
        # A double compile of some other tree says nothing about this one: the
        # staircase side of the comparison must be the final stage2, byte for byte.
        if not final["sha256"] or ddc.get("staircase_identity") != final["sha256"]:
            raise Refusal("the double compile's staircase tree is not the final stage2 "
                          "(its identity files differ from the ones being sealed)")
        check_ddc_build(ddc, final, rungs[-1]["invocations"][-1], root_admission, records)
        record["ddc"] = ddc
    return record


def require_compiler_record(record: dict, name: str) -> None:
    """A build whose census read no .rustc_info.json never recorded which compiler
    cargo saw (measured 2026-10-01: RUSTUP_HOME beside the rustup sentinel made
    cargo write none in a twelve-hour rung, and its census still said clean)."""
    if not (record.get("build_census") or {}).get("rustc_info_files"):
        raise Refusal(f"{name}'s build census read no .rustc_info.json: which compiler cargo saw is unrecorded")


def check_ddc_build(ddc: dict, final: dict, last: dict, root_admission: dict, records: list[dict]) -> None:
    """The other side of a double compile must be what the independent compiler
    built, held to the rung's own standard. Without this a manifest of any tree —
    the staircase's own, copied — compares `identical` to the staircase and
    proves nothing."""
    run = ddc.get("run")
    if run is None:
        raise Refusal("a double compile needs the independent compiler's build record (--ddc-run)")
    label = run.get("label")
    if run.get("rc") != 0 or run.get("commit") != final["commit"]:
        raise Refusal(f"the DDC build {label} is not a successful build of {final['commit'][:10]}")
    # Build-directory paths reach the compiler's bytes; the comparison holds only
    # for two builds at one path.
    if run.get("worktree") != last.get("worktree"):
        raise Refusal(f"the DDC build {label} ran in {run.get('worktree')}, not where the last rung "
                      f"built ({last.get('worktree')})")
    seed = ddc.get("ddc_seed") or {}
    if (not seed.get("sha256") or run.get("stage0_commit") != seed.get("commit")
            or run.get("stage0_sha256") != seed.get("sha256") or not run.get("stage0_matches_admission")):
        raise Refusal(f"the DDC build {label} did not run the admitted independent compiler")
    if not run.get("no_stock_evidence"):
        raise Refusal(f"the DDC build {label} carries no clean no-stock evidence")
    require_compiler_record(run, f"the DDC build {label}")
    if not ddc.get("ddc_identity") or ddc["ddc_identity"] != (run.get("produced") or {}).get("sha256"):
        raise Refusal("the double compile's independent tree is not the stage2 the DDC build produced")
    # Diverse means another compiler: not the root seed, not a rung's stage0,
    # not the compiler being sealed (that is a reproducibility control).
    independent = seed["sha256"].get("bin/trustc")
    chain = [root_admission.get("sha256") or {}, final["sha256"],
             *[r.get("stage0_sha256") or {} for r in records]]
    if not independent or any(independent == ids.get("bin/trustc") for ids in chain):
        raise Refusal("the independent compiler is a compiler of the staircase lineage itself, not a diverse one")


# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    if argv and argv[0] == "_sample":
        label, watched, out, allowed = argv[1:5]
        sample_processes(label, int(watched), Path(out), [a for a in allowed.split(":") if a], 1.0, 172800)
        return 0
    parser = argparse.ArgumentParser(prog="seed_staircase.py", description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("admit")
    p.add_argument("stage0")
    p.add_argument("--repo", required=True)
    p.add_argument("--target")
    p.add_argument("--compat-lib", action="append", default=[])
    p = sub.add_parser("seed-sysroot")
    p.add_argument("--payloads", required=True)
    p.add_argument("--stage0-file", required=True)
    p.add_argument("--out", required=True)
    p = sub.add_parser("libgit2-compat")
    p.add_argument("--crate", required=True)
    p.add_argument("--lock", required=True)
    p.add_argument("--out", required=True)
    p = sub.add_parser("seed-config")
    p.add_argument("--worktree", required=True)
    p.add_argument("--llvm-config")
    p = sub.add_parser("config")
    p.add_argument("--base", required=True)
    p.add_argument("--stage0", required=True)
    p.add_argument("--out", required=True)
    p = sub.add_parser("run")
    p.add_argument("--worktree", required=True)
    p.add_argument("--label", required=True)
    p.add_argument("--ledger", required=True)
    p.add_argument("--compat-lib", action="append", default=[])
    p.add_argument("--stage0-admission", required=True, help="`admit` output for this rung's stage0")
    p.add_argument("--tool-dir", action="append", default=[],
                   help="a directory of non-Rust build tools the OS lacks (e.g. a user-installed "
                        "ninja), appended to the rung's PATH after the OS directories; every entry "
                        "is recorded by real path and sha256 and refused if it is a Rust tool name "
                        "or resolves into a stock root; repeatable")
    p.add_argument("--min-available-gib", type=int, default=24)
    p.add_argument("--memory-wait-minutes", type=int, default=60)
    p.add_argument("--stop-grace-seconds", type=float, default=60.0,
                   help="after a stop request, how long the build may take to end before its session is killed")
    p.add_argument("--seed-mode", action="store_true",
                   help="x.py materializes stage0 in-tree from src/stage0 (no [build] compiler keys); "
                        "the in-tree stage0 must then be byte-identical to the admitted one")
    p.add_argument("--offline", action="store_true",
                   help="add CARGO_NET_OFFLINE=true to the rung's environment: the build resolves every "
                        "crate from the ledger's cargo home or fails")
    p.add_argument("--clean-lean-lib", metavar="DIR",
                   help="the absolute <installation>/lib/lean of the Lean toolchain the worktree's Clean pin "
                        "names: sets CLEAN_OLEAN_PINNED_LEAN_LIB and CLEAN_OLEAN_REQUIRE_PINNED_LEAN=1 once "
                        "mint_seed_support.clean_lean_inputs accepts it, and records its fingerprint and "
                        "manifest digest before and after the build under `clean_lean`")
    p.add_argument("--fifo-jobserver", action="store_true",
                   help="hand x.py a FIFO jobserver: <ledger>/tmp/jobserver.fifo (mode 0600) preloaded with N-1 "
                        "tokens for the job count N x.py runs with (its -j, else [build] jobs of its configuration; "
                        "refused when neither names one), held open until x.py exits and then removed, advertised as "
                        "MAKEFLAGS=\"-jN --jobserver-auth=fifo:PATH\", with <ledger>/pathbin/make an adapter that "
                        "hands the host's make (before 4.4 it cannot read fifo:) the FIFO as two descriptors; the "
                        "record's `jobserver` names both and the tokens the FIFO held at the end")
    p.add_argument("xpy", nargs=argparse.REMAINDER)
    p = sub.add_parser("scan")
    p.add_argument("--build-dir", required=True)
    p.add_argument("--repo", required=True)
    p.add_argument("--allow-commit", action="append",
                   help="a commit the build may name (its source, its stage0); repeatable. "
                        "Without it any commit in the repository's history passes.")
    p = sub.add_parser("lineage")
    p.add_argument("--root-admission", required=True, help="`admit` output for the pinned seed")
    p.add_argument("--rung", action="append", required=True, help="a rung record (JSON), in order")
    p.add_argument("--final-stage2", required=True)
    p.add_argument("--repo", required=True)
    p.add_argument("--ddc-manifests", nargs=2, metavar=("STAIRCASE", "DDC"),
                   help="`mint_seed_support.py stage2-manifest` of the final commit built from the "
                        "staircase and from an independent compiler, at the same path")
    p.add_argument("--ddc-seed-admission", help="`admit` output for the independent compiler")
    p.add_argument("--ddc-run", help="the `run` record of the independent compiler's build (required with "
                                     "--ddc-manifests; bound to the DDC manifest and seed, recorded verbatim)")
    args = parser.parse_args(argv)
    try:
        if args.command == "admit":
            target = None
            if args.target:
                target = commit_in_repo(Path(args.repo), args.target)
                if not target:
                    raise Refusal(f"--target {args.target} is not a commit in {args.repo}")
            result = admit(Path(args.stage0), Path(args.repo), target, [Path(d) for d in args.compat_lib])
        elif args.command == "seed-sysroot":
            result = seed_sysroot(Path(args.payloads), Path(args.stage0_file), Path(args.out))
        elif args.command == "libgit2-compat":
            result = libgit2_compat(Path(args.crate), Path(args.lock), Path(args.out))
        elif args.command == "seed-config":
            result = write_seed_config(Path(args.worktree).resolve(), args.llvm_config)
        elif args.command == "config":
            write_rung_config(Path(args.base), Path(args.stage0).resolve(), Path(args.out))
            result = {"schema": SCHEMA, "kind": "rung-config", "config": args.out}
        elif args.command == "run":
            if args.xpy and args.xpy[0] == "--":
                args.xpy = args.xpy[1:]
            if not args.xpy:
                parser.error("run needs x.py arguments after --")
            result = run_rung(args)
        elif args.command == "lineage":
            ddc = None
            if args.ddc_manifests:
                if not args.ddc_seed_admission or not args.ddc_run:
                    parser.error("--ddc-manifests needs --ddc-seed-admission and --ddc-run")
                ddc = ddc_record(Path(args.ddc_manifests[0]), Path(args.ddc_manifests[1]),
                                 json.loads(Path(args.ddc_seed_admission).read_text()), Path(args.repo))
                ddc["run"] = json.loads(Path(args.ddc_run).read_text())
            result = build_lineage(
                json.loads(Path(args.root_admission).read_text()),
                [json.loads(Path(r).read_text()) for r in args.rung],
                Path(args.final_stage2), Path(args.repo), ddc,
            )
        else:
            allowed = None
            if args.allow_commit:
                allowed = set()
                for commit in args.allow_commit:
                    full = commit_in_repo(Path(args.repo), commit)
                    if not full:
                        raise Refusal(f"--allow-commit {commit} is not a commit in {args.repo}")
                    allowed.add(full)
            result = scan_build(Path(args.build_dir), Path(args.repo), allowed)
    except Refusal as refusal:
        print(json.dumps({"schema": SCHEMA, "refused": str(refusal)}, indent=1))
        return 1
    print(json.dumps(result, indent=1, sort_keys=True))
    if result.get("refusals") or (args.command == "scan" and not result["clean"]):
        return 1
    if args.command == "lineage" and (result.get("ddc") or {}).get("verdict", "identical") not in (
            "identical", "compiler-and-std-identical"):
        return 1
    if args.command == "run" and result.get("rc") != 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
