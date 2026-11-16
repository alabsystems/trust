#!/usr/bin/env python3
"""Fail-closed support code for ``mint_and_prove_seed.sh``.

The shell entry point owns the long-running build.  This helper keeps the
security-sensitive filesystem work in one place: canonical metadata parsing,
exact dist-artifact admission, bounded archive extraction, temporary bootstrap
configuration, and construction of a PATH that cannot resolve ambient
Rust-family frontends by their public names.
"""

from __future__ import annotations

import argparse
import errno
import hashlib
import importlib.util
import io
import json
import os
import platform
import posixpath
import re
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile
import textwrap
import time
from pathlib import Path, PurePosixPath
from types import SimpleNamespace
from typing import BinaryIO, Iterable


# Trust: load the extraction-key owner by path, including under isolated -I -S.
_IDENTITY_PATH = Path(__file__).resolve().parents[1] / "src/bootstrap/stage0_identity.py"
if "__trust_source_loader__" in globals():
    # Keep the authenticated source graph closed over this transitive owner.
    _IDENTITY_OWNER = __trust_source_loader__.module("trust_stage0_identity", _IDENTITY_PATH)
else:
    _IDENTITY_SPEC = importlib.util.spec_from_file_location("trust_stage0_identity", _IDENTITY_PATH)
    _IDENTITY_OWNER = importlib.util.module_from_spec(_IDENTITY_SPEC)
    _IDENTITY_SPEC.loader.exec_module(_IDENTITY_OWNER)
stage0_extraction_stamp = _IDENTITY_OWNER.extraction_stamp

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - supported builders use 3.11+.
    try:
        # scripts/check_seed_freshness.py reads configs through this module and
        # may run on an older python3 that has the backport; the mint runs
        # under -I -S on 3.11+, where it is never needed.
        import tomli as tomllib  # type: ignore[no-redef]
    except ModuleNotFoundError:
        tomllib = None  # type: ignore[assignment]


COMPONENTS = ("trust-std", "trustc", "trustc-dev", "targo", "trustfmt")
SEED_COMPONENTS = (
    "targo", "targo-trust", "tippy", "trust-analyzer", "trust-src",
    "trust-std", "trustc", "trustc-dev", "trustfmt",
)
SEMVER_RE = re.compile(
    r"(?:0|[1-9][0-9]*)\."
    r"(?:0|[1-9][0-9]*)\."
    r"(?:0|[1-9][0-9]*)"
    r"(?:-(?:0|[1-9][0-9]*|[0-9A-Za-z-]*[A-Za-z-][0-9A-Za-z-]*)"
    r"(?:\.(?:0|[1-9][0-9]*|[0-9A-Za-z-]*[A-Za-z-][0-9A-Za-z-]*))*)?"
    r"(?:\+[0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*)?"
)
HOST_RE = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_.-]{2,127}")
COMMIT_RE = re.compile(r"[0-9a-f]{40,64}")
# `targo --version --verbose` keys that list independent software capabilities, one
# line each (src/tools/targo/src/bin/cargo/cli.rs). They grant no pair authority, so
# the seed pair reader skips them; every other key is scalar identity and may appear
# once. scripts/tests/seed_native_pair_test.py derives the keys targo repeats from
# that source and requires each to be named here.
TARGO_REPEATABLE_CAPABILITIES = frozenset({"cache-integrity", "freshness"})
SHA256_RE = re.compile(r"[0-9a-f]{64}")
DATE_RE = re.compile(r"[0-9]{4}-[0-9]{2}-[0-9]{2}")
MAX_METADATA_BYTES = 4096
MAX_CONFIG_BYTES = 4 * 1024 * 1024
MAX_CONFIG_FILES = 64
MAX_ARCHIVE_MEMBERS = 2_000_000
MAX_UNPACKED_BYTES = 64 * 1024 * 1024 * 1024
MAX_TOTAL_ARCHIVE_BYTES = 32 * 1024 * 1024 * 1024
MAX_TOTAL_UNPACKED_BYTES = 64 * 1024 * 1024 * 1024
MAX_MEMBER_PATH_BYTES = 4096
COPY_CHUNK = 1024 * 1024


class WorkflowError(RuntimeError):
    pass


def fail(message: str) -> "NoReturn":
    raise WorkflowError(message)


def canonical_regular_file(path: Path, description: str) -> Path:
    try:
        before = path.lstat()
    except OSError as exc:
        fail(f"{description} is unavailable: {path}: {exc}")
    if stat.S_ISLNK(before.st_mode) or not stat.S_ISREG(before.st_mode):
        fail(f"{description} must be a non-symlink regular file: {path}")
    try:
        resolved = path.resolve(strict=True)
        after = resolved.stat()
    except OSError as exc:
        fail(f"cannot canonicalize {description}: {path}: {exc}")
    if (before.st_dev, before.st_ino) != (after.st_dev, after.st_ino):
        fail(f"{description} changed identity while it was resolved: {path}")
    return resolved


def canonical_directory(path: Path, description: str, *, stock_oracle: bool = False) -> Path:
    """A real directory, never inside a stock toolchain tree -- except, with
    `stock_oracle`, a rustup toolchain's own sysroot: the DDC seed that anchors
    the seed chain (STOCK-AS-ORACLE, docs/DECISION_QUEUE.md D16). It compiles
    only the comparison build; nothing it builds ships."""
    try:
        before = path.lstat()
    except OSError as exc:
        fail(f"{description} is unavailable: {path}: {exc}")
    if stat.S_ISLNK(before.st_mode) or not stat.S_ISDIR(before.st_mode):
        fail(f"{description} must be a non-symlink directory: {path}")
    try:
        resolved = path.resolve(strict=True)
        after = resolved.stat()
    except OSError as exc:
        fail(f"cannot canonicalize {description}: {path}: {exc}")
    if (before.st_dev, before.st_ino) != (after.st_dev, after.st_ino):
        fail(f"{description} changed identity while it was resolved: {path}")
    if forbidden_tool_path(resolved) and not (stock_oracle and stock_toolchain_sysroot(resolved)):
        fail(f"{description} resolves through a forbidden stock-toolchain tree: {resolved}")
    if os.pathsep in str(resolved) or "\n" in str(resolved) or "\r" in str(resolved):
        fail(f"{description} cannot be represented safely in LIBRARY_PATH: {resolved}")
    return resolved


def read_bounded_text(path: Path, description: str) -> str:
    canonical_regular_file(path, description)
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    fd = os.open(path, flags)
    try:
        before = os.fstat(fd)
        if before.st_size > MAX_METADATA_BYTES:
            fail(f"{description} exceeds {MAX_METADATA_BYTES} bytes: {path}")
        raw = os.read(fd, MAX_METADATA_BYTES + 1)
        after = os.fstat(fd)
    finally:
        os.close(fd)
    if len(raw) > MAX_METADATA_BYTES:
        fail(f"{description} exceeds {MAX_METADATA_BYTES} bytes: {path}")
    if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
    ):
        fail(f"{description} changed while it was read: {path}")
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        fail(f"{description} is not UTF-8: {path}: {exc}")


def canonical_version(root: Path) -> str:
    value = read_bounded_text(root / "src" / "version", "source version").strip()
    if not SEMVER_RE.fullmatch(value):
        fail(f"src/version is not canonical SemVer: {value!r}")
    return value


def canonical_host(value: str) -> str:
    if not HOST_RE.fullmatch(value):
        fail(f"host triple is not canonical: {value!r}")
    return value


def native_host(value: str | None = None) -> str:
    """The mint is native: its launcher sets build, host and target together."""
    actual = detected_host()
    requested = canonical_host(value) if value else actual
    if requested != actual:
        fail(f"mint host {requested!r} is not the native host {actual!r}; cross-host minting is unsupported")
    return actual


def detected_host(
    system: str | None = None,
    machine: str | None = None,
    libc_name: str | None = None,
) -> str:
    system = system or platform.system()
    machine = (machine or platform.machine()).lower()
    arches = {
        "x86_64": "x86_64",
        "amd64": "x86_64",
        "aarch64": "aarch64",
        "arm64": "aarch64",
    }
    arch = arches.get(machine)
    if arch is None:
        fail(
            f"cannot infer a Trust host triple for {system}/{machine}; "
            "pass --host explicitly"
        )
    if system == "Darwin":
        return f"{arch}-apple-darwin"
    if system == "Linux":
        libc = (libc_name if libc_name is not None else platform.libc_ver()[0]).lower()
        if "musl" in libc:
            environment = "musl"
        elif "glibc" in libc or "gnu" in libc:
            environment = "gnu"
        elif any(Path("/lib").glob("ld-musl-*.so.1")) or any(
            Path("/usr/lib").glob("ld-musl-*.so.1")
        ):
            environment = "musl"
        else:
            fail(
                "cannot distinguish a GNU from musl Linux host; pass --host explicitly"
            )
        return f"{arch}-unknown-linux-{environment}"
    fail(
        f"cannot infer a Trust host triple for {system}/{machine}; "
        "pass --host explicitly"
    )


# The one symlink `build` may be: a link to the sibling REAL directory
# `build.noindex`, whose name keeps Spotlight from indexing hundreds of GiB of
# build output (docs/BUILD_AND_INSTALL.md, "Keeping Spotlight out of build/").
# Every other link is still refused, because it could send output outside the
# checkout. The same predicate is inlined in recreate_bootstrap.py,
# off_stock_rust_audit.py and collect_lambda_calculus_diagnostic.py (each runs
# standalone, some under `python -I -S`); scripts/tests/build_dir_symlink_test.py
# drives every copy over one fixture matrix so they cannot drift.
BUILD_NOINDEX = "build.noindex"


def is_sanctioned_build_link(root: Path) -> bool:
    """True iff `root/build` is a symlink resolving to the real `root/build.noindex`."""
    lexical = root / "build"
    try:
        if not stat.S_ISLNK(os.lstat(lexical).st_mode):
            return False
        physical = root.resolve(strict=True) / BUILD_NOINDEX
        if not stat.S_ISDIR(os.lstat(physical).st_mode):
            return False
        return lexical.resolve(strict=True) == physical
    except (OSError, RuntimeError):
        return False


def physical_build_directory(root: Path) -> Path:
    """`root/build`, or the `build.noindex` it links to under the sanctioned layout."""
    if is_sanctioned_build_link(root):
        return root.resolve(strict=True) / BUILD_NOINDEX
    return root / "build"


def ensure_within(root: Path, candidate: Path, description: str) -> Path:
    root = root.resolve(strict=True)
    try:
        resolved = candidate.resolve(strict=False)
        common = Path(os.path.commonpath((str(root), str(resolved))))
    except (OSError, ValueError) as exc:
        fail(f"cannot resolve {description}: {candidate}: {exc}")
    if common != root:
        fail(f"{description} escapes {root}: {candidate}")
    return resolved


def verify_output_path(root: Path, output: Path, description: str) -> None:
    build = root / "build"
    if (build.is_symlink() and not is_sanctioned_build_link(root)) or not build.is_dir():
        fail(f"repository build directory must be a non-symlink directory: {build}")
    physical = physical_build_directory(root)
    ensure_within(physical, output, description)
    if output.exists() or output.is_symlink():
        fail(f"{description} already exists; refusing to replace it: {output}")
    ancestor = output.parent
    while ancestor not in (build, physical):
        if ancestor.exists() or ancestor.is_symlink():
            if ancestor.is_symlink() or not ancestor.is_dir():
                fail(f"{description} has an unsafe parent component: {ancestor}")
            break
        ancestor = ancestor.parent


def make_work_directory(root: Path) -> Path:
    root = root.resolve(strict=True)
    build = root / "build"
    if (build.is_symlink() and not is_sanctioned_build_link(root)) or not build.is_dir():
        fail(f"repository build directory must be a non-symlink directory: {build}")
    work = Path(tempfile.mkdtemp(prefix=".mint-and-prove.", dir=physical_build_directory(root)))
    work.chmod(0o700)
    return work


def authenticated_work_directory(root: Path, work: Path) -> Path:
    build = physical_build_directory(root.resolve(strict=True))
    try:
        before = work.lstat()
        resolved = work.resolve(strict=True)
    except OSError as exc:
        fail(f"cannot authenticate workflow temporary directory {work}: {exc}")
    if work.parent.resolve(strict=True) != build or not work.name.startswith(".mint-and-prove."):
        fail(f"refusing to operate on a non-workflow temporary directory: {work}")
    if stat.S_ISLNK(before.st_mode) or not stat.S_ISDIR(before.st_mode) or resolved != work:
        fail(f"workflow temporary directory changed identity: {work}")
    return resolved


def cleanup_work_directory(root: Path, work: Path) -> None:
    authenticated_work_directory(root, work)
    shutil.rmtree(work)


def publish_directory(root: Path, source: Path, destination: Path, description: str) -> None:
    source = authenticated_work_directory(root, source.parent) / source.name
    if source.is_symlink() or not source.is_dir():
        fail(f"{description} source must be a non-symlink directory: {source}")
    verify_output_path(root, destination, description)
    destination.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    os.rename(source, destination)


# How long the members of a supervised command's process group get to exit by
# themselves once the command has: a helper that exits when it reads EOF on a
# pipe the command held is still alive the instant the command exits. One is
# multiprocessing's resource tracker, which the Pool bootstrap.py unpacks stage0
# with starts as a child of x.py; measured 2026-10-24, a mint stopped on it
# ("left descendant processes running") after a first build that had passed.
DESCENDANT_EXIT_GRACE_SECONDS = 10


def process_group_alive(pgid: int) -> bool:
    try:
        os.killpg(pgid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        # Darwin can answer EPERM while the group's last member is exiting
        # (measured as the resource tracker exited): count it as still there.
        return True
    return True


def wait_for_process_group_exit(pgid: int, seconds: float) -> bool:
    deadline = time.monotonic() + seconds
    while process_group_alive(pgid):
        if time.monotonic() >= deadline:
            return False
        time.sleep(0.1)
    return True


def supervise(
    command: list[str],
    timeout_seconds: int,
    grace_seconds: float = DESCENDANT_EXIT_GRACE_SECONDS,
) -> int:
    if not command:
        fail("supervise requires a command after --")
    if timeout_seconds < 1:
        fail("supervise timeout must be positive")
    try:
        child = subprocess.Popen(command, start_new_session=True)
    except OSError as exc:
        fail(f"cannot start supervised command {command[0]!r}: {exc}")

    forwarded: list[int] = []

    def forward(signum: int, _frame: object) -> None:
        forwarded.append(signum)
        try:
            os.killpg(child.pid, signum)
        except ProcessLookupError:
            pass

    previous = {
        signum: signal.signal(signum, forward)
        for signum in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM)
    }
    timed_out = False
    forced_after_signal = False
    started = time.monotonic()
    signal_deadline: float | None = None
    try:
        while True:
            try:
                status = child.wait(timeout=1)
                break
            except subprocess.TimeoutExpired:
                now = time.monotonic()
                if forwarded and signal_deadline is None:
                    signal_deadline = now + 30
                if signal_deadline is not None and now >= signal_deadline:
                    forced_after_signal = True
                    try:
                        os.killpg(child.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    status = child.wait()
                    break
                if now - started < timeout_seconds:
                    continue
                timed_out = True
                print(
                    f"error: command exceeded {timeout_seconds} seconds: {command[0]}",
                    file=sys.stderr,
                )
                try:
                    os.killpg(child.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    status = child.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(child.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    status = child.wait()
                break
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)
    # A member still alive after the grace is a leak: it is terminated, so none
    # outlives this function, and the run fails.
    had_descendant_leak = not wait_for_process_group_exit(child.pid, grace_seconds)
    if had_descendant_leak:
        try:
            os.killpg(child.pid, signal.SIGTERM)
        except (ProcessLookupError, PermissionError):
            pass
        if not wait_for_process_group_exit(child.pid, 30):
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass
    if timed_out:
        return 124
    if forwarded:
        if forced_after_signal:
            print("error: supervised command ignored termination for 30 seconds", file=sys.stderr)
        return 128 + forwarded[-1]
    if had_descendant_leak:
        print("error: supervised command left descendant processes running", file=sys.stderr)
        return 125
    return 128 + (-status) if status < 0 else status


def git_command(
    root: Path, *arguments: str, extra_env: dict[str, str] | None = None
) -> subprocess.CompletedProcess[str]:
    git = shutil.which("git")
    if git is None:
        fail("git is required to bind seed artifacts to the source revision")
    git = str(canonical_regular_file(Path(git), "git executable"))
    env = {
        "PATH": os.environ.get("PATH", ""),
        "HOME": str(root / "build" / ".mint-git-home"),
        "LC_ALL": "C",
        "LANG": "C",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": os.devnull,
        **(extra_env or {}),
    }
    try:
        return subprocess.run(
            [git, *arguments],
            cwd=root,
            env=env,
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
        )
    except subprocess.TimeoutExpired:
        fail(f"git {' '.join(arguments)} exceeded 60 seconds")


def repository_state(root: Path, expected_commit: str | None = None) -> dict[str, object]:
    root = root.resolve(strict=True)
    top = git_command(root, "rev-parse", "--show-toplevel")
    if top.returncode != 0:
        fail(f"cannot identify repository root: {top.stderr.strip()}")
    try:
        git_root = Path(top.stdout.strip()).resolve(strict=True)
    except OSError as exc:
        fail(f"cannot canonicalize git repository root: {exc}")
    if git_root != root:
        fail(f"workflow root {root} is not git repository root {git_root}")

    head = git_command(root, "rev-parse", "HEAD")
    commit = head.stdout.strip()
    if head.returncode != 0 or not COMMIT_RE.fullmatch(commit):
        fail(f"cannot read an exact source commit: {head.stderr.strip()}")
    if expected_commit is not None and commit != expected_commit:
        fail(f"source HEAD changed during the workflow: {expected_commit} -> {commit}")

    status_result = git_command(
        root,
        "status",
        "--porcelain=v1",
        "--untracked-files=all",
        "--ignore-submodules=none",
    )
    if status_result.returncode != 0:
        fail(f"cannot audit source-tree state: {status_result.stderr.strip()}")
    dirty = [line for line in status_result.stdout.splitlines() if line]
    if dirty:
        preview = ", ".join(dirty[:5])
        if len(dirty) > 5:
            preview += f", ... ({len(dirty)} entries)"
        fail(f"seed minting requires a clean, committed source tree: {preview}")
    # `git status` calls an uninitialized submodule clean, but the build needs
    # every gitlink's source: each must be checked out at its pinned commit.
    staged = git_command(root, "ls-files", "--stage", "-z")
    if staged.returncode != 0:
        fail(f"cannot list the gitlinks: {staged.stderr.strip()}")
    unpopulated = []
    for entry in staged.stdout.split("\0"):
        mode, _, rest = entry.partition(" ")
        if mode != "160000":
            continue
        pinned, _, path = rest.partition("\t")
        pinned = pinned.split(" ")[0]
        checkout = git_command(root, "-C", path, "rev-parse", "--show-toplevel", "HEAD")
        lines = checkout.stdout.split()
        if (
            checkout.returncode != 0
            or len(lines) != 2
            or Path(lines[0]).resolve() != (root / path).resolve()
            or lines[1] != pinned
        ):
            unpopulated.append(path)
    if unpopulated:
        fail(
            "every gitlink must be checked out at its pinned commit (scripts/submodule_sync.sh "
            f"says how): {', '.join(unpopulated)}"
        )

    epoch_result = git_command(root, "show", "-s", "--format=%ct", commit)
    epoch = epoch_result.stdout.strip()
    if epoch_result.returncode != 0 or not epoch.isdigit():
        fail(f"cannot read source commit timestamp: {epoch_result.stderr.strip()}")
    # The spelling bootstrap stamps as the compiler's commit-date
    # (src/bootstrap/src/utils/channel.rs), which a re-pin's compiler_date must equal.
    date_result = git_command(root, "log", "-1", "--date=short", "--pretty=format:%cd", commit)
    commit_date = date_result.stdout.strip()
    if date_result.returncode != 0 or not DATE_RE.fullmatch(commit_date):
        fail(f"cannot read source commit date: {date_result.stderr.strip()}")
    return {"commit": commit, "source_date_epoch": int(epoch), "commit_date": commit_date}


def sha256_stream(handle: BinaryIO) -> str:
    digest = hashlib.sha256()
    for block in iter(lambda: handle.read(COPY_CHUNK), b""):
        digest.update(block)
    return digest.hexdigest()


def write_all(fd: int, payload: bytes) -> None:
    view = memoryview(payload)
    while view:
        written = os.write(fd, view)
        if written <= 0:
            fail("short write while materializing workflow metadata")
        view = view[written:]


def sha256_file(path: Path) -> str:
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    fd = os.open(path, flags)
    try:
        before = os.fstat(fd)
        if not stat.S_ISREG(before.st_mode):
            fail(f"cannot hash a non-regular file: {path}")
        with os.fdopen(os.dup(fd), "rb") as handle:
            digest = sha256_stream(handle)
        after = os.fstat(fd)
    finally:
        os.close(fd)
    if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
    ):
        fail(f"file changed while it was hashed: {path}")
    return digest


def configuration_closure(root: Path, source: Path) -> dict[str, object]:
    if tomllib is None:
        fail("Python 3.11+ is required to authenticate bootstrap TOML includes")
    root = root.resolve(strict=True)
    source = canonical_regular_file(source, "bootstrap source configuration")
    ensure_within(root, source, "bootstrap source configuration")
    entries: list[dict[str, object]] = []
    active: set[Path] = set()
    seen: set[Path] = set()

    def visit(path: Path) -> None:
        path = canonical_regular_file(path, "bootstrap configuration include")
        ensure_within(root, path, "bootstrap configuration include")
        if path in active:
            fail(f"bootstrap configuration include cycle reaches {path}")
        if path in seen:
            return
        if len(seen) >= MAX_CONFIG_FILES:
            fail(f"bootstrap configuration closure exceeds {MAX_CONFIG_FILES} files")
        size = path.stat().st_size
        if size > MAX_CONFIG_BYTES:
            fail(f"bootstrap configuration exceeds {MAX_CONFIG_BYTES} bytes: {path}")
        flags = os.O_RDONLY
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        fd = os.open(path, flags)
        try:
            before = os.fstat(fd)
            raw = bytearray()
            while len(raw) <= MAX_CONFIG_BYTES:
                block = os.read(fd, min(COPY_CHUNK, MAX_CONFIG_BYTES + 1 - len(raw)))
                if not block:
                    break
                raw.extend(block)
            after = os.fstat(fd)
        finally:
            os.close(fd)
        if len(raw) > MAX_CONFIG_BYTES:
            fail(f"bootstrap configuration exceeds {MAX_CONFIG_BYTES} bytes: {path}")
        if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
            after.st_dev,
            after.st_ino,
            after.st_size,
            after.st_mtime_ns,
        ):
            fail(f"bootstrap configuration changed while it was read: {path}")
        try:
            text = bytes(raw).decode("utf-8")
            parsed = tomllib.loads(text)
        except (UnicodeError, tomllib.TOMLDecodeError) as exc:
            fail(f"cannot parse bootstrap configuration {path}: {exc}")
        includes = parsed.get("include", [])
        if includes is None:
            includes = []
        if not isinstance(includes, list) or not all(isinstance(item, str) for item in includes):
            fail(f"bootstrap configuration include must be an array of strings: {path}")
        active.add(path)
        seen.add(path)
        entries.append(
            {
                "relative_path": path.relative_to(root).as_posix(),
                "bytes": len(raw),
                "sha256": hashlib.sha256(raw).hexdigest(),
            }
        )
        for include in includes:
            visit(path.parent / include)
        active.remove(path)

    visit(source)
    # Bootstrap applies the selected profile after all includes. It is an input
    # too, even when the root file names the profile only through an include.
    profile = effective_bootstrap_config(root, source).get("profile")
    if profile is not None:
        visit(bootstrap_profile_path(root, profile))
    serialized = json.dumps(entries, separators=(",", ":"), sort_keys=True).encode("utf-8")
    return {
        "schema": "trust-bootstrap-config-closure-v1",
        "files": entries,
        "fingerprint": hashlib.sha256(serialized).hexdigest(),
    }


def native_library_manifest(directories: Iterable[Path]) -> dict[str, object]:
    directories = list(directories)
    admitted_suffixes = (".a", ".dylib", ".o", ".so", ".tbd")
    records: list[dict[str, object]] = []
    content_cache: dict[tuple[int, int, int, int], str] = {}
    total_bytes = 0
    total_files = 0
    for index, raw_directory in enumerate(directories):
        directory = canonical_directory(raw_directory, "explicit native library directory")
        for entry in sorted(os.scandir(directory), key=lambda candidate: candidate.name):
            name = entry.name
            if not (
                name.endswith(admitted_suffixes)
                or ".so." in name
                or ".dylib." in name
            ):
                continue
            path = directory / name
            link_target: str | None = None
            if path.is_symlink():
                link_target = os.readlink(path)
                try:
                    resolved = path.resolve(strict=True)
                except OSError as exc:
                    fail(f"native library symlink is broken: {path}: {exc}")
            else:
                resolved = path
            if forbidden_tool_path(resolved):
                fail(f"native library resolves through a forbidden stock-toolchain tree: {path}")
            metadata = resolved.stat()
            if not stat.S_ISREG(metadata.st_mode):
                fail(f"native library entry is not a regular file: {path}")
            total_files += 1
            total_bytes += metadata.st_size
            if total_files > 100_000 or total_bytes > MAX_TOTAL_UNPACKED_BYTES:
                fail("explicit native library inputs exceed audit bounds")
            key = (
                metadata.st_dev,
                metadata.st_ino,
                metadata.st_size,
                metadata.st_mtime_ns,
            )
            content_digest = content_cache.get(key)
            if content_digest is None:
                content_digest = sha256_file(resolved)
                content_cache[key] = content_digest
            records.append(
                {
                    "directory_index": index,
                    "name": name,
                    "link_target": link_target,
                    "resolved_path": str(resolved),
                    "bytes": metadata.st_size,
                    "mode": stat.S_IMODE(metadata.st_mode),
                    "sha256": content_digest,
                }
            )
    serialized = json.dumps(records, separators=(",", ":"), sort_keys=True).encode("utf-8")
    return {
        "schema": "trust-native-library-inputs-v1",
        "directories": [
            str(canonical_directory(path, "explicit native library directory"))
            for path in directories
        ],
        "files": records,
        "regular_file_bytes": total_bytes,
        "fingerprint": hashlib.sha256(serialized).hexdigest(),
    }


STAGE0_SELECTORS = ("rustc", "cargo", "rustdoc", "rustfmt", "cargo-clippy")


# Bootstrap's alias for a renamed profile (config.rs `profile_aliases`).
PROFILE_ALIASES = {"user": "dist"}


def bootstrap_profile_path(root: Path, profile: object) -> Path:
    if not isinstance(profile, str) or not re.fullmatch(r"[A-Za-z0-9_-]+", profile):
        fail(f"bootstrap profile must be a plain profile name: {profile!r}")
    return root / "src" / "bootstrap" / "defaults" / f"bootstrap.{PROFILE_ALIASES.get(profile, profile)}.toml"


def effective_bootstrap_config(
    root: Path, source: Path, *, confine: bool = True,
    inputs: dict[Path, str] | None = None,
    origins: dict[str, Path] | None = None,
) -> dict[str, object]:
    """The selector/LLVM tables bootstrap sees: root, includes, then profile defaults.

    Top-level tables and target triples merge fields; option dictionaries are
    replaced wholesale. `inputs` records the bytes read. `origins` records the
    winning file for each build key, so a seed refusal names its actual source.
    """
    if tomllib is None:
        fail("Python 3.11+ (or tomli) is required to authenticate bootstrap tool selectors")
    root = root.resolve(strict=True)
    active: set[Path] = set()

    def read(path: Path) -> tuple[dict[str, object], Path]:
        path = canonical_regular_file(path, "bootstrap tool-selector configuration")
        if confine:
            ensure_within(root, path, "bootstrap tool-selector configuration")
        raw = path.read_bytes()
        if len(raw) > MAX_CONFIG_BYTES:
            fail(f"bootstrap configuration exceeds {MAX_CONFIG_BYTES} bytes: {path}")
        if inputs is not None:
            inputs[path] = hashlib.sha256(raw).hexdigest()
        try:
            return tomllib.loads(raw.decode("utf-8")), path
        except (UnicodeError, tomllib.TOMLDecodeError) as exc:
            fail(f"cannot parse bootstrap configuration {path}: {exc}")

    def fill_missing(merged: dict[str, object], child: dict[str, object], path=()) -> None:
        for key, value in child.items():
            if key not in merged:
                merged[key] = value
            elif isinstance(merged[key], dict) and isinstance(value, dict) and (
                not path or path == ("target",)
            ):
                # Top-level tables and target.<triple> merge fields; dictionary
                # option values (e.g. llvm.build-config) are replaced wholesale.
                fill_missing(merged[key], value, (*path, key))

    def build_keys(config: dict[str, object]) -> set[str]:
        build = config.get("build", {})
        return set(build) if isinstance(build, dict) else set()

    def merge_config(merged: dict[str, object], origin: dict[str, Path],
                     child: dict[str, object], child_origin: dict[str, Path]) -> None:
        previous = build_keys(merged)
        fill_missing(merged, child)
        for key in build_keys(merged) - previous:
            origin[key] = child_origin[key]

    def effective(path: Path) -> tuple[dict[str, object], dict[str, Path]]:
        resolved = path.resolve()
        if resolved in active:
            fail(f"bootstrap configuration include cycle reaches {path}")
        parsed, canonical = read(path)
        merged = {key: value for key, value in parsed.items() if key != "include"}
        origin = dict.fromkeys(build_keys(merged), canonical)
        includes = parsed.get("include", []) or []
        if not isinstance(includes, list) or not all(isinstance(item, str) for item in includes):
            fail(f"bootstrap configuration include must be an array of strings: {path}")
        active.add(resolved)
        # Root first, then later includes over earlier includes, then profile.
        for include in reversed(includes):
            child, child_origin = effective(path.parent / include)
            merge_config(merged, origin, child, child_origin)
        active.remove(resolved)
        return merged, origin

    merged, origin = effective(source)
    profile = merged.get("profile")
    if profile is not None:
        child, child_origin = effective(bootstrap_profile_path(root, profile))
        merge_config(merged, origin, child, child_origin)
    if origins is not None:
        origins.update(origin)
    return merged


def effective_build_table(
    root: Path, source: Path, *, confine: bool = True,
    inputs: dict[Path, str] | None = None,
    origins: dict[str, Path] | None = None,
) -> dict[str, object]:
    build = effective_bootstrap_config(
        root, source, confine=confine, inputs=inputs, origins=origins).get("build", {})
    if not isinstance(build, dict):
        fail(f"bootstrap build configuration must be a table: {source}")
    return build


def require_pinned_seed_config(root: Path, source: Path) -> None:
    """The pack cut builds from the src/stage0 pin only (D12)."""
    build = effective_build_table(root, source)
    overrides = [name for name in STAGE0_SELECTORS if build.get(name) is not None]
    if overrides:
        fail(
            f"{source} sets build.{', build.'.join(overrides)}: a pack cut builds from the "
            "committed src/stage0 pin and nothing else (docs/DECISION_QUEUE.md D12); "
            "use a configuration without stage0 tool overrides"
        )


MINT_XPY_CONFIG_OVERRIDES = {
    "build.submodules": False, "rust.channel": "trust",
    "rust.download-rustc": False, "llvm.download-ci-llvm": False,
}


def checked_build_jobs(jobs: int | None) -> int | None:
    if jobs is not None and (type(jobs) is not int or not 1 <= jobs <= 2**32 - 1):
        fail("build jobs must be a positive u32 count")
    return jobs


def mint_build_jobs(jobs: int | None, environment=None) -> int | None:
    """Consume admission before the closed environment drops its variables."""
    jobs = checked_build_jobs(jobs)
    environment = os.environ if environment is None else environment
    if environment.get("BUILD_SLOT_HELD") == "1":
        share = environment.get("CARGO_BUILD_JOBS", "")
        if not share.isascii() or not share.isdecimal() or len(share) > 10:
            fail("build-slot admission requires a positive CARGO_BUILD_JOBS share")
        admitted = checked_build_jobs(int(share))
        return min(jobs, admitted) if jobs is not None else admitted
    return jobs


def mint_configuration_context(
    root: Path, source: Path, host: str, *, jobs: int | None = None,
    clean_lean_lib: Path | None = None,
) -> dict[str, object]:
    """The mint's validated seed config, complete closure and fixed x.py overrides.

    This explicit context is not a recreator mode guess. The mint always uses
    the pinned seed and disables downloaded compiler/LLVM at every x.py call.
    External LLVM and stage0 tool selectors still refuse, including in profiles
    and recursive includes. Re-read the closure around evaluation to bind the
    same files whose effective settings were checked.
    """
    root = root.resolve(strict=True)
    source = canonical_regular_file(source, "mint bootstrap configuration")
    closure = configuration_closure(root, source)
    require_pinned_seed_config(root, source)
    effective = effective_bootstrap_config(root, source)
    for name in ("build", "llvm", "rust", "target"):
        if not isinstance(effective.get(name, {}), dict):
            fail(f"mint bootstrap {name} configuration must be a table")
    for triple, target in effective.get("target", {}).items():
        if not isinstance(target, dict):
            fail(f"mint bootstrap target.{triple} configuration must be a table")
        if target.get("llvm-config") is not None:
            fail(f"mint stage evidence refuses external target.{triple}.llvm-config")
    if configuration_closure(root, source) != closure:
        fail("mint bootstrap configuration changed while its effective settings were checked")
    overrides = dict(MINT_XPY_CONFIG_OVERRIDES)
    if checked_build_jobs(jobs) is not None:
        overrides["build.jobs"] = jobs
    context = {
        "schema": "trust.mint-bootstrap-configuration.v1",
        "host": host, "config_path": source.relative_to(root).as_posix(),
        "configuration_closure": closure,
        "effective_build": effective.get("build", {}),
        "xpy_config_overrides": overrides,
    }
    if clean_lean_lib is not None:
        context["clean_lean_inputs"] = clean_lean_inputs(root, clean_lean_lib)
    return {**context, "fingerprint": hashlib.sha256(
        json.dumps(context, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()}


def mint_tool_manifest(root: Path, source: Path) -> dict[str, object]:
    root = root.resolve(strict=True)
    build = effective_build_table(root, source)
    declared = {name: build.get(name) for name in STAGE0_SELECTORS}
    if declared["rustdoc"] is None and isinstance(declared["rustc"], str):
        rustc_path = Path(declared["rustc"])
        if not rustc_path.is_absolute():
            rustc_path = root / rustc_path
        suffix = ".exe" if rustc_path.suffix.lower() == ".exe" else ""
        sibling = rustc_path.with_name(f"rustdoc{suffix}")
        if sibling.exists():
            declared["rustdoc"] = str(sibling)

    records: dict[str, object] = {}
    for name, value in declared.items():
        if value is None:
            records[name] = None
            continue
        if not isinstance(value, str) or not value or "\n" in value or "\r" in value:
            fail(f"build.{name} must be a nonempty executable path string")
        candidate = Path(value)
        if not candidate.is_absolute():
            if os.sep in value:
                candidate = root / candidate
            else:
                found = shutil.which(value)
                if found is None:
                    fail(f"cannot resolve configured build.{name} executable: {value}")
                candidate = Path(found)
        try:
            resolved = candidate.resolve(strict=True)
            metadata = resolved.stat()
        except OSError as exc:
            fail(f"cannot authenticate configured build.{name} executable {value!r}: {exc}")
        if not stat.S_ISREG(metadata.st_mode) or not os.access(resolved, os.X_OK):
            fail(f"configured build.{name} is not an executable regular file: {resolved}")
        records[name] = {
            "declared": value,
            "resolved": str(resolved),
            "bytes": metadata.st_size,
            "sha256": sha256_file(resolved),
        }
    serialized = json.dumps(records, separators=(",", ":"), sort_keys=True).encode("utf-8")
    return {
        "schema": "trust-seed-mint-tools-v1",
        "tools": records,
        "fingerprint": hashlib.sha256(serialized).hexdigest(),
    }


def copy_authenticated(source: Path, destination: Path) -> tuple[str, int]:
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    source_fd = os.open(source, flags)
    try:
        before = os.fstat(source_fd)
        if not stat.S_ISREG(before.st_mode):
            fail(f"dist artifact is not a regular file: {source}")
        destination.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        output_fd = os.open(destination, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        digest = hashlib.sha256()
        try:
            while True:
                block = os.read(source_fd, COPY_CHUNK)
                if not block:
                    break
                digest.update(block)
                view = memoryview(block)
                while view:
                    written = os.write(output_fd, view)
                    view = view[written:]
            os.fsync(output_fd)
        finally:
            os.close(output_fd)
        after = os.fstat(source_fd)
    finally:
        os.close(source_fd)
    if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
    ):
        destination.unlink(missing_ok=True)
        fail(f"dist artifact changed while it was admitted: {source}")
    return digest.hexdigest(), before.st_size


def normalized_member(name: str) -> PurePosixPath:
    if len(name.encode("utf-8", errors="surrogatepass")) > MAX_MEMBER_PATH_BYTES:
        fail(f"archive member path exceeds {MAX_MEMBER_PATH_BYTES} bytes")
    if "\\" in name or "\x00" in name:
        fail(f"archive member uses a non-portable path: {name!r}")
    path = PurePosixPath(name)
    if path.is_absolute():
        fail(f"archive member is absolute: {name!r}")
    pieces = tuple(piece for piece in path.parts if piece not in ("", "."))
    if not pieces or any(piece == ".." for piece in pieces):
        fail(f"archive member escapes its extraction root: {name!r}")
    return PurePosixPath(*pieces)


def resolved_link(member_path: PurePosixPath, linkname: str, *, hard: bool) -> PurePosixPath:
    if len(linkname.encode("utf-8", errors="surrogatepass")) > MAX_MEMBER_PATH_BYTES:
        fail(f"archive link target exceeds {MAX_MEMBER_PATH_BYTES} bytes: {member_path}")
    if "\\" in linkname or "\x00" in linkname:
        fail(f"archive link uses a non-portable target: {member_path} -> {linkname!r}")
    link = PurePosixPath(linkname)
    if link.is_absolute():
        fail(f"archive link uses an absolute target: {member_path} -> {linkname!r}")
    combined = link if hard else member_path.parent / link
    stack: list[str] = []
    for piece in combined.parts:
        if piece == "..":
            if not stack:
                fail(f"archive link escapes its extraction root: {member_path} -> {linkname}")
            stack.pop()
        elif piece not in ("", "."):
            stack.append(piece)
    if not stack:
        fail(f"archive link has an empty target: {member_path} -> {linkname}")
    if stack[0] != member_path.parts[0]:
        fail(
            f"archive link leaves exact package root {member_path.parts[0]}: "
            f"{member_path} -> {linkname}"
        )
    return PurePosixPath(*stack)


def _extraction_checkpoint(deadline: float | None) -> None:
    # A cooperative restriction on the caller's ALREADY selected local end.
    # This is neither a cross-clock transfer nor resident/native custody: the
    # actual owner separately retains its original hard deadline and children.
    if deadline is None:
        return
    # time.monotonic supplies a float. Do not normalize other caller DATA,
    # NaN or infinities into a local end, or import another native extension.
    if type(deadline) is not float or not (-float("inf") < deadline < float("inf")):
        fail("archive extraction requires the original finite endpoint")
    if time.monotonic() >= deadline:
        fail("archive extraction original deadline exhausted")


def archive_metadata(
    bundle: tarfile.TarFile, archive: Path, top: str, commit: str,
    *, deadline: float | None = None,
) -> tuple[list[tarfile.TarInfo], int]:
    members: list[tarfile.TarInfo] = []
    paths: dict[PurePosixPath, str] = {}
    total = 0
    commit_value: str | None = None
    try:
        for index, member in enumerate(bundle):
            _extraction_checkpoint(deadline)
            if index >= MAX_ARCHIVE_MEMBERS:
                fail(f"archive has more than {MAX_ARCHIVE_MEMBERS} members: {archive}")
            path = normalized_member(member.name)
            if path.parts[0] != top:
                fail(f"archive member is outside exact package root {top!r}: {member.name!r}")
            kind = (
                "dir"
                if member.isdir()
                else "file"
                if member.isfile()
                else "symlink"
                if member.issym()
                else "hardlink"
                if member.islnk()
                else "unsupported"
            )
            if kind == "unsupported":
                fail(f"archive contains an unsupported special entry: {member.name!r}")
            previous = paths.get(path)
            if previous is not None and not (previous == kind == "dir"):
                fail(f"archive contains a duplicate path: {member.name!r}")
            paths[path] = kind
            if member.isfile():
                if member.size < 0:
                    fail(f"archive member has a negative size: {member.name!r}")
                total += member.size
                if total > MAX_UNPACKED_BYTES:
                    fail(f"archive expands beyond {MAX_UNPACKED_BYTES} bytes: {archive}")
            elif member.issym():
                resolved_link(path, member.linkname, hard=False)
            elif member.islnk():
                resolved_link(path, member.linkname, hard=True)
            members.append(member)

        commit_path = PurePosixPath(top, "git-commit-hash")
        commit_member = next(
            (member for member in members if normalized_member(member.name) == commit_path),
            None,
        )
        if commit_member is None or not commit_member.isfile():
            fail(f"archive lacks a regular {top}/git-commit-hash: {archive}")
        extracted = bundle.extractfile(commit_member)
        if extracted is None or commit_member.size > MAX_METADATA_BYTES:
            fail(f"archive commit metadata is invalid: {archive}")
        _extraction_checkpoint(deadline)
        commit_value = extracted.read(MAX_METADATA_BYTES + 1).decode("ascii").strip()
        _extraction_checkpoint(deadline)
    except (tarfile.TarError, OSError, UnicodeError) as exc:
        fail(f"cannot authenticate xz archive {archive}: {exc}")
    if commit_value != commit:
        fail(
            f"dist artifact was not minted from current HEAD: {archive.name}: "
            f"archive={commit_value!r}, HEAD={commit!r}"
        )
    required = {
        PurePosixPath(top, "install.sh"): "file",
        PurePosixPath(top, "version"): "file",
        PurePosixPath(top, "git-commit-hash"): "file",
    }
    for path, expected_kind in required.items():
        if paths.get(path) != expected_kind:
            fail(f"archive lacks regular required member {path}: {archive}")
    return members, total


def destination_path(root: Path, member: tarfile.TarInfo) -> Path:
    relative = normalized_member(member.name)
    return root.joinpath(*relative.parts)


def extract_authenticated(archive: Path, destination: Path, top: str, commit: str) -> int:
    """Ordinary mint extraction, retaining its existing failed-output cleanup."""
    return _extract_authenticated(archive, destination, top, commit,
                                  deadline=None, retain_failed=False)


def extract_for_preparation(archive: Path, destination: Path, top: str, commit: str,
                            *, deadline: float) -> int:
    """The SAME canonical in-process extraction under an already selected end.

    The real resident must own its fresh producer, source/archive/config/cache,
    control SDK and hard native deadline BEFORE calling this helper. Failed or
    interrupted partial output stays with that original producer for quarantine;
    it is never deleted or adopted here. Neither this pathname, successful
    extraction, nor its return value validates a seed or creates any ownership,
    admission, settlement, availability or full/default Bootstrap credential.
    No installer or subprocess is run. There is no online/fetch fallback.
    """
    if deadline is None:
        fail("preparation extraction requires the original finite endpoint")
    _extraction_checkpoint(deadline)
    return _extract_authenticated(archive, destination, top, commit,
                                  deadline=deadline, retain_failed=True)


def _archive_descriptor_stamp(fd: int):
    item = os.fstat(fd)
    if not stat.S_ISREG(item.st_mode) or not 0 < item.st_size <= MAX_TOTAL_ARCHIVE_BYTES:
        fail("preparation archive description is not a bounded regular input")
    return (item.st_dev, item.st_ino, item.st_mode, item.st_uid, item.st_gid,
            item.st_nlink, item.st_size, item.st_mtime_ns, item.st_ctime_ns)


class _PositionalArchive(io.RawIOBase):
    """Read the SAME offered description without changing its shared cursor.

    Closing this reader closes no original descriptor. The native issuer keeps
    that readonly original and every other input through actual settlement.
    """
    def __init__(self, fd: int, stamp, deadline: float):
        self._fd, self._stamp, self._deadline, self._offset = fd, stamp, deadline, 0

    def _check(self):
        _extraction_checkpoint(self._deadline)
        if _archive_descriptor_stamp(self._fd) != self._stamp:
            fail("original preparation archive description changed")

    def readable(self):
        return True

    def seekable(self):
        return True

    def tell(self):
        self._check()
        return self._offset

    def seek(self, offset, whence=os.SEEK_SET):
        self._check()
        base = {os.SEEK_SET: 0, os.SEEK_CUR: self._offset, os.SEEK_END: self._stamp[6]}
        if whence not in base or type(offset) is not int or offset + base[whence] < 0:
            raise ValueError("invalid positional archive seek")
        self._offset = offset + base[whence]
        return self._offset

    def readinto(self, target):
        self._check()
        block = os.pread(self._fd, min(len(target), COPY_CHUNK), self._offset)
        self._check()
        target[:len(block)] = block
        self._offset += len(block)
        return len(block)


def extract_for_preparation_fd(archive_fd: int, destination: Path, top: str, commit: str,
                              *, deadline: float) -> int:
    """Use the resident's SAME held readonly archive in the canonical extractor.

    No archive pathname is reopened, cursor/flags changed, or descriptor closed.
    A descriptor is not an authentication or ownership assertion: the native
    issuer must retain and validate its original archive, source, fresh output,
    cache, SDK/GNU and hard endpoint independently before dispatch and after
    native settlement. Success supplies neither seed nor availability authority.
    Failures retain partial output with that same original producer.
    """
    _extraction_checkpoint(deadline)
    if deadline is None or type(archive_fd) is not int or archive_fd < 3:
        fail("preparation extraction requires an original archive description and endpoint")
    if not hasattr(os, "pread"):
        fail("positional preparation archive input is unsupported on this host")
    # This distinct native route requires a readonly original, not a writable
    # replacement or a path. Never alter the shared OFD's flags to make it fit.
    import fcntl
    if fcntl.fcntl(archive_fd, fcntl.F_GETFL) & os.O_ACCMODE != os.O_RDONLY:
        fail("preparation archive description is not readonly")
    stamp = _archive_descriptor_stamp(archive_fd)
    return _extract_authenticated(Path("<original-preparation-archive>"), destination, top, commit,
                                  deadline=deadline, retain_failed=True,
                                  original_archive=(archive_fd, stamp))


def project_for_preparation_fd(archive_fd: int, destination: Path, top: str, commit: str,
                              component: str, *, deadline: float) -> int:
    """Project one authenticated component with Bootstrap's SAME path rule.

    The resident separately owns this existing fresh producer directory and
    original readonly archive. Nothing is installed, executed, overwritten or
    deleted, including after failure. Several components may contribute only
    disjoint files and shared directories. The result is DATA, not a validated
    private seed, READY publication, SDK or native closure capability.
    """
    _extraction_checkpoint(deadline)
    if deadline is None or type(archive_fd) is not int or archive_fd < 3:
        fail("preparation projection requires an original archive description and endpoint")
    if not hasattr(os, "pread"):
        fail("positional preparation archive input is unsupported on this host")
    import fcntl
    if fcntl.fcntl(archive_fd, fcntl.F_GETFL) & os.O_ACCMODE != os.O_RDONLY:
        fail("preparation archive description is not readonly")
    if not isinstance(component, str) or not component:
        fail("preparation projection requires its exact component")
    # Validate the selector even if the archive contains no selected members.
    _IDENTITY_OWNER.component_projection(top, top, component)
    named = destination.lstat()
    if (not stat.S_ISDIR(named.st_mode) or destination.resolve(strict=True) != destination
            or named.st_uid != os.geteuid() or named.st_mode & 0o022):
        fail("preparation projection requires the existing protected producer directory")
    stamp = _archive_descriptor_stamp(archive_fd)
    return _extract_authenticated(Path("<original-preparation-archive>"), destination, top, commit,
                                  deadline=deadline, retain_failed=True,
                                  original_archive=(archive_fd, stamp), projection=component)


class _ProjectionOutput:
    """Confine writes to opened directories of the original fresh output.

    This only prevents pathname redirection. It does not supply the resident's
    original producer, source/config, semantic seed or native closure owner.
    """
    def __init__(self, root: Path, deadline: float):
        self.root, self.deadline, self.directories = root, deadline, {}
        self.created = set()
        self.flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
        descriptor = os.open(root, self.flags)
        try:
            self.directories[()] = (descriptor, self.identity(os.fstat(descriptor)))
            self.check()
        except BaseException:
            self.close()
            raise

    @staticmethod
    def identity(info):
        if (not stat.S_ISDIR(info.st_mode) or info.st_uid != os.geteuid()
                or info.st_mode & 0o022):
            fail("projected output directory is not protected and regular")
        return info.st_dev, info.st_ino, info.st_uid, info.st_gid, info.st_mode

    def check(self):
        _extraction_checkpoint(self.deadline)
        for parts, (descriptor, original) in self.directories.items():
            if parts:
                parent = self.directories[parts[:-1]][0]
                named = os.stat(parts[-1], dir_fd=parent, follow_symlinks=False)
            else:
                named = self.root.lstat()
            if (self.identity(named) != original
                    or self.identity(os.fstat(descriptor)) != original):
                fail("original projected output directory changed")
        _extraction_checkpoint(self.deadline)

    def directory(self, parts, mode=None):
        self.check()
        for count in range(1, len(parts) + 1):
            current = parts[:count]
            if current in self.directories:
                continue
            parent = self.directories[current[:-1]][0]
            try:
                os.mkdir(current[-1], 0o700, dir_fd=parent)
                self.created.add(current)
            except FileExistsError:
                pass
            descriptor = os.open(current[-1], self.flags, dir_fd=parent)
            try:
                original = self.identity(os.fstat(descriptor))
            except BaseException:
                os.close(descriptor)
                raise
            self.directories[current] = descriptor, original
        self.check()
        if mode is not None:
            if mode & 0o022:
                fail("projected directory permits foreign writers")
            if (parts not in self.created
                    and stat.S_IMODE(os.fstat(self.directories[parts][0]).st_mode) != mode):
                fail("projected components disagree on existing directory permissions")
        return self.directories[parts][0]

    def parent(self, path):
        parts = tuple(path.relative_to(self.root).parts)
        if not parts or any(part in ("", ".", "..") for part in parts):
            fail("projected output has no confined relative leaf")
        return self.directory(parts[:-1]), parts[-1]

    @staticmethod
    def file_stamp(descriptor):
        info = os.fstat(descriptor)
        return (info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_gid,
                info.st_nlink, info.st_size, info.st_mtime_ns, info.st_ctime_ns)

    def create(self, path, mode, size):
        if mode & 0o022:
            fail("projected file permits foreign writers")
        parent, name = self.parent(path)
        try:
            return (os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL
                            | os.O_NOFOLLOW | os.O_CLOEXEC, mode, dir_fd=parent), None)
        except FileExistsError:
            # Retain the established inode; a shared file is reusable ONLY if
            # its exact bytes/mode agree. No overwrite, chmod, alias following
            # or shared cursor/flag mutation is permitted.
            descriptor = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
                                 | os.O_CLOEXEC, dir_fd=parent)
            try:
                info = os.fstat(descriptor)
                if (not stat.S_ISREG(info.st_mode) or info.st_uid != os.geteuid()
                        or stat.S_IMODE(info.st_mode) != mode or info.st_size != size):
                    raise FileExistsError(errno.EEXIST, "projected components disagree on existing file shape", path)
                original = self.file_stamp(descriptor)
                self.check()
                return descriptor, original
            except BaseException:
                os.close(descriptor)
                raise

    def verify_existing(self, descriptor, path, original):
        parent, name = self.parent(path)
        info = os.stat(name, dir_fd=parent, follow_symlinks=False)
        named = (info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_gid,
                 info.st_nlink, info.st_size, info.st_mtime_ns, info.st_ctime_ns)
        if self.file_stamp(descriptor) != original or named != original:
            fail("original shared projected file changed")
        self.check()

    def link(self, source, target):
        source_parent, source_name = self.parent(source)
        target_parent, target_name = self.parent(target)
        if not stat.S_ISREG(os.stat(source_name, dir_fd=source_parent,
                                  follow_symlinks=False).st_mode):
            fail("projected hardlink target is not an extracted regular file")
        os.link(source_name, target_name, src_dir_fd=source_parent,
                dst_dir_fd=target_parent, follow_symlinks=False)
        self.check()

    def symlink(self, text, target):
        parent, name = self.parent(target)
        os.symlink(text, name, dir_fd=parent)
        self.check()

    def chmod(self, path, mode):
        parts = tuple(path.relative_to(self.root).parts)
        descriptor = self.directory(parts, mode)
        os.fchmod(descriptor, mode)
        self.directories[parts] = descriptor, self.identity(os.fstat(descriptor))
        self.check()

    def close(self):
        for descriptor, _ in reversed(list(self.directories.values())):
            os.close(descriptor)
        self.directories.clear()
        self.created.clear()


def _extract_authenticated(archive: Path, destination: Path, top: str, commit: str,
                           *, deadline: float | None, retain_failed: bool,
                           original_archive=None, projection=None) -> int:
    _extraction_checkpoint(deadline)
    if projection is None:
        destination.mkdir(mode=0o700, parents=True, exist_ok=False)
    projected = _ProjectionOutput(destination, deadline) if projection is not None else None
    directories: list[tuple[Path, int]] = []
    symlinks: list[tarfile.TarInfo] = []
    hardlinks: list[tarfile.TarInfo] = []
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    archive_fd = os.open(archive, flags) if original_archive is None else original_archive[0]
    try:
        before = os.fstat(archive_fd)
        if original_archive is None:
            archive_handle = os.fdopen(os.dup(archive_fd), "rb")
        else:
            if _archive_descriptor_stamp(archive_fd) != original_archive[1]:
                fail("original preparation archive description changed before extraction")
            archive_handle = io.BufferedReader(_PositionalArchive(archive_fd, original_archive[1], deadline))
        with archive_handle:
            with tarfile.open(fileobj=archive_handle, mode="r:xz") as bundle:
                members, total = archive_metadata(bundle, archive, top, commit, deadline=deadline)
                if projection is not None:
                    selected = []
                    for member in members:
                        _extraction_checkpoint(deadline)
                        relative = _IDENTITY_OWNER.component_projection(member.name, top, projection)
                        if not relative:
                            continue
                        if member.issym() or member.islnk():
                            target = resolved_link(normalized_member(member.name), member.linkname,
                                                   hard=member.islnk())
                            if not _IDENTITY_OWNER.component_projection(str(target), top, projection):
                                fail("projected archive link leaves its exact component")
                        selected.append(member)
                    if not any(member.isfile() for member in selected):
                        fail("archive has no regular files in its exact projected component")
                    members = selected
                    total = sum(member.size for member in members if member.isfile())

                def output_path(member):
                    if projection is None:
                        return destination_path(destination, member)
                    relative = _IDENTITY_OWNER.component_projection(member.name, top, projection)
                    return destination.joinpath(*PurePosixPath(relative).parts)

                for member in members:
                    _extraction_checkpoint(deadline)
                    target = output_path(member)
                    if member.isdir():
                        if projected is None:
                            target.mkdir(mode=0o700, parents=True, exist_ok=True)
                        else:
                            projected.directory(tuple(target.relative_to(destination).parts), member.mode & 0o777)
                        directories.append((target, member.mode & 0o777))
                    elif member.isfile():
                        if projected is None:
                            target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
                        source = bundle.extractfile(member)
                        if source is None:
                            fail(f"cannot read admitted archive member: {member.name}")
                        if projected is not None:
                            output_fd, original_output = projected.create(target, member.mode & 0o777, member.size)
                        else:
                            output_fd = os.open(target, os.O_WRONLY | os.O_CREAT | os.O_EXCL,
                                                member.mode & 0o777)
                            original_output = None
                        remaining = member.size
                        try:
                            while remaining:
                                _extraction_checkpoint(deadline)
                                block = source.read(min(COPY_CHUNK, remaining))
                                if not block:
                                    fail(f"archive member is truncated: {member.name}")
                                offset = member.size - remaining
                                remaining -= len(block)
                                if original_output is not None:
                                    actual = bytearray()
                                    while len(actual) < len(block):
                                        _extraction_checkpoint(deadline)
                                        part = os.pread(output_fd, len(block) - len(actual), offset + len(actual))
                                        if not part:
                                            fail("shared projected file is truncated")
                                        actual.extend(part)
                                    if actual != block:
                                        raise FileExistsError(errno.EEXIST, "projected components disagree on existing file bytes", target)
                                    continue
                                view = memoryview(block)
                                while view:
                                    _extraction_checkpoint(deadline)
                                    written = os.write(output_fd, view)
                                    if written <= 0:
                                        fail("short write while extracting authenticated archive")
                                    _extraction_checkpoint(deadline)
                                    view = view[written:]
                            if source.read(1):
                                fail(f"archive member exceeds its declared size: {member.name}")
                            if original_output is not None:
                                projected.verify_existing(output_fd, target, original_output)
                            elif projected is not None:
                                # This descriptor was created here with O_EXCL.
                                # Match Bootstrap's installed archive modes even
                                # under an inherited restrictive creation mask;
                                # never chmod an existing projected original.
                                _extraction_checkpoint(deadline)
                                os.fchmod(output_fd, member.mode & 0o777)
                                _extraction_checkpoint(deadline)
                        finally:
                            os.close(output_fd)
                    elif member.issym():
                        symlinks.append(member)
                    elif member.islnk():
                        hardlinks.append(member)

                for member in hardlinks:
                    _extraction_checkpoint(deadline)
                    target = output_path(member)
                    relative_target = resolved_link(
                        normalized_member(member.name), member.linkname, hard=True
                    )
                    if projection is not None:
                        relative_target = PurePosixPath(_IDENTITY_OWNER.component_projection(
                            str(relative_target), top, projection))
                    source = destination.joinpath(*relative_target.parts)
                    if not source.is_file() or source.is_symlink():
                        fail(
                            "archive hardlink target is not an extracted regular file: "
                            f"{member.name}"
                        )
                    if projected is None:
                        target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
                        os.link(source, target, follow_symlinks=False)
                    else:
                        projected.link(source, target)

                for member in symlinks:
                    _extraction_checkpoint(deadline)
                    target = output_path(member)
                    resolved_link(normalized_member(member.name), member.linkname, hard=False)
                    if projected is None:
                        target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
                        os.symlink(member.linkname, target)
                    else:
                        projected.symlink(member.linkname, target)

                for directory, mode in reversed(directories):
                    _extraction_checkpoint(deadline)
                    if projected is None:
                        directory.chmod(mode)
                    else:
                        projected.chmod(directory, mode)
                if projected is not None:
                    projected.check()
        _extraction_checkpoint(deadline)
        after = os.fstat(archive_fd)
        if original_archive is not None and _archive_descriptor_stamp(archive_fd) != original_archive[1]:
            fail("original preparation archive description changed during extraction")
        if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
            after.st_dev,
            after.st_ino,
            after.st_size,
            after.st_mtime_ns,
        ):
            fail(f"staged archive changed while it was extracted: {archive}")
    except Exception:
        if not retain_failed:
            shutil.rmtree(destination, ignore_errors=True)
        raise
    finally:
        if original_archive is None:
            os.close(archive_fd)
        if projected is not None:
            projected.close()
    _extraction_checkpoint(deadline)
    return total


def stage_artifacts(
    dist: Path,
    work: Path,
    version: str,
    host: str,
    commit: str,
    manifest_path: Path,
) -> dict[str, object]:
    version = canonical_version_value(version)
    host = canonical_host(host)
    if not COMMIT_RE.fullmatch(commit):
        fail(f"source commit is not canonical: {commit!r}")
    if dist.is_symlink() or not dist.is_dir():
        fail(f"dist root must be a non-symlink directory: {dist}")
    if work.is_symlink() or not work.is_dir():
        fail(f"work root must be a non-symlink directory: {work}")
    artifacts: list[dict[str, object]] = []
    total_archive_bytes = 0
    total_unpacked_bytes = 0
    for component in COMPONENTS:
        filename = f"{component}-{version}-trust-{host}.tar.xz"
        source = dist / filename
        canonical_regular_file(source, f"exact {component} dist artifact")
        declared_size = source.stat().st_size
        if declared_size < 1 or total_archive_bytes + declared_size > MAX_TOTAL_ARCHIVE_BYTES:
            fail(
                f"minimal seed archives exceed {MAX_TOTAL_ARCHIVE_BYTES} total bytes"
            )
        staged = work / "artifacts" / filename
        digest, size = copy_authenticated(source, staged)
        total_archive_bytes += size
        if total_archive_bytes > MAX_TOTAL_ARCHIVE_BYTES:
            fail(
                f"minimal seed archives exceed {MAX_TOTAL_ARCHIVE_BYTES} total bytes"
            )
        if not SHA256_RE.fullmatch(digest):
            fail(f"internal error: invalid SHA-256 for {source}")
        top = filename.removesuffix(".tar.xz")
        extracted = work / "unpack" / component
        unpacked_size = extract_authenticated(staged, extracted, top, commit)
        total_unpacked_bytes += unpacked_size
        if total_unpacked_bytes > MAX_TOTAL_UNPACKED_BYTES:
            fail(
                f"minimal seed expands beyond {MAX_TOTAL_UNPACKED_BYTES} total bytes"
            )
        artifacts.append(
            {
                "component": component,
                "filename": filename,
                "sha256": digest,
                "archive_bytes": size,
                "unpacked_bytes": unpacked_size,
                "package_root": top,
            }
        )
    manifest = {
        "schema": "trust-self-host-seed-input-v1",
        "source_version": version,
        "source_commit": commit,
        "host": host,
        "artifacts": artifacts,
    }
    write_json_exclusive(manifest_path, manifest)
    return manifest


def stage_rustc_dev_handoff(
    root: Path, input_manifest: Path, work: Path, output_root: Path
) -> tuple[Path, ...]:
    """Lay out prepare.py's trustc-dev handoff from the admitted archive.

    prepare.py writes a seed only once trustc-dev is materialized at
    <output root>/<artifact root>/<commit>/<archive> under each of its
    STAGE0_ARTIFACT_ROOTS (validate_rustc_dev_artifact_handoff). The cut's
    output root is new, so the cut lays that handoff out itself, from the
    trustc-dev archive stage-artifacts admitted and bound to HEAD: copied, never
    linked, each copy checked against the admitted digest. Both roots are
    gitignored, so the re-pin commits none of it, and publish_seed_cut.sh
    publishes dist/ alone.
    """
    roots = tuple(stage0_preparer(root).STAGE0_ARTIFACT_ROOTS)
    if not roots or not all(re.fullmatch(r"[a-z][a-z0-9-]*", item) for item in roots):
        fail(f"prepare.py declares no usable artifact roots: {roots!r}")
    manifest = load_json(input_manifest, "admitted seed-input manifest")
    if manifest.get("schema") != "trust-self-host-seed-input-v1":
        fail(f"admitted seed-input manifest has schema {manifest.get('schema')!r}")
    commit = manifest.get("source_commit")
    if not isinstance(commit, str) or not COMMIT_RE.fullmatch(commit):
        fail(f"admitted seed-input manifest names no canonical commit: {commit!r}")
    artifacts = manifest.get("artifacts")
    entries = [
        entry
        for entry in (artifacts if isinstance(artifacts, list) else [])
        if isinstance(entry, dict) and entry.get("component") == "trustc-dev"
    ]
    if len(entries) != 1:
        fail(f"admitted seed-input manifest lists {len(entries)} trustc-dev archives, not one")
    filename = entries[0].get("filename")
    digest = entries[0].get("sha256")
    if not isinstance(filename, str) or not re.fullmatch(
        r"trustc-dev-[A-Za-z0-9._+-]+\.tar\.xz", filename
    ):
        fail(f"admitted trustc-dev archive name is not canonical: {filename!r}")
    if not isinstance(digest, str) or not SHA256_RE.fullmatch(digest):
        fail(f"admitted trustc-dev archive has no canonical digest: {digest!r}")
    if output_root.exists() or output_root.is_symlink():
        fail(f"the prepared seed root must be new: {output_root}")
    source = work / "artifacts" / filename
    staged: list[Path] = []
    for artifact_root in roots:
        destination = output_root / artifact_root / commit / filename
        observed, _size = copy_authenticated(source, destination)
        if observed != digest:
            destination.unlink(missing_ok=True)
            fail(f"the admitted trustc-dev archive changed after admission: {source}")
        staged.append(destination)
    return tuple(staged)


def canonical_version_value(value: str) -> str:
    if not SEMVER_RE.fullmatch(value):
        fail(f"version is not canonical SemVer: {value!r}")
    return value


def toml_string(value: str) -> str:
    # JSON basic strings are also valid TOML basic strings for path characters.
    return json.dumps(value, ensure_ascii=True)


def write_seed_config(source: Path, output: Path, seed: Path, fail_tool: Path) -> None:
    source = canonical_regular_file(source, "bootstrap source configuration")
    for name in ("trustc", "targo", "cargo", "trustdoc", "trustfmt"):
        canonical_regular_file(seed / "bin" / name, f"seed {name}")
    if output.exists() or output.is_symlink():
        fail(f"temporary seed configuration already exists: {output}")
    fail_tool.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    fd = os.open(fail_tool, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o700)
    try:
        write_all(
            fd,
            b"#!/bin/sh\n"
            b"echo 'error: tippy is outside the minimal self-host seed workflow' >&2\n"
            b"exit 125\n",
        )
        os.fsync(fd)
    finally:
        os.close(fd)
    text = "\n".join(
        (
            "# Generated in an owner-private build directory; never commit this file.",
            f"include = [{toml_string(str(source))}]",
            "",
            "[build]",
            f"rustc = {toml_string(str(seed / 'bin' / 'trustc'))}",
            f"cargo = {toml_string(str(seed / 'bin' / 'cargo'))}",
            f"rustdoc = {toml_string(str(seed / 'bin' / 'trustdoc'))}",
            f"rustfmt = {toml_string(str(seed / 'bin' / 'trustfmt'))}",
            f"cargo-clippy = {toml_string(str(fail_tool))}",
            "submodules = false",
            "",
            "[rust]",
            'channel = "trust"',
            "download-rustc = false",
            "",
            "[llvm]",
            "download-ci-llvm = false",
            "",
        )
    )
    output.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    out_fd = os.open(output, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        write_all(out_fd, text.encode("utf-8"))
        os.fsync(out_fd)
    finally:
        os.close(out_fd)


def rust_family_name(name: str) -> bool:
    lower = name.lower()
    exact = {
        "rustc",
        "rustdoc",
        "rustfmt",
        "rustup",
        "cargo",
        "clippy-driver",
        "miri",
        "sccache",
        "tcargo",
        "trust",
        "trustc",
        "trustdoc",
        "trustfmt",
        "targo",
        "tippy",
    }
    return (
        lower in exact
        or lower.startswith("cargo-")
        or lower.startswith("rust-")
        or lower.startswith("rustc-")
        or lower.startswith("rustfmt-")
        or lower.startswith("clippy-")
        or lower.startswith("targo-")
        or lower.startswith("tcargo-")
        or lower.startswith("tippy-")
        or lower.startswith("trust-")
    )


def stock_toolchain_sysroot(path: Path) -> bool:
    """`path` is a rustup toolchain directory itself (<rustup>/toolchains/<name>),
    not a genesis adapter, whose bin/ holds wrappers rather than the compiler."""
    return path.parent.name == "toolchains" and "/genesis-stage0/" not in "/" + path.as_posix() + "/"


def forbidden_tool_path(path: Path) -> bool:
    rendered = "/" + str(path).replace("\\", "/").strip("/") + "/"
    return any(
        marker in rendered
        for marker in ("/.rustup/", "/rustup/toolchains/", "/genesis-stage0/")
    )


SANITIZED_PATH_PROFILE = "native-build-v3"
# This is a reviewed build interface, not an inventory of the person's PATH.
# Bootstrap/LLVM, the native dependencies of the extended tools (including
# openssl-src-trust's Perl + Make build), and rust-installer's install-template.sh
# are the readers. Additions require a source change and a new profile version.
# Both Make and Ninja are supported; no ambient compiler cache or Rust frontend
# is admitted. Python's two public names bind the explicitly selected interpreter.
# v2 (2026-11-05): x.py then took the former shell build-tree lock under this PATH, and v1
# omitted the lock's readers. `od` mints its token (without it the token was
# empty and x.py refused the mint's first build); `pgrep` finds an unwrapped
# bootstrap or sweep (without it that scan silently finds nothing); `lsof` reads
# a candidate's cwd on Darwin (without it the lock over-refuses); `hostname`,
# `id` and `sleep` record the holder and pace a wait.
# v3 (2026-11-06): Clean's locked gmp-mpfr-sys needs m4 for GMP's assembly
# sources; configure refuses without it. On Darwin its config.guess also reads
# system_profiler to recognize Apple CPU families. Bind both native readers
# instead of extending the private PATH with ambient executables.
COMMON_BUILD_HELPERS = (
    "ar", "as", "c++", "cc", "ld", "nm", "ranlib", "strip",
    "bash", "sh", "env", "perl", "m4", "cmake", "make", "ninja", "pkg-config",
    "git", "curl", "tar", "gzip", "xz",
    "hostname", "id", "od", "pgrep", "sleep",
    "awk", "basename", "cat", "chmod", "cmp", "cp", "cut", "date", "diff",
    "dirname", "expr", "file", "find", "grep", "head", "install", "ln", "ls",
    "mkdir", "mktemp", "mv", "printf", "ps", "pwd", "readlink", "rm", "rmdir", "sed", "sort",
    "tail", "touch", "tr", "uname", "uniq", "wc", "xargs",
)
PLATFORM_BUILD_HELPERS = {
    "apple-darwin": (
        "clang", "clang++", "codesign", "dsymutil", "install_name_tool",
        "libtool", "lipo", "lsof", "otool", "sw_vers", "sysctl", "system_profiler", "xcode-select", "xcodebuild",
        "xcrun",
    ),
    "unknown-linux-gnu": ("gcc", "g++", "ldd", "objcopy", "objdump", "readelf"),
    "unknown-linux-musl": ("gcc", "g++", "ldd", "objcopy", "objdump", "readelf"),
}
PYTHON_BUILD_HELPERS = ("python", "python3")


def build_helper_names(host: str) -> tuple[str, ...]:
    canonical_host(host)
    arch, _, platform_name = host.partition("-")
    if arch not in ("aarch64", "x86_64") or platform_name not in PLATFORM_BUILD_HELPERS:
        fail(f"sanitized PATH has no reviewed native build-helper profile for {host!r}")
    names = (*COMMON_BUILD_HELPERS, *PLATFORM_BUILD_HELPERS[platform_name], *PYTHON_BUILD_HELPERS)
    if len(set(names)) != len(names) or any(rust_family_name(name) for name in names):
        fail("sanitized PATH build-helper declaration is invalid")
    return names


def sanitized_tool_identity(target: Path) -> dict[str, object]:
    """Bind the executable at its original location; do not detach bundles/resources."""
    if not target.is_absolute() or any(char in str(target) for char in ("\n", "\r", "\x00")):
        fail(f"sanitized PATH helper has an unsafe path: {target!s}")
    if forbidden_tool_path(target) or rust_family_name(target.name):
        fail(f"sanitized PATH helper resolves to a forbidden Rust-family tool: {target}")
    try:
        before = target.lstat()
        if not stat.S_ISREG(before.st_mode) or not os.access(target, os.X_OK):
            fail(f"sanitized PATH helper must be an executable regular file: {target}")
        digest = sha256_file(target)
        after = target.lstat()
    except OSError as exc:
        fail(f"cannot authenticate sanitized PATH helper: {target}: {exc}")
    if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_mode) != (
        after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_mode,
    ):
        fail(f"sanitized PATH helper changed while it was admitted: {target}")
    return {
        "path": str(target), "device": before.st_dev, "inode": before.st_ino,
        "bytes": before.st_size, "mtime_ns": before.st_mtime_ns,
        "mode": stat.S_IMODE(before.st_mode), "sha256": digest,
    }


def create_sanitized_path(
    path_value: str, output: Path, host: str, python: Path,
) -> dict[str, object]:
    names = build_helper_names(host)
    if output.exists() or output.is_symlink():
        fail(f"sanitized PATH directory already exists: {output}")
    directories = []
    for raw in path_value.split(os.pathsep):
        if not raw or any(char in raw for char in ("\n", "\r", "\x00")):
            fail("PATH contains an empty, newline-bearing or NUL-bearing component")
        directory = Path(raw)
        if not directory.is_absolute():
            fail(f"PATH contains a relative component: {raw!r}")
        directories.append(directory)
    if not python.is_absolute():
        fail("sanitized PATH requires the explicitly selected absolute Python path")
    try:
        python = python.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        fail(f"cannot resolve sanitized PATH Python: {exc}")
    admitted = {}
    for name in names:
        if name in PYTHON_BUILD_HELPERS:
            target = python
        else:
            target = None
            for directory in directories:
                candidate = directory / name
                try:
                    metadata = candidate.stat()
                    # Match executable-file PATH precedence. Directories,
                    # nonexecutables and dangling links cannot shadow a helper.
                    if not stat.S_ISREG(metadata.st_mode) or not os.access(candidate, os.X_OK):
                        continue
                    target = candidate.resolve(strict=True)
                except (FileNotFoundError, NotADirectoryError):
                    continue
                except (OSError, RuntimeError) as exc:
                    fail(f"cannot resolve declared sanitized PATH helper {candidate}: {exc}")
                break
            if target is None:
                fail(f"sanitized PATH cannot supply declared build helper {name!r}")
        # An unreadable or forbidden first executable is an error, never a
        # fallback to a different implementation later in the ambient PATH.
        admitted[name] = sanitized_tool_identity(target)
    output.mkdir(mode=0o700, parents=True)
    for name, identity in admitted.items():
        os.symlink(identity["path"], output / name)
    return {
        "schema": "trust-sanitized-path-v2", "profile": SANITIZED_PATH_PROFILE,
        "host": host, "python": str(python), "admitted": admitted,
    }


def revalidate_sanitized_path(output: Path, manifest_path: Path) -> None:
    canonical_regular_file(manifest_path, "sanitized PATH manifest")
    try:
        with manifest_path.open("r", encoding="utf-8") as handle:
            manifest = json.load(handle)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        fail(f"cannot read sanitized PATH manifest: {exc}")
    if not isinstance(manifest, dict) or manifest.get("schema") != "trust-sanitized-path-v2":
        fail("sanitized PATH manifest has an unsupported schema")
    admitted = manifest.get("admitted")
    if manifest.get("profile") != SANITIZED_PATH_PROFILE or not isinstance(admitted, dict):
        fail("sanitized PATH manifest has an unsupported helper profile")
    host = manifest.get("host")
    if not isinstance(host, str) or set(admitted) != set(build_helper_names(host)):
        fail("sanitized PATH manifest does not contain the declared helper set")
    if any(not isinstance(admitted[name], dict) or
           admitted[name].get("path") != manifest.get("python") for name in PYTHON_BUILD_HELPERS):
        fail("sanitized PATH Python aliases do not bind the selected interpreter")
    if output.is_symlink() or not output.is_dir():
        fail(f"sanitized PATH directory changed identity: {output}")
    actual_names = {entry.name for entry in os.scandir(output)}
    if actual_names != set(admitted):
        fail("sanitized PATH entry set changed during the workflow")
    for name, expected in admitted.items():
        if not isinstance(name, str) or not isinstance(expected, dict):
            fail("sanitized PATH manifest contains a malformed entry")
        link = output / name
        if not link.is_symlink():
            fail(f"sanitized PATH entry is no longer a symlink: {link}")
        try:
            target = link.resolve(strict=True)
        except (OSError, RuntimeError) as exc:
            fail(f"sanitized PATH entry cannot be revalidated: {link}: {exc}")
        current = sanitized_tool_identity(target)
        for field, value in current.items():
            if expected.get(field) != value:
                fail(f"sanitized PATH target changed ({field}): {link}")


def tree_records(top: Path, description: str) -> list[dict[str, object]]:
    """Every entry under ``top`` in a fixed walk order, content-addressed."""
    records: list[dict[str, object]] = []
    content_cache: dict[tuple[int, int, int, int], str] = {}
    total_bytes = 0
    for directory, dirnames, filenames in os.walk(top, followlinks=False):
        dirnames.sort()
        filenames.sort()
        for name in (*dirnames, *filenames):
            if len(records) >= MAX_ARCHIVE_MEMBERS:
                fail(f"{description} exceeds {MAX_ARCHIVE_MEMBERS} filesystem entries")
            path = Path(directory) / name
            relative = path.relative_to(top).as_posix()
            metadata = path.lstat()
            mode = stat.S_IMODE(metadata.st_mode)
            if stat.S_ISLNK(metadata.st_mode):
                record: dict[str, object] = {
                    "path": relative,
                    "kind": "symlink",
                    "target": os.readlink(path),
                }
            elif stat.S_ISDIR(metadata.st_mode):
                record = {"path": relative, "kind": "directory", "mode": mode}
            elif stat.S_ISREG(metadata.st_mode):
                total_bytes += metadata.st_size
                if total_bytes > MAX_TOTAL_UNPACKED_BYTES:
                    fail(f"{description} exceeds {MAX_TOTAL_UNPACKED_BYTES} regular-file bytes")
                key = (
                    metadata.st_dev,
                    metadata.st_ino,
                    metadata.st_size,
                    metadata.st_mtime_ns,
                )
                content_digest = content_cache.get(key)
                if content_digest is None:
                    content_digest = sha256_file(path)
                    content_cache[key] = content_digest
                record = {
                    "path": relative,
                    "kind": "file",
                    "mode": mode,
                    "bytes": metadata.st_size,
                    "sha256": content_digest,
                }
            else:
                fail(f"{description} contains an unsupported special file: {path}")
            records.append(record)
    return records


def records_sha256(records: list[dict[str, object]]) -> str:
    digest = hashlib.sha256()
    for record in records:
        digest.update(json.dumps(record, separators=(",", ":"), sort_keys=True).encode("utf-8"))
        digest.update(b"\n")
    return digest.hexdigest()


CLEAN_LEAN_ENV = ("CLEAN_OLEAN_PINNED_LEAN_LIB", "CLEAN_OLEAN_REQUIRE_PINNED_LEAN")


def _canonical_json(value: object) -> bytes:
    # Python equality aliases JSON false/0 and true/1; custody must not.
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def _confined_lean_records(physical: Path) -> list[dict[str, object]]:
    """Validate the captured link graph, not an earlier filesystem walk.

    Every admitted file link ends at a captured regular file whose bytes are in
    this same snapshot. Directory links, escapes and cycles cannot hide inputs.
    """
    records = tree_records(physical, "Clean Lean installation")
    entries = {str(row["path"]): row for row in records}
    for row in records:
        if row["kind"] != "symlink":
            continue
        current = str(row["path"])
        seen = set()
        while True:
            if current in seen:
                fail("Clean Lean installation has a cyclic linked input")
            seen.add(current)
            raw = str(entries[current]["target"])
            if raw.startswith("/"):
                prefix = str(physical) + "/"
                if not raw.startswith(prefix):
                    fail("Clean Lean installation has an unbound linked input")
                resolved: list[str] = []
                components = raw[len(prefix):].split("/")
            else:
                resolved = list(Path(current).parts[:-1])
                components = raw.split("/")
            # Resolve raw components in order. normpath would erase a missing
            # or non-directory prefix in missing/../file or file/../file even
            # though the actual filesystem refuses both paths.
            for index, component in enumerate(components):
                if component in ("", "."):
                    continue
                if component == "..":
                    if not resolved:
                        fail("Clean Lean installation has an unbound linked input")
                    resolved.pop()
                    continue
                target = "/".join([*resolved, component])
                kind = entries.get(target, {}).get("kind")
                if kind == "directory":
                    resolved.append(component)
                    continue
                if kind == "file" and index == len(components) - 1:
                    break
                if kind == "symlink" and index == len(components) - 1:
                    current = target
                    break
                if kind == "symlink":
                    fail("Clean Lean installation has an unbound directory link")
                fail("Clean Lean installation has an unbound linked input")
            else:
                fail("Clean Lean installation has an unbound linked input")
            if kind == "file":
                break
    return records


def _lean_installation_selection(installation: Path) -> dict[str, object]:
    before = installation.lstat()
    link = os.readlink(installation) if stat.S_ISLNK(before.st_mode) else None
    physical = installation.resolve(strict=True)
    physical_before = physical.lstat()
    after = installation.lstat()
    physical_after = installation.stat()
    identity = lambda value: (value.st_dev, value.st_ino, value.st_mode,
                              value.st_mtime_ns, value.st_ctime_ns)
    if (identity(before) != identity(after)
            or not stat.S_ISDIR(physical_before.st_mode)
            or identity(physical_before) != identity(physical_after)):
        fail("Clean Lean installation selection changed while resolving it")
    return {"physical": str(physical), "link": link, "identity": list(identity(after)),
            "physical_identity": list(identity(physical_after))}


def verify_clean_lean_inputs(root: Path, manifest: Path, library: Path,
                             expected_sha256: str) -> dict[str, object]:
    """Join an immutable caller selector/hash to the complete current input."""
    if not isinstance(expected_sha256, str) or not SHA256_RE.fullmatch(expected_sha256):
        fail("Clean Lean manifest needs its independently bound SHA256")
    raw = canonical_regular_file(manifest, "Clean Lean input manifest").read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected_sha256:
        fail("Clean Lean input manifest bytes changed")
    value = json.loads(raw)
    current = clean_lean_inputs(root, library)
    if _canonical_json(value) != _canonical_json(current):
        fail("Clean Lean installation or source Oracle changed during the workflow")
    return current


def _lean_header_identity(path: Path) -> tuple[int, int, str]:
    """Clean's build.rs header key, used only to select its declared input.

    This is no import/kernel admission. Clean still validates whole parts,
    companions, the compiled digest manifest and the actual Oracle world.
    """
    with path.open("rb") as stream:
        header = stream.read(88)
    if len(header) < 6 or header[:5] != b"olean":
        fail(f"Clean Lean input has no olean header: {path}")
    version = header[5]
    needed, flags, start = (56, 0, 6) if version == 1 else (88, header[6] if len(header) > 6 else 0, 40)
    key = header[start:start + 40]
    if len(header) < needed or len(key) != 40 or not all(c in b"0123456789abcdefABCDEF" for c in key):
        fail(f"Clean Lean input has an invalid olean identity: {path}")
    return version, flags, key.decode("ascii")


def clean_lean_inputs(root: Path, selected_lib: Path) -> dict[str, object]:
    """Bind a declared pinned library, its source Oracle and full installation.

    The direct elan toolchain link may select a real installation elsewhere;
    that link and the physical contents are both bound. Nested directory links
    and escaping file links refuse, so tree_records cannot omit target bytes.
    """
    clean = root.resolve(strict=True) / "first-party/clean"
    pin_file = canonical_regular_file(clean / "lean-toolchain", "Clean Lean pin")
    pin = pin_file.read_text(encoding="utf-8").strip()
    if not re.fullmatch(r"leanprover/lean4:v[0-9A-Za-z.+-]+", pin):
        fail("unsupported Clean Lean pin")
    directory = pin.replace("/", "--").replace(":", "---", 1)
    if (not selected_lib.is_absolute() or ".." in selected_lib.parts
            or any(c in str(selected_lib) for c in ("\0", "\n", "\r"))
            or selected_lib.name != "lean" or selected_lib.parent.name != "lib"
            or selected_lib.parent.parent.name != directory):
        fail(f"Clean Lean library must select the exact pinned {directory}/lib/lean")
    installation = selected_lib.parent.parent
    installation = installation.parent.resolve(strict=True) / installation.name
    selected_lib = installation / "lib/lean"
    selection = _lean_installation_selection(installation)
    physical = Path(str(selection["physical"]))
    canonical_directory(physical, "Clean Lean installation")
    if selected_lib.is_symlink() or selected_lib.parent.is_symlink():
        fail("Clean Lean library directories must not be links")
    lib = canonical_directory(selected_lib, "Clean Lean library")
    if lib != physical / "lib/lean":
        fail("Clean Lean library escaped its selected installation")
    canonical_regular_file(lib / "Init/Prelude.olean", "Clean Lean Prelude")

    table = canonical_regular_file(clean / "crates/clean-olean/lean_worlds.tsv", "Clean Lean worlds")
    oracle_rows = []
    for line in table.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        columns = line.split("\t")
        if len(columns) != 4 or columns[1] not in {"oracle", "historical", "frontend-only", "measured", "canary"}:
            fail("malformed committed Clean Lean world row")
        if columns[1] == "oracle":
            oracle_rows.append(columns)
    if len(oracle_rows) != 1:
        fail("Clean Lean worlds must name exactly one Oracle")
    world, _, toolchain, names = oracle_rows[0]
    if toolchain != pin or world != pin.rsplit(":", 1)[1]:
        fail("Clean Lean Oracle differs from the committed pin")
    source_inputs = {"lean-toolchain": sha256_file(pin_file),
                     "crates/clean-olean/lean_worlds.tsv": sha256_file(table)}
    identity = None
    for name in names.split():
        path = canonical_regular_file(clean / name, "Clean Lean Oracle fixture")
        ensure_within(clean, path, "Clean Lean Oracle fixture")
        current = _lean_header_identity(path)
        if identity is not None and current != identity:
            fail("Clean Lean Oracle fixtures disagree")
        identity = current
        source_inputs[name] = sha256_file(path)
    if identity is None:
        fail("Clean Lean Oracle names no fixture")
    before = _confined_lean_records(physical)
    parts = []
    for row in before:
        name = str(row["path"])
        if name.startswith("lib/lean/") and name.endswith((".olean", ".olean.server", ".olean.private")):
            if _lean_header_identity(physical / name) != identity:
                fail(f"Clean Lean library part differs from the pinned Oracle world: {name}")
            parts.append(name)
    if not parts or "lib/lean/Init/Prelude.olean" not in parts:
        fail("Clean Lean library has no measured Prelude")
    if _canonical_json(_confined_lean_records(physical)) != _canonical_json(before):
        fail("Clean Lean installation changed during capture")
    value = {"schema": "trust.mint-clean-lean-inputs.v1", "toolchain": pin, "world": world,
             "oracle_identity": list(identity), "source_inputs": source_inputs,
             "library_path": str(selected_lib), "physical_installation": str(physical),
             "installation_link": selection["link"], "installation_selection": selection,
             "installation_mode": stat.S_IMODE(physical.stat().st_mode),
             "installation_entries": before, "olean_parts": parts,
             "environment": {CLEAN_LEAN_ENV[0]: str(selected_lib), CLEAN_LEAN_ENV[1]: "1"}}
    result = {**value, "fingerprint": hashlib.sha256(_canonical_json(value)).hexdigest()}
    # This is the final filesystem observation, after every physical-root read.
    if _canonical_json(_lean_installation_selection(installation)) != _canonical_json(selection):
        fail("Clean Lean installation selection changed during capture")
    return result


def selected_clean_lean_lib(root: Path, elan_home: Path) -> Path:
    pin = (root / "first-party/clean/lean-toolchain").read_text(encoding="utf-8").strip()
    directory = pin.replace("/", "--").replace(":", "---", 1)
    candidate = elan_home.resolve(strict=True) / "toolchains" / directory / "lib/lean"
    return Path(str(clean_lean_inputs(root, candidate)["library_path"]))


def seed_tree_fingerprint(seed: Path) -> dict[str, object]:
    records = tree_records(seed, "installed seed")
    kinds = [record["kind"] for record in records]
    return {
        "sha256": records_sha256(records),
        "entries": len(records),
        "regular_files": kinds.count("file"),
        "directories": kinds.count("directory"),
        "symlinks": kinds.count("symlink"),
        "regular_file_bytes": sum(
            int(record["bytes"]) for record in records if record["kind"] == "file"
        ),
    }


def native_seed_tool_pair(compiler_verbose: str, targo_verbose: str,
                          version: str, host: str) -> dict[str, str]:
    """Read official build bindings; never infer a pair from names or compat versions."""
    def fields(output: str, description: str) -> dict[str, str]:
        result = {}
        for line in output.splitlines():
            name, separator, value = line.partition(": ")
            if separator:
                # Targo lists independent freshness and cache capabilities under
                # repeatable metadata keys. They grant no pair authority; retain the
                # full verbose output elsewhere, but never parse them as scalar identity.
                if description == "targo" and name in TARGO_REPEATABLE_CAPABILITIES:
                    continue
                if name in result:
                    fail(f"seed {description} reports duplicate identity field {name}")
                result[name] = value
        return result

    compiler = fields(compiler_verbose, "trustc")
    frontend = fields(targo_verbose, "targo")
    commit = compiler.get("commit-hash", "")
    if len(commit) not in (40, 64) or not COMMIT_RE.fullmatch(commit):
        fail("seed trustc reports no exact source commit")
    if compiler.get("binary") != "trustc":
        fail("seed compiler is not the Trust-native entrypoint")
    if frontend.get("trust-repo-commit-hash") != commit:
        fail("seed targo is unbound or comes from a different Trust source commit")
    if compiler.get("host") != host or frontend.get("host") != host:
        fail("seed trustc/targo native host identity does not match the requested host")
    product = compiler.get("trust", "")
    if not SEMVER_RE.fullmatch(product) or product.split("+", 1)[0] != version:
        fail("seed trustc reports no exact Trust product version")
    if frontend.get("trust") != product:
        fail("seed targo Trust product version differs from its paired compiler")
    if not targo_verbose.startswith("targo "):
        fail("seed frontend is not the Trust-native targo entrypoint")
    return {"source_commit": commit, "host": host, "trust_version": product}


def _seed_probe_semantics(seed: Path, version: str, host: str, probe):
    verbose = probe("trustc", "-vV")
    if not re.search(rf"(?m)^host:\s*{re.escape(host)}\s*$", verbose):
        fail(f"seed trustc host does not match {host}: {verbose!r}")
    if version not in verbose:
        fail(f"seed trustc version does not contain {version}: {verbose!r}")
    reported_sysroot = probe("trustc", "--print", "sysroot")
    try:
        sysroot = Path(reported_sysroot).resolve(strict=True)
    except OSError as exc:
        fail(f"seed trustc reported an invalid sysroot {reported_sysroot!r}: {exc}")
    if sysroot != seed.resolve(strict=True):
        fail(f"seed trustc escaped its installed sysroot: {sysroot} != {seed}")
    targo_verbose = probe("targo", "--version", "--verbose")
    native_pair = native_seed_tool_pair(verbose, targo_verbose, version, host)
    tool_versions = {
        "trustc": verbose.splitlines()[0] if verbose else "",
        "targo": targo_verbose,
        "trustfmt": probe("trustfmt", "--version"),
    }

    return native_pair, tool_versions


def _native_seed_stdout(streams, label: str) -> str:
    if type(streams) is not tuple or len(streams) != 2 or any(
            type(raw) is not bytes or len(raw) > 64 * 1024 for raw in streams):
        fail(f"{label} output needs both bounded original byte streams")
    raw, stderr = streams
    # Separate pipes establish no inter-stream ordering. Never silently omit
    # stderr or fabricate the trace ordinary subprocess.STDOUT would produce.
    if stderr:
        fail(f"{label} stderr cannot be discarded or reordered")
    try:
        return raw.decode("utf-8").strip()
    except UnicodeDecodeError:
        fail(f"{label} output is not UTF-8")


def native_seed_probe_data(seed: Path, version: str, host: str,
                           observations: dict[tuple[str, tuple[str, ...]],
                                              tuple[bytes, bytes]]) -> dict[str, object]:
    """Check ONLY fixed probe text DATA without launching any process.

    The resident must supply these bytes from its same four actually closed
    native probes, and separately retains the real source/archive, six-entry
    static surface, loader, cache, producer and endpoint owners. This parser
    authenticates none of those obligations and returns no seed/SDK seal.
    It has no CLI, decoder, subprocess fallback or fresh deadline.
    """
    version = canonical_version_value(version)
    host = canonical_host(host)
    if seed.is_symlink() or not seed.is_dir():
        fail("native probe data needs the original non-symlink seed directory")
    expected = {
        ("trustc", ("-vV",)), ("trustc", ("--print", "sysroot")),
        ("targo", ("--version", "--verbose")), ("trustfmt", ("--version",)),
    }
    if type(observations) is not dict or observations.keys() != expected:
        fail("native seed probe data needs exactly the four fixed query outputs")
    texts = {}
    for key, streams in observations.items():
        texts[key] = _native_seed_stdout(streams, "native seed probe")

    def read(name, *arguments):
        return texts[(name, arguments)]

    native_pair, tool_versions = _seed_probe_semantics(seed, version, host, read)
    return {"native_tool_pair": native_pair, "tool_versions": tool_versions}


def seed_static_data(seed: Path) -> dict[str, object]:
    """Read the ordinary pre-probe surface without executing candidate tools.

    This is partial DATA, not a validated seed or an ownership capability. The
    real original probes, loader checks and final tree fingerprint remain
    separate obligations, alongside native source/output/resource custody.
    """
    if seed.is_symlink() or not seed.is_dir():
        fail(f"seed sysroot must be a non-symlink directory: {seed}")
    required = ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt")
    identities: dict[str, str] = {}
    for name in required:
        path = seed / "bin" / name
        try:
            resolved = path.resolve(strict=True)
        except OSError as exc:
            fail(f"seed is missing required entrypoint {name}: {exc}")
        ensure_within(seed, resolved, f"seed entrypoint {name}")
        if not resolved.is_file() or not os.access(resolved, os.X_OK):
            fail(f"seed entrypoint is not executable: {path}")
        identities[name] = sha256_file(resolved)

    for directory, dirnames, filenames in os.walk(seed, followlinks=False):
        for name in (*dirnames, *filenames):
            path = Path(directory) / name
            if path.is_symlink():
                try:
                    target = path.resolve(strict=True)
                except OSError as exc:
                    fail(f"seed contains a broken symlink: {path}: {exc}")
                ensure_within(seed, target, f"seed symlink {path}")

    return {"entrypoint_sha256": identities}


SEED_LOADER_PROGRAMS = ("trustc", "targo", "trustfmt")


def _seed_loader_program():
    return (shutil.which("otool") if platform.system() == "Darwin"
            else None if platform.system() == "Linux" else shutil.which("ldd"))


def _seed_loader_evidence(seed: Path, name: str, evidence: str) -> str:
    lowered = evidence.lower().replace("\\", "/")
    if "/.rustup/" in lowered or "/genesis-stage0/" in lowered:
        fail(f"seed {name} retains a forbidden stock-toolchain dependency: {evidence}")
    return evidence.replace(str(seed), "{seed}")


def _seed_surface(seed, version, host, identities, tool_versions, native_pair,
                  loader_evidence, linux_runtime=None):
    result: dict[str, object] = {
        "schema": "trust-self-host-seed-surface-v1",
        "source_version": version,
        "host": host,
        "entrypoint_sha256": identities,
        "tool_versions": tool_versions,
        "native_tool_pair": native_pair,
        "loader_evidence": loader_evidence,
        "tree": seed_tree_fingerprint(seed),
    }
    if linux_runtime is not None:
        result["linux_runtime_closure"] = linux_runtime
    return result


def native_seed_loader_plan() -> dict[str, object]:
    """Ordinary Darwin loader selection DATA, never native input ownership.

    The resident must bind and retain the actual search/read-set and selected
    native command before dispatch. This neither opens an input nor authorizes
    argv, child execution, a Seed, SDK or READY. Other native hosts are not
    implemented by this separate capture route.
    """
    if platform.system() != "Darwin":
        fail("native seed loader capture supports only Darwin")
    loader = _seed_loader_program()
    if loader is not None and (type(loader) is not str or not loader
            or "\0" in loader or len(os.fsencode(loader)) > 4096):
        fail("native seed loader selection is not bounded path DATA")
    return {"loader": loader, "programs": list(SEED_LOADER_PROGRAMS) if loader else []}


def native_seed_surface_data(seed: Path, version: str, host: str, observations,
                             selected_loader, loader_observations) -> dict[str, object]:
    """Reuse the entire ordinary Darwin seed surface on closed-probe DATA.

    No process is launched here. Only the native caller can supply the SAME
    actual closed four probes, selected loader and all three loader closures,
    original source/output/cache/SDK/GNU owners and endpoint. Freely fabricated
    bytes can call this reducer but cannot thereby acquire any such owner or a
    semantic Seed. Separate stderr refuses rather than inventing merged order.
    """
    plan = native_seed_loader_plan()
    if (type(selected_loader) not in (str, type(None))
            or selected_loader != plan["loader"]):
        fail("native seed loader selection changed")
    if (type(loader_observations) is not dict
            or loader_observations.keys() != set(plan["programs"])):
        fail("native seed loader data needs its complete original population")
    version = canonical_version_value(version)
    host = canonical_host(host)
    static = seed_static_data(seed)
    probes = native_seed_probe_data(seed, version, host, observations)
    evidence = {name: _seed_loader_evidence(
        seed, name, _native_seed_stdout(loader_observations[name], "native seed loader"))
        for name in plan["programs"]}
    return _seed_surface(seed, version, host, static["entrypoint_sha256"],
                         probes["tool_versions"], probes["native_tool_pair"], evidence)


def validate_seed(seed: Path, version: str, host: str) -> dict[str, object]:
    version = canonical_version_value(version)
    host = canonical_host(host)
    static = seed_static_data(seed)
    identities = static["entrypoint_sha256"]

    # Inspect every packaged native ELF (including libexec and transitive
    # providers) before executing any candidate tool. The final surface includes
    # this receipt, so the existing post-build byte comparison binds it too.
    linux_runtime = foreign_load_commands(seed, []) if platform.system() == "Linux" else None

    # The checked loader and executed Linux tools must see the same environment:
    # inherited LD_*/GLIBC_TUNABLES could otherwise select unobserved providers.
    # Darwin retains the mint's existing declared DYLD provider environment.
    probe_env = dict(linux_seed_support().ENV) if linux_runtime is not None else dict(os.environ)
    probe_env["LC_ALL"] = "C"
    probe_env["LANG"] = "C"

    def probe(name: str, *arguments: str) -> str:
        try:
            completed = subprocess.run(
                [str(seed / "bin" / name), *arguments],
                env=probe_env,
                check=False,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=30,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            fail(f"seed {name} probe failed: {exc}")
        if completed.returncode != 0:
            fail(
                f"seed {name} {' '.join(arguments)} probe failed with status "
                f"{completed.returncode}: {completed.stdout.strip()}"
            )
        return completed.stdout.strip()

    native_pair, tool_versions = _seed_probe_semantics(seed, version, host, probe)

    loader = _seed_loader_program()
    loader_evidence: dict[str, str] = {}
    if loader:
        for name in SEED_LOADER_PROGRAMS:
            try:
                completed = subprocess.run(
                    [loader, "-L", str(seed / "bin" / name)]
                    if Path(loader).name == "otool"
                    else [loader, str(seed / "bin" / name)],
                    env=probe_env,
                    check=False,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    timeout=30,
                )
            except (OSError, subprocess.TimeoutExpired) as exc:
                fail(f"cannot inspect seed {name} loader dependencies: {exc}")
            evidence = completed.stdout.strip()
            if completed.returncode != 0:
                fail(f"cannot inspect seed {name} loader dependencies: {evidence}")
            loader_evidence[name] = _seed_loader_evidence(seed, name, evidence)
    return _seed_surface(seed, version, host, identities, tool_versions, native_pair,
                         loader_evidence, linux_runtime)


def write_json_exclusive(path: Path, value: object) -> None:
    path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    payload = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        write_all(fd, payload)
        os.fsync(fd)
    finally:
        os.close(fd)


def continuation_context(
    root: Path, record_path: Path, expected_sha256: str, *, work_only: bool = False,
    config: Path | None = None, host: str | None = None,
    clean_lean_lib: Path | None = None, library_path: str = "",
    seed_dylib_path: str = "", ddc_seed: Path | None = None,
    cargo_source: Path | None = None, python: Path | None = None,
) -> dict[str, object]:
    """Bind phase two to a prepared record; this grants no self-host result."""
    spec = importlib.util.spec_from_file_location(
        "trust_mint_continuation", Path(__file__).with_name("mint_seed_recovery.py"))
    if spec is None or spec.loader is None:
        fail("cannot load the retained mint verifier")
    recovery = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(recovery)
    try:
        if not isinstance(expected_sha256, str) or not SHA256_RE.fullmatch(expected_sha256):
            fail("continuation record requires an exact SHA-256")
        record = recovery.document(record_path, expected_sha256)
        if record.get("mode") not in (None, recovery.AUDIT_MODE):
            fail("unknown continuation boundary")
        retained_audit = record.get("mode") == recovery.AUDIT_MODE
        if (record.get("schema") != recovery.SCHEMA or record.get("state") != "prepared"
                or record.get("qualification") is not False
                or record.get("strict_native_verifier_passed") is not True
                or record.get("original_work_retained") is not retained_audit
                or record.get("original_private_cargo_retained") is not retained_audit
                or record.get("cargo_home_absent_for_fresh_inputs") is not (not retained_audit)):
            fail("continuation requires a prepared, unqualified phase-split record")
        root = canonical_directory(root, "continuation product checkout")
        product = record["product_source"]
        if product["root"] != str(root) or record["root"] != str(root):
            fail("continuation product root differs")
        repository_state(root, product["commit"])
        version = canonical_version(root)
        retained_build = root / "build" / f"pack-mint-{version}-{canonical_host(record['host'])}-{product['commit'][:12]}"
        if record["version"] != version or record["build"] != str(retained_build):
            fail("continuation retained build differs from its product source")
        try:
            receipt_path = retained_build / record["host"] / "stage2/tool-provenance.json"
            if retained_audit:
                receipt_path = Path(record["stage_provenance_path"])
                if (not receipt_path.is_absolute() or receipt_path.parent != Path(record["evidence"])
                        or receipt_path.is_relative_to(retained_build)
                        or not re.fullmatch(r"mint-continuation-[A-Za-z0-9-]+-stage-provenance\.json", receipt_path.name)):
                    fail("continuation external stage audit path differs")
                if recovery.digest(Path(record["evidence"]) / "RETAINED.json") != record["evidence_sha256"]["retained_inventory"]:
                    fail("continuation original failure inventory changed")
                recovery.retained_files(Path(record["evidence"]))
            stage_receipt = recovery.document(receipt_path,
                                              record["evidence_sha256"]["stage_provenance"])
            if (stage_receipt.get("status") != "internal-release-ready" or stage_receipt.get("errors") != []
                    or stage_receipt.get("writer") != "scripts/mint_and_prove_seed.sh"
                    or stage_receipt.get("stage") != 2 or stage_receipt.get("host") != record["host"]
                    or not isinstance(stage_receipt.get("compiler"), dict)
                    or stage_receipt["compiler"].get("source_commit") != product["commit"]):
                fail("continuation stage audit is not an accepted mint of this product")
        except recovery.RecoveryError as exc:
            fail(f"continuation retained stage provenance changed: {exc}")
        engine_api = SimpleNamespace(git_command=git_command, COMMIT_RE=COMMIT_RE)
        if record["engine_source"] != recovery.engine_identity(engine_api):
            fail("continuation orchestration source changed")
        work = canonical_directory(Path(record["work"]), "continuation private workspace")
        if work.parent != root / "build" or not work.name.startswith(".mint-and-prove."):
            fail("continuation private workspace escapes the product build directory")
        for key, leaf in (("safe_bin", "safe-bin"), ("path_manifest", "safe-path.json"),
                          ("cargo_home", "cargo-home")):
            if record[key] != str(work / leaf):
                fail(f"continuation {key} differs from its private workspace")
        environment = record["declared_environment"]
        if (environment["CARGO_HOME"] != record["cargo_home"]
                or environment["RUSTUP_HOME"] != str(work / "environment-mint/rustup-home")):
            fail("continuation declared environment differs from its private workspace")
        safe = recovery.document(Path(record["path_manifest"]), record["evidence_sha256"]["safe_path"])
        revalidate_sanitized_path(Path(record["safe_bin"]), Path(record["path_manifest"]))
        if not work_only:
            if clean_lean_lib is not None:
                physical = canonical_directory(clean_lean_lib, "continuation Lean library")
                retained = Path(stage_receipt["build_authority"]["clean_lean_inputs"]["physical_installation"]) / "lib/lean"
                if physical != retained:
                    fail("continuation clean_lean_lib selection differs from retained evidence (physical installation changed)")
            selected = {
                "config": str(canonical_regular_file(config, "continuation bootstrap config")) if config else None,
                "host": host,
                # Clean binds both the declared Elan alias and its physical
                # installation. Preserve the literal environment selector.
                "clean_lean_lib": str(clean_lean_lib) if clean_lean_lib else None,
                "library_path": library_path, "seed_dylib_path": seed_dylib_path,
                "ddc_seed": str(canonical_directory(ddc_seed, "continuation DDC oracle", stock_oracle=True)) if ddc_seed else None,
                "cargo_source": str(canonical_directory(cargo_source, "continuation Cargo input")) if cargo_source else None,
                "python": str(canonical_regular_file(python, "continuation Python")) if python else None,
            }
            expected = {"config": record["config"], "host": record["host"],
                        "clean_lean_lib": environment["CLEAN_OLEAN_PINNED_LEAN_LIB"],
                        "library_path": environment.get("LIBRARY_PATH", ""),
                        "seed_dylib_path": environment.get("DYLD_LIBRARY_PATH", ""),
                        "ddc_seed": record["ddc_seed"], "cargo_source": record["cargo_source"],
                        "python": safe["python"]}
            for key, value in expected.items():
                if selected[key] != value:
                    fail(f"continuation {key} selection differs from retained evidence")
        return record
    except (recovery.RecoveryError, OSError, ValueError, KeyError, TypeError) as exc:
        fail(f"continuation context refused: {exc}")


def finalize_manifest(
    root: Path,
    input_manifest: Path,
    output: Path,
    config: Path,
    source_config: Path,
    stage2: Path,
    source_date_epoch: int,
    path_manifest: Path,
    surface_manifest: Path,
    library_path: str,
    config_manifest: Path,
    library_manifest: Path,
    mint_tools_manifest: Path,
    mint_receipt: Path,
    cargo_home_manifest: Path,
    seed_dylib_path: str,
    seed_dylib_manifest: Path,
    clean_lean_manifest: Path,
    clean_lean_lib: Path,
    clean_lean_manifest_sha256: str,
    continuation_record: Path | None = None,
    continuation_record_sha256: str | None = None,
    continuation_build_jobs: int | None = None,
) -> None:
    root = root.resolve(strict=True)
    with input_manifest.open("r", encoding="utf-8") as handle:
        manifest = json.load(handle)
    with path_manifest.open("r", encoding="utf-8") as handle:
        safe_path = json.load(handle)
    with surface_manifest.open("r", encoding="utf-8") as handle:
        seed_surface = json.load(handle)
    with config_manifest.open("r", encoding="utf-8") as handle:
        config_closure = json.load(handle)
    with library_manifest.open("r", encoding="utf-8") as handle:
        native_libraries = json.load(handle)
    with mint_tools_manifest.open("r", encoding="utf-8") as handle:
        mint_tools = json.load(handle)
    cargo_home = load_json(cargo_home_manifest, "cargo home input manifest")
    seed_dylibs = load_json(seed_dylib_manifest, "seed dylib input manifest")
    lean = verify_clean_lean_inputs(root, clean_lean_manifest, clean_lean_lib,
                                   clean_lean_manifest_sha256)
    manifest["source_date_epoch"] = source_date_epoch
    manifest["bootstrap_config_sha256"] = sha256_file(config)
    source_config = canonical_regular_file(source_config, "bootstrap source configuration")
    ensure_within(root, source_config, "bootstrap source configuration")
    manifest["source_config"] = source_config.relative_to(root).as_posix()
    manifest["source_config_sha256"] = sha256_file(source_config)
    manifest["source_config_closure"] = config_closure
    manifest["mint_toolchain"] = mint_tools
    stage2 = canonical_regular_file(stage2, "fresh stage2 trustc")
    ensure_within(root, stage2, "fresh stage2 trustc")
    manifest["stage2_trustc"] = stage2.relative_to(root).as_posix()
    manifest["stage2_trustc_sha256"] = sha256_file(stage2)
    manifest["environment"] = {
        "ambient_environment_inherited": False,
        "cargo_network_offline": True,
        "ambient_rust_family_on_path": False,
        "sanitized_path_inputs": safe_path,
        "explicit_library_path": library_path.split(os.pathsep) if library_path else [],
        "native_library_inputs": native_libraries,
        # Inputs of this phase; a continuation explicitly records its fresh copy.
        "cargo_home_inputs": cargo_home,
        # First on DYLD_LIBRARY_PATH: what a seed's foreign load commands resolve to.
        "seed_dylib_path": seed_dylib_path.split(os.pathsep) if seed_dylib_path else [],
        "seed_dylib_inputs": seed_dylibs,
        "clean_lean_inputs": lean,
        "clean_lean_manifest_sha256": clean_lean_manifest_sha256,
    }
    manifest["seed_surface"] = seed_surface
    receipt_path = canonical_regular_file(mint_receipt, "seed-mint receipt")
    manifest["pack_cut"] = {
        "receipt_sha256": sha256_file(receipt_path),
        **parse_receipt(receipt_path.read_text(encoding="utf-8")),
    }
    manifest["result"] = "self-host-rebuild-and-sanity-pass"
    manifest["claim_boundary"] = (
        "This records exact inputs and a minimal-environment rebuild. It is not a kernel "
        "execution trace; scripts/prove_rust_free_build.sh --build owns that claim."
    )
    if any(value is not None for value in
           (continuation_record, continuation_record_sha256, continuation_build_jobs)):
        if (continuation_record is None or continuation_record_sha256 is None
                or type(continuation_build_jobs) is not int or continuation_build_jobs < 1):
            fail("continuation finalization requires its record, SHA-256 and positive fresh job count")
        record = continuation_context(root, continuation_record, continuation_record_sha256, work_only=True)
        record = continuation_context(root, continuation_record, continuation_record_sha256,
                                      config=source_config, host=manifest["host"],
                                      clean_lean_lib=clean_lean_lib, library_path=library_path,
                                      seed_dylib_path=seed_dylib_path,
                                      ddc_seed=Path(record["ddc_seed"]),
                                      cargo_source=Path(cargo_home["source"]) if cargo_home.get("source") else None,
                                      python=Path(sys.executable))
        cargo_scope = ("original retained private Cargo inputs; new audit and actual continuation tail"
                       if record.get("mode") == "retained-work-at-provenance" else
                       "fresh continuation phase; original private Cargo inputs were not retained")
        manifest["continuation"] = {"record_sha256": continuation_record_sha256, "record": record,
                                    "fresh_selfhost_jobs": continuation_build_jobs,
                                    "cargo_inputs_scope": cargo_scope}
        manifest["environment"]["cargo_home_inputs_scope"] = (cargo_scope if record.get("mode") == "retained-work-at-provenance"
                                                               else "fresh continuation phase")
    write_json_exclusive(output, manifest)


# ---------------------------------------------------------------------------
# The pack cut (docs/DECISION_QUEUE.md D12): build from the pinned seed,
# double-compile the result against an independent seed (diverse only when
# that seed is lineage-disjoint), and emit the commit-bound re-pin.

STAGE0_GENERATED_MARKER = "# The section below was generated by src/tools/trust-stage0-dist/prepare.py"
MINT_BUILD_PREFIX = "pack-mint-"
RECEIPT_SCHEMA = "trust-seed-mint-v1"


def read_stage0_pin(root: Path) -> dict[str, str]:
    """The key=value records of the committed src/stage0."""
    path = canonical_regular_file(root / "src" / "stage0", "src/stage0")
    return parse_stage0_pin(path.read_bytes())


def parse_stage0_pin(raw: bytes) -> dict[str, str]:
    """SAME maintained pin parser over retained bytes; no source authority."""
    if type(raw) is not bytes:
        fail("src/stage0 capture must be immutable bytes")
    if len(raw) > MAX_CONFIG_BYTES:
        fail(f"src/stage0 exceeds {MAX_CONFIG_BYTES} bytes")
    fields: dict[str, str] = {}
    for number, line in enumerate(raw.decode("utf-8").splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        key, separator, value = line.partition("=")
        if not separator or not key.strip() or not value.strip():
            fail(f"src/stage0:{number}: expected a key=value record")
        if key.strip() in fields:
            fail(f"src/stage0:{number}: duplicate key {key.strip()!r}")
        fields[key.strip()] = value.strip()
    for key in ("compiler_git_commit_hash", "compiler_date", "compiler_version", "dist_server"):
        if not fields.get(key):
            fail(f"src/stage0 does not declare {key}")
    if not COMMIT_RE.fullmatch(fields["compiler_git_commit_hash"]):
        fail("src/stage0 compiler_git_commit_hash is not a canonical commit")
    if not DATE_RE.fullmatch(fields["compiler_date"]):
        fail("src/stage0 compiler_date is not YYYY-MM-DD")
    return fields


def preparation_seed_archive_plan(raw: bytes, host: str) -> dict[str, object]:
    """Use Bootstrap's SAME full refresh selection on captured original DATA.

    This neither opens an archive nor admits its hash, creates an input owner,
    extracts, probes, or issues Seed/SDK. The resident must retain the original
    committed/physical pin and code through actual native closure and match all
    selected archives to its actual guarded population before any projection.
    """
    pin = parse_stage0_pin(raw)
    host = canonical_host(host)
    version, date = pin["compiler_version"], pin["compiler_date"]
    if not SEMVER_RE.fullmatch(version):
        fail("src/stage0 compiler_version is not canonical SemVer")
    archives, legacy_targo, legacy_tippy = _IDENTITY_OWNER.component_archives(
        pin, date, version, host, ".tar.xz")
    selected = []
    for filename, component in archives:
        path = "dist/{}/{}".format(date, filename)
        checksum = pin.get(path)
        if not isinstance(checksum, str) or not SHA256_RE.fullmatch(checksum):
            fail("src/stage0 lacks the exact selected archive checksum: " + path)
        top = filename.removesuffix(".tar.xz")
        _IDENTITY_OWNER.component_projection(top, top, component)
        selected.append({"path": "bootstrap/trust-stage0/" + path,
                         "sha256": checksum, "top": top, "component": component})
    return {"schema": "trust-native-seed-archive-plan-v1", "host": host,
            "commit": pin["compiler_git_commit_hash"], "date": date,
            "version": version, "extraction_stamp": stage0_extraction_stamp(pin),
            "archives": selected, "legacy_targo": legacy_targo,
            "legacy_tippy": legacy_tippy}


def compiler_identity(sysroot: Path, description: str, *, stock_oracle: bool = False) -> dict[str, object]:
    """Who a sysroot's compiler says it is, and the bytes that say it."""
    sysroot = canonical_directory(sysroot, description, stock_oracle=stock_oracle)
    compiler = sysroot / "bin" / "trustc"
    if not compiler.is_file():
        compiler = sysroot / "bin" / "rustc"
    compiler = canonical_regular_file(compiler, f"{description} compiler")
    environment = {
        "PATH": os.environ.get("PATH", ""),
        "LC_ALL": "C",
        "LANG": "C",
        "HOME": os.environ.get("HOME", "/"),
    }
    try:
        if '__trust_source_loader__' in globals() and __trust_source_loader__.context is not None:
            live = __trust_source_loader__.context
            completed = live.auxiliary('compiler-identity','mint_seed_support.compiler_identity',
                [str(compiler),'-vV'],Path.cwd(),environment,maximum=65536,seconds=60)
        else:
            completed = subprocess.run(
                [str(compiler), "-vV"],
                env=environment,
                check=False,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=60,
            )
    except (OSError, subprocess.TimeoutExpired) as exc:
        fail(f"cannot run {compiler} -vV: {exc}")
    if completed.returncode != 0:
        fail(f"{compiler} -vV exited {completed.returncode}: {completed.stdout.strip()}")
    fields: dict[str, str] = {}
    for line in completed.stdout.splitlines():
        key, separator, value = line.partition(": ")
        if separator:
            fields[key.strip()] = value.strip()
    commit = fields.get("commit-hash", "")
    if not COMMIT_RE.fullmatch(commit):
        fail(f"{description} compiler reports no commit-hash: {completed.stdout.strip()!r}")
    host = canonical_host(fields.get("host", ""))
    drivers = sorted(
        path
        for pattern in ("librustc_driver-*.dylib", "librustc_driver-*.so")
        for path in (sysroot / "lib").glob(pattern)
    )
    if len(drivers) != 1:
        fail(f"{description} must ship exactly one lib/librustc_driver, found {len(drivers)}")
    driver = canonical_regular_file(drivers[0], f"{description} compiler driver")
    return {
        "sysroot": str(sysroot),
        "compiler": compiler.relative_to(sysroot).as_posix(),
        "compiler_sha256": sha256_file(compiler),
        "driver": driver.relative_to(sysroot).as_posix(),
        "driver_sha256": sha256_file(driver),
        "commit": commit,
        "host": host,
        "date": fields.get("commit-date", ""),
        "release": fields.get("release", ""),
        "trust": fields.get("trust"),
        # A Trust compiler names itself; anything else is another lineage.
        "lineage": "trust" if fields.get("binary") == "trustc" or "trust" in fields else "stock",
    }


SYSTEM_DYLIB_PREFIXES = ("/usr/lib/", "/System/Library/")
MACHO_MAGICS = {
    b"\xcf\xfa\xed\xfe", b"\xce\xfa\xed\xfe", b"\xfe\xed\xfa\xcf", b"\xfe\xed\xfa\xce",
    b"\xca\xfe\xba\xbe", b"\xbe\xba\xfe\xca",
}


def macho_load_commands(binary: Path) -> list[str]:
    """The dylibs a Mach-O names (`otool -L`), its own install name included."""
    try:
        completed = subprocess.run(
            ["/usr/bin/otool", "-L", str(binary)],
            env={"PATH": "/usr/bin:/bin", "LC_ALL": "C", "LANG": "C"},
            check=False, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        fail(f"cannot read the load commands of {binary}: {exc}")
    if completed.returncode != 0:
        fail(f"otool -L {binary} exited {completed.returncode}: {completed.stdout.strip()[:400]}")
    return [
        line.strip().split(" (compatibility", 1)[0].strip()
        for line in completed.stdout.splitlines()[1:]
        if line.strip()
    ]


def linux_seed_support():
    """Load the shared ELF checker under the mint launcher's isolated Python."""
    import importlib.util

    path = Path(__file__).resolve().parent / "lib" / "seed_linux.py"
    if "__trust_source_loader__" in globals():
        module = __trust_source_loader__.module("trust_mint_seed_linux", path)
    else:
        spec = importlib.util.spec_from_file_location("trust_mint_seed_linux", path)
        if spec is None or spec.loader is None:
            fail(f"cannot load Linux runtime closure helper: {path}")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
    return module


def foreign_load_commands(
    sysroot: Path, providers: list[Path], *, external_bootstrap: bool = False
) -> dict[str, object]:
    """Linux binds the shared strict native ELF closure. On macOS, every load
    command of a Mach-O under the sysroot's bin/, lib/ and
    libexec/ that names neither the OS nor the sysroot itself, and the declared
    directory (--seed-dylib-path) that provides it. The cut puts those
    directories first on DYLD_LIBRARY_PATH, which dyld searches by the leaf name
    BEFORE an absolute load path, so a foreign copy at that path is never loaded.
    An unprovided foreign load is refused: dyld would load whatever that path
    holds on this machine. Measured 2026-10-09: the 2026-07-13 seed's cargo
    (minted before targo vendored libgit2) names Homebrew's libgit2.1.9.dylib,
    and under the cut it mapped Homebrew's libgit2 1.9.7 and, through it,
    libssh2, llhttp and openssl@3 -- five libraries nothing declared."""
    if platform.system() == "Linux":
        # DYLD_LIBRARY_PATH has no Linux meaning. Do not silently accept an
        # override that the actual loader will never use.
        if providers:
            fail("Linux --seed-dylib-path is unsupported; runtime providers must be internal or OS files")
        try:
            helper = linux_seed_support()
            host = native_host()
            closure = (helper.external_bootstrap_closure(sysroot, host) if external_bootstrap
                       else helper.closure(sysroot, host, []))
        except (ValueError, OSError, subprocess.TimeoutExpired) as exc:
            fail(f"Linux ELF runtime closure refused: {exc}")
        if closure["unresolved"]:
            fail("Linux ELF runtime closure has undeclared foreign providers: " + "; ".join(
                f"{row['binary']} -> {row['provider']}" for row in closure["unresolved"][:8]))
        return closure
    if platform.system() != "Darwin":
        return {"checked": False, "reason": f"implemented for macOS only ({platform.system()})"}
    sysroot = sysroot.resolve(strict=True)
    internal_leaves = {path.name for path in sysroot.rglob("*.dylib")}
    rows: list[dict[str, object]] = []
    for sub in ("bin", "lib", "libexec"):
        base = sysroot / sub
        if not base.is_dir():
            continue
        for binary in sorted(base.rglob("*")):
            if binary.is_symlink() or not binary.is_file():
                continue
            with binary.open("rb") as handle:
                if handle.read(4) not in MACHO_MAGICS:
                    continue
            for load in macho_load_commands(binary):
                leaf = load.rsplit("/", 1)[-1]
                if load.startswith(SYSTEM_DYLIB_PREFIXES):
                    continue
                if binary.suffix == ".dylib" and leaf == binary.name:
                    continue  # a dylib's own install name
                if load.startswith(("@rpath/", "@loader_path/", "@executable_path/")):
                    if leaf in internal_leaves:
                        continue
                elif Path(load).is_absolute() and Path(load).resolve().is_relative_to(sysroot):
                    continue
                provider = next(
                    (directory / leaf for directory in providers if (directory / leaf).is_file()), None
                )
                rows.append({
                    "binary": binary.relative_to(sysroot).as_posix(),
                    "load": load,
                    "provider": str(provider) if provider is not None else None,
                    "provider_sha256": sha256_file(provider) if provider is not None else None,
                })
    unprovided = [row for row in rows if row["provider"] is None]
    if unprovided:
        fail(
            f"{sysroot} loads {len(unprovided)} foreign librar"
            f"{'y' if len(unprovided) == 1 else 'ies'} that no --seed-dylib-path provides, so dyld "
            "would load whatever this machine holds there: "
            + "; ".join(f"{row['binary']} -> {row['load']}" for row in unprovided[:8])
        )
    return {"checked": True, "foreign": rows}


def pinned_stage0_identity(
    root: Path, build: Path, host: str, providers: list[Path] | None = None
) -> dict[str, object]:
    """The seed bootstrap extracted for this build IS the src/stage0 pin."""
    pin = read_stage0_pin(root)
    stage0 = build / canonical_host(host) / "stage0"
    stamp_path = stage0 / ".rustc-stamp"
    try:
        stamp = stamp_path.read_text(encoding="utf-8")
    except OSError as exc:
        fail(f"no bootstrap extraction stamp at {stamp_path}: {exc}")
    expected_stamp = stage0_extraction_stamp(pin)
    if stamp != expected_stamp:
        fail(f"{stamp_path} records {stamp!r}, not the pin's extraction identity {expected_stamp!r}")
    runtime = foreign_load_commands(stage0, providers or [])
    identity = compiler_identity(stage0, "pinned stage0")
    if identity["host"] != host:
        fail(f"the extracted stage0 reports host {identity['host']!r}, not {host!r}")
    if identity["commit"] != pin["compiler_git_commit_hash"] or identity["date"] != pin["compiler_date"]:
        fail(
            f"the extracted stage0 is {identity['commit']} ({identity['date']}), not the "
            f"src/stage0 pin {pin['compiler_git_commit_hash']} ({pin['compiler_date']})"
        )
    identity["foreign_loads"] = runtime
    return identity


CARGO_HOME_INPUT_TREES = ("registry/index", "registry/cache", "git/db")


def cargo_home_inputs(source: Path | None, destination: Path) -> dict[str, object]:
    """Fill the cut's ONE private cargo home from `source`, a cargo home that a
    networked build of this commit filled, and bind what it was given by content.

    Every x.py run of the cut is offline (CARGO_NET_OFFLINE) and starts from an
    empty environment, so the crate sources -- the crates.io index and archives,
    and the git dependencies (ty and clean pin first-party repositories by
    revision) -- are handed in. Measured 2026-10-09: with a fresh cargo home the
    first real cut stopped at "Building bootstrap" ("no matching package named
    `cc` found ... offline mode"). Only the trees cargo reads offline are copied:
    never `bin/` (a cargo home's bin holds rustup proxies and the `cargo-*`
    subcommands cargo dispatches to) or `config.toml` (which can name a compiler,
    a wrapper or a target directory). Cargo checks each archive against the
    lockfile's checksum and each git dependency by revision; this records which
    cache the cut was given. Every run of the cut uses this one cargo home, so
    its paths (git checkouts are not remapped in debuginfo) are the same in both
    builds of the double compile.
    """
    if destination.exists() or destination.is_symlink():
        fail(f"private cargo home already exists: {destination}")
    destination.mkdir(mode=0o700, parents=True)
    trees: dict[str, object] = {}
    resolved: Path | None = None
    if source is not None:
        resolved = canonical_directory(source, "cargo home input")
        for relative in CARGO_HOME_INPUT_TREES:
            tree = resolved / relative
            if not tree.exists() and not tree.is_symlink():
                trees[relative] = None
                continue
            if tree.is_symlink() or not tree.is_dir():
                fail(f"cargo home input {relative} must be a non-symlink directory: {tree}")
            given = tree_records(tree, f"cargo home input {relative}")
            target = destination / relative
            target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
            clone_tree(tree, target)
            if tree_records(target, f"private cargo home {relative}") != given:
                fail(f"the private copy of cargo home input {relative} is not the input")
            trees[relative] = {"entries": len(given), "sha256": records_sha256(given)}
    serialized = json.dumps(trees, separators=(",", ":"), sort_keys=True).encode("utf-8")
    return {
        "schema": "trust-cargo-home-inputs-v1",
        "source": str(resolved) if resolved is not None else None,
        "trees": trees,
        "fingerprint": hashlib.sha256(serialized).hexdigest(),
    }


def verify_cargo_home_source(manifest_path: Path) -> None:
    """The cargo home the cut was given still holds what it copied."""
    manifest = load_json(manifest_path, "cargo home input manifest")
    source = manifest.get("source")
    trees = manifest.get("trees")
    if not isinstance(trees, dict):
        fail("cargo home input manifest has no trees")
    if source is None:
        if trees:
            fail("cargo home input manifest names trees but no source")
        return
    root = canonical_directory(Path(str(source)), "cargo home input")
    for relative, expected in trees.items():
        tree = root / relative
        if expected is None:
            if tree.exists() or tree.is_symlink():
                fail(f"cargo home input {relative} appeared during the workflow")
            continue
        records = tree_records(tree, f"cargo home input {relative}")
        if records_sha256(records) != expected.get("sha256"):
            fail(f"cargo home input {relative} changed during the workflow")


# How the DDC seed relates to the pin: what the double compile can catch. Only
# a lineage-disjoint seed makes it DIVERSE (Wheeler's condition).
DDC_RELATIONS = {
    "lineage-disjoint": (
        "diverse: a stock-lineage compiler, never built by a Trust compiler, so a "
        "subversion introduced anywhere in the Trust lineage cannot be in both seeds "
        "(what every rustc inherits from rust-lang's bootstrap chain before Trust's "
        "genesis is not covered)"
    ),
    "same-lineage": (
        "not diverse: another Trust compiler; it catches a subversion the pin carries "
        "and this seed does not, but a shared Trust ancestor can carry one into both"
    ),
    "pin-ancestor": (
        "not diverse: a compiler src/stage0 pinned earlier, or the seed that built the "
        "pin; the seed chain can have carried anything it holds into the pin, so this "
        "catches only a subversion introduced after it (such as the last cut's)"
    ),
    "reproducibility-control": (
        "not a DDC: the pin's own commit; it measures build determinism only"
    ),
}

# The commits a fixed-point host record's root_disclosure names as its producers
# (scripts/seed_fixed_point.py DISCLOSED): the host chain's root and the stage0
# commits of the producer and cross-check builds.
FIXED_POINT_PRODUCER_FIELDS = ("root_commit", "producer_stage0_commit", "cross_check_stage0_commit")
# seed_host_ledger.FIXED_POINT_SCHEMA and scripts/seed_fixed_point.py KIND, that
# record's schema and admission_kind (dual_host_seed_ledger_test holds them equal),
# for checks that read a committed ledger without loading either module.
FIXED_POINT_HOST_SCHEMA = "trust-seed-fixed-point-host-record-v1"
FIXED_POINT_ADMISSION_KIND = "fixed-point-unpinned-root"


def seed_host_ledger_module():
    """Load the repository helper even under the mint launcher's isolated Python."""
    import importlib.util

    path = Path(__file__).resolve().with_name("seed_host_ledger.py")
    if "__trust_source_loader__" in globals():
        module = __trust_source_loader__.module("trust_seed_host_ledger", path)
    else:
        spec = importlib.util.spec_from_file_location("trust_seed_host_ledger", path)
        if spec is None or spec.loader is None:
            raise ValueError(f"cannot load seed host ledger helper: {path}")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
    return module


def committed_seed_mint(root: Path) -> dict[str, str]:
    """The committed seed ledger's [release.mint]: the cut that minted the pin."""
    ledger = root / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
    if not ledger.exists():
        return {}
    if tomllib is None:
        fail("Python 3.11+ is required to read the seed ledger")
    try:
        parsed = tomllib.loads(canonical_regular_file(ledger, "seed ledger").read_text(encoding="utf-8"))
    except (UnicodeError, tomllib.TOMLDecodeError) as exc:
        fail(f"cannot parse bootstrap/trust-stage0/seed-ledger.toml: {exc}")
    release = parsed.get("release", {})
    if isinstance(release, dict) and "hosts" in release:
        helper = seed_host_ledger_module()
        host = detected_host()
        try:
            record = helper.select_host_record(release, host)
            record, _metadata_sha256 = helper.capture_host_record(ledger.parent, read_stage0_pin(root), host, record)
        except (OSError, UnicodeError, ValueError) as exc:
            fail(f"cannot validate committed {host} seed mint: {exc}")
        if record["schema"] == helper.SCHEMA:
            mint = record["mint"]
        elif record["schema"] == helper.GENESIS_SCHEMA:
            # This host has no predecessor. Carry its actual diverse anchor;
            # never manufacture an ordinary pinned_seed_commit for genesis.
            mint = {"lineage_disjoint_anchor": record["source_commit"]}
        elif record["schema"] == helper.FIXED_POINT_SCHEMA:
            # A fixed point of an unpinned host chain (docs/PLAN.md PKG-S6) has no
            # mint receipt, no pinned predecessor and no diverse double compile, so
            # it carries no anchor: a later cut on this host inherits none, and this
            # branch is explicit so that no other kind's anchor reaches it.
            mint = {"lineage_disjoint_anchor": "none"}
        else:
            mint = {}
    else:
        mint = release.get("mint", {}) if isinstance(release, dict) else {}
    return {str(key): str(value) for key, value in mint.items()} if isinstance(mint, dict) else {}


def pin_ancestry(root: Path) -> set[str]:
    """Every compiler src/stage0 has pinned on this history, and the seed the
    committed ledger says built the pin. At a pack cut each pin is built by
    the one before it, so any of these may share what the pin carries."""
    history = git_command(
        root, "log", "-p", "--format=", "-G^compiler_git_commit_hash=", "--", "src/stage0"
    )
    if history.returncode != 0:
        fail(f"cannot read the src/stage0 history: {history.stderr.strip()}")
    ancestry = {
        match.group(1)
        for match in re.finditer(r"^[-+ ]compiler_git_commit_hash=([0-9a-f]{40,64})$", history.stdout, re.M)
    }
    builder = committed_seed_mint(root).get("pinned_seed_commit", "")
    if COMMIT_RE.fullmatch(builder):
        ancestry.add(builder)
    ledger = root / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
    if ledger.exists() and tomllib is not None:
        release = tomllib.loads(canonical_regular_file(ledger, "seed ledger").read_text(encoding="utf-8")).get("release", {})
        hosts = release.get("hosts", {}) if isinstance(release, dict) else {}
        if isinstance(hosts, dict):
            for record in hosts.values():
                mint = record.get("mint", {}) if isinstance(record, dict) else {}
                builder = mint.get("pinned_seed_commit", "") if isinstance(mint, dict) else ""
                if isinstance(builder, str) and COMMIT_RE.fullmatch(builder):
                    ancestry.add(builder)
                # A fixed point was built by its host chain, not by a pin: the
                # chain's root and the two compilers that built it are its
                # producers, so a seed among them is no independent compiler.
                disclosure = record.get("root_disclosure", {}) if isinstance(record, dict) else {}
                for key in FIXED_POINT_PRODUCER_FIELDS:
                    producer = disclosure.get(key, "") if isinstance(disclosure, dict) else ""
                    if isinstance(producer, str) and COMMIT_RE.fullmatch(producer):
                        ancestry.add(producer)
    return ancestry


def ddc_seed_identity(root: Path, seed: Path, host: str | None = None) -> dict[str, object]:
    """The independent compiler, and how it relates to the pin (DDC_RELATIONS)."""
    pin = read_stage0_pin(root)["compiler_git_commit_hash"]
    identity = compiler_identity(seed, "DDC seed", stock_oracle=True)
    if host is not None and identity["host"] != canonical_host(host):
        fail(f"the DDC seed reports host {identity['host']!r}, not {host!r}")
    if identity["commit"] == pin:
        relation = "reproducibility-control"
    elif identity["lineage"] == "stock":
        relation = "lineage-disjoint"
    elif identity["commit"] in pin_ancestry(root):
        relation = "pin-ancestor"
    else:
        relation = "same-lineage"
    identity["relation"] = relation
    return identity


def default_ddc_seed(root: Path, store: Path | None = None) -> Path:
    """The newest atpkg-installed trust pack whose compiler is not the pin.

    Once packs are cut from pins, the current pack IS the pin, so this is the
    previous-but-one pack: the seed that built the pin, a `pin-ancestor`, which
    no one should call diverse. Before the first such cut it is the current pack
    (`same-lineage`). A cut that anchors the chain passes --ddc-seed with a
    stock-lineage compiler instead. Search only atpkg's default per-user store
    for this platform; discovery grants no seed admission or DDC authority.
    """
    if store is None:
        system = platform.system()
        if system == "Darwin":
            prefix = Path.home() / "Library/Application Support/aterm/pkg"
        elif system == "Linux":
            prefix = Path.home() / ".local/share/aterm/pkg"
        else:
            fail(f"unsupported native atpkg mint platform: {system}")
        store = prefix / "store/trust"
    pin = read_stage0_pin(root.resolve(strict=True))["compiler_git_commit_hash"]
    builds: dict[int, tuple[tuple[bool, bool, str], Path]] = {}
    if store.is_dir() or store.is_symlink():
        store = canonical_directory(store, "atpkg trust store")
        for entry in store.iterdir():
            match = re.fullmatch(r"([0-9]+)(\.noindex)?", entry.name)
            if match is None or entry.is_symlink() or not entry.is_dir():
                continue
            build = int(match[1])
            # New stores own N.noindex; N is normally only a compatibility
            # symlink. Keep legacy real numeric directories, but inspect one
            # physical candidate per build, preferring its canonical image.
            rank = (match[2] is not None, match[1] == str(build), entry.name)
            if build not in builds or rank > builds[build][0]:
                builds[build] = (rank, entry)
    for build in sorted(builds, reverse=True):
        candidate = builds[build][1]
        try:
            candidate = canonical_directory(candidate, "atpkg trust pack")
            if candidate.parent != store:
                continue
            identity = compiler_identity(candidate, "atpkg trust pack")
        except WorkflowError:
            continue
        if identity["commit"] != pin:
            return candidate
    fail(
        f"no --ddc-seed given, and {store} holds no trust pack whose compiler is not the "
        "pin; pass --ddc-seed <an independent compiler sysroot>"
    )


def mint_build_directory(root: Path, build: Path) -> Path:
    physical = physical_build_directory(root.resolve(strict=True))
    build = ensure_within(physical, build, "mint build directory")
    if not build.name.startswith(MINT_BUILD_PREFIX) or build.parent != physical:
        fail(f"mint build directory must be {physical}/{MINT_BUILD_PREFIX}*: {build}")
    return build


_STAGE_EVIDENCE_OWNER = None
MINT_OBSERVATION_SCHEMA = "trust.mint-build-observation.v1"
MINT_ENVIRONMENT = (
    "CARGO_HOME", "RUSTUP_HOME", "SOURCE_DATE_EPOCH", "CARGO_NET_OFFLINE",
    "GIT_CONFIG_NOSYSTEM", "GIT_CONFIG_GLOBAL", "LIBRARY_PATH", "DYLD_LIBRARY_PATH",
)


def stage_evidence_owner():
    """The actual stage-evidence capture/writer owner, also used by the recreator CLI."""
    global _STAGE_EVIDENCE_OWNER
    if _STAGE_EVIDENCE_OWNER is None:
        import importlib.util

        path = canonical_regular_file(Path(__file__).with_name("recreate_bootstrap.py"), "stage evidence owner")
        spec = importlib.util.spec_from_file_location("trust_mint_stage_evidence", path)
        if spec is None or spec.loader is None:
            fail(f"cannot load stage evidence owner: {path}")
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        _STAGE_EVIDENCE_OWNER = module
    return _STAGE_EVIDENCE_OWNER


def mint_evidence_context(root: Path, build: Path, config: Path):
    """Explicit layout and process environment of the mint, never ambient defaults."""
    root = root.resolve(strict=True)
    build = mint_build_directory(root, build)
    config = canonical_regular_file(config, "mint bootstrap config")
    ensure_within(root, config, "mint bootstrap config")
    require_pinned_seed_config(root, config)
    environment = {name: os.environ[name] for name in MINT_ENVIRONMENT if name in os.environ}
    for name in MINT_ENVIRONMENT[:6]:
        if name not in environment:
            fail(f"stage evidence must run inside the mint closed environment: missing {name}")
    cargo_home = canonical_directory(Path(environment["CARGO_HOME"]), "mint private Cargo home")
    ensure_within(physical_build_directory(root), cargo_home, "mint private Cargo home")
    return root, build, config, environment, cargo_home


def mint_clean_lean_environment(root: Path) -> dict[str, object]:
    library = os.environ.get(CLEAN_LEAN_ENV[0])
    if not library or os.environ.get(CLEAN_LEAN_ENV[1]) != "1":
        fail("mint requires its explicit Clean Lean library and strict discovery environment")
    return clean_lean_inputs(root, Path(library))


def capture_mint_stage_evidence(
    root: Path, build: Path, config: Path, host: str, *, jobs: int | None = None,
) -> dict[str, object]:
    """Observe the fresh mint BEFORE its first compiler build; no post-hoc receipt."""
    root, build, config, environment, cargo_home = mint_evidence_context(root, build, config)
    if os.path.lexists(build):
        fail(f"mint stage evidence requires an unstarted build directory: {build}")
    owner = stage_evidence_owner()
    lean = mint_clean_lean_environment(root)
    configuration = mint_configuration_context(root, config, host, jobs=jobs,
                                               clean_lean_lib=Path(str(lean["library_path"])))
    source = owner.capture_source_lineage(root)
    bootstrap = owner.capture_bootstrap_lineage(
        root, host, build_root=build, config_path=config, mint_configuration=configuration,
    )
    native = owner.capture_build_authority(root, host, None, cargo_home=cargo_home,
                                           declared_environment={**environment, **lean["environment"]},
                                           mint_configuration=configuration)
    llvm = owner.capture_llvm_before_build(
        root, host, None, config, build_root=build, mint_configuration=configuration,
    )
    for name, observation in (("source", source), ("bootstrap", bootstrap), ("native", native)):
        if observation.get("status") == "rejected" or observation.get("errors") != []:
            fail(f"mint {name} evidence was rejected: {observation.get('errors')}")
    if source.get("status") != "immutable_release":
        fail("mint source evidence requires an immutable committed source closure")
    if llvm.get("mode") != "in-tree" or llvm.get("mode_reasons"):
        fail(f"mint LLVM evidence requires a known in-tree build: {llvm.get('mode_reasons')}")
    if llvm.get("output", {}).get("present") is not False:
        fail("mint LLVM evidence did not observe an absent LLVM build")
    return {
        "schema": MINT_OBSERVATION_SCHEMA,
        "host": host,
        "build_root": owner._repository_relative_path(root, build),
        "config_path": owner._repository_relative_path(root, config),
        "config_closure_sha256": configuration_closure(root, config)["fingerprint"],
        "mint_configuration": configuration,
        "declared_environment": environment,
        "source_lineage": source,
        "bootstrap_lineage": bootstrap,
        "build_authority": native,
        "llvm_before": llvm,
    }


def finish_mint_stage_evidence(
    root: Path, build: Path, config: Path, host: str, before_path: Path, *, jobs: int | None = None,
    receipt_path: Path | None = None,
) -> None:
    """Audit THIS mint using its pre-build observations, then independently re-read it."""
    root, build, config, environment, cargo_home = mint_evidence_context(root, build, config)
    before = load_json(before_path, "mint pre-build stage observation")
    owner = stage_evidence_owner()
    lean = mint_clean_lean_environment(root)
    configuration = mint_configuration_context(root, config, host, jobs=jobs,
                                               clean_lean_lib=Path(str(lean["library_path"])))
    expected = {
        "schema": MINT_OBSERVATION_SCHEMA, "host": host,
        "build_root": owner._repository_relative_path(root, build),
        "config_path": owner._repository_relative_path(root, config),
        "config_closure_sha256": configuration_closure(root, config)["fingerprint"],
        "mint_configuration": configuration,
        "declared_environment": environment,
    }
    if any(_canonical_json(before.get(key)) != _canonical_json(value) for key, value in expected.items()):
        fail("mint stage observation names another build, config, host or closed environment")
    options = {"build_root": build, "config_path": config, "cargo_home": cargo_home,
               "declared_environment": {**environment, **lean["environment"]},
               "mint_configuration": configuration}
    if receipt_path is not None:
        options["receipt_path"] = receipt_path
    if not owner.audit_stage_tool_provenance(
        root, host, 2, before["source_lineage"], before["bootstrap_lineage"],
        before["build_authority"], llvm_before=before["llvm_before"],
        writer="scripts/mint_and_prove_seed.sh", **options,
    ):
        fail("mint stage tool/source/native provenance audit failed")
    if not owner.verify_stage_tool_provenance(
        root, host, 2, require_immutable_lineage=True, require_llvm_identity=True, **options,
    ):
        fail("mint stage evidence failed immutable-lineage/LLVM re-verification")


def clone_tree(source: Path, destination: Path) -> None:
    """Copy a tree cheaply: an APFS clone or a reflink when the filesystem has one."""
    if platform.system() == "Darwin":
        commands = (["cp", "-c", "-R", "-p", str(source), str(destination)],)
    else:
        commands = (["cp", "-a", "--reflink=auto", str(source), str(destination)],)
    for command in commands:
        if subprocess.run(command, check=False).returncode == 0:
            return
        if destination.exists():
            shutil.rmtree(destination)
    shutil.copytree(source, destination, symlinks=True)


def ddc_stage(root: Path, build: Path, host: str) -> None:
    """Move the pinned-seed build aside so the DDC build reuses its exact path.

    Both builds run at ONE absolute path: build-directory paths reach the
    compiler's bytes (OUT_DIR includes, `file!()` in generated code), and
    `rust.remap-debuginfo` remaps only the source root. LLVM is cloned, not
    rebuilt: it is compiled by the host C++ toolchain, never by the Rust seed,
    so it belongs to the environment both builds share.
    """
    build = mint_build_directory(root, build)
    pinned = build.with_name(build.name + ".pinned")
    if pinned.exists() or pinned.is_symlink():
        fail(f"a previous DDC stage was not restored: {pinned}")
    llvm = build / canonical_host(host) / "llvm"
    if llvm.is_symlink() or not llvm.is_dir():
        fail(f"the pinned-seed build has no LLVM build to share: {llvm}")
    os.rename(build, pinned)
    (build / host).mkdir(mode=0o700, parents=True)
    clone_tree(pinned / host / "llvm", build / host / "llvm")


def ddc_restore(root: Path, build: Path) -> None:
    """Put the pinned-seed build back; drop the DDC build. Idempotent."""
    build = mint_build_directory(root, build)
    pinned = build.with_name(build.name + ".pinned")
    if not pinned.exists():
        return
    if pinned.is_symlink() or not pinned.is_dir():
        fail(f"refusing to restore a non-directory DDC stage: {pinned}")
    if build.is_symlink():
        fail(f"refusing to remove a symlinked DDC build: {build}")
    if build.exists():
        shutil.rmtree(build)
    os.rename(pinned, build)


def write_ddc_config(source: Path, output: Path, rustc: Path, cargo: Path, fail_tool: Path) -> None:
    """Bootstrap configuration for the DDC build: the independent compiler
    compiles, and the pinned seed's cargo drives, exactly as it drove the
    pinned-seed build. Holding the build driver fixed keeps cargo's metadata
    hashing (and so every symbol name) out of the comparison."""
    source = canonical_regular_file(source, "bootstrap source configuration")
    rustc = canonical_regular_file(rustc, "DDC compiler")
    cargo = canonical_regular_file(cargo, "pinned seed cargo")
    if output.exists() or output.is_symlink():
        fail(f"temporary DDC configuration already exists: {output}")
    rustdoc = next(
        (
            candidate
            for candidate in (rustc.parent / "trustdoc", rustc.parent / "rustdoc")
            if candidate.is_file()
        ),
        None,
    )
    fail_tool.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    if not fail_tool.exists():
        fd = os.open(fail_tool, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o700)
        try:
            write_all(
                fd,
                b"#!/bin/sh\n"
                b"echo 'error: tippy is outside the pack-cut workflow' >&2\n"
                b"exit 125\n",
            )
            os.fsync(fd)
        finally:
            os.close(fd)
    lines = [
        "# Generated for one DDC build of the pack cut; never commit this file.",
        f"include = [{toml_string(str(source))}]",
        "",
        "[build]",
        f"rustc = {toml_string(str(rustc))}",
        f"cargo = {toml_string(str(cargo))}",
        *([f"rustdoc = {toml_string(str(rustdoc))}"] if rustdoc else []),
        f"cargo-clippy = {toml_string(str(fail_tool))}",
        "submodules = false",
        "",
        "[rust]",
        'channel = "trust"',
        "download-rustc = false",
        "",
        "[llvm]",
        "download-ci-llvm = false",
        "",
    ]
    output.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    out_fd = os.open(output, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        write_all(out_fd, "\n".join(lines).encode("utf-8"))
        os.fsync(out_fd)
    finally:
        os.close(out_fd)


def stage2_manifest(stage2: Path) -> dict[str, object]:
    stage2 = canonical_directory(stage2, "stage2 sysroot")
    records = tree_records(stage2, "stage2 sysroot")
    return {"schema": "trust-stage2-tree-v1", "sha256": records_sha256(records), "records": records}


def load_json(path: Path, description: str, *, unique_keys: bool = False) -> dict[str, object]:
    path = canonical_regular_file(path, description)

    def unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
        value: dict[str, object] = {}
        for key, item in pairs:
            if key in value:
                fail(f"{description} repeats JSON key {key!r}")
            value[key] = item
        return value

    try:
        value = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=unique_object if unique_keys else None,
        )
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        fail(f"cannot read {description} {path}: {exc}")
    if not isinstance(value, dict):
        fail(f"{description} is not a JSON object: {path}")
    return value


def stage2_records(manifest: dict[str, object], description: str) -> list[dict[str, object]]:
    """Validate the captured tree before indexing paths or trusting its digest."""
    if set(manifest) != {"schema", "sha256", "records"} or manifest.get("schema") != "trust-stage2-tree-v1":
        fail(f"{description} has an invalid stage2 manifest schema")
    records = manifest["records"]
    digest = manifest["sha256"]
    if not isinstance(digest, str) or not SHA256_RE.fullmatch(digest):
        fail(f"{description} has an invalid stage2 tree digest")
    if not isinstance(records, list) or len(records) > MAX_ARCHIVE_MEMBERS:
        fail(f"{description} has an invalid stage2 record list")
    by_path: dict[str, dict[str, object]] = {}
    total_bytes = 0
    fields = {
        "directory": {"path", "kind", "mode"},
        "file": {"path", "kind", "mode", "bytes", "sha256"},
        "symlink": {"path", "kind", "target"},
    }
    for record in records:
        if not isinstance(record, dict):
            fail(f"{description} has a non-object stage2 record")
        relative = record.get("path")
        if not isinstance(relative, str) or not relative or "\0" in relative:
            fail(f"{description} has an invalid stage2 record path")
        path = PurePosixPath(relative)
        if path.is_absolute() or ".." in path.parts or path.as_posix() != relative or relative == ".":
            fail(f"{description} has an unconfined stage2 record path: {relative!r}")
        if relative in by_path:
            fail(f"{description} repeats stage2 record path: {relative}")
        kind = record.get("kind")
        if not isinstance(kind, str) or kind not in fields or set(record) != fields[kind]:
            fail(f"{description} has an invalid stage2 record: {relative}")
        if kind == "symlink":
            target = record["target"]
            if not isinstance(target, str) or not target or "\0" in target:
                fail(f"{description} has an invalid stage2 link target: {relative}")
        else:
            mode = record["mode"]
            if type(mode) is not int or not 0 <= mode <= 0o7777:
                fail(f"{description} has an invalid stage2 record mode: {relative}")
        if kind == "file":
            size, content_digest = record["bytes"], record["sha256"]
            if (type(size) is not int or size < 0 or not isinstance(content_digest, str)
                    or not SHA256_RE.fullmatch(content_digest)):
                fail(f"{description} has invalid stage2 file metadata: {relative}")
            total_bytes += size
            if total_bytes > MAX_TOTAL_UNPACKED_BYTES:
                fail(f"{description} exceeds {MAX_TOTAL_UNPACKED_BYTES} regular-file bytes")
        by_path[relative] = record
    for relative in by_path:
        for parent in PurePosixPath(relative).parents:
            if parent == PurePosixPath("."):
                break
            if by_path.get(parent.as_posix(), {}).get("kind") != "directory":
                fail(f"{description} has a stage2 record without its directory: {relative}")
    if records_sha256(records) != digest:
        fail(f"{description} stage2 tree digest does not match its records")
    return records


def ddc_differences(pinned: dict[str, object], independent: dict[str, object]) -> list[str]:
    left = {record["path"]: record for record in stage2_records(pinned, "pinned-seed stage2 manifest")}
    right = {record["path"]: record for record in stage2_records(independent, "DDC-seed stage2 manifest")}
    differences = []
    for path in sorted(left.keys() | right.keys()):
        if path not in right:
            differences.append(f"only from the pinned seed: {path}")
        elif path not in left:
            differences.append(f"only from the DDC seed: {path}")
        elif left[path] != right[path]:
            differences.append(f"differs: {path}")
    return differences


def ddc_compare(pinned_path: Path, independent_path: Path) -> str:
    pinned = load_json(pinned_path, "pinned-seed stage2 manifest", unique_keys=True)
    independent = load_json(independent_path, "DDC-seed stage2 manifest", unique_keys=True)
    differences = ddc_differences(pinned, independent)
    if differences:
        preview = "\n  ".join(differences[:40])
        more = f"\n  ... {len(differences) - 40} more" if len(differences) > 40 else ""
        fail(
            f"DDC FAILED: the two seeds built different stage2 trees "
            f"({len(differences)} entries):\n  {preview}{more}\n"
            "Before reading this as a subverted seed, rule out build nondeterminism: "
            "re-run the cut with --ddc-seed pointing at a sysroot of the pinned seed "
            "itself (a reproducibility control) and compare."
        )
    if pinned["sha256"] != independent["sha256"]:  # pragma: no cover - records equal
        fail("DDC manifests agree record by record but not in digest")
    return str(pinned["sha256"])


def ddc_evidence(
    pinned_manifest: Path,
    independent_manifest: Path,
    pinned_stage2: Path,
    independent_stage2: Path,
    output: Path,
) -> int:
    """Keep each seed's copy of every entry the two stage2 trees disagree on.

    `ddc-restore` deletes the DDC build, and with it the only copy of the bytes
    a failed comparison names; a failure nobody can diff cannot tell a
    subverted seed from a nondeterministic build. Measured: the 1.101 cut's
    double compile named 12 entries, and with the DDC tree gone neither a
    pinned-seed rebuild nor an oracle-seeded rebuild at the same path
    reproduced the difference. Regular files are cloned, so the copies cost no
    space on APFS; nothing is written when the trees agree. Returns the number
    of differing entries.
    """
    pinned = load_json(pinned_manifest, "pinned-seed stage2 manifest", unique_keys=True)
    independent = load_json(independent_manifest, "DDC-seed stage2 manifest", unique_keys=True)
    differences = ddc_differences(pinned, independent)
    if not differences:
        return 0
    # Claim the evidence root before any copies, including for differences
    # containing no regular files: aliases and empty directories still need both
    # manifests. An existing or racing destination is not ours.
    try:
        output.mkdir(mode=0o700, parents=True)
    except FileExistsError:
        fail(f"DDC evidence directory already exists: {output}")
    left = {record["path"]: record for record in pinned["records"]}
    right = {record["path"]: record for record in independent["records"]}
    for label, records, stage2 in (
        ("pinned", left, pinned_stage2),
        ("ddc", right, independent_stage2),
    ):
        for path in sorted(left.keys() | right.keys()):
            if left.get(path) == right.get(path):
                continue
            record = records.get(path)
            if record is None or record.get("kind") != "file":
                continue
            source = stage2 / str(path)
            if source.is_symlink() or not source.is_file():
                continue
            destination = output / label / str(path)
            destination.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
            if platform.system() == "Darwin" and subprocess.run(
                ["cp", "-c", "-p", str(source), str(destination)], check=False
            ).returncode == 0:
                continue
            shutil.copy2(source, destination)
    shutil.copyfile(pinned_manifest, output / "stage2-pinned-seed.json")
    shutil.copyfile(independent_manifest, output / "stage2-ddc-seed.json")
    (output / "differences.txt").write_text("\n".join(differences) + "\n", encoding="utf-8")
    return len(differences)


def verify_stage2_unchanged(manifest_path: Path, stage2: Path) -> None:
    """The stage2 the seal copies still holds every entry the DDC compared:
    each file with its bytes, each link with its target, each directory."""
    manifest = load_json(manifest_path, "pinned-seed stage2 manifest", unique_keys=True)
    records = stage2_records(manifest, "pinned-seed stage2 manifest")
    stage2 = canonical_directory(stage2, "stage2 sysroot")
    for record in records:
        path = stage2 / str(record["path"])
        kind = record["kind"]
        if kind == "file":
            unchanged = not path.is_symlink() and path.is_file() and sha256_file(path) == record["sha256"]
        elif kind == "symlink":
            unchanged = path.is_symlink() and os.readlink(path) == record["target"]
        else:
            unchanged = not path.is_symlink() and path.is_dir()
        if not unchanged:
            fail(f"stage2 changed after the DDC compared it: {record['path']}")


def confined_link(record: dict[str, object]) -> bool:
    """A stage2 link whose target stays inside stage2: the seal keeps it
    verbatim. Links out of it (the rust-src links bootstrap aims at the
    checkout) are replaced or dropped by scripts/promote-toolchain.sh."""
    target = str(record["target"])
    if target.startswith("/"):
        return False
    resolved = posixpath.normpath(posixpath.join(posixpath.dirname(str(record["path"])), target))
    return resolved != ".." and not resolved.startswith("../")


def verify_archives_carry_compared(seed: Path, manifest_path: Path, host: str) -> int:
    """The minted archives, installed at `seed`, ship the compiler, its driver
    and std as the very bytes the DDC compared. Every compared file the
    archives install must match; returns how many did."""
    manifest = load_json(manifest_path, "pinned-seed stage2 manifest", unique_keys=True)
    records = stage2_records(manifest, "pinned-seed stage2 manifest")
    seed = canonical_directory(seed, "installed seed")
    host = canonical_host(host)
    matched: list[str] = []
    for record in records:
        if record["kind"] != "file":
            continue
        relative = str(record["path"])
        path = seed / relative
        if not os.path.lexists(path):
            continue
        if path.is_symlink() or not path.is_file() or sha256_file(path) != record["sha256"]:
            fail(f"the minted archives ship {relative} with other bytes than the DDC compared")
        matched.append(relative)
    required = {
        "the compiler": lambda name: name in ("bin/trustc", "bin/rustc"),
        "its driver": lambda name: re.fullmatch(r"lib/librustc_driver-[^/]+\.(dylib|so)", name) is not None,
        "std": lambda name: re.fullmatch(rf"lib/rustlib/{re.escape(host)}/lib/libstd-[^/]+\.rlib", name)
        is not None,
    }
    missing = [what for what, wanted in required.items() if not any(wanted(name) for name in matched)]
    if missing:
        fail(f"the minted archives ship no compared copy of {', '.join(missing)}")
    return len(matched)


def find_build_manifest_tool(build: Path, host: str) -> Path:
    # BuildManifest uses compiler stage 1 and output compiler stage 2.
    # ToolBuild passes that output compiler to Session::tools_bin_dir, which
    # adds one and appends the target triple. Other stages and the former flat
    # layout can contain stale artifacts; neither is this recipe's producer.
    host = canonical_host(host)
    tool = build / host / "stage3-tools-bin" / host / "build-manifest"
    if not tool.is_file() or tool.is_symlink() or not os.access(tool, os.X_OK):
        fail(f"expected a regular executable build-manifest at {tool}")
    return tool


def splice_stage0(current: str, generated: str) -> str:
    """The re-pinned src/stage0: this tree's editable head, the mint's generated body."""
    if current.count(STAGE0_GENERATED_MARKER) != 1 or generated.count(STAGE0_GENERATED_MARKER) != 1:
        fail("src/stage0 and prepare.py's output must each carry the generated-section marker once")
    head = current[: current.index(STAGE0_GENERATED_MARKER)]
    body = generated[generated.index(STAGE0_GENERATED_MARKER):]
    return head + body


def stage0_payload_pins(text: str) -> dict[str, str]:
    pins = {}
    for line in text.splitlines():
        key, separator, value = line.strip().partition("=")
        if separator and key.startswith("dist/") and key.endswith(".tar.xz"):
            pins[key] = value
    return pins


# The host-table comment of a ledger in which some host is not a mint record.
NON_MINT_HOSTS_COMMENT = (
    "# Each host binds its own native evidence, installed surface, and exact archives.",
    "# Foreign cross artifacts alone do not admit a host. A host whose table carries",
    "# root_disclosure is a fixed point of an unpinned host chain: it has no mint",
    "# receipt, no pinned predecessor and no diverse double compile, and its",
    "# root_disclosure table says so (docs/PLAN.md PKG-S6).",
)
# A top-level string, never a table, for a ledger with no [release.mint] table.
# Its reader is aterm (crates/atpkg-publish/src/artifact/lineage_switch.rs), which
# reads this file as text and keeps the seed pin on only for a line that starts
# with `[release.mint]`. TOML finds no release.mint table here, and no reader in
# this repository reads the key.
MINT_SWITCH_LINES = (
    "# Compatibility text for aterm's seed-pin switch, its only reader",
    "# (crates/atpkg-publish/src/artifact/lineage_switch.rs in aterm): it reads this",
    "# file as text and keeps the seed pin on only for a line that starts with",
    "# `[release.mint]`. A ledger whose hosts carry their own tables has no such",
    "# table, so this string carries the line. It is a string, not a table.",
    'aterm_seed_pin_switch = """',
    "[release.mint] is recorded per host, in each release.hosts table below",
    '"""',
)


def render_seed_ledger(
    current: str,
    stage0: dict[str, str],
    stage0_text: str,
    host: str,
    identities: dict[str, str],
    receipt: dict[str, str],
    *,
    host_records: dict[str, dict[str, object]] | None = None,
    title_hosts: bool = False,
    mint_switch_line: bool = False,
) -> tuple[str, str]:
    """The seed ledger for the re-pin, and the release tag it names.

    Scope, promotion decision, signatures, repository and visibility are
    carried over unchanged: re-pinning moves the seed, never its admission.

    `title_hosts`: the release title names every host of `host_records`, not
    only `host`. `mint_switch_line`: the ledger carries MINT_SWITCH_LINES, a
    top-level string one of whose lines starts with `[release.mint]`, for a
    ledger that has no such table (more than one host). Both default off, and
    with both off the text is what it was before they existed.
    """
    if tomllib is None:
        fail("Python 3.11+ is required to read the seed ledger")
    try:
        previous = tomllib.loads(current)
    except tomllib.TOMLDecodeError as exc:
        fail(f"cannot parse bootstrap/trust-stage0/seed-ledger.toml: {exc}")
    release = previous.get("release")
    if not isinstance(release, dict) or not isinstance(release.get("repo"), str):
        fail("the seed ledger declares no [release] repo to publish the re-pin under")
    header = []
    for line in current.splitlines():
        if line.startswith("#") or not line.strip():
            header.append(line)
        else:
            break
    date = stage0["compiler_date"]
    commit = stage0["compiler_git_commit_hash"]
    version = stage0["compiler_version"]
    repo = release["repo"]
    tag = f"trust-stage0-{date}-{commit[:9]}"
    title_names = sorted(host_records) if title_hosts and host_records is not None else [host]
    title = f"Trust stage0 seed {date} ({version}, {', '.join(title_names)})"
    pins = stage0_payload_pins(stage0_text)
    lines = [*header]
    if lines and lines[-1].strip():
        lines.append("")
    lines += [
        f"scope = {toml_string(str(previous.get('scope', 'internal')))}",
        f"promotion_decision = {toml_string(str(previous.get('promotion_decision', 'admit-internal')))}",
        "",
        "signatures = [",
        *(f"  {toml_string(str(item))}," for item in previous.get("signatures", [])),
        "]",
        "",
        f"# sha256:<hex> for every dist/*.tar.xz archive pinned in src/stage0 (all {len(pins)}).",
        "checksums = [",
        *(
            f"  {toml_string('sha256:' + digest)}, # {Path(key).name}"
            for key, digest in sorted(pins.items(), key=lambda item: Path(item[0]).name)
        ),
        "]",
        "",
        "[release]",
        f"repo = {toml_string(repo)}",
        f"tag = {toml_string(tag)}",
        f"title = {toml_string(title)}",
        f"date = {toml_string(date)}",
        f"host_triple = {toml_string(host)}",
        f"compiler_version = {toml_string(version)}",
        f"compiler_git_commit_hash = {toml_string(commit)}",
        f"channel_manifest_hash = {toml_string(stage0['compiler_channel_manifest_hash'])}",
        f"visibility = {toml_string(str(release.get('visibility', 'private')))}",
        "authenticated_fetch = "
        + toml_string(
            f"gh release download {tag} --repo {repo} --dir bootstrap/trust-stage0/dist/{date} "
            "--pattern '*.tar.xz' --clobber"
        ),
        "",
        "# The exact first line every canonical version probe prints (distribution",
        "# archive labels and product-reported versions are distinct namespaces).",
        "[release.reported_product_identities]",
        *(f"{name} = {toml_string(value)}" for name, value in sorted(identities.items())),
        "",
        "# The pack cut that minted this seed (scripts/mint_and_prove_seed.sh). The",
        "# pack's SEED-MINT file carries the same record and every compared file.",
        "# ddc_seed_relation says what the double compile can catch; only",
        "# lineage-disjoint is diverse. lineage_disjoint_anchor is the latest cut on",
        "# this chain that was, carried forward by every later cut (or none).",
        "[release.mint]",
        *(
            f"{key} = {toml_string(receipt[key])}"
            for key in (
                "pinned_seed_commit",
                "ddc_seed_relation",
                "ddc_seed_commit",
                "ddc_seed_lineage",
                "lineage_disjoint_anchor",
                "stage2_tree_sha256_pinned_seed",
                "stage2_tree_sha256_ddc_seed",
                "self_host_proof",
            )
        ),
        "",
        "[artifact_root]",
        f"path = {toml_string(f'https://github.com/{repo}/releases/tag/{tag}')}",
        "",
    ]
    if host_records is not None:
        helper = seed_host_ledger_module()
        if set(host_records) != set(helper.pinned_hosts(stage0)):
            fail("host mint records do not cover the exact prepared seed cohort")
        if len(host_records) > 1:
            lines = [line for line in lines if not line.startswith("host_triple = ")]
            first = lines.index("# The exact first line every canonical version probe prints (distribution")
            last = lines.index("[artifact_root]")
            del lines[first:last]
        insertion = lines.index("[artifact_root]")
        if all(record.get("schema") == helper.SCHEMA for record in host_records.values()):
            comment = [
                "# Each host binds its own completed native mint receipt, installed",
                "# surface, and exact archives. Foreign cross artifacts alone do not admit a host.",
            ]
        else:
            comment = NON_MINT_HOSTS_COMMENT
        lines[insertion:insertion] = [*comment, *helper.render_host_tables(host_records), ""]
    if mint_switch_line:
        if any(line.startswith("[release.mint]") for line in lines):
            fail("the seed ledger already has a [release.mint] table; the compatibility line is only for a "
                 "ledger without one (more than one host)")
        release_header = lines.index("[release]")
        lines[release_header:release_header] = [*MINT_SWITCH_LINES, ""]
    return "\n".join(lines), tag


def stage0_preparer(root: Path) -> object:
    """The checkout's own src/tools/trust-stage0-dist/prepare.py, loaded."""
    import importlib.util

    path = canonical_regular_file(
        root.resolve(strict=True) / "src" / "tools" / "trust-stage0-dist" / "prepare.py",
        "stage0 dist preparer",
    )
    if "__trust_source_loader__" in globals():
        module = __trust_source_loader__.module("trust_stage0_prepare", path)
    else:
        spec = importlib.util.spec_from_file_location("trust_stage0_prepare", path)
        if spec is None or spec.loader is None:
            fail(f"cannot load {path}")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
    return module


def dist_producer_components(root: Path) -> tuple[str, ...]:
    """The `x.py dist` components of the seed cohort, read from prepare.py itself.

    prepare.py's producer list also names trust-docs and trust-llvm-tools, and
    with --stage0-seed-only it pins every archive the dist holds. The seed is the
    SEED_COMPONENTS cohort: the re-pin binds exactly those archives
    (seed_host_ledger.COMPONENTS refuses any other pinned archive as "outside the
    exact seed cohort"). So the cut asks x.py dist for the cohort alone, by
    prepare.py's own spelling, and every cohort component must have a producer.
    """
    components = tuple(stage0_preparer(root).STAGE0_DIST_PRODUCER_ALIASES)
    if not components or not all(re.fullmatch(r"[a-z][a-z0-9-]*", item) for item in components):
        fail(f"prepare.py declares no usable dist components: {components!r}")
    cohort = tuple(component for component in components if component in SEED_COMPONENTS)
    missing = sorted(set(SEED_COMPONENTS) - set(cohort))
    if missing:
        fail(f"prepare.py declares no x.py dist producer for seed component(s): {missing}")
    return cohort


def check_repin_date(root: Path, commit_date: str) -> None:
    """Validate real cut dates; extraction identity now distinguishes same-day pins."""
    read_stage0_pin(root.resolve(strict=True))
    try:
        import datetime
        canonical = datetime.date.fromisoformat(commit_date).isoformat()
    except (TypeError, ValueError):
        fail("cut commit date must be canonical YYYY-MM-DD")
    if canonical != commit_date:
        fail("cut commit date must be canonical YYYY-MM-DD")


def parse_receipt(text: str) -> dict[str, str]:
    receipt: dict[str, str] = {}
    for line in text.splitlines():
        if not line or line.startswith("#") or line.startswith(("compiler_file=", "compiler_link=")):
            continue
        key, separator, value = line.partition("=")
        if not separator:
            fail(f"malformed seed-mint receipt line: {line!r}")
        if key in receipt:
            fail(f"duplicate seed-mint receipt key: {key!r}")
        receipt[key] = value
    return receipt


def render_receipt(
    *,
    source: dict[str, object],
    version: str,
    host: str,
    pinned: dict[str, object],
    ddc: dict[str, object],
    pinned_manifest: dict[str, object],
    ddc_manifest_sha256: str,
    previous_anchor: str = "",
) -> str:
    """SEED-MINT: key=value lines a shell can read, then every compared file.

    `lineage_disjoint_anchor` is the source commit of the latest cut on this
    seed chain whose double compile was lineage-disjoint: this one, or the one
    the committed ledger carries forward, or `none`.
    """
    host = canonical_host(host)
    for description, seed in (("pinned seed", pinned), ("DDC seed", ddc)):
        if seed.get("host") != host:
            fail(f"{description} identity does not name mint host {host!r}")
    relation = str(ddc["relation"])
    if relation not in DDC_RELATIONS:
        fail(f"unknown DDC seed relation {relation!r}")
    anchor = source["commit"] if relation == "lineage-disjoint" else (previous_anchor or "none")
    rows = [
        ("schema", RECEIPT_SCHEMA),
        ("source_commit", source["commit"]),
        ("source_commit_date", source["commit_date"]),
        ("source_version", version),
        ("host", host),
        ("pinned_seed_commit", pinned["commit"]),
        ("pinned_seed_date", pinned["date"]),
        ("pinned_seed_compiler_sha256", pinned["compiler_sha256"]),
        ("pinned_seed_driver_sha256", pinned["driver_sha256"]),
        ("ddc_seed_relation", relation),
        ("ddc_seed_commit", ddc["commit"]),
        ("ddc_seed_date", ddc["date"]),
        ("ddc_seed_lineage", ddc["lineage"]),
        ("ddc_seed_compiler_sha256", ddc["compiler_sha256"]),
        ("ddc_seed_driver_sha256", ddc["driver_sha256"]),
        ("ddc_build_driver", "the pinned seed's cargo, in both builds"),
        ("ddc_scope", "<build>/<host>/stage2 after x.py build --stage 2 compiler/rustc library/std"),
        ("stage2_tree_sha256_pinned_seed", pinned_manifest["sha256"]),
        ("stage2_tree_sha256_ddc_seed", ddc_manifest_sha256),
        ("ddc_verdict", "identical" if pinned_manifest["sha256"] == ddc_manifest_sha256 else "DIFFERENT"),
        ("lineage_disjoint_anchor", anchor),
        ("self_host_proof", "pass"),
    ]
    for key, value in rows:
        if "\n" in str(value) or "\r" in str(value):
            fail(f"seed-mint receipt value for {key} spans lines")
    lines = [
        "# SEED-MINT: the pack cut that produced this toolchain (scripts/mint_and_prove_seed.sh).",
        "# compiler_file rows are the stage2 files the double compile compared, and",
        "# compiler_link rows its links that stay inside stage2, which a seal keeps.",
        "# The commits name the dev history; a public snapshot rewrites it, so there",
        "# they are provenance to quote, not commits a reader can check out.",
        *(f"{key}={value}" for key, value in rows),
        *(
            f"compiler_file={record['sha256']} {record['path']}"
            for record in pinned_manifest["records"]
            if record["kind"] == "file"
        ),
        *(
            f"compiler_link={record['target']} {record['path']}"
            for record in pinned_manifest["records"]
            if record["kind"] == "symlink" and confined_link(record)
        ),
        "",
    ]
    return "\n".join(lines)


def repin_files(root: Path, prepared: Path) -> tuple[dict[str, Path | bytes], list[str]]:
    """Tracked paths the re-pin writes, and tracked paths it removes.

    prepare.py's output root mirrors bootstrap/trust-stage0; its archives are
    ignored by the checkout (they are published, not committed), everything
    else it wrote is tracked metadata.
    """
    prepared = canonical_directory(prepared, "prepared re-pin")
    writes: dict[str, Path | bytes] = {}
    output_root = prepared / "bootstrap" / "trust-stage0"
    for directory, _dirnames, filenames in os.walk(output_root):
        for name in sorted(filenames):
            path = Path(directory) / name
            relative = "bootstrap/trust-stage0/" + path.relative_to(output_root).as_posix()
            ignored = git_command(root, "check-ignore", "-q", "--no-index", relative)
            if ignored.returncode == 0:
                continue
            if ignored.returncode != 1:
                fail(f"git check-ignore failed for {relative}: {ignored.stderr.strip()}")
            writes[relative] = path
    listed = git_command(root, "ls-files", "-z", "--", "bootstrap/trust-stage0/dist", "bootstrap/trust-stage0/host-proofs")
    if listed.returncode != 0:
        fail(f"cannot list the tracked seed metadata: {listed.stderr.strip()}")
    removals = [
        path
        for path in listed.stdout.split("\0")
        if path and path not in writes and (
            re.fullmatch(r"bootstrap/trust-stage0/dist/[0-9-]+/.+", path)
            or re.fullmatch(r"bootstrap/trust-stage0/host-proofs/[A-Za-z0-9_.-]+/(SEED-MINT|seed-surface\.json|host-record\.json)", path)
            # A fixed-point host's receipt and evidence (docs/PLAN.md PKG-S6),
            # which only a typed --drop-host lets a re-pin leave behind.
            or re.fullmatch(r"bootstrap/trust-stage0/host-proofs/[A-Za-z0-9_.-]+/(SEED-FIXED-POINT|fixed-point/.+)", path)
        )
    ]
    return writes, removals


def create_repin_commit(
    root: Path,
    parent: str,
    branch: str,
    writes: dict[str, Path | bytes],
    removals: list[str],
    message: str,
    identity: str,
    work: Path,
) -> str:
    """One commit on `branch` whose parent is the cut commit, built in a
    private index: the checkout, its index and HEAD are never touched."""
    match = re.fullmatch(r"(.+?) <([^<>\s]+@[^<>\s]+)>", identity.strip())
    if match is None:
        fail(f"commit identity must be 'Name <email>': {identity!r}")
    if not re.fullmatch(r"[A-Za-z0-9._/-]+", branch) or branch.startswith("-"):
        fail(f"unsafe re-pin branch name: {branch!r}")
    index = work / "repin.index"
    environment = {
        "GIT_INDEX_FILE": str(index),
        "GIT_AUTHOR_NAME": match.group(1),
        "GIT_AUTHOR_EMAIL": match.group(2),
        "GIT_COMMITTER_NAME": match.group(1),
        "GIT_COMMITTER_EMAIL": match.group(2),
    }

    def git(*arguments: str) -> str:
        completed = git_command(root, *arguments, extra_env=environment)
        if completed.returncode != 0:
            fail(f"git {' '.join(arguments)} failed: {completed.stderr.strip()}")
        return completed.stdout.strip()

    git("read-tree", parent)
    for path in removals:
        git("update-index", "--force-remove", "--", path)
    for path, content in sorted(writes.items()):
        if isinstance(content, bytes):
            staged = work / "repin-blob"
            staged.write_bytes(content)
            source = staged
        else:
            source = content
        blob = git("hash-object", "-w", f"--path={path}", "--", str(source))
        git("update-index", "--add", "--cacheinfo", f"100644,{blob},{path}")
    tree = git("write-tree")
    message_path = work / "repin.message"
    message_path.write_text(message, encoding="utf-8")
    commit = git("commit-tree", tree, "-p", parent, "-F", str(message_path))
    # Create-only: an existing branch of this name is never moved.
    git("update-ref", f"refs/heads/{branch}", commit, "0" * 40)
    return commit


def validate_repin_tuple(
    stage0: dict[str, str],
    source: dict[str, object],
    version: str,
    host: str,
    receipt: dict[str, str],
    surface: dict[str, object],
) -> list[str]:
    """Bind the single-host re-pin to the cut and both measured result records."""
    host = canonical_host(host)
    version = canonical_version_value(version)
    for key, expected in (
        ("schema", RECEIPT_SCHEMA), ("source_commit", source["commit"]),
        ("source_commit_date", source["commit_date"]), ("source_version", version),
        ("host", host), ("self_host_proof", "pass"),
    ):
        if receipt.get(key) != expected:
            fail(f"seed-mint receipt {key} is {receipt.get(key)!r}, expected {expected!r}")
    for key, expected in (
        ("schema", "trust-self-host-seed-surface-v1"),
        ("source_version", version), ("host", host),
    ):
        if surface.get(key) != expected:
            fail(f"minted seed surface {key} is {surface.get(key)!r}, expected {expected!r}")
    for component in ("compiler", "rustfmt"):
        for suffix, expected in (
            ("git_commit_hash", source["commit"]),
            ("date", source["commit_date"]), ("version", f"{version}-trust"),
        ):
            key = f"{component}_{suffix}"
            if stage0.get(key) != expected:
                fail(f"prepared pin {key} is {stage0.get(key)!r}, expected {expected!r}")
        if not SHA256_RE.fullmatch(stage0.get(f"{component}_channel_manifest_hash", "")):
            fail(f"prepared pin has no canonical {component} channel manifest digest")
    expected_archives = []
    for component in SEED_COMPONENTS:
        archive_version = stage0["rustfmt_version" if component == "trustfmt" else "compiler_version"]
        suffix = "" if component == "trust-src" else f"-{host}"
        relative = f"dist/{source['commit_date']}/{component}-{archive_version}{suffix}.tar.xz"
        if not SHA256_RE.fullmatch(stage0.get(relative, "")):
            fail(f"prepared pin is missing the exact host archive or its canonical digest: {relative}")
        expected_archives.append(relative)
    return expected_archives


def committed_host_records(root: Path) -> dict[str, dict[str, object]]:
    """Every host the committed seed ledger records, with its host table: a
    `[release.hosts]` ledger's tables, or the host_triple of a legacy single-host
    ledger (with no table). Only an absent ledger records none: a ledger that is
    there and does not say which hosts it records (no [release] table, an empty
    [release.hosts], or a legacy ledger without a host_triple string) is refused,
    never read as recording nothing, which would let a cut drop what it holds."""
    ledger = root / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
    if not os.path.lexists(ledger):
        return {}
    if tomllib is None:
        fail("Python 3.11+ is required to read the seed ledger")
    try:
        parsed = tomllib.loads(canonical_regular_file(ledger, "seed ledger").read_text(encoding="utf-8"))
    except (UnicodeError, tomllib.TOMLDecodeError) as exc:
        fail(f"cannot parse bootstrap/trust-stage0/seed-ledger.toml: {exc}")
    malformed = ("so which hosts it records is unknown. Nothing was built or changed; repair the committed "
                 "ledger first")
    release = parsed.get("release")
    if not isinstance(release, dict):
        fail(f"the committed seed ledger has no [release] table, {malformed}")
    hosts = release.get("hosts")
    if hosts is not None:
        if not isinstance(hosts, dict) or not all(isinstance(record, dict) for record in hosts.values()):
            fail(f"the committed seed ledger's [release.hosts] is not a table of host tables, {malformed}")
        if not hosts:
            fail(f"the committed seed ledger's [release.hosts] is empty, {malformed}")
        return {str(name): record for name, record in hosts.items()}
    triple = release.get("host_triple")
    if not isinstance(triple, str) or not triple:
        fail(f"the committed seed ledger has no [release.hosts] and its host_triple is {triple!r}, not a host "
             f"triple, {malformed}")
    return {triple: {}}


def check_recorded_hosts(
    recorded: dict[str, dict[str, object]], kept: Iterable[str], drop_hosts: Iterable[str]
) -> list[str]:
    """Refuse a re-pin that would leave out a host the committed ledger records,
    unless a typed --drop-host names it; return the hosts it drops.

    A --drop-host that names a host twice, a host the ledger does not record, or
    a host the cut keeps is refused too: a drop is said once, of what it drops."""
    kept = set(kept)
    drops = [canonical_host(value) for value in drop_hosts]
    recorded_names = ", ".join(sorted(recorded)) or "none"
    for name in drops:
        if drops.count(name) > 1:
            fail(f"--drop-host {name} is given more than once; name each dropped host once. Nothing was changed")
        if name not in recorded:
            fail(f"--drop-host {name} names a host the committed seed ledger does not record (it records "
                 f"{recorded_names}). Nothing was changed")
        if name in kept:
            fail(f"--drop-host {name} names a host this cut keeps (its cohort: {', '.join(sorted(kept))}). "
                 "Nothing was changed")
    lost = sorted(set(recorded) - kept - set(drops))
    if lost:
        fail(
            f"this re-pin would drop {', '.join(lost)}: the committed seed ledger records it and this cut's "
            f"cohort ({', '.join(sorted(kept)) or 'none'}) does not, so its record, proofs and archive pins would "
            "leave src/stage0 and the ledger. Nothing was built, committed or changed; to drop it on purpose, "
            + " ".join(f"pass --drop-host {name}" for name in lost)
        )
    return sorted(drops)


def check_disclosed_successors(
    recorded: dict[str, dict[str, object]], successors: dict[str, dict[str, object]]
) -> None:
    """Refuse a successor record for a host whose committed record carries
    root_disclosure (a fixed point of an unpinned host chain) unless it carries
    the same table: a re-pin never turns that disclosure into a record without it.

    A committed record of the fixed-point kind by its schema or its admission_kind
    is that host too, with or without the table: one without it is malformed, and
    no successor can carry a table it does not have, so it is refused."""
    for name, record in sorted(successors.items()):
        committed = recorded.get(name, {})
        committed = committed if isinstance(committed, dict) else {}
        disclosure = committed.get("root_disclosure")
        fixed_point = (disclosure is not None or committed.get("schema") == FIXED_POINT_HOST_SCHEMA
                       or committed.get("admission_kind") == FIXED_POINT_ADMISSION_KIND)
        if fixed_point and not isinstance(disclosure, dict):
            fail(
                f"{name}'s committed host record is the fixed-point kind (schema {committed.get('schema')!r}, "
                f"admission_kind {committed.get('admission_kind')!r}) and carries no root_disclosure table, so "
                "no successor record can keep its disclosure. Nothing was committed and the committed record is "
                f"kept; repair the committed record, or drop the host on purpose with --drop-host {name}"
            )
        if fixed_point and record.get("root_disclosure") != disclosure:
            fail(
                f"{name}'s committed host record carries root_disclosure (a fixed point of an unpinned host "
                "chain: no pinned predecessor, no diverse double compile), and the successor record this re-pin "
                "would write does not carry the same table. Nothing was committed and the committed record is "
                f"kept; drop the host on purpose with --drop-host {name}, or re-pin it with a record that "
                "carries its disclosure"
            )


def recorded_hosts(root: Path, host: str, drop_hosts: Iterable[str]) -> list[str]:
    """The early check a cut of `host` runs before it builds: the mint cuts one
    host, so every other recorded host must be dropped by a typed --drop-host,
    and a host whose committed record carries root_disclosure cannot be cut at
    all (the mint writes a record that cannot carry it). Returns the drops."""
    host = canonical_host(host)
    recorded = committed_host_records(root.resolve(strict=True))
    dropped = check_recorded_hosts(recorded, {host}, drop_hosts)
    check_disclosed_successors(recorded, {host: {}})
    return dropped


def repin(
    root: Path,
    prepared: Path,
    commit: str,
    host: str,
    branch: str,
    identity: str,
    receipt_path: Path,
    surface_path: Path,
    work: Path,
    *,
    drop_hosts: Iterable[str] = (),
) -> tuple[str, str, str]:
    """Emit the commit-bound re-pin; return (commit, tag, new src/stage0 sha256).

    A host the committed ledger records and the prepared cohort lacks is
    refused unless `drop_hosts` names it (check_recorded_hosts), and a host
    whose committed record carries root_disclosure cannot get a successor
    record without it (check_disclosed_successors)."""
    root = root.resolve(strict=True)
    prepared = canonical_directory(prepared, "prepared re-pin")
    source = repository_state(root, commit)
    current_pin = read_stage0_pin(root)
    generated = canonical_regular_file(prepared / "src-stage0", "prepared src/stage0").read_text(
        encoding="utf-8"
    )
    current_text = (root / "src" / "stage0").read_text(encoding="utf-8")
    stage0_text = splice_stage0(current_text, generated)
    stage0 = {}
    for line in stage0_text.splitlines():
        key, separator, value = line.strip().partition("=")
        if separator and not key.startswith("#"):
            if key in stage0:
                fail(f"duplicate prepared pin key: {key!r}")
            stage0[key] = value
    if stage0.get("compiler_git_commit_hash") != commit:
        fail(f"the prepared pin names {stage0.get('compiler_git_commit_hash')}, not the cut commit {commit}")
    check_repin_date(root, stage0.get("compiler_date", ""))
    helper = seed_host_ledger_module()
    # Before any archive is hashed: a host the committed ledger records leaves
    # it only by a typed drop.
    recorded = committed_host_records(root)
    try:
        cohort = helper.pinned_hosts(stage0)
    except ValueError as exc:
        fail(f"the prepared pin's archive cohort is malformed: {exc}")
    dropped = check_recorded_hosts(recorded, cohort, drop_hosts)
    receipt_path = canonical_regular_file(receipt_path, "seed-mint receipt")
    try:
        receipt_bytes = helper.read_proof_file(receipt_path)
    except (OSError, ValueError) as exc:
        fail(f"cannot capture bounded seed-mint receipt: {exc}")
    receipt = parse_receipt(receipt_bytes.decode("utf-8"))
    if receipt.get("source_commit") != commit or receipt.get("ddc_verdict") != "identical":
        fail("the seed-mint receipt does not record an identical DDC of this commit")
    if receipt.get("ddc_seed_relation") not in DDC_RELATIONS or receipt["ddc_seed_relation"] == "reproducibility-control":
        fail(
            f"the seed-mint receipt records {receipt.get('ddc_seed_relation')!r}: a re-pin needs a "
            "double compile against another compiler, not a reproducibility control"
        )
    if stage0.get("compiler_date") != receipt.get("source_commit_date"):
        fail(
            f"the prepared pin is dated {stage0.get('compiler_date')}, but the compiler reports "
            f"its commit date {receipt.get('source_commit_date')}"
        )
    surface_path = canonical_regular_file(surface_path, "minted seed surface")
    try:
        surface_bytes = helper.read_proof_file(surface_path)
    except (OSError, ValueError) as exc:
        fail(f"cannot capture bounded minted seed surface: {exc}")
    try:
        surface = json.loads(surface_bytes.decode("utf-8"))
    except (UnicodeError, json.JSONDecodeError) as exc:
        fail(f"cannot read minted seed surface: {exc}")
    if not isinstance(surface, dict):
        fail("minted seed surface is not a JSON object")
    required_archives = validate_repin_tuple(
        stage0, source, canonical_version(root), host, receipt, surface
    )
    prepared_root = prepared / "bootstrap" / "trust-stage0"
    # These are the complete seed components, beyond the five archives installed
    # for the compiler/std self-host comparison. Re-pin only what was materialized.
    for relative in required_archives:
        observed = sha256_file(canonical_regular_file(prepared_root / relative, "prepared seed archive"))
        if observed != stage0[relative]:
            fail(f"prepared seed archive digest differs from its pin: {relative}")
    manifest = prepared_root / "dist" / stage0["compiler_date"] / "channel-rust-trust.toml"
    observed_manifest = sha256_file(canonical_regular_file(manifest, "prepared channel manifest"))
    for component in ("compiler", "rustfmt"):
        if observed_manifest != stage0[f"{component}_channel_manifest_hash"]:
            fail(f"prepared channel manifest differs from the {component} pin")
    tool_versions = surface.get("tool_versions")
    if not isinstance(tool_versions, dict) or not all(
        isinstance(tool_versions.get(name), str) and tool_versions[name]
        for name in ("trustc", "targo", "trustfmt")
    ):
        fail("the minted seed surface does not record the trustc/targo/trustfmt identities")
    try:
        host_records, proof_bytes = helper.collect_host_records(
            prepared_root, stage0, host, receipt_bytes, surface_bytes
        )
        # Every native producer must have used this source checkout's previous
        # canonical pin; a development seal is not an alternative predecessor.
        for record in host_records.values():
            if (record["mint"]["pinned_seed_commit"] != current_pin.get("compiler_git_commit_hash")
                    or record["pinned_seed_date"] != current_pin.get("compiler_date")):
                fail(f"{record['host']} native receipt does not name the actual previous src/stage0 pin")
        # Recheck every adopted host's bytes, not just this producer's archives.
        for record in host_records.values():
            for relative, digest in record["payloads"].items():
                observed = sha256_file(canonical_regular_file(prepared_root / relative, "prepared host seed archive"))
                if observed != digest:
                    fail(f"prepared host seed archive digest differs from its pin: {relative}")
    except (OSError, UnicodeError, ValueError) as exc:
        fail(f"cannot bind prepared native host mint records: {exc}")
    check_disclosed_successors(recorded, host_records)
    ledger_path = root / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
    ledger_text, tag = render_seed_ledger(
        canonical_regular_file(ledger_path, "seed ledger").read_text(encoding="utf-8"),
        stage0,
        stage0_text,
        host,
        {name: tool_versions[name].splitlines()[0] for name in ("trustc", "targo", "trustfmt")},
        receipt,
        host_records=host_records,
    )
    writes, removals = repin_files(root, prepared)
    for relative, payload in proof_bytes.items():
        writes["bootstrap/trust-stage0/" + relative] = payload
    removals = [relative for relative in removals if relative not in writes]
    writes["src/stage0"] = stage0_text.encode("utf-8")
    writes["bootstrap/trust-stage0/seed-ledger.toml"] = ledger_text.encode("utf-8")
    message = "\n".join(
        [
            f"seed: re-pin src/stage0 to {commit[:10]} ({stage0['compiler_version']}, {stage0['compiler_date']})",
            "",
            "Minted at a pack cut by scripts/mint_and_prove_seed.sh from its parent, the",
            "commit the pack's compiler reports (docs/DECISION_QUEUE.md D12). The pack's",
            "SEED-MINT file carries the same record.",
            "",
            f"* built from the pin {receipt['pinned_seed_commit'][:10]} ({receipt['pinned_seed_date']})",
            f"* double compile against {receipt['ddc_seed_commit'][:10]} ({receipt['ddc_seed_lineage']}"
            f" lineage, {receipt['ddc_seed_relation']}): both stage2 trees"
            f" {receipt['stage2_tree_sha256_pinned_seed']}",
            *textwrap.wrap(
                DDC_RELATIONS.get(receipt["ddc_seed_relation"], "unknown relation"),
                width=72,
                initial_indent="  ",
                subsequent_indent="  ",
            ),
            f"* latest lineage-disjoint cut on this seed chain: {receipt['lineage_disjoint_anchor']}",
            "* self-host proof: the minted archives rebuilt this commit's stage2",
            f"* archives: release {tag}, not in this commit (gitignored payloads)",
            *(
                [f"* dropped recorded host(s), by a typed --drop-host: {', '.join(dropped)}"]
                if dropped else []
            ),
            "",
        ]
    )
    new_commit = create_repin_commit(root, commit, branch, writes, removals, message, identity, work)
    stage0_sha256 = hashlib.sha256(stage0_text.encode("utf-8")).hexdigest()
    rows = "".join(
        f"{key}={value}\n"
        for key, value in (
            ("repin_commit", new_commit),
            ("repin_branch", branch),
            ("repin_release_tag", tag),
            ("repin_compiler_git_commit_hash", commit),
            ("repin_stage0_sha256", stage0_sha256),
        )
    )
    with receipt_path.open("a", encoding="utf-8") as handle:
        handle.write(rows)
    return new_commit, tag, stage0_sha256


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    sub = result.add_subparsers(dest="command", required=True)

    version = sub.add_parser("version")
    version.add_argument("root", type=Path)

    host = sub.add_parser("host")
    host.add_argument("--value")

    jobs = sub.add_parser("build-jobs")
    jobs.add_argument("--jobs", type=int)

    lean = sub.add_parser("clean-lean-inputs")
    lean.add_argument("--root", type=Path, required=True)
    selection = lean.add_mutually_exclusive_group(required=True)
    selection.add_argument("--library", type=Path)
    selection.add_argument("--elan-home", type=Path)
    lean.add_argument("--output", type=Path)
    lean.add_argument("--path-only", action="store_true")
    lean_verify = sub.add_parser("verify-clean-lean-inputs")
    lean_verify.add_argument("root", type=Path)
    lean_verify.add_argument("manifest", type=Path)
    lean_verify.add_argument("--library", type=Path, required=True)
    lean_verify.add_argument("--sha256", required=True)

    state = sub.add_parser("repo-state")
    state.add_argument("root", type=Path)
    state.add_argument("--expect-commit")
    state.add_argument("--json", action="store_true")

    output = sub.add_parser("check-output")
    output.add_argument("root", type=Path)
    output.add_argument("path", type=Path)
    output.add_argument("description")

    canonical = sub.add_parser("canonical-file")
    canonical.add_argument("path", type=Path)
    canonical.add_argument("description")

    directory = sub.add_parser("canonical-directory")
    directory.add_argument("path", type=Path)
    directory.add_argument("description")

    digest = sub.add_parser("file-sha256")
    digest.add_argument("path", type=Path)

    config_fingerprint = sub.add_parser("config-fingerprint")
    config_fingerprint.add_argument("root", type=Path)
    config_fingerprint.add_argument("source", type=Path)

    config_manifest = sub.add_parser("config-manifest")
    config_manifest.add_argument("root", type=Path)
    config_manifest.add_argument("source", type=Path)
    config_manifest.add_argument("output", type=Path)

    library_manifest = sub.add_parser("library-manifest")
    library_manifest.add_argument("output", type=Path)
    library_manifest.add_argument("directories", type=Path, nargs="*")

    cargo_home = sub.add_parser("cargo-home-inputs")
    cargo_home.add_argument("--source", type=Path)
    cargo_home.add_argument("--destination", type=Path, required=True)
    cargo_home.add_argument("--output", type=Path, required=True)

    cargo_home_verify = sub.add_parser("verify-cargo-home-inputs")
    cargo_home_verify.add_argument("manifest", type=Path)

    mint_tools = sub.add_parser("mint-tools-manifest")
    mint_tools.add_argument("root", type=Path)
    mint_tools.add_argument("source", type=Path)
    mint_tools.add_argument("output", type=Path)

    for verb in ("stage-evidence-before", "stage-evidence-after"):
        evidence = sub.add_parser(verb)
        evidence.add_argument("--root", type=Path, required=True)
        evidence.add_argument("--build", type=Path, required=True)
        evidence.add_argument("--config", type=Path, required=True)
        evidence.add_argument("--host", required=True)
        evidence.add_argument("--observation", type=Path, required=True)
        evidence.add_argument("--jobs", type=int)

    work = sub.add_parser("make-work")
    work.add_argument("root", type=Path)

    cleanup = sub.add_parser("cleanup-work")
    cleanup.add_argument("root", type=Path)
    cleanup.add_argument("work", type=Path)

    publish = sub.add_parser("publish")
    publish.add_argument("root", type=Path)
    publish.add_argument("source", type=Path)
    publish.add_argument("destination", type=Path)
    publish.add_argument("description")

    supervisor = sub.add_parser("supervise")
    supervisor.add_argument("--timeout-seconds", type=int, default=43200)
    supervisor.add_argument("remainder", nargs=argparse.REMAINDER)

    stage = sub.add_parser("stage-artifacts")
    stage.add_argument("--dist", type=Path, required=True)
    stage.add_argument("--work", type=Path, required=True)
    stage.add_argument("--version", required=True)
    stage.add_argument("--host", required=True)
    stage.add_argument("--commit", required=True)
    stage.add_argument("--manifest", type=Path, required=True)

    handoff = sub.add_parser("rustc-dev-handoff")
    handoff.add_argument("--root", type=Path, required=True)
    handoff.add_argument("--input-manifest", type=Path, required=True)
    handoff.add_argument("--work", type=Path, required=True)
    handoff.add_argument("--output-root", type=Path, required=True)

    config = sub.add_parser("write-config")
    config.add_argument("--source", type=Path, required=True)
    config.add_argument("--output", type=Path, required=True)
    config.add_argument("--seed", type=Path, required=True)
    config.add_argument("--fail-tool", type=Path, required=True)

    safe_path = sub.add_parser("safe-path")
    safe_path.add_argument("--input", required=True)
    safe_path.add_argument("--output", type=Path, required=True)
    safe_path.add_argument("--manifest", type=Path, required=True)
    safe_path.add_argument("--host", required=True)
    safe_path.add_argument("--python", type=Path, required=True)

    revalidate_path = sub.add_parser("revalidate-path")
    revalidate_path.add_argument("--path", type=Path, required=True)
    revalidate_path.add_argument("--manifest", type=Path, required=True)

    seed = sub.add_parser("validate-seed")
    seed.add_argument("--seed", type=Path, required=True)
    seed.add_argument("--version", required=True)
    seed.add_argument("--host", required=True)
    seed.add_argument("--output", type=Path, required=True)

    pinned_config = sub.add_parser("require-pinned-seed")
    pinned_config.add_argument("root", type=Path)
    pinned_config.add_argument("source", type=Path)

    pin = sub.add_parser("pin")
    pin.add_argument("root", type=Path)

    components = sub.add_parser("dist-components")
    components.add_argument("root", type=Path)

    repin_date = sub.add_parser("check-repin-date")
    repin_date.add_argument("root", type=Path)
    repin_date.add_argument("date")

    pinned_stage0 = sub.add_parser("pinned-stage0")
    pinned_stage0.add_argument("--root", type=Path, required=True)
    pinned_stage0.add_argument("--build", type=Path, required=True)
    pinned_stage0.add_argument("--host", required=True)
    pinned_stage0.add_argument("--output", type=Path, required=True)
    pinned_stage0.add_argument("--seed-dylib-path", type=Path, action="append", default=[])

    default_seed = sub.add_parser("default-ddc-seed")
    default_seed.add_argument("root", type=Path)

    ddc_seed = sub.add_parser("ddc-seed")
    ddc_seed.add_argument("--root", type=Path, required=True)
    ddc_seed.add_argument("--seed", type=Path, required=True)
    ddc_seed.add_argument("--host")
    ddc_seed.add_argument("--output", type=Path)
    ddc_seed.add_argument("--seed-dylib-path", type=Path, action="append", default=[])

    manifest = sub.add_parser("stage2-manifest")
    manifest.add_argument("stage2", type=Path)
    manifest.add_argument("output", type=Path)

    stage_ddc = sub.add_parser("ddc-stage")
    stage_ddc.add_argument("--root", type=Path, required=True)
    stage_ddc.add_argument("--build", type=Path, required=True)
    stage_ddc.add_argument("--host", required=True)

    restore_ddc = sub.add_parser("ddc-restore")
    restore_ddc.add_argument("--root", type=Path, required=True)
    restore_ddc.add_argument("--build", type=Path, required=True)

    ddc_config = sub.add_parser("write-ddc-config")
    ddc_config.add_argument("--source", type=Path, required=True)
    ddc_config.add_argument("--output", type=Path, required=True)
    ddc_config.add_argument("--rustc", type=Path, required=True)
    ddc_config.add_argument("--cargo", type=Path, required=True)
    ddc_config.add_argument("--fail-tool", type=Path, required=True)

    compare = sub.add_parser("ddc-compare")
    compare.add_argument("pinned", type=Path)
    compare.add_argument("independent", type=Path)

    evidence = sub.add_parser("ddc-evidence")
    evidence.add_argument("--pinned-manifest", type=Path, required=True)
    evidence.add_argument("--ddc-manifest", type=Path, required=True)
    evidence.add_argument("--pinned-stage2", type=Path, required=True)
    evidence.add_argument("--ddc-stage2", type=Path, required=True)
    evidence.add_argument("--output", type=Path, required=True)

    carried = sub.add_parser("verify-archives-carry-compared")
    carried.add_argument("--seed", type=Path, required=True)
    carried.add_argument("--manifest", type=Path, required=True)
    carried.add_argument("--host", required=True)

    unchanged = sub.add_parser("verify-stage2-unchanged")
    unchanged.add_argument("manifest", type=Path)
    unchanged.add_argument("stage2", type=Path)

    manifest_tool = sub.add_parser("build-manifest-tool")
    manifest_tool.add_argument("--build", type=Path, required=True)
    manifest_tool.add_argument("--host", required=True)

    receipt = sub.add_parser("write-receipt")
    receipt.add_argument("--root", type=Path, required=True)
    receipt.add_argument("--version", required=True)
    receipt.add_argument("--host", required=True)
    receipt.add_argument("--pinned-seed", type=Path, required=True)
    receipt.add_argument("--ddc-seed", type=Path, required=True)
    receipt.add_argument("--pinned-manifest", type=Path, required=True)
    receipt.add_argument("--ddc-manifest", type=Path, required=True)
    receipt.add_argument("--output", type=Path, required=True)

    repin_parser = sub.add_parser("repin")
    repin_parser.add_argument("--root", type=Path, required=True)
    repin_parser.add_argument("--prepared", type=Path, required=True)
    repin_parser.add_argument("--commit", required=True)
    repin_parser.add_argument("--host", required=True)
    repin_parser.add_argument("--branch", required=True)
    repin_parser.add_argument("--identity", required=True)
    repin_parser.add_argument("--receipt", type=Path, required=True)
    repin_parser.add_argument("--surface", type=Path, required=True)
    repin_parser.add_argument("--work", type=Path, required=True)
    repin_parser.add_argument("--drop-host", action="append", default=[])

    recorded = sub.add_parser("recorded-hosts")
    recorded.add_argument("--root", type=Path, required=True)
    recorded.add_argument("--host", required=True)
    recorded.add_argument("--drop-host", action="append", default=[])

    continuation = sub.add_parser("continuation-context")
    continuation.add_argument("--root", type=Path, required=True)
    continuation.add_argument("--record", type=Path, required=True)
    continuation.add_argument("--sha256", required=True)
    continuation.add_argument("--work-only", action="store_true")
    continuation.add_argument("--config", type=Path)
    continuation.add_argument("--host")
    continuation.add_argument("--clean-lean-lib", type=Path)
    continuation.add_argument("--library-path", default="")
    continuation.add_argument("--seed-dylib-path", default="")
    continuation.add_argument("--ddc-seed", type=Path)
    continuation.add_argument("--cargo-source", type=Path)
    continuation.add_argument("--python", type=Path)

    final = sub.add_parser("finalize")
    final.add_argument("--root", type=Path, required=True)
    final.add_argument("--input", type=Path, required=True)
    final.add_argument("--output", type=Path, required=True)
    final.add_argument("--config", type=Path, required=True)
    final.add_argument("--source-config", type=Path, required=True)
    final.add_argument("--stage2", type=Path, required=True)
    final.add_argument("--source-date-epoch", type=int, required=True)
    final.add_argument("--path-manifest", type=Path, required=True)
    final.add_argument("--surface-manifest", type=Path, required=True)
    final.add_argument("--library-path", default="")
    final.add_argument("--config-manifest", type=Path, required=True)
    final.add_argument("--library-manifest", type=Path, required=True)
    final.add_argument("--mint-tools-manifest", type=Path, required=True)
    final.add_argument("--mint-receipt", type=Path, required=True)
    final.add_argument("--cargo-home-manifest", type=Path, required=True)
    final.add_argument("--seed-dylib-path", default="")
    final.add_argument("--seed-dylib-manifest", type=Path, required=True)
    final.add_argument("--clean-lean-manifest", type=Path, required=True)
    final.add_argument("--clean-lean-lib", type=Path, required=True)
    final.add_argument("--clean-lean-manifest-sha256", required=True)
    final.add_argument("--continuation-record", type=Path)
    final.add_argument("--continuation-record-sha256")
    final.add_argument("--continuation-build-jobs", type=int)
    return result


def main(argv: Iterable[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        if args.command == "version":
            print(canonical_version(args.root.resolve(strict=True)))
        elif args.command == "host":
            print(native_host(args.value))
        elif args.command == "build-jobs":
            jobs = mint_build_jobs(args.jobs)
            print("" if jobs is None else jobs)
        elif args.command == "clean-lean-inputs":
            library = args.library or selected_clean_lean_lib(args.root, args.elan_home)
            value = clean_lean_inputs(args.root, library)
            if args.output is not None:
                write_json_exclusive(args.output, value)
            elif args.path_only:
                print(value["library_path"])
            else:
                print(json.dumps(value, sort_keys=True))
        elif args.command == "verify-clean-lean-inputs":
            verify_clean_lean_inputs(args.root, args.manifest, args.library, args.sha256)
        elif args.command == "repo-state":
            state = repository_state(args.root, args.expect_commit)
            if args.json:
                print(json.dumps(state, sort_keys=True))
            else:
                print(f"{state['commit']}\t{state['source_date_epoch']}\t{state['commit_date']}")
        elif args.command == "check-output":
            verify_output_path(args.root.resolve(strict=True), args.path, args.description)
        elif args.command == "canonical-file":
            print(canonical_regular_file(args.path, args.description))
        elif args.command == "canonical-directory":
            print(canonical_directory(args.path, args.description))
        elif args.command == "file-sha256":
            print(sha256_file(canonical_regular_file(args.path, "input file")))
        elif args.command == "config-fingerprint":
            print(configuration_closure(args.root, args.source)["fingerprint"])
        elif args.command == "config-manifest":
            write_json_exclusive(
                args.output, configuration_closure(args.root, args.source)
            )
        elif args.command == "library-manifest":
            write_json_exclusive(
                args.output, native_library_manifest(args.directories)
            )
        elif args.command == "cargo-home-inputs":
            write_json_exclusive(args.output, cargo_home_inputs(args.source, args.destination))
        elif args.command == "verify-cargo-home-inputs":
            verify_cargo_home_source(args.manifest)
        elif args.command == "mint-tools-manifest":
            write_json_exclusive(
                args.output, mint_tool_manifest(args.root, args.source)
            )
        elif args.command == "stage-evidence-before":
            write_json_exclusive(args.observation, capture_mint_stage_evidence(
                args.root, args.build, args.config, args.host,
                jobs=args.jobs,
            ))
        elif args.command == "stage-evidence-after":
            finish_mint_stage_evidence(args.root, args.build, args.config, args.host, args.observation, jobs=args.jobs)
        elif args.command == "make-work":
            print(make_work_directory(args.root))
        elif args.command == "cleanup-work":
            cleanup_work_directory(args.root, args.work)
        elif args.command == "publish":
            publish_directory(
                args.root, args.source, args.destination, args.description
            )
        elif args.command == "supervise":
            command = args.remainder
            if command and command[0] == "--":
                command = command[1:]
            return supervise(command, args.timeout_seconds)
        elif args.command == "stage-artifacts":
            stage_artifacts(
                args.dist,
                args.work,
                args.version,
                args.host,
                args.commit,
                args.manifest,
            )
        elif args.command == "rustc-dev-handoff":
            for staged in stage_rustc_dev_handoff(
                args.root, args.input_manifest, args.work, args.output_root
            ):
                print(f"  trustc-dev handoff: {staged}")
        elif args.command == "write-config":
            write_seed_config(args.source, args.output, args.seed, args.fail_tool)
        elif args.command == "safe-path":
            manifest = create_sanitized_path(args.input, args.output, args.host, args.python)
            write_json_exclusive(args.manifest, manifest)
        elif args.command == "revalidate-path":
            revalidate_sanitized_path(args.path, args.manifest)
        elif args.command == "validate-seed":
            manifest = validate_seed(args.seed, args.version, args.host)
            write_json_exclusive(args.output, manifest)
        elif args.command == "require-pinned-seed":
            require_pinned_seed_config(args.root, args.source)
        elif args.command == "pin":
            pin = read_stage0_pin(args.root.resolve(strict=True))
            print(
                f"{pin['compiler_git_commit_hash']}\t{pin['compiler_date']}\t"
                f"{pin['compiler_version']}\t{pin['dist_server']}"
            )
        elif args.command == "dist-components":
            print(" ".join(dist_producer_components(args.root)))
        elif args.command == "check-repin-date":
            check_repin_date(args.root, args.date)
        elif args.command == "pinned-stage0":
            write_json_exclusive(
                args.output,
                pinned_stage0_identity(
                    args.root.resolve(strict=True), args.build, args.host, args.seed_dylib_path
                ),
            )
        elif args.command == "default-ddc-seed":
            print(default_ddc_seed(args.root))
        elif args.command == "ddc-seed":
            # Observe dependencies before running the independent compiler. This
            # external-bootstrap role grants no Trust stage0 or seed authority.
            runtime = foreign_load_commands(
                args.seed, args.seed_dylib_path, external_bootstrap=True
            )
            identity = ddc_seed_identity(args.root.resolve(strict=True), args.seed, args.host)
            identity["foreign_loads"] = runtime
            if args.output is not None:
                write_json_exclusive(args.output, identity)
            print(
                f"{identity['relation']}\t{identity['commit']}\t{identity['date']}\t"
                f"{identity['lineage']}\t{identity['sysroot']}/{identity['compiler']}\t{identity['sysroot']}"
            )
        elif args.command == "stage2-manifest":
            write_json_exclusive(args.output, stage2_manifest(args.stage2))
        elif args.command == "ddc-stage":
            ddc_stage(args.root, args.build, args.host)
        elif args.command == "ddc-restore":
            ddc_restore(args.root, args.build)
        elif args.command == "write-ddc-config":
            write_ddc_config(args.source, args.output, args.rustc, args.cargo, args.fail_tool)
        elif args.command == "ddc-compare":
            print(ddc_compare(args.pinned, args.independent))
        elif args.command == "ddc-evidence":
            print(
                ddc_evidence(
                    args.pinned_manifest,
                    args.ddc_manifest,
                    args.pinned_stage2,
                    args.ddc_stage2,
                    args.output,
                )
            )
        elif args.command == "verify-archives-carry-compared":
            print(verify_archives_carry_compared(args.seed, args.manifest, args.host))
        elif args.command == "verify-stage2-unchanged":
            verify_stage2_unchanged(args.manifest, args.stage2)
        elif args.command == "build-manifest-tool":
            print(find_build_manifest_tool(args.build, args.host))
        elif args.command == "write-receipt":
            if args.output.exists() or args.output.is_symlink():
                fail(f"seed-mint receipt already exists: {args.output}")
            pinned_manifest = load_json(args.pinned_manifest, "pinned-seed stage2 manifest", unique_keys=True)
            ddc_manifest = load_json(args.ddc_manifest, "DDC-seed stage2 manifest", unique_keys=True)
            stage2_records(pinned_manifest, "pinned-seed stage2 manifest")
            stage2_records(ddc_manifest, "DDC-seed stage2 manifest")
            text = render_receipt(
                source=repository_state(args.root),
                version=canonical_version_value(args.version),
                host=canonical_host(args.host),
                pinned=load_json(args.pinned_seed, "pinned seed identity"),
                ddc=load_json(args.ddc_seed, "DDC seed identity"),
                pinned_manifest=pinned_manifest,
                ddc_manifest_sha256=str(ddc_manifest["sha256"]),
                previous_anchor=committed_seed_mint(args.root.resolve(strict=True)).get(
                    "lineage_disjoint_anchor", ""
                ),
            )
            args.output.write_text(text, encoding="utf-8")
        elif args.command == "repin":
            new_commit, tag, stage0_sha256 = repin(
                args.root,
                args.prepared,
                args.commit,
                canonical_host(args.host),
                args.branch,
                args.identity,
                args.receipt,
                args.surface,
                args.work,
                drop_hosts=args.drop_host,
            )
            print(f"{new_commit}\t{tag}\t{stage0_sha256}")
        elif args.command == "recorded-hosts":
            dropped = recorded_hosts(args.root, args.host, args.drop_host)
            if dropped:
                print(f"re-pin drops recorded host(s) {', '.join(dropped)} (typed --drop-host)")
        elif args.command == "continuation-context":
            record = continuation_context(args.root, args.record, args.sha256,
                                          work_only=args.work_only, config=args.config,
                                          host=args.host, clean_lean_lib=args.clean_lean_lib,
                                          library_path=args.library_path,
                                          seed_dylib_path=args.seed_dylib_path,
                                          ddc_seed=args.ddc_seed, cargo_source=args.cargo_source,
                                          python=args.python)
            print(record["work"])
        elif args.command == "finalize":
            finalize_manifest(
                args.root,
                args.input,
                args.output,
                args.config,
                args.source_config,
                args.stage2,
                args.source_date_epoch,
                args.path_manifest,
                args.surface_manifest,
                args.library_path,
                args.config_manifest,
                args.library_manifest,
                args.mint_tools_manifest,
                args.mint_receipt,
                args.cargo_home_manifest,
                args.seed_dylib_path,
                args.seed_dylib_manifest,
                args.clean_lean_manifest,
                args.clean_lean_lib,
                args.clean_lean_manifest_sha256,
                args.continuation_record,
                args.continuation_record_sha256,
                args.continuation_build_jobs,
            )
        else:  # pragma: no cover - argparse makes this unreachable.
            fail(f"unsupported command: {args.command}")
    except WorkflowError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
