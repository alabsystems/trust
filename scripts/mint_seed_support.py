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
from pathlib import Path, PurePosixPath
from typing import BinaryIO, Iterable

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - supported builders use 3.11+.
    tomllib = None  # type: ignore[assignment]


COMPONENTS = ("trust-std", "trustc", "trustc-dev", "targo", "trustfmt")
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
SHA256_RE = re.compile(r"[0-9a-f]{64}")
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


def canonical_directory(path: Path, description: str) -> Path:
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
    if forbidden_tool_path(resolved):
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
    if build.is_symlink() or not build.is_dir():
        fail(f"repository build directory must be a non-symlink directory: {build}")
    ensure_within(build, output, description)
    if output.exists() or output.is_symlink():
        fail(f"{description} already exists; refusing to replace it: {output}")
    ancestor = output.parent
    while ancestor != build:
        if ancestor.exists() or ancestor.is_symlink():
            if ancestor.is_symlink() or not ancestor.is_dir():
                fail(f"{description} has an unsafe parent component: {ancestor}")
            break
        ancestor = ancestor.parent


def make_work_directory(root: Path) -> Path:
    build = root.resolve(strict=True) / "build"
    if build.is_symlink() or not build.is_dir():
        fail(f"repository build directory must be a non-symlink directory: {build}")
    work = Path(tempfile.mkdtemp(prefix=".mint-and-prove.", dir=build))
    work.chmod(0o700)
    return work


def authenticated_work_directory(root: Path, work: Path) -> Path:
    build = root.resolve(strict=True) / "build"
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


def supervise(command: list[str], timeout_seconds: int) -> int:
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
    descendant_leak = False
    had_descendant_leak = False
    try:
        os.killpg(child.pid, 0)
    except ProcessLookupError:
        pass
    else:
        descendant_leak = True
        had_descendant_leak = True
        try:
            os.killpg(child.pid, signal.SIGTERM)
        except ProcessLookupError:
            descendant_leak = False
        if descendant_leak:
            deadline = time.monotonic() + 30
            while time.monotonic() < deadline:
                try:
                    os.killpg(child.pid, 0)
                except ProcessLookupError:
                    descendant_leak = False
                    break
                time.sleep(0.1)
            if descendant_leak:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    descendant_leak = False
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


def git_command(root: Path, *arguments: str) -> subprocess.CompletedProcess[str]:
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

    epoch_result = git_command(root, "show", "-s", "--format=%ct", commit)
    epoch = epoch_result.stdout.strip()
    if epoch_result.returncode != 0 or not epoch.isdigit():
        fail(f"cannot read source commit timestamp: {epoch_result.stderr.strip()}")
    return {"commit": commit, "source_date_epoch": int(epoch)}


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


def mint_tool_manifest(root: Path, source: Path) -> dict[str, object]:
    if tomllib is None:
        fail("Python 3.11+ is required to authenticate bootstrap tool selectors")
    root = root.resolve(strict=True)
    active: set[Path] = set()

    def effective_build(path: Path) -> dict[str, object]:
        path = canonical_regular_file(path, "bootstrap tool-selector configuration")
        ensure_within(root, path, "bootstrap tool-selector configuration")
        if path in active:
            fail(f"bootstrap configuration include cycle reaches {path}")
        raw = path.read_bytes()
        if len(raw) > MAX_CONFIG_BYTES:
            fail(f"bootstrap configuration exceeds {MAX_CONFIG_BYTES} bytes: {path}")
        try:
            parsed = tomllib.loads(raw.decode("utf-8"))
        except (UnicodeError, tomllib.TOMLDecodeError) as exc:
            fail(f"cannot parse bootstrap configuration {path}: {exc}")
        build = parsed.get("build", {})
        if not isinstance(build, dict):
            fail(f"bootstrap build configuration must be a table: {path}")
        merged: dict[str, object] = dict(build)
        includes = parsed.get("include", []) or []
        if not isinstance(includes, list) or not all(isinstance(item, str) for item in includes):
            fail(f"bootstrap configuration include must be an array of strings: {path}")
        active.add(path)
        # Bootstrap gives the root file precedence, then later includes over
        # earlier includes. Fill only missing values in that same order.
        for include in reversed(includes):
            child = effective_build(path.parent / include)
            for key, value in child.items():
                merged.setdefault(key, value)
        active.remove(path)
        return merged

    build = effective_build(source)
    selector_names = ("rustc", "cargo", "rustdoc", "rustfmt", "cargo-clippy")
    declared = {name: build.get(name) for name in selector_names}
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


def archive_metadata(
    bundle: tarfile.TarFile, archive: Path, top: str, commit: str
) -> tuple[list[tarfile.TarInfo], int]:
    members: list[tarfile.TarInfo] = []
    paths: dict[PurePosixPath, str] = {}
    total = 0
    commit_value: str | None = None
    try:
        for index, member in enumerate(bundle):
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
        commit_value = extracted.read(MAX_METADATA_BYTES + 1).decode("ascii").strip()
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
    destination.mkdir(mode=0o700, parents=True, exist_ok=False)
    directories: list[tuple[Path, int]] = []
    symlinks: list[tarfile.TarInfo] = []
    hardlinks: list[tarfile.TarInfo] = []
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    archive_fd = os.open(archive, flags)
    try:
        before = os.fstat(archive_fd)
        with os.fdopen(os.dup(archive_fd), "rb") as archive_handle:
            with tarfile.open(fileobj=archive_handle, mode="r:xz") as bundle:
                members, total = archive_metadata(bundle, archive, top, commit)
                for member in members:
                    target = destination_path(destination, member)
                    if member.isdir():
                        target.mkdir(mode=0o700, parents=True, exist_ok=True)
                        directories.append((target, member.mode & 0o777))
                    elif member.isfile():
                        target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
                        source = bundle.extractfile(member)
                        if source is None:
                            fail(f"cannot read admitted archive member: {member.name}")
                        output_fd = os.open(
                            target,
                            os.O_WRONLY | os.O_CREAT | os.O_EXCL,
                            member.mode & 0o777,
                        )
                        remaining = member.size
                        try:
                            while remaining:
                                block = source.read(min(COPY_CHUNK, remaining))
                                if not block:
                                    fail(f"archive member is truncated: {member.name}")
                                remaining -= len(block)
                                view = memoryview(block)
                                while view:
                                    written = os.write(output_fd, view)
                                    view = view[written:]
                        finally:
                            os.close(output_fd)
                        if source.read(1):
                            fail(f"archive member exceeds its declared size: {member.name}")
                    elif member.issym():
                        symlinks.append(member)
                    elif member.islnk():
                        hardlinks.append(member)

                for member in hardlinks:
                    target = destination_path(destination, member)
                    relative_target = resolved_link(
                        normalized_member(member.name), member.linkname, hard=True
                    )
                    source = destination.joinpath(*relative_target.parts)
                    if not source.is_file() or source.is_symlink():
                        fail(
                            "archive hardlink target is not an extracted regular file: "
                            f"{member.name}"
                        )
                    target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
                    os.link(source, target, follow_symlinks=False)

                for member in symlinks:
                    target = destination_path(destination, member)
                    resolved_link(normalized_member(member.name), member.linkname, hard=False)
                    target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
                    os.symlink(member.linkname, target)

                for directory, mode in reversed(directories):
                    directory.chmod(mode)
        after = os.fstat(archive_fd)
        if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
            after.st_dev,
            after.st_ino,
            after.st_size,
            after.st_mtime_ns,
        ):
            fail(f"staged archive changed while it was extracted: {archive}")
    except Exception:
        shutil.rmtree(destination, ignore_errors=True)
        raise
    finally:
        os.close(archive_fd)
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


def forbidden_tool_path(path: Path) -> bool:
    rendered = "/" + str(path).replace("\\", "/").strip("/") + "/"
    return any(
        marker in rendered
        for marker in ("/.rustup/", "/rustup/toolchains/", "/genesis-stage0/")
    )


def create_sanitized_path(path_value: str, output: Path) -> dict[str, object]:
    if output.exists() or output.is_symlink():
        fail(f"sanitized PATH directory already exists: {output}")
    output.mkdir(mode=0o700, parents=True)
    admitted: dict[str, dict[str, object]] = {}
    identity_cache: dict[tuple[int, int, int, int], str] = {}
    rejected: list[str] = []
    for raw in path_value.split(os.pathsep):
        if not raw or "\n" in raw or "\r" in raw:
            fail("PATH contains an empty or newline-bearing component")
        directory = Path(raw)
        if not directory.is_absolute():
            fail(f"PATH contains a relative component: {raw!r}")
        try:
            canonical_dir = directory.resolve(strict=True)
        except OSError:
            continue
        if not canonical_dir.is_dir() or forbidden_tool_path(canonical_dir):
            continue
        try:
            entries = sorted(os.scandir(canonical_dir), key=lambda entry: entry.name)
        except OSError:
            continue
        for entry in entries:
            name = entry.name
            if name in admitted or (output / name).exists() or (output / name).is_symlink():
                continue
            if rust_family_name(name):
                rejected.append(str(canonical_dir / name))
                continue
            candidate = canonical_dir / name
            try:
                resolved = candidate.resolve(strict=True)
                mode = resolved.stat().st_mode
            except OSError:
                continue
            if forbidden_tool_path(resolved) or not stat.S_ISREG(mode) or not os.access(resolved, os.X_OK):
                continue
            identity = resolved.stat()
            identity_key = (
                identity.st_dev,
                identity.st_ino,
                identity.st_size,
                identity.st_mtime_ns,
            )
            digest = identity_cache.get(identity_key)
            if digest is None:
                digest = sha256_file(resolved)
                identity_cache[identity_key] = digest
            os.symlink(resolved, output / name)
            admitted[name] = {
                "path": str(resolved),
                "device": identity.st_dev,
                "inode": identity.st_ino,
                "bytes": identity.st_size,
                "mtime_ns": identity.st_mtime_ns,
                "sha256": digest,
            }
    for required in ("git", "sh"):
        if required not in admitted:
            fail(f"sanitized PATH cannot supply required non-Rust tool {required!r}")
    return {
        "schema": "trust-sanitized-path-v1",
        "admitted": admitted,
        "excluded_rust_family": sorted(rejected),
    }


def revalidate_sanitized_path(output: Path, manifest_path: Path) -> None:
    canonical_regular_file(manifest_path, "sanitized PATH manifest")
    try:
        with manifest_path.open("r", encoding="utf-8") as handle:
            manifest = json.load(handle)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        fail(f"cannot read sanitized PATH manifest: {exc}")
    admitted = manifest.get("admitted")
    if manifest.get("schema") != "trust-sanitized-path-v1" or not isinstance(admitted, dict):
        fail("sanitized PATH manifest has an unsupported schema")
    if output.is_symlink() or not output.is_dir():
        fail(f"sanitized PATH directory changed identity: {output}")
    actual_names = {entry.name for entry in os.scandir(output)}
    if actual_names != set(admitted):
        fail("sanitized PATH entry set changed during the workflow")
    digest_cache: dict[tuple[int, int, int, int], str] = {}
    for name, expected in admitted.items():
        if not isinstance(name, str) or not isinstance(expected, dict):
            fail("sanitized PATH manifest contains a malformed entry")
        link = output / name
        if not link.is_symlink():
            fail(f"sanitized PATH entry is no longer a symlink: {link}")
        try:
            target = link.resolve(strict=True)
            identity = target.stat()
        except OSError as exc:
            fail(f"sanitized PATH entry cannot be revalidated: {link}: {exc}")
        current = {
            "path": str(target),
            "device": identity.st_dev,
            "inode": identity.st_ino,
            "bytes": identity.st_size,
            "mtime_ns": identity.st_mtime_ns,
        }
        for field, value in current.items():
            if expected.get(field) != value:
                fail(f"sanitized PATH target changed ({field}): {link}")
        key = (identity.st_dev, identity.st_ino, identity.st_size, identity.st_mtime_ns)
        digest = digest_cache.get(key)
        if digest is None:
            digest = sha256_file(target)
            digest_cache[key] = digest
        if expected.get("sha256") != digest:
            fail(f"sanitized PATH target content changed: {link}")


def seed_tree_fingerprint(seed: Path) -> dict[str, object]:
    digest = hashlib.sha256()
    content_cache: dict[tuple[int, int, int, int], str] = {}
    regular_files = 0
    symlinks = 0
    directories = 0
    total_bytes = 0
    total_entries = 0
    for directory, dirnames, filenames in os.walk(seed, followlinks=False):
        dirnames.sort()
        filenames.sort()
        for name in (*dirnames, *filenames):
            total_entries += 1
            if total_entries > MAX_ARCHIVE_MEMBERS:
                fail(f"installed seed exceeds {MAX_ARCHIVE_MEMBERS} filesystem entries")
            path = Path(directory) / name
            relative = path.relative_to(seed).as_posix()
            metadata = path.lstat()
            mode = stat.S_IMODE(metadata.st_mode)
            if stat.S_ISLNK(metadata.st_mode):
                symlinks += 1
                target = os.readlink(path)
                record: dict[str, object] = {
                    "path": relative,
                    "kind": "symlink",
                    "target": target,
                }
            elif stat.S_ISDIR(metadata.st_mode):
                directories += 1
                record = {"path": relative, "kind": "directory", "mode": mode}
            elif stat.S_ISREG(metadata.st_mode):
                regular_files += 1
                total_bytes += metadata.st_size
                if total_bytes > MAX_TOTAL_UNPACKED_BYTES:
                    fail(
                        f"installed seed exceeds {MAX_TOTAL_UNPACKED_BYTES} regular-file bytes"
                    )
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
                fail(f"installed seed contains an unsupported special file: {path}")
            digest.update(
                json.dumps(record, separators=(",", ":"), sort_keys=True).encode("utf-8")
            )
            digest.update(b"\n")
    return {
        "sha256": digest.hexdigest(),
        "entries": total_entries,
        "regular_files": regular_files,
        "directories": directories,
        "symlinks": symlinks,
        "regular_file_bytes": total_bytes,
    }


def validate_seed(seed: Path, version: str, host: str) -> dict[str, object]:
    version = canonical_version_value(version)
    host = canonical_host(host)
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

    probe_env = dict(os.environ)
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
    tool_versions = {
        "trustc": verbose.splitlines()[0] if verbose else "",
        "targo": probe("targo", "--version"),
        "trustfmt": probe("trustfmt", "--version"),
    }

    loader = shutil.which("otool") if platform.system() == "Darwin" else shutil.which("ldd")
    loader_evidence: dict[str, str] = {}
    if loader:
        for name in ("trustc", "targo", "trustfmt"):
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
            lowered = evidence.lower().replace("\\", "/")
            if "/.rustup/" in lowered or "/genesis-stage0/" in lowered:
                fail(f"seed {name} retains a forbidden stock-toolchain dependency: {evidence}")
            loader_evidence[name] = evidence.replace(str(seed), "{seed}")
    return {
        "schema": "trust-self-host-seed-surface-v1",
        "source_version": version,
        "host": host,
        "entrypoint_sha256": identities,
        "tool_versions": tool_versions,
        "loader_evidence": loader_evidence,
        "tree": seed_tree_fingerprint(seed),
    }


def write_json_exclusive(path: Path, value: object) -> None:
    path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    payload = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        write_all(fd, payload)
        os.fsync(fd)
    finally:
        os.close(fd)


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
        "rust_family_path_entries_excluded": len(safe_path["excluded_rust_family"]),
        "explicit_library_path": library_path.split(os.pathsep) if library_path else [],
        "native_library_inputs": native_libraries,
    }
    manifest["seed_surface"] = seed_surface
    manifest["result"] = "self-host-rebuild-and-sanity-pass"
    manifest["claim_boundary"] = (
        "This records exact inputs and a minimal-environment rebuild. It is not a kernel "
        "execution trace; scripts/prove_rust_free_build.sh --build owns that claim."
    )
    write_json_exclusive(output, manifest)


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    sub = result.add_subparsers(dest="command", required=True)

    version = sub.add_parser("version")
    version.add_argument("root", type=Path)

    host = sub.add_parser("host")
    host.add_argument("--value")

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

    mint_tools = sub.add_parser("mint-tools-manifest")
    mint_tools.add_argument("root", type=Path)
    mint_tools.add_argument("source", type=Path)
    mint_tools.add_argument("output", type=Path)

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

    config = sub.add_parser("write-config")
    config.add_argument("--source", type=Path, required=True)
    config.add_argument("--output", type=Path, required=True)
    config.add_argument("--seed", type=Path, required=True)
    config.add_argument("--fail-tool", type=Path, required=True)

    safe_path = sub.add_parser("safe-path")
    safe_path.add_argument("--input", required=True)
    safe_path.add_argument("--output", type=Path, required=True)
    safe_path.add_argument("--manifest", type=Path, required=True)

    revalidate_path = sub.add_parser("revalidate-path")
    revalidate_path.add_argument("--path", type=Path, required=True)
    revalidate_path.add_argument("--manifest", type=Path, required=True)

    seed = sub.add_parser("validate-seed")
    seed.add_argument("--seed", type=Path, required=True)
    seed.add_argument("--version", required=True)
    seed.add_argument("--host", required=True)
    seed.add_argument("--output", type=Path, required=True)

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
    return result


def main(argv: Iterable[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        if args.command == "version":
            print(canonical_version(args.root.resolve(strict=True)))
        elif args.command == "host":
            print(canonical_host(args.value) if args.value else detected_host())
        elif args.command == "repo-state":
            state = repository_state(args.root, args.expect_commit)
            if args.json:
                print(json.dumps(state, sort_keys=True))
            else:
                print(f"{state['commit']}\t{state['source_date_epoch']}")
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
        elif args.command == "mint-tools-manifest":
            write_json_exclusive(
                args.output, mint_tool_manifest(args.root, args.source)
            )
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
        elif args.command == "write-config":
            write_seed_config(args.source, args.output, args.seed, args.fail_tool)
        elif args.command == "safe-path":
            manifest = create_sanitized_path(args.input, args.output)
            write_json_exclusive(args.manifest, manifest)
        elif args.command == "revalidate-path":
            revalidate_sanitized_path(args.path, args.manifest)
        elif args.command == "validate-seed":
            manifest = validate_seed(args.seed, args.version, args.host)
            write_json_exclusive(args.output, manifest)
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
            )
        else:  # pragma: no cover - argparse makes this unreachable.
            fail(f"unsupported command: {args.command}")
    except WorkflowError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
