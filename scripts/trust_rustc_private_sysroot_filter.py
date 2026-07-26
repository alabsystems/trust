#!/usr/bin/env python3
"""Filter Cargo dependency search paths for rustc-private Zani crates.

Cargo places every compiled dependency artifact in one `-L dependency=<deps>`
directory. When a crate using `#![feature(rustc_private)]` loads rustc sysroot
crates such as `rustc_public`, rustc may also see crates.io artifacts with the
same crate name in that directory. Zani's native leaf crates currently collide
with crates.io `hashbrown` this way before the verifier sample reaches CHC/PDR
execution.

This wrapper is intentionally narrow: it rewrites `-L dependency` only for the
configured rustc-private leaf crates and only filters configured crate names.
Other crates, including normal Zani/Cargo dependencies, compile with the
original rustc arguments.
"""

from __future__ import annotations

import hashlib
import os
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Iterable


DEFAULT_PRIVATE_CRATES = frozenset(
    {
        "zani_codegen_shared",
        "zani_codegen_types",
        "zani_kani_types",
    }
)
DEFAULT_FILTERED_CRATES = frozenset({"hashbrown"})
ARTIFACT_RE = re.compile(
    r"^lib(?P<crate>[A-Za-z0-9_]+)(?:-[A-Za-z0-9_]+)?\.(?:rlib|rmeta|dylib|so|dll|a)$"
)


def _env_set(name: str, default: frozenset[str]) -> frozenset[str]:
    raw = os.environ.get(name)
    if raw is None:
        return default
    entries = {
        entry.strip().replace("-", "_")
        for entry in re.split(r"[,:\s]+", raw)
        if entry.strip()
    }
    return frozenset(entries)


def crate_name_from_args(args: list[str]) -> str | None:
    for index, arg in enumerate(args):
        if arg == "--crate-name" and index + 1 < len(args):
            return args[index + 1].replace("-", "_")
        if arg.startswith("--crate-name="):
            return arg.split("=", 1)[1].replace("-", "_")
    return None


def artifact_crate_name(path: Path) -> str | None:
    match = ARTIFACT_RE.match(path.name)
    if match is None:
        return None
    return match.group("crate").replace("-", "_")


def should_filter_artifact(path: Path, filtered_crates: frozenset[str]) -> bool:
    crate_name = artifact_crate_name(path)
    return crate_name in filtered_crates if crate_name is not None else False


def _unique_filter_dir(dependency_dir: Path, crate_name: str) -> Path:
    base = dependency_dir.parent / ".trust-rustc-private-filtered-deps"
    digest = hashlib.sha256(
        f"{dependency_dir.resolve()}\0{crate_name}\0{os.getpid()}\0{time.time_ns()}".encode()
    ).hexdigest()[:16]
    filtered = base / f"{crate_name}-{digest}"
    filtered.mkdir(parents=True, exist_ok=False)
    return filtered


def filtered_dependency_dir(
    dependency_dir: Path,
    crate_name: str,
    filtered_crates: frozenset[str],
) -> Path:
    dependency_dir = dependency_dir.resolve()
    filtered = _unique_filter_dir(dependency_dir, crate_name)
    for child in dependency_dir.iterdir():
        if should_filter_artifact(child, filtered_crates):
            continue
        destination = filtered / child.name
        os.symlink(child, destination, target_is_directory=child.is_dir())
    return filtered


def _split_paths(raw: str) -> list[Path]:
    return [Path(entry) for entry in raw.split(os.pathsep) if entry]


def _rustc_output(rustc: str, args: list[str]) -> str | None:
    try:
        output = subprocess.check_output([rustc, *args], text=True, stderr=subprocess.DEVNULL)
    except (OSError, subprocess.CalledProcessError):
        return None
    output = output.strip()
    return output or None


def _host_tuple(rustc: str) -> str | None:
    verbose = _rustc_output(rustc, ["-vV"])
    if verbose is None:
        return None
    for line in verbose.splitlines():
        if line.startswith("host:"):
            return line.split(":", 1)[1].strip()
    return None


def compiler_private_deps_dirs(rustc: str) -> list[Path]:
    configured = os.environ.get("TRUST_RUSTC_PRIVATE_SYSROOT_DEPS")
    if configured:
        return [path.resolve() for path in _split_paths(configured) if path.is_dir()]

    sysroot = _rustc_output(rustc, ["--print", "sysroot"])
    host = _host_tuple(rustc)
    if sysroot is None or host is None:
        return []

    sysroot_path = Path(sysroot).resolve()
    stage_name = sysroot_path.name
    build_root = sysroot_path.parent
    candidates = [
        build_root / f"{stage_name}-rustc" / host / "release" / "deps",
        build_root / f"{stage_name}-rustc" / "release" / "deps",
    ]
    return [candidate.resolve() for candidate in candidates if candidate.is_dir()]


def split_search_path(payload: str) -> tuple[str | None, str]:
    if "=" not in payload:
        return None, payload
    kind, path = payload.split("=", 1)
    return kind, path


def rewrite_dependency_search_paths(
    args: list[str],
    crate_name: str,
    filtered_crates: frozenset[str],
    compiler_deps_dirs: list[Path] | None = None,
) -> list[str]:
    compiler_deps_dirs = compiler_deps_dirs or []
    compiler_deps = {path.resolve() for path in compiler_deps_dirs}
    rewritten: list[str] = [
        item
        for path in compiler_deps_dirs
        for item in ("-L", f"dependency={path}")
    ]
    index = 0
    while index < len(args):
        arg = args[index]
        if arg == "-L" and index + 1 < len(args):
            payload = args[index + 1]
            kind, path = split_search_path(payload)
            if kind == "dependency":
                dependency_dir = Path(path).resolve()
                if dependency_dir in compiler_deps:
                    rewritten.extend([arg, payload])
                else:
                    filtered = filtered_dependency_dir(dependency_dir, crate_name, filtered_crates)
                    rewritten.extend(["-L", f"dependency={filtered}"])
            else:
                rewritten.extend([arg, payload])
            index += 2
            continue
        if arg.startswith("-L") and len(arg) > 2:
            payload = arg[2:]
            kind, path = split_search_path(payload)
            if kind == "dependency":
                dependency_dir = Path(path).resolve()
                if dependency_dir in compiler_deps:
                    rewritten.append(arg)
                else:
                    filtered = filtered_dependency_dir(dependency_dir, crate_name, filtered_crates)
                    rewritten.append(f"-Ldependency={filtered}")
            else:
                rewritten.append(arg)
            index += 1
            continue
        rewritten.append(arg)
        index += 1
    return rewritten


def exec_rustc(rustc: str, args: Iterable[str]) -> None:
    os.execv(rustc, [rustc, *args])


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        return 2

    rustc = argv[1]
    rustc_args = argv[2:]
    crate_name = crate_name_from_args(rustc_args)
    private_crates = _env_set("TRUST_RUSTC_PRIVATE_SYSROOT_FILTER_CRATES", DEFAULT_PRIVATE_CRATES)
    filtered_crates = _env_set(
        "TRUST_RUSTC_PRIVATE_SYSROOT_FILTER_NAMES", DEFAULT_FILTERED_CRATES
    )

    if crate_name not in private_crates or not filtered_crates:
        exec_rustc(rustc, rustc_args)

    try:
        rustc_args = rewrite_dependency_search_paths(
            rustc_args,
            crate_name,
            filtered_crates,
            compiler_private_deps_dirs(rustc),
        )
    except Exception as error:
        print(
            f"trust_rustc_private_sysroot_filter: failed to prepare filtered deps for "
            f"{crate_name}: {error}",
            file=sys.stderr,
        )
        return 2

    exec_rustc(rustc, rustc_args)
    raise AssertionError("exec_rustc returned unexpectedly")


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
