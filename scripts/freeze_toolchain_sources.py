#!/usr/bin/env python3
"""Freeze committed compiler/std sources and std's declared out-of-tree leaves."""
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import runpy
import shutil
import subprocess
import sys
import tarfile
import tempfile
try:
    import tomllib
except ModuleNotFoundError:
    # macOS's bare python3 may still be 3.9 while a supported versioned
    # interpreter is on PATH. Keep selection here so every promotion caller
    # gets the same source-parser requirement, including the isolated fixture.
    if __name__ != "__main__":
        raise
    for name in ("python3.14", "python3.13", "python3.12", "python3.11"):
        candidate = shutil.which(name)
        if candidate:
            probe = subprocess.run([candidate, "-I", "-S", "-c", "import tomllib"],
                                   capture_output=True, timeout=10)
            if probe.returncode == 0:
                os.execv(candidate, [candidate, *sys.argv])
    raise SystemExit("source freeze requires Python 3.11+ with tomllib on PATH")


LEAVES = ("trust-bignum", "trust-memchr")


class Refused(ValueError):
    pass


def git_environment() -> dict[str, str]:
    environment = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    environment["GIT_OPTIONAL_LOCKS"] = "0"
    return environment


def git(repository: Path, *arguments: str) -> bytes:
    return subprocess.run(["git", "-C", str(repository), *arguments],
                          env=git_environment(), capture_output=True, check=True, timeout=120).stdout


def real_directory(path: Path) -> None:
    if path.is_symlink() or not path.is_dir():
        raise Refused(f"source snapshot parent is not a real directory: {path}")


def archive(repository: Path, commit: str, roots: list[str], destination: Path) -> None:
    real_directory(destination)
    with tempfile.TemporaryFile(dir=destination.parent) as stream:
        subprocess.run(["git", "-C", str(repository), "archive", "--format=tar", commit, "--", *roots],
                       env=git_environment(), stdout=stream, stderr=subprocess.PIPE,
                       check=True, timeout=120)
        stream.seek(0)
        with tarfile.open(fileobj=stream, mode="r:") as image:
            for entry in image:
                relative = PurePosixPath(entry.name)
                if relative.is_absolute() or not relative.parts or any(p in {"", ".", ".."} for p in relative.parts):
                    raise Refused(f"invalid source archive member: {entry.name}")
                target = destination
                for part in relative.parts[:-1]:
                    target /= part
                    target.mkdir(exist_ok=True)
                    real_directory(target)
                target /= relative.name
                if entry.isdir():
                    target.mkdir(exist_ok=True)
                    real_directory(target)
                elif entry.isfile():
                    source = image.extractfile(entry)
                    if source is None:
                        raise Refused(f"source archive member has no bytes: {entry.name}")
                    with source, target.open("xb") as output:
                        shutil.copyfileobj(source, output)
                    target.chmod(entry.mode & 0o777)
                else:
                    raise Refused(f"link or special file in frozen sources: {entry.name}")


def normalize_manifest(text: str, defaults: dict, writer) -> str:
    """The std-source transform in bootstrap dist.rs, without inheriting a dev workspace."""
    value = tomllib.loads(text)
    package = value.get("package", {})
    for key, item in list(package.items()):
        if isinstance(item, dict) and item.get("workspace") is True:
            if key not in defaults:
                raise Refused(f"std source manifest inherits package.{key} without a committed default")
            package[key] = defaults[key]
    value.pop("lints", None)
    value.pop("dev-dependencies", None)

    def inherited(item):
        if isinstance(item, dict):
            return item.get("workspace") is True or any(inherited(v) for v in item.values())
        return isinstance(item, list) and any(inherited(v) for v in item)

    if inherited(value):
        raise Refused("std source manifest still inherits from a workspace after normalization")
    rendered = writer(value)
    if tomllib.loads(rendered) != value:
        raise Refused("std source manifest changed meaning during serialization")
    return ("# Normalized for the frozen std sources using bootstrap dist.rs rules:\n"
            "# inherited package fields resolved; workspace lints and dev-dependencies removed.\n" + rendered)


def freeze(repository: Path, commit: str, destination: Path, *, writer=None) -> dict:
    repository = repository.resolve(strict=True)
    real_directory(destination)
    if destination.absolute() != destination.resolve(strict=True):
        raise Refused(f"source snapshot destination traverses a link: {destination}")
    if any(destination.iterdir()):
        raise Refused(f"source snapshot destination is not empty: {destination}")
    commit = git(repository, "rev-parse", "--verify", commit + "^{commit}").decode().strip()
    roots = ["library", "compiler", *(f"crates/{name}" for name in LEAVES)]
    archive(repository, commit, roots, destination)
    defaults = tomllib.loads(git(repository, "show", f"{commit}:Cargo.toml").decode())["workspace"]["package"]
    if writer is None:
        owner = Path(__file__).resolve().parents[1] / "src/tools/trust-stage0-dist/prepare.py"
        if owner.is_symlink() or not owner.is_file():
            raise Refused(f"stage0 TOML writer is not a regular file: {owner}")
        # Reading the serializer must not dirty the source checkout with .pyc files.
        previous_bytecode = sys.dont_write_bytecode
        try:
            sys.dont_write_bytecode = True
            writer = runpy.run_path(str(owner), run_name="frozen_std_source_toml_owner")["dump_toml"]
        finally:
            sys.dont_write_bytecode = previous_bytecode
    normalized = {}
    for name in LEAVES:
        path = destination / "crates" / name / "Cargo.toml"
        original = path.read_bytes()
        text = normalize_manifest(original.decode(), defaults, writer)
        path.write_text(text)
        normalized[name] = {"original_sha256": hashlib.sha256(original).hexdigest(),
                            "normalized_sha256": hashlib.sha256(text.encode()).hexdigest()}
    llvm = git(repository, "ls-tree", commit, "--", "src/llvm-project").decode().strip()
    llvm_commit = None
    if llvm.startswith("160000 commit "):
        llvm_commit = llvm.split()[2]
        submodule = repository / "src/llvm-project"
        if Path(git(submodule, "rev-parse", "--show-toplevel").decode().strip()).resolve() != submodule.resolve():
            raise Refused("the recorded LLVM source object store is not initialized")
        output = destination / "src/llvm-project"
        output.mkdir(parents=True)
        archive(submodule, llvm_commit, ["libunwind"], output)
    else:
        # Vendored source trees (and small fixtures) have no separate gitlink.
        archive(repository, commit, ["src/llvm-project/libunwind"], destination)
    return {"source_commit": commit, "llvm_gitlink": llvm_commit, "normalized_std_leaves": normalized}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", type=Path)
    parser.add_argument("commit")
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    try:
        print(json.dumps(freeze(args.repository, args.commit, args.destination), sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError, subprocess.SubprocessError, tarfile.TarError) as error:
        print(f"source freeze refused: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
