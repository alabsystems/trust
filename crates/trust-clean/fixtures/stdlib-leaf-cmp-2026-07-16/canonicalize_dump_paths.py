#!/usr/bin/env python3
"""Canonicalize and validate source paths in the cmp harvest JSON corpus."""

import json
import os
from pathlib import Path, PurePosixPath
import re
import sys


CORE_PREFIX = "library/core/"
SOURCE_PREFIX = (
    "crates/trust-clean/fixtures/stdlib-leaf-cmp-2026-07-16/SOURCE/"
)
HOST_PATH = re.compile(
    r"(?:[A-Za-z]:[/\\]|/(?:Users|private|tmp|var/folders)(?:/|$))"
)


def canonical_file(value: str) -> str:
    normalized = value.replace("\\", "/")
    if normalized.startswith(CORE_PREFIX + "src/"):
        suffix = normalized[len(CORE_PREFIX) :]
        prefix = CORE_PREFIX
    elif normalized.startswith(SOURCE_PREFIX):
        suffix = normalized[len(SOURCE_PREFIX) :]
        prefix = SOURCE_PREFIX
    elif "/crates/trust-clean/fixtures/stdlib-leaf-cmp-2026-07-16/SOURCE/" in normalized:
        suffix = normalized.rsplit(
            "/crates/trust-clean/fixtures/stdlib-leaf-cmp-2026-07-16/SOURCE/", 1
        )[1]
        prefix = SOURCE_PREFIX
    elif "/core/src/" in normalized:
        suffix = "src/" + normalized.rsplit("/core/src/", 1)[1]
        prefix = CORE_PREFIX
    else:
        raise ValueError(f"source path is outside the recorded core/SOURCE inputs: {value!r}")
    if not suffix or ".." in PurePosixPath(suffix).parts:
        raise ValueError(f"unsafe source path: {value!r}")
    if prefix == CORE_PREFIX and not suffix.startswith("src/"):
        raise ValueError(f"unexpected library/core source path: {value!r}")
    return prefix + suffix


def canonicalize(node: object) -> None:
    if isinstance(node, dict):
        for key, value in node.items():
            if key == "file" and isinstance(value, str):
                node[key] = canonical_file(value)
            else:
                canonicalize(value)
    elif isinstance(node, list):
        for value in node:
            canonicalize(value)


def reject_host_paths(node: object) -> None:
    if isinstance(node, dict):
        for value in node.values():
            reject_host_paths(value)
    elif isinstance(node, list):
        for value in node:
            reject_host_paths(value)
    elif isinstance(node, str) and HOST_PATH.search(node):
        raise ValueError(f"host-specific absolute path remains: {node!r}")


def canonicalize_file(path: Path) -> None:
    data = json.loads(path.read_text(encoding="utf-8"))
    canonicalize(data)
    reject_host_paths(data)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(
        json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    os.replace(temporary, path)


def main() -> None:
    if len(sys.argv) < 2:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} <dump-directory> [...]")
    for argument in sys.argv[1:]:
        directory = Path(argument)
        paths = sorted(directory.glob("**/*.json"))
        if not paths:
            raise SystemExit(f"no JSON dumps found in {directory}")
        for path in paths:
            canonicalize_file(path)


if __name__ == "__main__":
    main()
