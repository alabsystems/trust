#!/usr/bin/env python3
"""Canonicalize host-specific source paths in Trust MIR JSON dumps."""

import json
import os
from pathlib import Path, PurePosixPath
import re
import sys


CANONICAL_PREFIX = "library/core/"
ABSOLUTE_HOST_PATH = re.compile(
    r"(?:^[A-Za-z]:[\\/]|(?:^|/)(?:private|Users|tmp|var/folders)/)"
)


def canonicalize(node: object) -> None:
    if isinstance(node, dict):
        for key, value in node.items():
            if key == "file" and isinstance(value, str):
                normalized = value.replace("\\", "/")
                if normalized.startswith(CANONICAL_PREFIX + "src/"):
                    suffix = normalized[len(CANONICAL_PREFIX) :]
                else:
                    marker = "/core/"
                    if marker not in normalized:
                        raise ValueError(f"source path is outside library/core: {value!r}")
                    suffix = normalized.rsplit(marker, 1)[1]
                if not suffix.startswith("src/") or ".." in PurePosixPath(suffix).parts:
                    raise ValueError(f"unexpected library/core source path: {value!r}")
                node[key] = CANONICAL_PREFIX + suffix
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
    elif isinstance(node, str) and ABSOLUTE_HOST_PATH.search(node):
        raise ValueError(f"host-specific absolute path remains: {node!r}")


def canonicalize_file(path: Path) -> None:
    data = json.loads(path.read_text(encoding="utf-8"))
    canonicalize(data)
    reject_host_paths(data)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} <dump-directory>")
    directory = Path(sys.argv[1])
    paths = sorted(directory.glob("*.json"))
    if not paths:
        raise SystemExit(f"no JSON dumps found in {directory}")
    for path in paths:
        canonicalize_file(path)


if __name__ == "__main__":
    main()
