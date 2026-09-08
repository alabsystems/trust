#!/usr/bin/env python3
"""Remove links whose resolved targets escape a newly copied toolchain seal."""

# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

import os
from pathlib import Path
import sys


def prune_escaping_symlinks(directory: Path) -> list[Path]:
    root = directory.resolve(strict=True)
    if not root.is_dir():
        raise ValueError(f"seal is not a directory: {directory}")
    escaping = []
    # Decide the whole set before deleting: a link through an escaping link
    # must be classified while its intermediate target still exists.
    for parent, directories, files in os.walk(root, followlinks=False):
        for name in directories + files:
            link = Path(parent) / name
            if not link.is_symlink():
                continue
            try:
                try:
                    target = link.resolve(strict=True)
                except FileNotFoundError:
                    target = link.resolve(strict=False)
                target.relative_to(root)
            except (ValueError, RuntimeError, OSError):
                escaping.append(link)
    for link in escaping:
        link.unlink()
    return escaping


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: prune_seal_symlinks.py SEAL_DIRECTORY")
    for removed in prune_escaping_symlinks(Path(sys.argv[1])):
        print(f"seal: dropped escaping or cyclic symlink {removed}")
