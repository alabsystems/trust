#!/usr/bin/env python3
"""Confinement controls for the exact helper invoked during promotion."""

# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

import importlib.util
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "prune_seal_symlinks", Path(__file__).parents[1] / "prune_seal_symlinks.py"
)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SealSymlinkTests(unittest.TestCase):
    def test_resolved_targets_stay_inside_seal(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary).resolve()
            root = base / "seal"
            root.mkdir()
            (root / "lib").mkdir()
            (root / "lib" / "inside").touch()
            outside = base / "outside"
            outside.mkdir()
            (outside / "keep").touch()
            (root / "relative").symlink_to("lib/inside")
            (root / "absolute").symlink_to(root / "lib" / "inside")
            (root / "internal-dangling").symlink_to("lib/missing")
            (root / "traversal").symlink_to("../outside/keep")
            (root / "absolute-traversal").symlink_to(root / ".." / "outside" / "keep")
            (root / "sibling").symlink_to(base / "seal-other" / "missing")
            (root / "escape-directory").symlink_to(outside, target_is_directory=True)
            (root / "chain").symlink_to("escape-directory/keep")
            (root / "cycle-a").symlink_to("cycle-b")
            (root / "cycle-b").symlink_to("cycle-a")
            removed = MODULE.prune_escaping_symlinks(root)
            self.assertEqual(
                {path.name for path in removed},
                {"traversal", "absolute-traversal", "sibling", "escape-directory", "chain", "cycle-a", "cycle-b"},
            )
            for name in ("relative", "absolute", "internal-dangling"):
                self.assertTrue((root / name).is_symlink(), name)
            self.assertTrue((outside / "keep").is_file())
            self.assertEqual(MODULE.prune_escaping_symlinks(root), [])


if __name__ == "__main__":
    unittest.main()
