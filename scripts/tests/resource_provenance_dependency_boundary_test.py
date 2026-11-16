#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Copyright 2026 Andrew Yates

"""Keep source/build guards below Git transport in every committed native graph.

Run with Python >=3.11. Native locked metadata separately checks that these
committed graphs resolve; this regression checks the boundary across all of them.
"""
import copy
from pathlib import Path
import tomllib
import unittest

ROOT = Path(__file__).resolve().parents[2]
LOCKS = (
    "Cargo.lock",
    "src/bootstrap/Cargo.lock",
    "src/tools/targo/Cargo.lock",
    "crates/trust-resource-provenance/Cargo.lock",
)
TRANSPORT = {"gix", "git2", "curl", "curl-sys", "openssl", "openssl-sys", "openssl-src-trust"}


def transport_path(packages):
    """Follow all recorded dependency candidates, including build dependencies."""
    by_name = {}
    for package in packages:
        by_name.setdefault(package["name"], []).append(package)
    roots = by_name.get("trust-resource-provenance", [])
    if not roots:
        raise AssertionError("graph omits the provenance guard")
    pending = [(package, [package["name"]]) for package in roots]
    seen = set()
    while pending:
        package, path = pending.pop()
        key = (package["name"], package["version"], package.get("source"))
        if key in seen:
            continue
        seen.add(key)
        if package["name"] in TRANSPORT:
            return path
        for dependency in package.get("dependencies", []):
            fields = dependency.split(" ", 2)
            candidates = by_name.get(fields[0], [])
            if len(fields) > 1:
                candidates = [p for p in candidates if p["version"] == fields[1]]
            if len(fields) > 2:
                candidates = [p for p in candidates if p.get("source") == fields[2][1:-1]]
            if not candidates:
                raise AssertionError(f"unresolved committed dependency: {dependency}")
            pending.extend((p, path + [p["name"]]) for p in candidates)
    return None


def declared_dependency_names(manifest):
    """Include optional/renamed/target dependencies before any lock is rewritten."""
    names = set()
    for section in ("dependencies", "build-dependencies", "dev-dependencies"):
        for alias, declaration in manifest.get(section, {}).items():
            names.add(declaration.get("package", alias) if isinstance(declaration, dict) else alias)
    for target in manifest.get("target", {}).values():
        names.update(declared_dependency_names(target))
    return names


class ResourceProvenanceDependencyBoundary(unittest.TestCase):
    def test_all_committed_native_graphs_keep_provenance_below_git_transport(self):
        manifest = tomllib.loads((ROOT / "crates/trust-resource-provenance/Cargo.toml").read_text())
        self.assertFalse(declared_dependency_names(manifest) & TRANSPORT)
        for lock in LOCKS:
            with self.subTest(lock=lock):
                packages = tomllib.loads((ROOT / lock).read_text())["package"]
                self.assertIsNone(transport_path(packages), lock)

    def test_reintroduced_git_dependency_is_detected_in_the_real_bootstrap_graph(self):
        packages = copy.deepcopy(tomllib.loads((ROOT / "src/bootstrap/Cargo.lock").read_text())["package"])
        provenance = next(p for p in packages if p["name"] == "trust-resource-provenance")
        git = next(p for p in packages if p["name"] == "gix")
        provenance.setdefault("dependencies", []).append(f"gix {git['version']}")
        self.assertEqual(transport_path(packages), ["trust-resource-provenance", "gix"])

    def test_optional_renamed_target_edge_cannot_hide_behind_an_unchanged_lock(self):
        manifest = tomllib.loads((ROOT / "crates/trust-resource-provenance/Cargo.toml").read_text())
        manifest.setdefault("target", {}).setdefault("cfg(unix)", {}).setdefault("dependencies", {})[
            "local-git-reader"
        ] = {"package": "gix", "version": "=0.85.0", "optional": True}
        self.assertEqual(declared_dependency_names(manifest) & TRANSPORT, {"gix"})


if __name__ == "__main__":
    unittest.main()
