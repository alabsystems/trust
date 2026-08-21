#!/usr/bin/env python3
"""check_patch_binds.py — a `[patch]` that does not BIND is worse than no patch.

Trust's root manifest redirects several git URLs to vendored first-party paths
so the workspace builds exactly ONE instance of each crate:

    [patch."https://github.com/alabsystems/clean.git"]
    clean-kernel = { path = "first-party/clean/crates/clean-kernel" }

Cargo applies such an entry only when the replacement's VERSION satisfies the
dependency's version requirement. When a submodule pin moves across a version
bump, the requirement stops being satisfied, the patch silently stops applying,
and cargo reaches for the original git rev instead — producing a SECOND copy of
the crate that the patch existed to prevent. Nothing warns; `--locked` fails
with a message about updating the lock file, which reads like lock staleness.

That is what happened on 2026-08-19: `8dddf6c755` moved `first-party/clean` to
`bc0941514` as "fmt-only", but that rev carries clean's `0.1.0 -> 0.2.0`
workspace bump. `Cargo.lock` still records `clean-kernel 1.5.0`.

This gate reads only files in the superproject, so it costs milliseconds and
runs anywhere. For every `[patch.<url>] <name> = { path = P }`:

  * P/Cargo.toml's version (resolving `version.workspace = true` against the
    nearest enclosing `[workspace.package]`) must MATCH a `[[package]]` entry
    of that name in Cargo.lock -- otherwise `--locked` cannot hold; and
  * Cargo.lock must hold exactly ONE `[[package]]` entry of that name --
    otherwise a second instance already resolved.

Exit 0 iff every patch entry binds. Author: Andrew Yates | Apache-2.0
"""
from __future__ import annotations

import pathlib
import re
import subprocess
import sys

PATCH_HEADER = re.compile(r'^\[patch\.(?:crates-io|"([^"]+)")\]\s*$')
TABLE_HEADER = re.compile(r"^\[")
ENTRY = re.compile(r'^\s*([A-Za-z0-9_-]+)\s*=\s*\{(.*)\}\s*$')
PATH_FIELD = re.compile(r'path\s*=\s*"([^"]+)"')
VERSION_FIELD = re.compile(r'^\s*version\s*=\s*"([^"]+)"', re.M)
WORKSPACE_VERSION = re.compile(r'^\s*version\s*\.?\s*workspace\s*=\s*true', re.M)


def repo_root() -> pathlib.Path:
    """The workspace to check: argv[1] if given, else this script's own repo."""
    if len(sys.argv) > 1:
        return pathlib.Path(sys.argv[1]).resolve()
    out = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        cwd=pathlib.Path(__file__).resolve().parent,
        capture_output=True, text=True, check=True,
    )
    return pathlib.Path(out.stdout.strip())


def patch_entries(manifest: pathlib.Path):
    """(url, crate_name, path) for every `name = { path = ... }` under [patch.*]."""
    url = None
    for line in manifest.read_text().splitlines():
        header = PATCH_HEADER.match(line)
        if header:
            url = header.group(1) or "crates-io"
            continue
        if url is not None and TABLE_HEADER.match(line):
            url = None
            continue
        if url is None:
            continue
        entry = ENTRY.match(line)
        if not entry:
            continue
        path = PATH_FIELD.search(entry.group(2))
        if path:
            yield url, entry.group(1), path.group(1)


def manifest_version(root: pathlib.Path, rel: str) -> tuple[str | None, str]:
    """Declared version of the crate at `rel`, and where it came from."""
    crate = root / rel / "Cargo.toml"
    if not crate.is_file():
        return None, f"no manifest at {rel}/Cargo.toml"
    text = crate.read_text()
    # The crate's own `[package] version = "..."` wins over anything later in
    # the file (a `[dependencies] foo = { version = ... }` must not be read as
    # the package version), so scan only the [package] table.
    package = re.split(r"^\[", text, flags=re.M)
    for chunk in package:
        if not chunk.startswith("package]"):
            continue
        own = VERSION_FIELD.search(chunk)
        if own:
            return own.group(1), f"{rel}/Cargo.toml"
        if WORKSPACE_VERSION.search(chunk):
            break
    # `version.workspace = true`: walk up to the nearest [workspace.package].
    here = (root / rel).resolve()
    while True:
        candidate = here / "Cargo.toml"
        if candidate.is_file():
            body = candidate.read_text()
            for chunk in re.split(r"^\[", body, flags=re.M):
                if chunk.startswith("workspace.package]"):
                    ws = VERSION_FIELD.search(chunk)
                    if ws:
                        return ws.group(1), f"{candidate.relative_to(root)} [workspace.package]"
        if here == here.parent or here == root:
            return None, f"{rel}: version.workspace = true but no [workspace.package] above it"
        here = here.parent


def lock_versions(lock: pathlib.Path) -> dict[str, list[tuple[str, str | None]]]:
    """name -> [(version, source-or-None)] for every [[package]] in Cargo.lock."""
    found: dict[str, list[tuple[str, str | None]]] = {}
    name = version = source = None
    for line in lock.read_text().splitlines() + ["[[package]]"]:
        if line.strip() == "[[package]]":
            if name and version:
                found.setdefault(name, []).append((version, source))
            name = version = source = None
            continue
        key, _, raw = line.partition(" = ")
        value = raw.strip().strip('"')
        if key == "name":
            name = value
        elif key == "version":
            version = value
        elif key == "source":
            source = value
    return found


def main() -> int:
    root = repo_root()
    manifest, lock = root / "Cargo.toml", root / "Cargo.lock"
    if not lock.is_file():
        print(f"check_patch_binds: no Cargo.lock at {lock}", file=sys.stderr)
        return 1
    locked = lock_versions(lock)

    problems: list[str] = []
    checked = 0
    skipped = 0
    for url, name, rel in patch_entries(manifest):
        # An un-checked-out submodule is a DIFFERENT condition, owned by
        # check_pin_coherence.sh. Failing here too would only teach lanes to
        # ignore this gate in every worktree that has not run `submodule update`.
        if not (root / rel / "Cargo.toml").is_file():
            skipped += 1
            continue
        declared, origin = manifest_version(root, rel)
        checked += 1
        if declared is None:
            problems.append(
                f"UNREADABLE  [patch.\"{url}\"] {name} -> {rel}\n"
                f"            {origin}"
            )
            continue
        entries = locked.get(name, [])
        if not entries:
            problems.append(
                f"UNLOCKED    [patch.\"{url}\"] {name} -> {rel}\n"
                f"            manifest says {declared} ({origin}) but Cargo.lock has no\n"
                f"            [[package]] named {name} at all."
            )
            continue
        if len(entries) > 1:
            shown = ", ".join(f"{v} ({s or 'path'})" for v, s in entries)
            problems.append(
                f"DUPLICATED  [patch.\"{url}\"] {name} -> {rel}\n"
                f"            Cargo.lock holds {len(entries)} copies: {shown}\n"
                f"            A second instance is exactly what this patch exists to prevent."
            )
            continue
        version, source = entries[0]
        if version != declared:
            problems.append(
                f"UNBOUND     [patch.\"{url}\"] {name} -> {rel}\n"
                f"            manifest says {declared} ({origin})\n"
                f"            Cargo.lock says {version} ({source or 'path'})\n"
                f"            `--locked` cannot hold, and any dependency requiring the\n"
                f"            locked version no longer accepts the patched crate -- so the\n"
                f"            patch stops applying and cargo resolves the ORIGINAL git rev.\n"
                f"            Fix by moving the pin, the requirement, or the lock -- and say\n"
                f"            which, because they are three different claims."
            )

    if problems:
        print("check_patch_binds: FAIL — a [patch] entry does not bind\n", file=sys.stderr)
        if skipped:
            print(f"({skipped} further entries skipped: submodule not checked out)\n", file=sys.stderr)
        for problem in problems:
            print(problem + "\n", file=sys.stderr)
        return 1
    note = f" ({skipped} skipped: submodule not checked out)" if skipped else ""
    print(f"check_patch_binds: OK — {checked} path-redirecting [patch] entries bind{note}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
