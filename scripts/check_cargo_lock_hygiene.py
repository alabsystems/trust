#!/usr/bin/env python3
"""Fail-closed guard for the `cargo --locked` refusal in this workspace.

WHY THIS EXISTS
---------------
Lanes repeatedly hit::

    error: cannot update the lock file ... because --locked was passed

and worked around it with ``cargo --offline`` plus ``git checkout -- Cargo.lock``.
That workaround is a footgun: the intermediate step leaves a *regenerated*
Cargo.lock in the tree, and committing it silently rewrites the dependency graph
of the whole constellation. One lane came within a step of doing exactly that.

The refusal is almost never a defect in the committed state. Measured on
2026-08-13 at superproject 352aa0306d: a pristine checkout of trust `main` with
all nine ``first-party/*`` submodules at their **recorded gitlinks** passes
``cargo metadata --locked`` with exit 0. The refusal is produced by the *working
tree*, when a submodule pointer is moved off its recorded gitlink onto a branch
whose manifest demands a version the root ``[patch]`` tables cannot supply.

THE MECHANISM
-------------
A Cargo ``[patch]`` entry applies only when the version of the *patched* crate
satisfies the dependency's version requirement. The root ``[patch]`` tables
redirect every ``alabsystems/*`` git edge to the checked-out submodule path,
so the committed Cargo.lock contains **zero** ``git+`` sources -- that is the
invariant this script enforces.

If a submodule is moved to a commit that asks for, say, ``ay-core = { version =
"0.8.0", git = "...ay.git", rev = "d58d6280" }`` while ``first-party/ay`` is at
0.9.0, then ``^0.8.0`` is not satisfied by 0.9.0, the patch silently does *not*
apply, and cargo must resolve the real git source -- which needs the network and
new lock entries. ``--locked`` correctly refuses.

THE REMEDY IS TO RESTORE THE POINTER, NEVER TO REGENERATE THE LOCK.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path
from typing import List, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]

GIT_SOURCE_RE = re.compile(r'^source = "git\+([^"]+)"', re.MULTILINE)
# `name = { version = "X", git = "...<repo>.git", rev = "..." }` on one line.
GIT_DEP_RE = re.compile(
    r'^\s*(?P<name>[A-Za-z0-9_-]+)\s*=\s*\{[^}]*?'
    r'version\s*=\s*"(?P<version>[^"]+)"[^}]*?'
    r'git\s*=\s*"(?P<url>[^"]*alabsystems/[^"]+)"'
    r'(?:[^}]*?rev\s*=\s*"(?P<rev>[0-9a-f]+)")?',
    re.MULTILINE,
)


def git(args: List[str], cwd: Path = REPO_ROOT) -> str:
    out = subprocess.run(
        ["git", *args], cwd=str(cwd), capture_output=True, text=True, check=False
    )
    return out.stdout


def dirty_submodules() -> List[Tuple[str, str, str]]:
    """Return (path, recorded_sha, worktree_sha) for moved gitlinks.

    ``git submodule status`` prefixes a moved pointer with ``+``. The recorded
    gitlink is read from HEAD rather than from that line, because the line
    reports the worktree sha.
    """
    moved = []
    for line in git(["submodule", "status"]).splitlines():
        if not line.startswith("+"):
            continue
        parts = line[1:].split()
        if len(parts) < 2:
            continue
        worktree_sha, path = parts[0], parts[1]
        recorded = git(["rev-parse", f"HEAD:{path}"]).strip()
        moved.append((path, recorded, worktree_sha))
    return moved


def explain_submodule(path: str, recorded: str, worktree: str) -> List[str]:
    """Name the version requirements that changed when the pointer moved."""
    lines = []
    sub = REPO_ROOT / path

    def deps_at(ref: str):
        found = {}
        blob = git(["show", f"{ref}:Cargo.toml"], cwd=sub)
        for m in GIT_DEP_RE.finditer(blob):
            found[m.group("name")] = (m.group("version"), m.group("rev") or "")
        return found

    before, after = deps_at(recorded), deps_at(worktree)
    for name in sorted(set(before) | set(after)):
        b, a = before.get(name), after.get(name)
        if b != a:
            bs = f'{b[0]} @ {b[1][:10]}' if b else "(absent)"
            as_ = f'{a[0]} @ {a[1][:10]}' if a else "(absent)"
            lines.append(f"      {name}: recorded wants {bs} -> worktree wants {as_}")
    return lines


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--explain",
        action="store_true",
        help="also diagnose which moved submodule pointer caused a refusal",
    )
    args = parser.parse_args()

    lock = REPO_ROOT / "Cargo.lock"
    if not lock.is_file():
        print(f"FAIL: {lock} does not exist", file=sys.stderr)
        return 2

    sources = sorted(set(GIT_SOURCE_RE.findall(lock.read_text())))
    moved = dirty_submodules()

    if not sources:
        print("PASS: Cargo.lock contains zero git+ sources "
              "(every first-party git edge is patched to a submodule path)")
        if moved and args.explain:
            print("\nnote: these submodule pointers are moved off their recorded "
                  "gitlinks, which can still make `cargo --locked` refuse:")
            for path, recorded, worktree in moved:
                print(f"  {path}: recorded {recorded[:12]} -> worktree {worktree[:12]}")
        return 0

    print("FAIL: Cargo.lock contains git+ sources; it has been regenerated.",
          file=sys.stderr)
    print("", file=sys.stderr)
    for s in sources:
        print(f"  git+{s}", file=sys.stderr)
    print("", file=sys.stderr)
    print("  The committed lock redirects every alabsystems/* git edge to a", file=sys.stderr)
    print("  submodule path via the root [patch] tables, so a git+ source means", file=sys.stderr)
    print("  a [patch] entry stopped applying and cargo re-resolved from git.", file=sys.stderr)
    print("  A [patch] applies only when the patched crate's version SATISFIES", file=sys.stderr)
    print("  the dependency's version requirement.", file=sys.stderr)

    if moved:
        print("", file=sys.stderr)
        print("  Moved submodule pointers (the usual cause):", file=sys.stderr)
        for path, recorded, worktree in moved:
            print(f"    {path}: recorded {recorded[:12]} -> worktree {worktree[:12]}",
                  file=sys.stderr)
            for line in explain_submodule(path, recorded, worktree):
                print(line, file=sys.stderr)

    print("", file=sys.stderr)
    print("  REMEDY: restore the submodule pointer, do NOT commit this lock:", file=sys.stderr)
    print("    git checkout -- Cargo.lock", file=sys.stderr)
    for path, recorded, _ in moved or []:
        print(f"    git -C {path} checkout --detach {recorded}", file=sys.stderr)
    print("", file=sys.stderr)
    print("  If the version bump is intended, the whole constellation must move", file=sys.stderr)
    print("  together (the patched submodule too) -- that is a pinning decision,", file=sys.stderr)
    print("  not a lockfile edit.", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
