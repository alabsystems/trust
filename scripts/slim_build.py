#!/usr/bin/env python3
"""Reclaim the bootstrap's intermediate target trees without touching the sysroot.

WHY THIS EXISTS. On 2026-07-30 `build/` was 194 GB, of which 184 GB was three
intermediate cargo target directories -- `stage1-rustc` (48G), `stage2-rustc`
(92G) and `stage2-tools` (44G). Deleting them reclaimed 172 GB and left a fully
working stage2 toolchain. That was safe, but only because of an invariant that
was verified empirically first and is easy to get wrong from memory:

    EVERY artifact x.py INSTALLS into `build/<host>/stage2/` is HARDLINKED
    there. Deleting a target tree removes one link; the data survives as long
    as the sysroot's own link remains.

Measured that day: `stage2/bin/trustc` had st_nlink=3 with one link inside
`stage2-rustc/.../release/rustc-main`; `stage2/bin/cargo` likewise into
`stage2-tools`; `stage2/lib/rustlib/.../libstd-*.rlib` into `stage1-std`.
Deleting the other links changed nothing about the sysroot.

The invariant fails in exactly one case: a build that has not finished
installing. Then the sysroot is incomplete and the target trees are the only
copy. So this script REFUSES to run against an incomplete or in-progress build
rather than trusting the caller to know.

It does NOT touch: stage2/ (the sysroot), stage2-tools-bin, stage0*, llvm,
bootstrap-tools, or anything under crates/. Those are either the product or are
not regenerable from a target tree.

COST OF RUNNING THIS: the next `x.py build` recompiles from scratch. This trades
disk for build time. It does not change what a build PRODUCES -- for that, see
docs/zero-stock-rust-plan.md and the `tools = [...]` list in bootstrap.toml.
"""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path

# Intermediate cargo target trees. Each is regenerable and each has its installed
# artifacts hardlinked into the sysroot. Order is cosmetic.
PURGE_TARGETS = ("stage1-rustc", "stage2-rustc", "stage2-tools")

# Never purge these, and say why -- a future cleanup will read this list before
# it reads the docstring.
KEEP = {
    "stage2": "the installed sysroot: this IS the product",
    "stage2-tools-bin": "installed tool binaries; not a regenerable target tree",
    "stage0": "the checksum-pinned Trust seed; re-fetching needs authenticated gh",
    "stage0-sysroot": "extracted seed sysroot; same",
    "llvm": "hours to rebuild and not a cargo target tree",
    "bootstrap-tools": "the bootstrap driver itself",
    "stage1": "stage1 sysroot; stage2 is built FROM it",
    "stage1-std": "holds the only copy of some std artifacts the sysroot links to",
}


def human(n: int) -> str:
    x = float(n)
    for unit in ("B", "KiB", "MiB", "GiB", "TiB"):
        if x < 1024 or unit == "TiB":
            return f"{x:.1f} {unit}"
        x /= 1024
    return f"{x:.1f} TiB"


def tree_size(path: Path) -> int:
    """Bytes actually attributable to this tree, counting each inode once.

    Hardlinked files are shared with the sysroot, so counting them per-path
    would overstate what deletion reclaims. This is the honest number.
    """
    seen: set[tuple[int, int]] = set()
    total = 0
    for root, _dirs, files in os.walk(path, onerror=lambda _e: None):
        for name in files:
            try:
                st = os.lstat(os.path.join(root, name))
            except OSError:
                continue
            key = (st.st_dev, st.st_ino)
            if key in seen:
                continue
            seen.add(key)
            # A file with links elsewhere (i.e. into the sysroot) does not free
            # its blocks when this tree goes away. Count only what actually frees.
            if st.st_nlink == 1:
                total += st.st_size
    return total


def build_in_progress(root: Path) -> str | None:
    lock = root / "build" / "lock"
    try:
        out = subprocess.run(
            ["pgrep", "-f", "x.py|recreate_bootstrap"],
            capture_output=True, text=True, check=False,
        )
        if out.returncode == 0 and out.stdout.strip():
            return f"a build appears to be running (pids {out.stdout.split()})"
    except OSError:
        pass
    if lock.exists():
        try:
            if lock.stat().st_size > 0:
                return f"{lock} is held"
        except OSError:
            pass
    return None


def sysroot_is_complete(host_root: Path) -> tuple[bool, str]:
    """A sysroot we are willing to delete the scaffolding around."""
    bindir = host_root / "stage2" / "bin"
    trustc = bindir / "trustc"
    if not bindir.is_dir():
        return False, f"{bindir} does not exist"
    entries = sorted(p.name for p in bindir.iterdir())
    if not entries:
        return False, f"{bindir} is EMPTY -- the build has not installed yet"
    if not trustc.is_file():
        return False, f"{trustc} is missing"
    try:
        out = subprocess.run(
            [str(trustc), "--version"], capture_output=True, text=True,
            timeout=60, check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return False, f"{trustc} could not be executed: {exc}"
    if out.returncode != 0:
        return False, f"{trustc} --version exited {out.returncode}"
    return True, out.stdout.strip()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", default=str(Path(__file__).resolve().parent.parent))
    ap.add_argument("--host", default=None, help="target triple; auto-detected")
    ap.add_argument("--dry-run", action="store_true", help="report, delete nothing")
    ap.add_argument("--force", action="store_true",
                    help="skip the in-progress-build refusal (NOT the sysroot check)")
    args = ap.parse_args()

    root = Path(args.root).resolve()
    build = root / "build"
    if not build.is_dir():
        print(f"no build directory at {build} -- nothing to do")
        return 0

    host = args.host
    if host is None:
        # A host-triple directory is identified by CONTENT, not by name shape:
        # `synthetic-target-specs` and `tmp-dry-run` are also dash-bearing.
        candidates = [
            p.name for p in build.iterdir()
            if p.is_dir() and not p.is_symlink()
            and any((p / s).is_dir() for s in ("stage2", "stage1", "stage0-sysroot"))
        ]
        if len(candidates) != 1:
            print(f"cannot auto-detect host triple (found {candidates}); pass --host")
            return 2
        host = candidates[0]
    host_root = build / host
    if not host_root.is_dir():
        print(f"{host_root} does not exist")
        return 2

    busy = build_in_progress(root)
    if busy and not args.force:
        print(f"REFUSING: {busy}.")
        print("A half-installed sysroot has no second copy of its artifacts, so the")
        print("hardlink invariant this script relies on does not hold yet.")
        print("Wait for the build to finish, or pass --force if you are certain.")
        return 1

    ok, detail = sysroot_is_complete(host_root)
    if not ok:
        print(f"REFUSING: {detail}.")
        print("This script only reclaims scaffolding around a COMPLETE sysroot.")
        return 1
    print(f"sysroot OK: {detail}")

    total = 0
    plan: list[tuple[Path, int]] = []
    for name in PURGE_TARGETS:
        path = host_root / name
        if not path.is_dir():
            print(f"  {name:16} absent")
            continue
        size = tree_size(path)
        plan.append((path, size))
        total += size
        print(f"  {name:16} {human(size):>10} reclaimable")

    if not plan:
        print("nothing to reclaim")
        return 0

    print(f"\ntotal reclaimable: {human(total)}")
    print("(hardlinked-into-sysroot files are excluded -- deleting them frees nothing)")

    if args.dry_run:
        print("\n--dry-run: nothing deleted")
        return 0

    for path, size in plan:
        print(f"removing {path.name} ({human(size)}) ...", flush=True)
        shutil.rmtree(path, ignore_errors=True)

    ok, detail = sysroot_is_complete(host_root)
    if not ok:
        print(f"\n*** POST-CHECK FAILED: {detail}")
        print("*** The sysroot is damaged. Rebuild with:")
        print("***   python3 scripts/recreate_bootstrap.py --require-seed --stage 2 --no-register")
        return 1
    print(f"\npost-check OK: {detail}")
    print(f"reclaimed {human(total)}. The next x.py build recompiles from scratch.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
