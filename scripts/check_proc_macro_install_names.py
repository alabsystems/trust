#!/usr/bin/env python3
"""Find -- and optionally repair -- proc-macro dylibs that alias each other in dyld.

WHY THIS EXISTS
---------------
A proc-macro dylib is ``dlopen``ed by absolute path and is never linked against,
so its Mach-O ``LC_ID_DYLIB`` install name has exactly one consumer: dyld's
already-loaded-image registry. The linker's default leaves that install name as
the build OUTPUT PATH, and bootstrap copies these dylibs into every stage sysroot
without rewriting it -- so each copy goes on claiming the original file's path.
Load such a copy in a process and ``dlopen`` of the original path returns the
COPY; ``dlsym`` of the current build's ``__rustc_proc_macro_decls_*`` then misses,
with an error that names neither file::

    error: .../libdisplaydoc-2ef9e771ac39abb5.dylib:
           dlsym(0x74d8a430, __rustc_proc_macro_decls_fd4ef7673192df2e__): symbol not found

Upstream mostly survives this: a rebuild at the same version exports the same
symbol, so the substitution is invisible. Trust's ``CFG_VERSION`` embeds the git
short sha and ``StableCrateId::new`` hashes the version, so every commit changes
the symbol and the aliasing becomes a hard failure.

rustc no longer produces such files -- proc-macro dylibs are given an
identity-keyed install name (``rustc-proc-macro/<version>/<file name>``, see
``rustc_codegen_ssa::back::linker``). This script exists for artifacts built
BEFORE that fix, which keep hijacking their claimed path until repaired: measured,
a fixed build sitting beside one legacy copy still fails.

REPAIRING `build/` ALONE IS NOT ENOUGH -- IT SILENTLY REVERTS
-------------------------------------------------------------
Bootstrap assembles `stage0-sysroot` by HARDLINKING from the stage0 compiler,
which lives OUTSIDE the repo (a snapshot directory, a sealed toolchain under
`~/toolchains/`, or an atpkg store path). Repairing only `build/` rewrites the
copies, `install_name_tool` writes a new inode rather than editing in place, and
the next `x.py` run re-links the ORIGINAL poisoned inode straight back in.

Measured 2026-09-13: a repair pass reported 937 of 937 fixed with no failures,
and a re-scan minutes later -- across one `x.py check` -- found eight of them
poisoned again, every one in `stage0-sysroot`, every one a hardlink to the
sibling `trust-stage0-snapshot` checkout beside this one.

So pass the stage0 source as well. Find it from any restored file::

    find / -inum "$(stat -f %i build/<host>/stage0-sysroot/lib/rustlib/<host>/lib/lib<crate>-<hash>.dylib)"

and hand this script both roots. Do NOT do that while a build is running: these
are the dylibs the running compiler has open.

THE INVARIANT IT CHECKS
-----------------------
Sharing an install name is only a bug when the images actually DIFFER. So:

  1. No install name may be carried by two dylibs with different declarations
     symbols.
  2. No dylib may claim, as its install name, the absolute path of an existing
     file whose declarations symbol differs from its own.

Identical copies sharing a name are fine and are left alone -- dyld substituting
one for the other is a no-op. On this tree that exempts the 108 files carrying an
``@rpath/...`` name, which come in groups of six byte-identical copies.

Full analysis: reports/2026-09-13-proc-macro-install-name-aliasing.md
"""

from __future__ import annotations

import argparse
import os
import platform
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

DECLS_RE = re.compile(r"__rustc_proc_macro_decls_([0-9a-f]+)__")


def run(*args: str) -> str:
    try:
        return subprocess.run(args, capture_output=True, text=True, timeout=60).stdout
    except (OSError, subprocess.SubprocessError):
        return ""


def decls_symbol(path: Path) -> str | None:
    """The `__rustc_proc_macro_decls_*` id this dylib exports, or None if it is
    not a proc-macro dylib at all."""
    m = DECLS_RE.search(run("nm", "-m", str(path)))
    return m.group(1) if m else None


def install_name(path: Path) -> str:
    lines = [l.strip() for l in run("otool", "-D", str(path)).splitlines() if l.strip()]
    # `otool -D` prints the file name, then the install name.
    return lines[-1] if len(lines) >= 2 else ""


def identity_name(path: Path, decls: str) -> str:
    return f"rustc-proc-macro/{decls}/{path.name}"


def collect(root: Path) -> list[tuple[Path, str, str]]:
    found = []
    for path in root.rglob("*.dylib"):
        if not path.is_file():
            continue
        decls = decls_symbol(path)
        if decls is None:
            continue
        found.append((path, install_name(path), decls))
    return found


def harmful(entries):
    """Return the entries that actually alias a DIFFERENT image."""
    by_name = defaultdict(set)
    for _, name, decls in entries:
        by_name[name].add(decls)
    contested = {n for n, d in by_name.items() if len(d) > 1}

    by_abspath = {str(p.resolve()): decls for p, _, decls in entries}

    bad = []
    for path, name, decls in entries:
        if name.startswith("rustc-proc-macro/"):
            continue
        reason = None
        if name in contested:
            reason = f"install name {name!r} is carried by images with different identities"
        else:
            owner = by_abspath.get(name)
            if owner is not None and owner != decls and str(path.resolve()) != name:
                reason = (
                    f"claims {name!r}, which is a different image "
                    f"(that file declares {owner}, this one {decls})"
                )
        if reason:
            bad.append((path, decls, reason))
    return bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument(
        "roots",
        nargs="*",
        default=[Path("build")],
        type=Path,
        help="directories to scan; pass the stage0 compiler source as well as build/",
    )
    ap.add_argument("--repair", action="store_true", help="rewrite aliasing install names in place")
    args = ap.parse_args()

    if platform.system() != "Darwin":
        print(f"install names are a Mach-O concept; nothing to check on {platform.system()}")
        return 0
    for root in args.roots:
        if not root.is_dir():
            print(f"error: no such directory: {root}", file=sys.stderr)
            return 1

    entries = [e for root in args.roots for e in collect(root)]
    bad = harmful(entries)
    print(f"proc-macro dylibs scanned: {len(entries)}")
    print(f"aliasing a different image: {len(bad)}")

    if not bad:
        return 0

    if not args.repair:
        for path, _, reason in bad[:40]:
            print(f"\n  {path}\n    {reason}")
        if len(bad) > 40:
            print(f"\n  ... and {len(bad) - 40} more")
        print(
            "\nEach of these hijacks dlopen() of the image it aliases, for the whole life\n"
            "of any process that loads it. Repair in place with:\n"
            f"\n    python3 {sys.argv[0]} --repair {' '.join(str(r) for r in args.roots)}\n"
            "\nor delete the stage directories holding them and let bootstrap rebuild."
        )
        return 1

    repaired = failed = 0
    for path, decls, _ in bad:
        new = identity_name(path, decls)
        ok = subprocess.run(
            ["install_name_tool", "-id", new, str(path)], capture_output=True, text=True
        ).returncode == 0
        # install_name_tool invalidates the signature; re-sign ad hoc.
        if ok:
            ok = subprocess.run(
                ["codesign", "-f", "-s", "-", str(path)], capture_output=True, text=True
            ).returncode == 0
        if ok:
            repaired += 1
        else:
            failed += 1
            print(f"REPAIR FAILED: {path}", file=sys.stderr)
    print(f"repaired: {repaired}    failed: {failed}")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
