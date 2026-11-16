#!/usr/bin/env python3
"""The content identity of a sealed Trust toolchain: one digest over every file it ships.

Plan `docs/design/2026-09-29-incremental-deterministic-trust-results.md`, T13 (T13a) and
the seal-identity row of section 4.2. Before this, a seal's PROVENANCE named its build by
the sha256 of six files (the driver dylib, `trustc`, `ay`, `clean`, `ty`, `targo`), so
two seals that differed only in `targo-trust` (which prints the Summary and applies the
publication boundary), `trustd`, or a sysroot rlib whose MIR verification bundles shared
an identity. A verdict depends on all of them.

THE SET, decided from what a promoted toolchain contains (a seal is `cp -a` of a stage2,
its source links frozen, its escaping links pruned): every regular file, directory and
symlink under the seal, at any depth, EXCEPT the four records promotion writes about the
seal at its root (`PROVENANCE`, `PROVENANCE.build-status`, `SEED-MINT`, `STAGE0-LINEAGE`).
That covers, with no list to keep in step with bootstrap:

* every shipped executable: `bin/` (the Trust tools, their stock-name links, any staged
  trust-wp driver), `libexec/`, and `lib/rustlib/<target>/bin/` (the LLVM tools, the
  linker and its `gcc-ld/` wrappers);
* every dynamic library: `lib/` (`librustc_driver`, which links the verifier, ay and
  trust-mc; the std dylib; a shared LLVM), the codegen backends, the proc-macro dylibs;
* the sysroot crates of every target: `lib/rustlib/<target>/lib/` rlibs (std, core,
  alloc, whose bodies verification bundles), rmeta (the rustc-dev closure) and the
  `self-contained/` objects;
* the frozen source snapshot (`lib/rustlib/src`, `rustc-src`), the target-spec schema,
  the man pages and the debugger scripts. These change no verdict that is known today;
  hashing them costs little, and an identity that over-covers is only a cache miss
  (section 4.2, "Over-keying is sound"), where one that under-covers is a wrong reuse.

The rustc-private sysroot promotion seals BESIDE the toolchain (rustc_private consumers
such as trust-mc link it) is not under the seal; promotion records its identity by the
same rule as `private_sysroot_content_*` (`--prefix`).

WHAT AN ENTRY IS. A regular file contributes its path, its mode and its sha256; a
directory below the root its path and its mode (so an empty directory, which a sysroot
probe can see, is content); a symlink its path and its link text (never followed:
promotion has already pruned the links that escape). The MODE is every permission and
special bit except group and other WRITE: setuid, setgid and sticky, the owner's bits,
and group and other read and execute. Group and other write are left out because
promotion clears them (`chmod -R go-w`), so a stage2 and its seal agree; owners, times
and inode numbers are left out because they differ between two copies of the same bytes.
So a stock name laid as a hard link and the same bytes as a copy give the same identity,
and two builds whose files differ in who may read or run them do not. Any other file
type (a fifo, a socket, a device) is refused: nothing a toolchain ships is one.

THE DIGEST is sha256 over the entries in byte order of their '/'-separated relative
paths, each entry `kind NUL mode NUL value NUL path NUL`, where kind is `F`, `D` or `L`,
mode is four octal digits (`-` for a link), and value is the file's sha256 in hex, the
link text, or empty for a directory. No field can hold a NUL, so the encoding is
unambiguous. `--manifest` prints the same entries one per line (an empty value as `-`),
to answer "which file differs between these two seals". `--prefix NAME` names the
PROVENANCE lines `NAME_sha256` and so on, for another tree promotion seals (the
rustc-private sysroot beside the toolchain).
"""

# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import stat
import sys

SCOPE = "seal-content-v1"

# Written by scripts/promote-toolchain.sh ABOUT the seal, at its root. They describe the
# content; they are not content. The same names anywhere below the root are covered.
SEAL_RECORDS = frozenset(
    {"PROVENANCE", "PROVENANCE.build-status", "SEED-MINT", "STAGE0-LINEAGE"}
)

_CHUNK = 1 << 20

# Every permission and special bit but group and other write, which promotion clears.
MODE_MASK = 0o7755


class SealContentError(Exception):
    """The tree holds something a toolchain never ships, or could not be read."""


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(_CHUNK), b""):
            digest.update(block)
    return digest.hexdigest()


def entries(root: Path, *, excluded_root_records=SEAL_RECORDS, mode_mask=MODE_MASK) -> list[tuple[bytes, bytes, bytes, bytes]]:
    """Every covered entry as (path, kind, mode, value), sorted by path bytes."""
    # The name the caller reached the seal by (`trust-current`, a rustup link) is not
    # content; what lies under it is.
    try:
        root = root.resolve(strict=True)
    except (OSError, RuntimeError) as error:
        raise SealContentError(f"cannot resolve seal {root}: {error}") from error
    if not root.is_dir():
        raise SealContentError(f"seal is not a directory: {root}")
    # One hash per inode: a stock name hard-linked to its Trust tool is read once.
    by_inode: dict[tuple[int, int], str] = {}
    out: list[tuple[bytes, bytes, bytes, bytes]] = []
    pending = [Path()]
    while pending:
        relative_dir = pending.pop()
        directory = root / relative_dir
        try:
            names = sorted(os.listdir(directory))
        except OSError as error:
            raise SealContentError(f"cannot list {directory}: {error}") from error
        for name in names:
            relative = relative_dir / name
            if relative_dir == Path() and name in excluded_root_records:
                continue
            path = root / relative
            try:
                metadata = os.lstat(path)
            except OSError as error:
                raise SealContentError(f"cannot inspect {path}: {error}") from error
            encoded = os.fsencode(relative.as_posix())
            st_mode = metadata.st_mode
            mode = b"%04o" % (stat.S_IMODE(st_mode) & mode_mask)
            if stat.S_ISDIR(st_mode):
                out.append((encoded, b"D", mode, b""))
                pending.append(relative)
            elif stat.S_ISLNK(st_mode):
                out.append((encoded, b"L", b"-", os.fsencode(os.readlink(path))))
            elif stat.S_ISREG(st_mode):
                key = (metadata.st_dev, metadata.st_ino)
                sha = by_inode.get(key)
                if sha is None:
                    try:
                        sha = _file_sha256(path)
                    except OSError as error:
                        raise SealContentError(f"cannot read {path}: {error}") from error
                    by_inode[key] = sha
                out.append((encoded, b"F", mode, sha.encode("ascii")))
            else:
                raise SealContentError(
                    f"{path} is neither a regular file, a symlink nor a directory "
                    f"(mode {stat.filemode(st_mode)}); a toolchain ships none, so it has no identity"
                )
    out.sort(key=lambda entry: entry[0])
    return out


def identity(root: Path) -> tuple[str, int, int, int]:
    """(sha256 hex, regular files, symlinks, directories) of the seal at `root`."""
    digest = hashlib.sha256()
    counts = {b"F": 0, b"L": 0, b"D": 0}
    for path, kind, mode, value in entries(root):
        for field in (kind, mode, value, path):
            digest.update(field)
            digest.update(b"\0")
        counts[kind] += 1
    return digest.hexdigest(), counts[b"F"], counts[b"L"], counts[b"D"]


DEFAULT_PREFIX = "artifact_content"


def provenance_lines(root: Path, prefix: str = DEFAULT_PREFIX) -> list[str]:
    sha, files, links, directories = identity(root)
    return [
        f"{prefix}_sha256={sha}",
        f"{prefix}_files={files}",
        f"{prefix}_links={links}",
        f"{prefix}_dirs={directories}",
        f"{prefix}_scope={SCOPE}",
    ]


def main(argv: list[str]) -> int:
    usage = "usage: seal_content_identity.py [--manifest | --prefix NAME] SEAL_DIRECTORY"
    manifest = False
    prefix = DEFAULT_PREFIX
    if argv and argv[0] == "--manifest":
        manifest = True
        argv = argv[1:]
    elif len(argv) >= 2 and argv[0] == "--prefix":
        prefix = argv[1]
        argv = argv[2:]
        if not prefix.replace("_", "").isalnum() or not prefix.isascii():
            print(f"{usage}\n  NAME must be letters, digits and underscores", file=sys.stderr)
            return 2
    if len(argv) != 1:
        print(usage, file=sys.stderr)
        return 2
    root = Path(argv[0])
    try:
        if manifest:
            out = sys.stdout.buffer
            try:
                for path, kind, mode, value in entries(root):
                    out.write(b" ".join((kind, mode, value or b"-", path)) + b"\n")
                out.flush()
            except BrokenPipeError:
                # `| head` read what it wanted; that is not a failure to report.
                os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())
        else:
            print("\n".join(provenance_lines(root, prefix)))
    except (SealContentError, OSError) as error:
        print(f"seal_content_identity: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
