#!/usr/bin/env python3
"""Stage 0.5 denominator `imports`: the import set of each std and rustc_driver dylib, per target.

Design of record: docs/design/2026-09-16-trust-core-architecture.md, §5.2 Stage 0.5 ("Import sets
per artifact and target"), exit E0.12 ("All published, each with its predicate"). The numbers
feed D-10's denominators (§3.10), E2.6.6 (an ExtSpec or named refusal for 100% of std's imports
on aarch64/x86_64-apple-darwin and x86_64/aarch64-unknown-linux-gnu), I-FFI-SPECIFIED, and the
D-18 case against libc++ in the authority image. Table: docs/trust-core/denominators/imports.toml.

Every number here is measured from the bytes of a pinned artifact (its sha256 is the pin), never
copied from the design. For each input the script copies the file into a private temporary
directory while hashing it (a build can delete or rewrite build/ under a reader), refuses a copy
whose digest is not the pinned one, and parses the copy with its own Mach-O / ELF reader (stdlib
only; no nm/otool/dyld_info is consulted, so the result does not depend on the host's tools).

PREDICATES (the exact text is rendered into the table; `PREDICATE_*` below):
  Mach-O   the distinct names of LC_SYMTAB entries that are not stabs, are external, and are
           undefined (N_UNDF or N_PBUD) with n_value == 0 (commons excluded). Nothing else is
           excluded. Two fail-closed cross-checks re-derive the same set from other structures
           of the same image: LC_DYSYMTAB's undefined range, and the names dyld binds (the bind
           and lazy-bind opcode streams of LC_DYLD_INFO[_ONLY], or the import table of
           LC_DYLD_CHAINED_FIXUPS), with the same library ordinal per name.
  ELF      the distinct names of .dynsym entries (index > 0) with st_shndx == SHN_UNDEF,
           binding GLOBAL or WEAK and a non-empty name; the required version is recorded.
  classes  cxx_mangled: the C-level name (a Mach-O name less its one leading '_') starts with
           '_Z' and is not a Rust legacy symbol; rust_mangled: v0 ('_R' + [0-9A-Z]) or legacy
           ('_ZN' ... '17h' + 16 hex + 'E'); c: the rest.
  bound_to the Mach-O two-level-namespace library ordinal of each import, resolved to the
           LC_LOAD_DYLIB-family command it names.

MODES
  (default)      measure every pinned input, print the rows, exit 1 on any failure, or 3 when
                 the failure is only that pinned inputs are not on this host (no candidate file has
                 the pinned sha256): the table cannot be re-measured here, which is not drift and
                 never a pass
  --check        also regenerate the table and compare it byte for byte with the committed one. It
                 first runs --check-dispositions on the committed table, which needs no pinned input,
                 so a disposition violation fails (exit 1) even on a host that cannot re-measure
  --write        regenerate the table
  --check-dispositions
                 validate the committed table's disposition column (I-FFI-SPECIFIED's numerator) against
                 its own committed [[import_set]] names and DISPOSITIONS below, without re-measuring:
                 every name of each canonical std Mach-O set has a row and every row names an import,
                 each row's key and fields obey its disposition, the counts are the rows' tallies, and
                 the column is byte for byte its rendering. Exit 0 or 1
  --write-dispositions
                 re-render only the disposition column from the committed [[import_set]] names (the
                 rest of the table is untouched), then validate it as --check-dispositions does
  --artifact P --target T [--names]
                 measure one unpinned file (for example a Linux libstd-*.so once one exists)
  --rev REV      the superproject revision whose design the [[design_claim]] rows read (default HEAD);
                 scripts/trust_core/denominators.py passes the record's measured_at_commit
  --record F     the table to write or check (default docs/trust-core/denominators/imports.toml)
Inputs are found under --build-dir (default: <superproject checkout>/build, the parent of the git
common dir) and --atpkg-store (default: $ATPKG_BIN/../store, else ~/Library/Application
Support/aterm/pkg/store); --artifact-dir DIR is searched by digest for a pinned input that has
left its path (keep copies there: build/ is rewritten by every build).

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import mmap
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import zlib
from pathlib import Path

KEY = "imports"
SCHEMA = "trust.core.denominator.v1"
CONSUMERS = (
    "D-10 (§3.10): the denominators of the OS and foreign-code boundary (the design's std 195, rustc_driver 491 "
    "and '93 libc++'; see [[design_claim]])",
    "E2.6.6: an ExtSpec or a named refusal for 100% of std's imports on aarch64/x86_64-apple-darwin and "
    "x86_64/aarch64-unknown-linux-gnu",
    "I-FFI-SPECIFIED",
    "D-18: the case against libc++ in the proof authority's image (the design's '93 libc++ imports'; see "
    "[[design_claim]] D18-libcxx)",
    "E1.10.2 / E5.1.1: trustc-core's import set must be a subset of std's",
)
MEASURED_AT = re.compile(r'^measured_at_commit = "[0-9a-f]{40}"$', re.M)
SCRIPT = Path(__file__).resolve()
REPO = SCRIPT.parents[3]
SCRIPT_REL = "scripts/trust_core/denominators/imports.py"
TABLE_REL = "docs/trust-core/denominators/imports.toml"
DESIGN_REL = "docs/design/2026-09-16-trust-core-architecture.md"


class Refusal(Exception):
    """A fail-closed stop: a malformed image, a digest that is not the pin, a cross-check that disagrees."""


# --------------------------------------------------------------------------------------------
# Predicates, verbatim as published.
# --------------------------------------------------------------------------------------------

PREDICATE_MACHO = (
    "Mach-O import set: take the image of the target's architecture (the thin file, or the fat slice whose "
    "cputype is the target's). Its imports are the DISTINCT NAMES of the LC_SYMTAB nlist entries with "
    "(n_type & N_STAB) == 0, (n_type & N_EXT) != 0, (n_type & N_TYPE) in {N_UNDF, N_PBUD}, and n_value == 0 "
    "(an N_UNDF entry with n_value != 0 is a common symbol and is excluded). Nothing else is excluded: "
    "dyld_stub_binder, weak references (N_WEAK_REF) and flat/dynamic-lookup ordinals all count. The value is "
    "the number of those names. Fail-closed cross-checks (a disagreement refuses the measurement): the same "
    "set is LC_DYSYMTAB's undefined range [iundefsym, iundefsym+nundefsym); and the same set, with the same "
    "library ordinal per name, is what dyld binds: the bind and lazy-bind opcode streams of "
    "LC_DYLD_INFO[_ONLY] (the weak-bind stream lists coalesced definitions, not imports) or the import table "
    "of LC_DYLD_CHAINED_FIXUPS."
)
PREDICATE_ELF = (
    "ELF import set: the DISTINCT NAMES of the .dynsym (SHT_DYNSYM) entries with index > 0, "
    "st_shndx == SHN_UNDEF, binding STB_GLOBAL or STB_WEAK, and a non-empty st_name. The required version "
    "(.gnu.version indexing .gnu.version_r) is recorded per name; a name is counted once whatever its version. "
    "The value is the number of those names."
)
PREDICATE_CXX = (
    "Of the import set, the names whose C-level spelling (a Mach-O name less its one leading '_'; an ELF name "
    "as is) starts with '_Z' (Itanium C++ ABI mangling) and is not a Rust legacy symbol "
    "('_ZN' ... '17h' followed by 16 hex digits and 'E')."
)
PREDICATE_RUST = (
    "Of the import set, the names whose C-level spelling is Rust-mangled: v0 ('_R' followed by [0-9A-Z]) or "
    "legacy ('_ZN' ... '17h' followed by 16 hex digits and 'E')."
)
PREDICATE_C = "Of the import set, the names that are neither cxx_mangled nor rust_mangled."
PREDICATE_BOUND = (
    "Of the Mach-O import set, the names whose two-level-namespace library ordinal "
    "(GET_LIBRARY_ORDINAL(n_desc) = (n_desc >> 8) & 0xff, 1-based over the LC_LOAD_DYLIB, LC_LOAD_WEAK_DYLIB, "
    "LC_REEXPORT_DYLIB, LC_LAZY_LOAD_DYLIB and LC_LOAD_UPWARD_DYLIB commands in order) names the dylib with "
    "install name {path}. A linked dylib with no import bound to it is a row with value 0."
)
PREDICATE_XTARGET = (
    "Names in the Mach-O import set of the {a} input and not in that of the {b} input; both inputs come "
    "from one build ({commit}), so the difference is the target's, not a commit's."
)


# --------------------------------------------------------------------------------------------
# Pinned inputs. `sha256` is the pin; every other measured field is recomputed from the bytes.
# `source` is a hand-written provenance claim; `source_commit` must occur in the artifact's own
# version strings or the run refuses, so the claim cannot drift from the bytes.
# --------------------------------------------------------------------------------------------

INPUTS = [
    {
        "id": "std.aarch64-apple-darwin@stage2-248a9f1dd",
        "artifact": "std", "target": "aarch64-apple-darwin", "canonical": True,
        "root": "build", "path": "aarch64-apple-darwin/stage2/lib/libstd-65d90f8a341318da.dylib",
        "sha256": "525cbcf86e5806041c6f9a21c1062f26c3d801d927515f4ebcc93f789f0a2d9e", "size": 1765312,
        "source_commit": "248a9f1dd",
        "source": "The stage-2 std dylib of the 2026-09-14 build (the build the design's D-10 denominators name), "
                  "compiled by that build's stage-1 compiler. Also hard-linked as "
                  "stage2/lib/rustlib/aarch64-apple-darwin/lib/.",
    },
    {
        "id": "std.aarch64-apple-darwin@stage1-9a0656816",
        "artifact": "std", "target": "aarch64-apple-darwin", "canonical": False,
        "root": "build", "path": "aarch64-apple-darwin/stage1/lib/rustlib/aarch64-apple-darwin/lib/libstd-f5bec4abf41aa11a.dylib",
        "sha256": "6d494fdbf9ba861cc6f2983c1186932b5d58f2790ad05718a1eedc0c68b6f0fc", "size": 1765104,
        "source_commit": "9a0656816",
        "source": "The target std of the current stage-1 sysroot (2026-09-25 build), compiled by the stage-1 "
                  "compiler; the same file as stage1-std/aarch64-apple-darwin/dist/deps/.",
    },
    {
        "id": "std.aarch64-apple-darwin@stage0-8b50cbcc5",
        "artifact": "std", "target": "aarch64-apple-darwin", "canonical": False,
        "root": "build", "path": "aarch64-apple-darwin/stage0-sysroot/lib/rustlib/aarch64-apple-darwin/lib/libstd-65d90f8a341318da.dylib",
        "sha256": "54f812eebec68dfb150ea2f99c6835e73aa4a0082ea1a0b5edaa27af4cc35e27", "size": 1765424,
        "source_commit": "8b50cbcc5",
        "source": "The stage-0 compiler's own std: bootstrap.toml's build.rustc is a local snapshot of the "
                  "8b50cbcc5 build's stage 2, and this is that snapshot's aarch64 std, hard-linked into "
                  "stage0-sysroot and into the stage-1 host lib dir (stage1/lib/).",
    },
    {
        "id": "std.aarch64-apple-darwin@installed-321aaeda7",
        "artifact": "std", "target": "aarch64-apple-darwin", "canonical": False,
        "root": "atpkg-store", "path": "trust/9192/lib/rustlib/aarch64-apple-darwin/lib/libstd-8d1f608658776950.dylib",
        "sha256": "d294c01e4fa6d7c5676728431cd08b5cf7ca0eed3ea1d872e86d410119d064f5", "size": 1238768,
        "source_commit": "321aaeda7",
        "source": "The installed trust toolchain (atpkg store generation 9192, `trustc -vV` commit-hash 321aaeda7, "
                  "`trustc --print sysroot` = <atpkg-store>/trust/9192); lib/libstd-8d1f608658776950.dylib is "
                  "byte-identical.",
    },
    {
        "id": "std.x86_64-apple-darwin@stage0-8b50cbcc5",
        "artifact": "std", "target": "x86_64-apple-darwin", "canonical": True,
        "root": "build", "path": "aarch64-apple-darwin/stage0-sysroot/lib/rustlib/x86_64-apple-darwin/lib/libstd-6d213322c6e21d72.dylib",
        "sha256": "d268d76ecc8d324b83df15668ff5df86ae132c136987659127f1afbdaee87d62", "size": 1644088,
        "source_commit": "8b50cbcc5",
        "source": "The only x86_64-apple-darwin std dylib on the measuring host: the stage-0 snapshot's (the "
                  "8b50cbcc5 build, whose build.target lists both Apple architectures). The current stage-1 "
                  "build produced only check metadata for x86_64 (stage1-std/x86_64-apple-darwin has no dylib).",
    },
    {
        "id": "rustc_driver.aarch64-apple-darwin@stage2-248a9f1dd",
        "artifact": "rustc_driver", "target": "aarch64-apple-darwin", "canonical": True,
        "root": "build", "path": "aarch64-apple-darwin/stage2/lib/librustc_driver-0043129bfc5486d8.dylib",
        "sha256": "db9a0ff384ef7f6930c5e9c6721f6113950a2a0854ace56777b43c5a5aff042b", "size": 699159912,
        "source_commit": "248a9f1dd",
        "source": "The stage-2 librustc_driver of the 2026-09-14 build, compiled by that build's stage-1 compiler.",
    },
    {
        "id": "rustc_driver.aarch64-apple-darwin@stage1-9a0656816",
        "artifact": "rustc_driver", "target": "aarch64-apple-darwin", "canonical": False,
        "root": "build", "path": "aarch64-apple-darwin/stage1/lib/librustc_driver-833473aeaeba2307.dylib",
        "sha256": "58de5ff537234e6013cead969aaff3ef3be5226d5008982608db91f204be850e", "size": 756601720,
        "source_commit": "9a0656816",
        "source": "The current stage-1 librustc_driver (2026-09-25 build of 9a0656816), compiled by the stage-0 "
                  "snapshot compiler (8b50cbcc5).",
    },
    {
        "id": "rustc_driver.aarch64-apple-darwin@installed-321aaeda7",
        "artifact": "rustc_driver", "target": "aarch64-apple-darwin", "canonical": False,
        "root": "atpkg-store", "path": "trust/9192/lib/librustc_driver-6fb93c367b721e46.dylib",
        "sha256": "13997326c927b73e5768c42844564d18d7828ab83be55112a8ca62ebc98f446f", "size": 380018976,
        "source_commit": "321aaeda7",
        "source": "The installed trust toolchain's librustc_driver (atpkg store generation 9192, commit 321aaeda7); "
                  "lib/rustlib/aarch64-apple-darwin/lib/ holds a byte-identical copy.",
    },
]

# The cross-target comparison: two inputs from one build.
XTARGET = ("std.x86_64-apple-darwin@stage0-8b50cbcc5", "std.aarch64-apple-darwin@stage0-8b50cbcc5", "8b50cbcc5")

LINUX_SEARCH = (
    "Searched on 2026-09-26 on the measuring host (Apple silicon, macOS): `find -xdev` over <home> /opt, "
    "/usr/local, /Applications/Xcode.app and /Library/Developer (directories the user cannot read excepted) found "
    "no libstd-*.so, no librustc_driver-*.so and no rustlib/<linux target> directory; the rustup toolchains "
    "(1.97.1, nightly-2026-04-20, trust) carry only aarch64-apple-darwin std; build/ has no Linux target "
    "directory. Nothing on the host can produce one: no glibc sysroot (no libc.so.6 or libgcc_s.so.1 under "
    "<home> /opt or /usr/local), no ELF linker (build/<host>/llvm/bin has no lld, the stage-1 sysroot "
    "no rust-lld, and there is no ld.lld, x86_64-linux-gnu-gcc, aarch64-linux-gnu-gcc or zig on PATH), and no "
    "container or VM runtime (docker, podman, lima, colima, orb, UTM, Parallels, VMware, VirtualBox)."
)

BLOCKED = [
    {
        "name": "imports.rustc_driver.x86_64-apple-darwin",
        "artifact": "rustc_driver", "target": "x86_64-apple-darwin", "predicate": "macho",
        "reason": (
            "No x86_64-apple-darwin librustc_driver exists on the measuring host. bootstrap.toml lists "
            "x86_64-apple-darwin under build.target only, never build.host, so no build has produced an x86_64 "
            "compiler: build/x86_64-apple-darwin/ holds only native/rust-test-helpers, and the installed trust "
            "toolchain (store generation 9192) ships the aarch64-apple-darwin host only."
        ),
        "unblock": (
            "A Trust build with host x86_64-apple-darwin (bootstrap.toml build.host = [\"aarch64-apple-darwin\", "
            "\"x86_64-apple-darwin\"], then x.py build --stage 2 --host x86_64-apple-darwin compiler/rustc, which "
            "also builds LLVM for that host; Apple clang and the macOS SDK target x86_64, so no further cross "
            "toolchain is expected, though no such build has been tried here), run by the build owner "
            "under native Targo build-tree ownership. Pin the resulting "
            "build/x86_64-apple-darwin/stage2/lib/librustc_driver-*.dylib (a Mach-O x86_64 MH_DYLIB) as an input "
            "here; the Mach-O predicate applies unchanged."
        ),
    },
    {
        "name": "imports.std.x86_64-unknown-linux-gnu",
        "artifact": "std", "target": "x86_64-unknown-linux-gnu", "predicate": "elf",
        "reason": "No x86_64-unknown-linux-gnu libstd-*.so (ELF) of Trust's std exists on the measuring host. " + LINUX_SEARCH,
        "unblock": (
            "Either (a) an x86_64 Linux host (glibc) of the D0.11 roster runs a Trust build of library/std "
            "(x.py build --stage 2 library/std) and hands over build/x86_64-unknown-linux-gnu/stage2/lib/"
            "rustlib/x86_64-unknown-linux-gnu/lib/libstd-*.so; or (b) this host cross-builds it: "
            "x86_64-unknown-linux-gnu added to build.target, plus [target.x86_64-unknown-linux-gnu] cc, ar and "
            "linker for a glibc sysroot that provides crti.o/crtn.o, gcc's crtbeginS.o/crtendS.o, libc.so.6, libm and "
            "libgcc_s.so.1 (std links -lgcc_s) and an ELF linker (ld.lld or x86_64-linux-gnu-ld), none of which is installed. Then measure "
            "it with --artifact <libstd.so> --target x86_64-unknown-linux-gnu and pin it here. An upstream "
            "rust-std component is not a substitute: it measures rust-lang's std, not Trust's."
        ),
    },
    {
        "name": "imports.std.aarch64-unknown-linux-gnu",
        "artifact": "std", "target": "aarch64-unknown-linux-gnu", "predicate": "elf",
        "reason": "No aarch64-unknown-linux-gnu libstd-*.so (ELF) of Trust's std exists on the measuring host. " + LINUX_SEARCH,
        "unblock": (
            "Either (a) an AArch64 Linux host (glibc) of the D0.11 roster runs x.py build --stage 2 library/std; "
            "or (b) this host cross-builds it with aarch64-unknown-linux-gnu in build.target and a "
            "[target.aarch64-unknown-linux-gnu] cc/ar/linker over an aarch64 glibc sysroot (crti.o/crtn.o, "
            "crtbeginS.o/crtendS.o, libc.so.6, libm, libgcc_s.so.1) plus an ELF linker, none of which is installed. Then measure with "
            "--artifact <libstd.so> --target aarch64-unknown-linux-gnu and pin it here."
        ),
    },
    {
        "name": "imports.rustc_driver.x86_64-unknown-linux-gnu",
        "artifact": "rustc_driver", "target": "x86_64-unknown-linux-gnu", "predicate": "elf",
        "reason": "No x86_64-unknown-linux-gnu librustc_driver-*.so exists on the measuring host. " + LINUX_SEARCH,
        "unblock": (
            "An x86_64 Linux host (glibc) of the D0.11 roster runs a Trust build of compiler/rustc (x.py build "
            "--stage 2 compiler/rustc) and hands over build/x86_64-unknown-linux-gnu/stage2/lib/"
            "librustc_driver-*.so. Cross-building rustc for Linux from this host would further need LLVM built "
            "for the Linux target and a C++ cross toolchain with libstdc++ in the glibc sysroot; none is installed."
        ),
    },
    {
        "name": "imports.rustc_driver.aarch64-unknown-linux-gnu",
        "artifact": "rustc_driver", "target": "aarch64-unknown-linux-gnu", "predicate": "elf",
        "reason": "No aarch64-unknown-linux-gnu librustc_driver-*.so exists on the measuring host. " + LINUX_SEARCH,
        "unblock": (
            "An AArch64 Linux host (glibc) of the D0.11 roster runs x.py build --stage 2 compiler/rustc and hands "
            "over build/aarch64-unknown-linux-gnu/stage2/lib/librustc_driver-*.so; a cross build from this host "
            "would further need LLVM and a C++ cross toolchain with libstdc++ for aarch64 Linux, none installed."
        ),
    },
]

# Design sentences that state a number this key owns. Each quote must occur exactly once in the design
# (read from git at --rev, default HEAD); `expect` is what the measurement is expected to show, so an explanation can never
# silently outlive the numbers it explains: a changed outcome refuses until the text is revisited. A compare
# carries a fourth element when its row counts something other than what the design's words name
# ("other predicate"): such a row's equality is a reproduction only under that predicate, never as worded.
OTHER_PREDICATE = "other predicate"
DESIGN_CLAIMS = [
    {
        "id": "D10-std",
        "quote": "* the stage-2 `libstd` dylib imports **195** undefined symbols, none C++-mangled;",
        "compare": [("imports.std.aarch64-apple-darwin", 195, True),
                    ("imports.std.aarch64-apple-darwin.cxx_mangled", 0, True)],
        "explanation": "Reproduced on the stage-2 std of the 2026-09-14 build. Every aarch64-apple-darwin std "
                       "input (commits 8b50cbcc5, 248a9f1dd, 321aaeda7, 9a0656816) has the same 195-name set.",
    },
    {
        "id": "D10-driver",
        "quote": "* `librustc_driver` imports **491**, of which **93** are libc++ [M†].",
        "compare": [("imports.rustc_driver.aarch64-apple-darwin", 491, True),
                    ("imports.rustc_driver.aarch64-apple-darwin.cxx_mangled", 93, True, OTHER_PREDICATE),
                    ("imports.rustc_driver.aarch64-apple-darwin.bound_to.libc++", 93, False)],
        "explanation": "491 reproduces on the 2026-09-14 stage-2 librustc_driver; the count is per build (492 at "
                       "9a0656816, 487 at 321aaeda7). '93 are libc++' is reproduced only under a different "
                       "predicate: 93 is the number of C++-mangled imports, all of which bind to libc++. As the "
                       "sentence reads, counted by binding library, it is not reproduced: 96 imports bind to "
                       "/usr/lib/libc++.1.dylib, the other 3 being unmangled C++ ABI entry points "
                       "(___cxa_guard_acquire, ___cxa_guard_release, ___cxa_pure_virtual). The design's 93 is "
                       "the mangled count; the libc++ import count is 96.",
    },
    {
        "id": "S05-list",
        "quote": "* Import sets per artifact and target: std 195 and `rustc_driver` 491 on",
        "compare": [("imports.std.aarch64-apple-darwin", 195, True),
                    ("imports.rustc_driver.aarch64-apple-darwin", 491, True)],
        "explanation": "Both reproduce on the 2026-09-14 stage-2 artifacts. The same item's 'Linux and x86 to be "
                       "measured': x86_64-apple-darwin std is measured (195 names, a different set); the "
                       "x86_64-apple-darwin rustc_driver and all four Linux combinations are blocked rows.",
    },
    {
        "id": "D18-libcxx",
        "quote": "* LLVM and 93 libc++ imports [M†].",
        "compare": [("imports.rustc_driver.aarch64-apple-darwin.cxx_mangled", 93, True, OTHER_PREDICATE),
                    ("imports.rustc_driver.aarch64-apple-darwin.bound_to.libc++", 93, False)],
        "explanation": "As D10-driver: reproduced only as the count of C++-mangled imports (93); as worded, "
                       "96 imports bind to libc++, so not reproduced.",
    },
    {
        "id": "D10-build",
        "quote": "**Denominators** (aarch64-apple-darwin, measured on the 2026-09-14 stage-2 build):",
        "compare": [],
        "explanation": "The canonical aarch64-apple-darwin inputs are that build's stage-2 dylibs: their embedded "
                       "compiler version is 'rustc 1.99.0-dev (248a9f1dd 2026-09-14)'.",
    },
]

# Dispositions: the NUMERATOR of E2.6.6 / I-FFI-SPECIFIED, which the import sets above are only the
# denominator of. Every name of every canonical std Mach-O import set gets one row per OS release it is
# disposed for, keyed by (exact Mach-O spelling, target, OS release): `_close` and `_close$NOCANCEL` are
# different symbols, and a clause conformance-tested on one macOS release says nothing about another.
#   specified    an ExtSpec clause exists for exactly this key. `os_release` must name one release (never
#                ANY_RELEASE) and `spec` the clause, as `<repo path>#<clause>`; the path must exist.
#   refused      the import is refused by name. `refusal` is the refusal's name and `reason` says why.
#   unspecified  neither. It is the default, stated with os_release ANY_RELEASE, and it is never listed
#                below: a name with no entry here is unspecified on every release.
# DISPOSITIONS lists the specified and refused rows, as dicts with the keys symbol, target, os_release,
# disposition and spec (specified) or refusal and reason (refused). It is empty: no ExtSpec or
# PlatformSpec exists anywhere in the tree, and no import is refused by name, so the numerator is 0 of
# 195 on each target (docs/design/2026-09-29-descriptor-protocols-as-compiler-errors.md; design only).
# Add a row only in the commit that lands the clause or the refusal it names.
DISPOSITION_VOCABULARY = ("specified", "refused", "unspecified")
ANY_RELEASE = "*"
DISPOSITIONS: list[dict] = []
PREDICATE_DISPOSITION = (
    "Per name of the input's Mach-O import set, one row per OS release it is disposed for, keyed by "
    "(symbol: the exact Mach-O spelling, target, os_release). disposition = specified: an ExtSpec clause "
    "(`spec`) exists for exactly that key and os_release names one release; refused: the import is refused by "
    "name (`refusal`, `reason`); unspecified: neither, on every release (os_release = \"*\"). numerator = the "
    "names with at least one specified or refused row; imports = the size of the set. The rows are joined to "
    "the committed [[import_set]] both ways: a name with no row, or a row naming no import, refuses."
)
DISPOSITION_BEGIN = "# Dispositions (I-FFI-SPECIFIED's numerator)"


TARGETS = {
    "aarch64-apple-darwin": ("macho", 0x0100000C),
    "x86_64-apple-darwin": ("macho", 0x01000007),
    "x86_64-unknown-linux-gnu": ("elf", 62),
    "aarch64-unknown-linux-gnu": ("elf", 183),
}
MACHO_CPU = {0x0100000C: "arm64", 0x01000007: "x86_64", 0x0200000C: "arm64_32", 7: "i386", 12: "arm"}


# --------------------------------------------------------------------------------------------
# Name classes.
# --------------------------------------------------------------------------------------------

RUST_LEGACY = re.compile(r"^_ZN.*17h[0-9a-f]{16}E$")
RUST_V0 = re.compile(r"^_R[0-9A-Z]")


def c_level(name: str, macho: bool) -> str:
    return name[1:] if macho and name.startswith("_") else name


def name_class(name: str, macho: bool) -> str:
    c = c_level(name, macho)
    if RUST_V0.match(c) or RUST_LEGACY.match(c):
        return "rust_mangled"
    if c.startswith("_Z"):
        return "cxx_mangled"
    return "c"


def short_library(path: str) -> str:
    """nm -m's spelling of a dylib: the framework name, else the file name up to its first dot."""
    m = re.search(r"/([^/]+)\.framework/", path)
    if m:
        return m.group(1)
    base = path.rsplit("/", 1)[-1]
    return base.split(".", 1)[0] if base else path


# --------------------------------------------------------------------------------------------
# Mach-O reader.
# --------------------------------------------------------------------------------------------

LC_REQ_DYLD = 0x80000000
LC_SEGMENT, LC_SYMTAB, LC_DYSYMTAB, LC_LOAD_DYLIB, LC_ID_DYLIB = 0x1, 0x2, 0xB, 0xC, 0xD
LC_SEGMENT_64, LC_LAZY_LOAD_DYLIB = 0x19, 0x20
LC_LOAD_WEAK_DYLIB, LC_REEXPORT_DYLIB, LC_LOAD_UPWARD_DYLIB = 0x18 | LC_REQ_DYLD, 0x1F | LC_REQ_DYLD, 0x23 | LC_REQ_DYLD
LC_DYLD_INFO, LC_DYLD_INFO_ONLY = 0x22, 0x22 | LC_REQ_DYLD
LC_DYLD_CHAINED_FIXUPS = 0x34 | LC_REQ_DYLD
LC_VERSION_MIN_MACOSX, LC_BUILD_VERSION = 0x24, 0x32
DYLIB_COMMANDS = {LC_LOAD_DYLIB: "LC_LOAD_DYLIB", LC_LOAD_WEAK_DYLIB: "LC_LOAD_WEAK_DYLIB",
                  LC_REEXPORT_DYLIB: "LC_REEXPORT_DYLIB", LC_LAZY_LOAD_DYLIB: "LC_LAZY_LOAD_DYLIB",
                  LC_LOAD_UPWARD_DYLIB: "LC_LOAD_UPWARD_DYLIB"}
N_STAB, N_PEXT, N_TYPE, N_EXT = 0xE0, 0x10, 0x0E, 0x01
N_UNDF, N_PBUD = 0x0, 0xC
N_WEAK_REF = 0x40
MH_TWOLEVEL = 0x80
MH_FILETYPES = {1: "MH_OBJECT", 2: "MH_EXECUTE", 6: "MH_DYLIB", 8: "MH_BUNDLE"}
SPECIAL_ORDINALS = {0: "SELF_LIBRARY_ORDINAL", 0xFE: "DYNAMIC_LOOKUP_ORDINAL", 0xFF: "EXECUTABLE_ORDINAL"}


def cstring(buf, off: int, end: int | None = None) -> str:
    stop = buf.find(b"\0", off, len(buf) if end is None else end)
    if stop < 0:
        raise Refusal(f"unterminated string at file offset {off}")
    return bytes(buf[off:stop]).decode("utf-8")


def uleb(buf, off: int) -> tuple[int, int]:
    value = shift = 0
    while True:
        if off >= len(buf):
            raise Refusal("truncated ULEB128")
        byte = buf[off]
        off += 1
        value |= (byte & 0x7F) << shift
        shift += 7
        if not byte & 0x80:
            return value, off


def sleb(buf, off: int) -> tuple[int, int]:
    value = shift = 0
    while True:
        if off >= len(buf):
            raise Refusal("truncated SLEB128")
        byte = buf[off]
        off += 1
        value |= (byte & 0x7F) << shift
        shift += 7
        if not byte & 0x80:
            if byte & 0x40:
                value -= 1 << shift
            return value, off


def version_text(v: int) -> str:
    return f"{v >> 16}.{(v >> 8) & 0xFF}.{v & 0xFF}"


def macho_slice(buf, cputype: int) -> int:
    """File offset of the image for `cputype`: 0 for a thin file of that type, the slice offset in a fat file."""
    magic_be = struct.unpack_from(">I", buf, 0)[0]
    if magic_be in (0xCAFEBABE, 0xCAFEBABF):
        wide = magic_be == 0xCAFEBABF
        count = struct.unpack_from(">I", buf, 4)[0]
        entry = 32 if wide else 20
        found = []
        for i in range(count):
            off = 8 + i * entry
            if wide:
                ct, _sub, offset, _size, _align, _res = struct.unpack_from(">iiQQII", buf, off)
            else:
                ct, _sub, offset, _size, _align = struct.unpack_from(">iiIII", buf, off)
            if ct & 0xFFFFFFFF == cputype:
                found.append(offset)
        if len(found) != 1:
            raise Refusal(f"fat file has {len(found)} slices of cputype {cputype:#x}")
        return found[0]
    return 0


def read_macho(buf, cputype: int) -> dict:
    base = macho_slice(buf, cputype)
    magic_le = struct.unpack_from("<I", buf, base)[0]
    if magic_le in (0xFEEDFACF, 0xFEEDFACE):
        e = "<"
    elif magic_le in (0xCFFAEDFE, 0xCEFAEDFE):
        e = ">"
    else:
        raise Refusal(f"not a Mach-O image (magic {magic_le:#x})")
    wide = struct.unpack_from(e + "I", buf, base)[0] == 0xFEEDFACF
    ct, _sub, filetype, ncmds, sizeofcmds, flags = struct.unpack_from(e + "iiIIII", buf, base + 4)
    if ct & 0xFFFFFFFF != cputype:
        raise Refusal(f"image cputype {ct & 0xFFFFFFFF:#x} is not the target's {cputype:#x}")
    header = 32 if wide else 28
    info: dict = {"format": "Mach-O", "arch": MACHO_CPU.get(cputype, hex(cputype)),
                  "filetype": MH_FILETYPES.get(filetype, str(filetype)), "twolevel": bool(flags & MH_TWOLEVEL),
                  "dylibs": [], "install_name": None, "min_os": None, "sdk": None, "fixups": "none",
                  "rustc_section": None}
    symtab = dysymtab = dyld_info = chained = None
    off = base + header
    end = off + sizeofcmds
    for _ in range(ncmds):
        cmd, cmdsize = struct.unpack_from(e + "II", buf, off)
        if cmdsize < 8 or off + cmdsize > end:
            raise Refusal(f"load command {cmd:#x} has size {cmdsize} outside the header")
        if cmd == LC_SYMTAB:
            symtab = struct.unpack_from(e + "IIII", buf, off + 8)
        elif cmd == LC_DYSYMTAB:
            dysymtab = struct.unpack_from(e + "18I", buf, off + 8)
        elif cmd in DYLIB_COMMANDS or cmd == LC_ID_DYLIB:
            name_off = struct.unpack_from(e + "I", buf, off + 8)[0]
            name = cstring(buf, off + name_off, off + cmdsize)
            if cmd == LC_ID_DYLIB:
                info["install_name"] = name
            else:
                info["dylibs"].append({"command": DYLIB_COMMANDS[cmd], "path": name})
        elif cmd in (LC_DYLD_INFO, LC_DYLD_INFO_ONLY):
            dyld_info = struct.unpack_from(e + "10I", buf, off + 8)
            info["fixups"] = "LC_DYLD_INFO_ONLY" if cmd == LC_DYLD_INFO_ONLY else "LC_DYLD_INFO"
        elif cmd == LC_DYLD_CHAINED_FIXUPS:
            chained = struct.unpack_from(e + "II", buf, off + 8)
            info["fixups"] = "LC_DYLD_CHAINED_FIXUPS"
        elif cmd == LC_BUILD_VERSION:
            _platform, minos, sdk = struct.unpack_from(e + "III", buf, off + 8)
            info["min_os"], info["sdk"] = version_text(minos), version_text(sdk)
        elif cmd == LC_VERSION_MIN_MACOSX:
            minos, sdk = struct.unpack_from(e + "II", buf, off + 8)
            info["min_os"], info["sdk"] = version_text(minos), version_text(sdk)
        elif cmd in (LC_SEGMENT_64, LC_SEGMENT):
            seg64 = cmd == LC_SEGMENT_64
            nsects = struct.unpack_from(e + "I", buf, off + (64 if seg64 else 48))[0]
            sect = off + (72 if seg64 else 56)
            for _ in range(nsects):
                sectname = bytes(buf[sect:sect + 16]).rstrip(b"\0").decode()
                if seg64:
                    _addr, size, offset = struct.unpack_from(e + "QQI", buf, sect + 32)
                else:
                    _addr, size, offset = struct.unpack_from(e + "III", buf, sect + 32)
                if sectname == ".rustc":
                    info["rustc_section"] = (base + offset, size)
                sect += 80 if seg64 else 68
        off += cmdsize
    if chained and dyld_info:
        raise Refusal("image has both LC_DYLD_INFO and LC_DYLD_CHAINED_FIXUPS")
    if symtab is None:
        raise Refusal("image has no LC_SYMTAB")

    # The predicate: undefined external nlist entries.
    symoff, nsyms, stroff, strsize = symtab
    strtab_start, strtab_end = base + stroff, base + stroff + strsize
    if strtab_end > len(buf):
        raise Refusal("string table runs past the end of the file")
    entry = 16 if wide else 12
    fmt = e + ("IBBHQ" if wide else "IBBHI")
    imports: dict[str, dict] = {}
    commons = 0
    undef_indices = []
    for index, (strx, ntype, _nsect, ndesc, nvalue) in enumerate(
            struct.iter_unpack(fmt, buf[base + symoff: base + symoff + nsyms * entry])):
        if ntype & N_STAB or not ntype & N_EXT or (ntype & N_TYPE) not in (N_UNDF, N_PBUD):
            continue
        if (ntype & N_TYPE) == N_UNDF and nvalue != 0:
            commons += 1
            continue
        if strx >= strsize:
            raise Refusal(f"symbol {index} names string offset {strx} past the string table")
        name = cstring(buf, strtab_start + strx, strtab_end)
        ordinal = (ndesc >> 8) & 0xFF
        weak = bool(ndesc & N_WEAK_REF)
        undef_indices.append(index)
        seen = imports.get(name)
        if seen is not None and seen["ordinal"] != ordinal:
            raise Refusal(f"{name} is undefined twice with ordinals {seen['ordinal']} and {ordinal}")
        imports[name] = {"ordinal": ordinal, "weak": weak or bool(seen and seen["weak"])}
    info["commons_excluded"] = commons

    # Cross-check 1: LC_DYSYMTAB's undefined range is the same entries.
    if dysymtab is not None:
        iundef, nundef = dysymtab[4], dysymtab[5]
        if undef_indices != list(range(iundef, iundef + nundef)):
            raise Refusal(f"LC_DYSYMTAB undefined range [{iundef}, {iundef + nundef}) is not the "
                          f"{len(undef_indices)} undefined external entries")

    # Cross-check 2: dyld binds the same names with the same ordinals.
    if dyld_info is not None:
        _ro, _rs, bind_off, bind_size, _wo, _ws, lazy_off, lazy_size, _eo, _es = dyld_info
        bound = {}
        bind_stream(buf, base + bind_off, bind_size, bound, lazy=False)
        bind_stream(buf, base + lazy_off, lazy_size, bound, lazy=True)
    elif chained is not None:
        bound = chained_imports(buf, base + chained[0], chained[1], e)
    else:
        bound = None
    if bound is not None:
        mismatch = sorted(set(bound) ^ set(imports))
        if mismatch:
            raise Refusal(f"symbol table and dyld binding disagree on {len(mismatch)} names, e.g. {mismatch[:5]}")
        for name, ordinals in bound.items():
            want = imports[name]["ordinal"]
            if any((o & 0xFF) != want for o in ordinals):
                raise Refusal(f"{name}: symbol-table ordinal {want} but dyld binds ordinals {sorted(ordinals)}")
    info["bind_cross_check"] = bound is not None

    libs = [d["path"] for d in info["dylibs"]]
    for name, rec in imports.items():
        o = rec["ordinal"]
        if not info["twolevel"]:
            rec["library"] = "(flat namespace)"
        elif o in SPECIAL_ORDINALS:
            rec["library"] = f"({SPECIAL_ORDINALS[o]})"
        elif 1 <= o <= len(libs):
            rec["library"] = libs[o - 1]
        else:
            raise Refusal(f"{name} names library ordinal {o}; the image loads {len(libs)} dylibs")
    info["imports"] = imports
    return info


def bind_stream(buf, start: int, size: int, bound: dict, lazy: bool) -> None:
    """Collect (name -> set of ordinals) from a dyld bind opcode stream."""
    off, end = start, start + size
    if end > len(buf):
        raise Refusal("bind stream runs past the end of the file")
    ordinal, name = 0, None

    def record():
        if name is None:
            raise Refusal("bind opcode before any symbol name")
        bound.setdefault(name, set()).add(ordinal)

    while off < end:
        byte = buf[off]
        off += 1
        op, imm = byte & 0xF0, byte & 0x0F
        if op == 0x00:  # DONE
            if not lazy:
                break
        elif op == 0x10:  # SET_DYLIB_ORDINAL_IMM
            ordinal = imm
        elif op == 0x20:  # SET_DYLIB_ORDINAL_ULEB
            ordinal, off = uleb(buf, off)
        elif op == 0x30:  # SET_DYLIB_SPECIAL_IMM (0, -1, -2, -3), kept as the low byte like n_desc's ordinal
            ordinal = 0 if imm == 0 else (imm | 0xF0) & 0xFF
        elif op == 0x40:  # SET_SYMBOL_TRAILING_FLAGS_IMM
            name = cstring(buf, off, end)
            off = buf.find(b"\0", off, end) + 1
        elif op == 0x50:  # SET_TYPE_IMM
            pass
        elif op == 0x60:  # SET_ADDEND_SLEB
            _, off = sleb(buf, off)
        elif op == 0x70:  # SET_SEGMENT_AND_OFFSET_ULEB
            _, off = uleb(buf, off)
        elif op == 0x80:  # ADD_ADDR_ULEB
            _, off = uleb(buf, off)
        elif op == 0x90:  # DO_BIND
            record()
        elif op == 0xA0:  # DO_BIND_ADD_ADDR_ULEB
            record()
            _, off = uleb(buf, off)
        elif op == 0xB0:  # DO_BIND_ADD_ADDR_IMM_SCALED
            record()
        elif op == 0xC0:  # DO_BIND_ULEB_TIMES_SKIPPING_ULEB
            _, off = uleb(buf, off)
            _, off = uleb(buf, off)
            record()
        elif op == 0xD0:  # THREADED
            if imm == 0x00:  # SET_BIND_ORDINAL_TABLE_SIZE_ULEB
                _, off = uleb(buf, off)
            elif imm != 0x01:  # APPLY has no operand
                raise Refusal(f"unknown threaded bind sub-opcode {imm:#x}")
        else:
            raise Refusal(f"unknown bind opcode {byte:#x}")


def chained_imports(buf, start: int, size: int, e: str) -> dict:
    """(name -> set of ordinals) from LC_DYLD_CHAINED_FIXUPS' import table."""
    (_version, _starts, imports_off, symbols_off, count, imports_format,
     symbols_format) = struct.unpack_from(e + "7I", buf, start)
    symbols = bytes(buf[start + symbols_off: start + size])
    if symbols_format == 1:
        symbols = zlib.decompress(symbols)
    elif symbols_format != 0:
        raise Refusal(f"unknown chained-fixups symbols_format {symbols_format}")
    bound: dict = {}
    for i in range(count):
        if imports_format == 1:
            raw = struct.unpack_from(e + "I", buf, start + imports_off + 4 * i)[0]
            ordinal, name_off = raw & 0xFF, raw >> 9
        elif imports_format == 2:
            raw = struct.unpack_from(e + "I", buf, start + imports_off + 8 * i)[0]
            ordinal, name_off = raw & 0xFF, raw >> 9
        elif imports_format == 3:
            raw = struct.unpack_from(e + "Q", buf, start + imports_off + 16 * i)[0]
            ordinal, name_off = raw & 0xFFFF, raw >> 32
            ordinal = ordinal if ordinal < 0xFFF0 else ordinal & 0xFF
        else:
            raise Refusal(f"unknown chained-fixups imports_format {imports_format}")
        stop = symbols.find(b"\0", name_off)
        if stop < 0:
            raise Refusal("unterminated chained-fixups import name")
        bound.setdefault(symbols[name_off:stop].decode("utf-8"), set()).add(ordinal)
    return bound


# --------------------------------------------------------------------------------------------
# ELF reader.
# --------------------------------------------------------------------------------------------

SHT_DYNSYM, SHT_DYNAMIC, SHT_GNU_VERSYM, SHT_GNU_VERNEED = 11, 6, 0x6FFFFFFF, 0x6FFFFFFE
SHN_UNDEF, SHN_XINDEX = 0, 0xFFFF
STB_GLOBAL, STB_WEAK = 1, 2
DT_NEEDED = 1


def read_elf(buf, machine: int) -> dict:
    if bytes(buf[:4]) != b"\x7fELF":
        raise Refusal("not an ELF file")
    wide = {1: False, 2: True}.get(buf[4])
    e = {1: "<", 2: ">"}.get(buf[5])
    if wide is None or e is None:
        raise Refusal("unknown ELF class or data encoding")
    if wide:
        etype, emachine, _v, _entry, _phoff, shoff, _flags, _eh, _phes, _phn, shentsize, shnum, shstrndx = \
            struct.unpack_from(e + "HHIQQQIHHHHHH", buf, 16)
    else:
        etype, emachine, _v, _entry, _phoff, shoff, _flags, _eh, _phes, _phn, shentsize, shnum, shstrndx = \
            struct.unpack_from(e + "HHIIIIIHHHHHH", buf, 16)
    if emachine != machine:
        raise Refusal(f"ELF e_machine {emachine} is not the target's {machine}")
    if shoff == 0:
        raise Refusal("ELF file has no section headers; this reader requires them")
    shfmt = e + ("IIQQQQIIQQ" if wide else "IIIIIIIIII")

    def section(i):
        name, stype, _fl, _addr, offset, size, link, sinfo, _al, entsize = struct.unpack_from(
            shfmt, buf, shoff + i * shentsize)
        return {"type": stype, "offset": offset, "size": size, "link": link, "info": sinfo, "entsize": entsize}

    first = section(0)
    if shnum == 0:
        shnum = first["size"]
    if shstrndx == SHN_XINDEX:
        shstrndx = first["link"]
    sections = [section(i) for i in range(shnum)]
    names_at = sections[shstrndx]["offset"] if shstrndx < len(sections) else None
    rustc_section = None
    for i, s in enumerate(sections):
        s_name = struct.unpack_from(e + "I", buf, shoff + i * shentsize)[0]
        if names_at is not None and cstring(buf, names_at + s_name) == ".rustc":
            rustc_section = (s["offset"], s["size"])
    dynsyms = [s for s in sections if s["type"] == SHT_DYNSYM]
    if len(dynsyms) != 1:
        raise Refusal(f"ELF file has {len(dynsyms)} SHT_DYNSYM sections")
    dynsym = dynsyms[0]
    strtab = sections[dynsym["link"]]
    s0, s1 = strtab["offset"], strtab["offset"] + strtab["size"]

    versions: dict[int, tuple[str, str]] = {}
    for s in sections:
        if s["type"] != SHT_GNU_VERNEED:
            continue
        vstr = sections[s["link"]]
        off, left = s["offset"], s["info"]
        while left:
            _ver, cnt, vfile, aux, nxt = struct.unpack_from(e + "HHIII", buf, off)
            lib = cstring(buf, vstr["offset"] + vfile)
            a = off + aux
            for _ in range(cnt):
                _hash, _flags, other, vname, anext = struct.unpack_from(e + "IHHII", buf, a)
                versions[other] = (lib, cstring(buf, vstr["offset"] + vname))
                a += anext
            off += nxt
            left -= 1
    versym = next((s for s in sections if s["type"] == SHT_GNU_VERSYM), None)

    entry = 24 if wide else 16
    count = dynsym["size"] // entry
    imports: dict[str, dict] = {}
    for i in range(1, count):
        o = dynsym["offset"] + i * entry
        if wide:
            st_name, st_info, _other, st_shndx, _value, _size = struct.unpack_from(e + "IBBHQQ", buf, o)
        else:
            st_name, _value, _size, st_info, _other, st_shndx = struct.unpack_from(e + "IIIBBH", buf, o)
        bind = st_info >> 4
        if st_shndx != SHN_UNDEF or bind not in (STB_GLOBAL, STB_WEAK) or st_name == 0:
            continue
        name = cstring(buf, s0 + st_name, s1)
        library, version = "(unversioned: DT_NEEDED search order)", None
        if versym is not None:
            v = struct.unpack_from(e + "H", buf, versym["offset"] + 2 * i)[0] & 0x7FFF
            if v in versions:
                library, version = versions[v]
        imports.setdefault(name, {"library": library, "version": version, "weak": bind == STB_WEAK})

    needed = []
    for s in sections:
        if s["type"] != SHT_DYNAMIC:
            continue
        dstr = sections[s["link"]]
        dfmt, dsize = (e + "qQ", 16) if wide else (e + "iI", 8)
        for j in range(s["size"] // dsize):
            tag, val = struct.unpack_from(dfmt, buf, s["offset"] + j * dsize)
            if tag == 0:
                break
            if tag == DT_NEEDED:
                needed.append(cstring(buf, dstr["offset"] + val))
    return {"format": "ELF", "arch": f"e_machine {emachine}", "filetype": {2: "ET_EXEC", 3: "ET_DYN"}.get(etype, str(etype)),
            "dylibs": [{"command": "DT_NEEDED", "path": n} for n in needed], "install_name": None,
            "min_os": None, "sdk": None, "fixups": "n/a", "rustc_section": rustc_section, "imports": imports,
            "commons_excluded": 0, "bind_cross_check": False}


# --------------------------------------------------------------------------------------------
# Measuring a file.
# --------------------------------------------------------------------------------------------

VERSION_TAIL = re.compile(rb" \(([0-9a-f]{9}) (\d{4}-\d{2}-\d{2})\)")
VERSION_HEAD = re.compile(rb"(\d+\.\d+\.\d+(?:-[a-z]+)?)$")
RUSTC_VERSION = re.compile(rb"rustc (\d+\.\d+\.\d+(?:-[a-z]+)?) \(([0-9a-f]{9}) (\d{4}-\d{2}-\d{2})\)")


def version_strings(buf) -> dict[str, int]:
    """Every `X.Y.Z[-chan] (<9 hex> <date>)` in the file, with its count (rustc's CFG_VERSION shape)."""
    found: dict[str, int] = {}
    for m in VERSION_TAIL.finditer(buf):
        head = VERSION_HEAD.search(bytes(buf[max(0, m.start() - 24):m.start()]))
        if head:
            text = f"{head.group(1).decode()} ({m.group(1).decode()} {m.group(2).decode()})"
            found[text] = found.get(text, 0) + 1
    return dict(sorted(found.items()))


def copy_and_hash(src: Path, dst: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    with open(src, "rb") as fin, open(dst, "wb") as fout:
        while True:
            chunk = fin.read(1 << 22)
            if not chunk:
                break
            digest.update(chunk)
            fout.write(chunk)
            size += len(chunk)
    return digest.hexdigest(), size


def measure_file(path: Path, target: str, workdir: Path) -> dict:
    """Copy `path` into `workdir`, hash the copy, parse the copy. Returns the measurement."""
    kind, arch = TARGETS[target]
    copy = workdir / path.name
    sha, size = copy_and_hash(path, copy)
    with open(copy, "rb") as fh, mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ) as buf:
        info = read_macho(buf, arch) if kind == "macho" else read_elf(buf, arch)
        compiled_by = []
        if info["rustc_section"]:
            off, n = info["rustc_section"]
            compiled_by = sorted({m.group(0).decode() for m in RUSTC_VERSION.finditer(buf[off:off + n])})
        info["compiled_by"] = compiled_by
        info["version_strings"] = version_strings(buf)
    copy.unlink()
    info["sha256"], info["size"], info["kind"] = sha, size, kind
    names = sorted(info["imports"])
    info["names"] = names
    info["set_digest"] = hashlib.sha256("".join(n + "\n" for n in names).encode()).hexdigest()
    macho = kind == "macho"
    classes = {"c": 0, "cxx_mangled": 0, "rust_mangled": 0}
    for n in names:
        classes[name_class(n, macho)] += 1
    info["classes"] = classes
    by_lib: dict[str, int] = {d["path"]: 0 for d in info["dylibs"]}
    for rec in info["imports"].values():
        by_lib[rec["library"]] = by_lib.get(rec["library"], 0) + 1
    info["by_library"] = by_lib
    info["weak"] = sorted(n for n, r in info["imports"].items() if r["weak"])
    return info


# --------------------------------------------------------------------------------------------
# Locating pinned inputs.
# --------------------------------------------------------------------------------------------

def default_build_dir() -> Path:
    try:
        common = subprocess.run(["git", "-C", str(REPO), "rev-parse", "--path-format=absolute", "--git-common-dir"],
                                check=True, capture_output=True, text=True).stdout.strip()
        return Path(common).parent / "build"
    except (OSError, subprocess.CalledProcessError):
        return REPO / "build"


def file_sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 22), b""):
            h.update(chunk)
    return h.hexdigest()


def default_atpkg_store() -> Path:
    if os.environ.get("ATPKG_BIN"):
        return Path(os.environ["ATPKG_BIN"]).parent / "store"
    return Path.home() / "Library/Application Support/aterm/pkg/store"


def candidates(inp: dict, roots: dict, artifact_dirs: list[Path]) -> list[tuple[Path, str]]:
    """The pinned path, then every file of the same size in an --artifact-dir; the digest decides."""
    out = []
    path = roots[inp["root"]] / inp["path"]
    if path.is_file():
        out.append((path, "pinned path"))
    for d in artifact_dirs:
        for cand in sorted(d.iterdir()) if d.is_dir() else []:
            if cand.is_file() and cand.stat().st_size == inp["size"]:
                out.append((cand, "artifact dir"))
    return out


# --------------------------------------------------------------------------------------------
# Rows.
# --------------------------------------------------------------------------------------------

def headline(inp: dict) -> str:
    base = f"imports.{inp['artifact']}.{inp['target']}"
    return base if inp["canonical"] else f"{base}@{inp['id'].split('@', 1)[1]}"


def build_rows(inputs: list[dict], measured: dict[str, dict]) -> list[dict]:
    rows = []
    canonical = {(i["artifact"], i["target"]): i["id"] for i in inputs if i["canonical"]}
    for inp in inputs:
        m = measured[inp["id"]]
        pred = PREDICATE_MACHO if m["kind"] == "macho" else PREDICATE_ELF
        name = headline(inp)
        row = {"name": name, "value": len(m["names"]), "status": "measured", "predicate": pred,
               "inputs": [inp["id"]]}
        if not inp["canonical"]:
            ref = measured[canonical[(inp["artifact"], inp["target"])]]
            row["added_vs_canonical"] = sorted(set(m["names"]) - set(ref["names"]))
            row["removed_vs_canonical"] = sorted(set(ref["names"]) - set(m["names"]))
        rows.append(row)
        if not inp["canonical"]:
            continue
        for cls, text in (("cxx_mangled", PREDICATE_CXX), ("rust_mangled", PREDICATE_RUST), ("c", PREDICATE_C)):
            rows.append({"name": f"{name}.{cls}", "value": m["classes"][cls], "status": "measured",
                         "predicate": text, "inputs": [inp["id"]]})
        if m["kind"] == "macho":
            for lib, n in m["by_library"].items():
                short = lib.strip("()").lower() if lib.startswith("(") else short_library(lib)
                rows.append({"name": f"{name}.bound_to.{short}", "value": n, "status": "measured",
                             "predicate": PREDICATE_BOUND.format(path=lib), "inputs": [inp["id"]]})
    a, b, commit = XTARGET
    ma, mb = measured[a], measured[b]
    ia = next(i for i in inputs if i["id"] == a)
    ib = next(i for i in inputs if i["id"] == b)
    for x, y, ix, iy in ((ma, mb, ia, ib), (mb, ma, ib, ia)):
        only = sorted(set(x["names"]) - set(y["names"]))
        rows.append({"name": f"imports.std.{ix['target']}.not_in.{iy['target']}@{commit}", "value": len(only),
                     "status": "measured",
                     "predicate": PREDICATE_XTARGET.format(a=ix["id"], b=iy["id"], commit=commit),
                     "inputs": [ix["id"], iy["id"]], "names": only})
    for blk in BLOCKED:
        rows.append({"name": blk["name"], "status": "blocked",
                     "predicate": PREDICATE_MACHO if blk["predicate"] == "macho" else PREDICATE_ELF,
                     "inputs": [], "blocked": blk["reason"], "unblock": blk["unblock"]})
    return rows


def prose_facts(measured: dict[str, dict]) -> None:
    """Every factual sentence of DESIGN_CLAIMS' explanations, re-derived: a changed fact refuses."""
    def ids(artifact, target):
        return [i["id"] for i in INPUTS if i["artifact"] == artifact and i["target"] == target]
    std_a = ids("std", "aarch64-apple-darwin")
    if len({measured[i]["set_digest"] for i in std_a}) != 1:
        raise Refusal("prose: the aarch64-apple-darwin std inputs no longer share one import set")
    xs = measured["std.x86_64-apple-darwin@stage0-8b50cbcc5"]
    if len(xs["names"]) != 195 or xs["set_digest"] == measured[std_a[0]]["set_digest"]:
        raise Refusal("prose: the x86_64-apple-darwin std set is no longer 195 names different from aarch64's")
    counts = {i: len(measured[i]["names"]) for i in ids("rustc_driver", "aarch64-apple-darwin")}
    if counts != {"rustc_driver.aarch64-apple-darwin@stage2-248a9f1dd": 491,
                  "rustc_driver.aarch64-apple-darwin@stage1-9a0656816": 492,
                  "rustc_driver.aarch64-apple-darwin@installed-321aaeda7": 487}:
        raise Refusal(f"prose: rustc_driver counts per build changed: {counts}")
    d = measured["rustc_driver.aarch64-apple-darwin@stage2-248a9f1dd"]
    libcxx = {n for n, r in d["imports"].items() if r["library"] == "/usr/lib/libc++.1.dylib"}
    cxx = {n for n in d["names"] if name_class(n, True) == "cxx_mangled"}
    if not cxx <= libcxx or libcxx - cxx != {"___cxa_guard_acquire", "___cxa_guard_release", "___cxa_pure_virtual"}:
        raise Refusal(f"prose: libc++-bound minus mangled is {sorted(libcxx - cxx)}; mangled outside libc++ "
                      f"{sorted(cxx - libcxx)}")
    for i in INPUTS:
        if i["id"].endswith("@stage2-248a9f1dd") and measured[i["id"]]["compiled_by"] != [
                "rustc 1.99.0-dev (248a9f1dd 2026-09-14)"]:
            raise Refusal(f"prose: {i['id']} is no longer compiled by the 2026-09-14 stage-1 compiler")


def design_claims(rows: list[dict], design_text: str) -> list[dict]:
    values = {r["name"]: r.get("value") for r in rows}
    lines = design_text.split("\n")
    out = []
    for claim in DESIGN_CLAIMS:
        hits = [i + 1 for i, line in enumerate(lines) if claim["quote"] in line]
        if len(hits) != 1:
            raise Refusal(f"design claim {claim['id']}: quote occurs {len(hits)} times in {DESIGN_REL}")
        compares = []
        for row, design_value, expect, *reading in claim["compare"]:
            if row not in values:
                raise Refusal(f"design claim {claim['id']} compares missing row {row}")
            reproduces = values[row] == design_value
            if reproduces != expect:
                raise Refusal(f"design claim {claim['id']}: {row} = {values[row]} vs design {design_value}; "
                              f"expected reproduces={expect}. Revisit the explanation before regenerating.")
            compares.append({"row": row, "design_value": design_value, "measured": values[row],
                             "reproduces": reproduces, "reading": reading[0] if reading else "as worded"})
        out.append({"id": claim["id"], "line": hits[0], "quote": claim["quote"], "compare": compares,
                    "explanation": claim["explanation"]})
    return out


# --------------------------------------------------------------------------------------------
# Dispositions (the numerator).
# --------------------------------------------------------------------------------------------

DISPOSITION_KEYS = {
    "specified": ("symbol", "target", "os_release", "disposition", "spec"),
    "refused": ("symbol", "target", "os_release", "disposition", "refusal", "reason"),
    "unspecified": ("symbol", "target", "os_release", "disposition"),
}
DISPOSITION_COUNTS = ("imports", "numerator", "specified", "refused", "unspecified")


def disposition_inputs() -> list[dict]:
    """The inputs whose import sets are disposed of: the canonical std Mach-O inputs (E2.6.6 is about std)."""
    return [i for i in INPUTS if i["artifact"] == "std" and i["canonical"] and TARGETS[i["target"]][0] == "macho"]


def disposition_rows(sets: dict[str, list[str]], table: list[dict] | None = None) -> dict[str, list[dict]]:
    """input id -> its disposition rows, in name order, one per (name, os_release). Refuses a table entry
    that breaks a rule; a name with no entry is one `unspecified` row on ANY_RELEASE."""
    table = DISPOSITIONS if table is None else table
    by_target = {i["target"]: i["id"] for i in disposition_inputs()}
    listed: dict[tuple[str, str], list[dict]] = {}
    for n, d in enumerate(table):
        where = f"DISPOSITIONS[{n}] {d.get('symbol')!r} on {d.get('target')!r}"
        disposition = d.get("disposition")
        if disposition not in ("specified", "refused"):
            raise Refusal(f"{where}: disposition {disposition!r} is neither `specified` nor `refused` "
                          "(`unspecified` is the default and is never listed)")
        if set(d) != set(DISPOSITION_KEYS[disposition]):
            raise Refusal(f"{where}: a {disposition} row has exactly the keys {list(DISPOSITION_KEYS[disposition])}, "
                          f"not {sorted(d)}")
        if not all(isinstance(v, str) and v.strip() for v in d.values()):
            raise Refusal(f"{where}: every field is non-empty text")
        if d["target"] not in by_target:
            raise Refusal(f"{where}: {d['target']!r} is not a target whose std import set is disposed of "
                          f"({sorted(by_target)})")
        if d["symbol"] not in sets[by_target[d["target"]]]:
            raise Refusal(f"{where}: names no import of {by_target[d['target']]} (the exact Mach-O spelling is the key)")
        if disposition == "specified":
            if d["os_release"] == ANY_RELEASE:
                raise Refusal(f"{where}: a specified row names the one OS release its clause was conformance-tested "
                              f"on, never {ANY_RELEASE!r}")
            path, _, clause = d["spec"].partition("#")
            if not clause or not (REPO / path).is_file():
                raise Refusal(f"{where}: spec {d['spec']!r} is not `<existing repo path>#<clause>`")
        rows = listed.setdefault((d["target"], d["symbol"]), [])
        if any(r["os_release"] == d["os_release"] for r in rows):
            raise Refusal(f"{where}: a second row for OS release {d['os_release']!r}")
        rows.append(dict(d))
    out = {}
    for inp in disposition_inputs():
        rows = []
        for name in sets[inp["id"]]:
            got = listed.get((inp["target"], name))
            if got:
                rows.extend(sorted(got, key=lambda r: r["os_release"]))
            else:
                rows.append({"symbol": name, "target": inp["target"], "os_release": ANY_RELEASE,
                             "disposition": "unspecified"})
        out[inp["id"]] = rows
    return out


def disposition_counts(names: list[str], rows: list[dict]) -> dict[str, int]:
    """Counts of NAMES (not rows): a name disposed of on two releases counts once."""
    by = {v: {r["symbol"] for r in rows if r["disposition"] == v} for v in ("specified", "refused")}
    numerator = by["specified"] | by["refused"]
    return {"imports": len(names), "numerator": len(numerator), "specified": len(by["specified"]),
            "refused": len(by["refused"]), "unspecified": len(set(names) - numerator)}


def render_dispositions(sets: dict[str, list[str]], table: list[dict] | None = None) -> str:
    rows_by_input = disposition_rows(sets, table)
    L = [DISPOSITION_BEGIN + ". Rendered from the [[import_set]] names above and the script's",
         "# DISPOSITIONS table, by --write or alone by --write-dispositions; --check and --check-dispositions",
         "# validate it. A name with no specified or refused row is unspecified on every OS release (\"*\")."]
    w = L.append
    for inp in disposition_inputs():
        rows = rows_by_input[inp["id"]]
        w("")
        w("[[disposition]]")
        w(f"input = {q(inp['id'])}")
        w(f"target = {q(inp['target'])}")
        w(f"predicate = {q(PREDICATE_DISPOSITION)}")
        for key, value in disposition_counts(sets[inp["id"]], rows).items():
            w(f"{key} = {value}")
        w("rows = [")
        for r in rows:
            w("  { " + ", ".join(f"{k} = {q(r[k])}" for k in DISPOSITION_KEYS[r["disposition"]]) + " },")
        w("]")
    return "\n".join(L) + "\n"


SET_FIELD = re.compile(r'^(input|sha256) = ("(?:[^"\\]|\\.)*")$')
COUNT_FIELD = re.compile(r"^(\w+) = (\d+)$")
LIST_ITEM = re.compile(r'^  ("(?:[^"\\]|\\.)*"),$')
LIST_HEAD = re.compile(r'^"(?:[^"\\]|\\.)*" = \[$')
INLINE_FIELD = re.compile(r'(\w+) = ("(?:[^"\\]|\\.)*")')


def committed_import_sets(text: str) -> dict[str, list[str]]:
    """input id -> the sorted names of its committed [[import_set]], read from this script's own rendering of
    it. The recorded count and set sha256 must be those of the names read, so a parse that lost or invented a
    name refuses instead of disposing of the wrong set."""
    sets: dict[str, list[str]] = {}
    recorded: dict[str, tuple[int | None, str | None]] = {}
    current, names, in_names, count, digest = None, [], False, None, None

    def close():
        if current is not None:
            sets[current] = sorted(names)
            recorded[current] = (count, digest)

    for line in text.split("\n"):
        if line.startswith("[[") or line.startswith(DISPOSITION_BEGIN):
            close()
            current, names, in_names, count, digest = None, [], False, None, None
            if line == "[[import_set]]":
                current = ""
            continue
        if current is None or not line:
            continue
        if line == "[import_set.names]":
            in_names = True
        elif in_names:
            m = LIST_ITEM.match(line)
            if m:
                names.append(json.loads(m.group(1)))
            elif not (LIST_HEAD.match(line) or line == "]"):
                raise Refusal(f"[import_set.names] of {current!r}: unexpected line {line!r}")
        else:
            m, c = SET_FIELD.match(line), COUNT_FIELD.match(line)
            if m and m.group(1) == "input":
                current = json.loads(m.group(2))
            elif m:
                digest = json.loads(m.group(2))
            elif c and c.group(1) == "count":
                count = int(c.group(2))
    close()
    for inp, names_read in sets.items():
        count, digest = recorded[inp]
        got = hashlib.sha256("".join(n + "\n" for n in names_read).encode()).hexdigest()
        if count != len(names_read) or digest != got or len(set(names_read)) != len(names_read):
            raise Refusal(f"[[import_set]] {inp!r}: read {len(names_read)} names (sha256 {got}), but it records "
                          f"count {count} and sha256 {digest}")
    return sets


def committed_disposition_blocks(section: str) -> list[dict]:
    """The [[disposition]] blocks of the committed column: their scalar fields and their rows."""
    blocks: list[dict] = []
    in_rows = False
    for line in section.split("\n"):
        if line == "[[disposition]]":
            blocks.append({"rows": []})
            in_rows = False
        elif not blocks or not line or line.startswith("#"):
            continue
        elif in_rows:
            if line == "]":
                in_rows = False
            elif line.startswith("  { ") and line.endswith(" },"):
                blocks[-1]["rows"].append({k: json.loads(v) for k, v in INLINE_FIELD.findall(line)})
            else:
                raise Refusal(f"disposition rows: unexpected line {line!r}")
        elif line == "rows = [":
            in_rows = True
        else:
            m, c = re.match(r'^(\w+) = ("(?:[^"\\]|\\.)*")$', line), COUNT_FIELD.match(line)
            if m:
                blocks[-1][m.group(1)] = json.loads(m.group(2))
            elif c:
                blocks[-1][c.group(1)] = int(c.group(2))
            else:
                raise Refusal(f"[[disposition]]: unexpected line {line!r}")
    return blocks


def check_dispositions(text: str, table: list[dict] | None = None) -> list[str]:
    """Validate the committed disposition column; returns one summary line per input, or raises Refusal.

    The rules are checked on the committed rows themselves first, so a violation is named as the rule it
    breaks; then the column must be byte for byte its rendering from the committed sets and DISPOSITIONS."""
    sets = committed_import_sets(text)
    wanted = [i["id"] for i in disposition_inputs()]
    for inp in wanted:
        if inp not in sets:
            raise Refusal(f"the table has no [[import_set]] for {inp}, whose names the dispositions dispose of")
    at = text.find("\n" + DISPOSITION_BEGIN)
    if at < 0:
        raise Refusal("the table has no disposition column (I-FFI-SPECIFIED's numerator); run --write-dispositions")
    section = text[at + 1:]
    blocks = committed_disposition_blocks(section)
    if [b.get("input") for b in blocks] != wanted:
        raise Refusal(f"the [[disposition]] blocks are for {[b.get('input') for b in blocks]}, not {wanted}")
    summary = []
    for inp, block in zip(disposition_inputs(), blocks):
        where = f"[[disposition]] {inp['id']}"
        if block.get("target") != inp["target"]:
            raise Refusal(f"{where}: target {block.get('target')!r} is not {inp['target']!r}")
        seen: dict[str, set[str]] = {}
        for r in block["rows"]:
            d, row_at = r.get("disposition"), f"{where} row {r.get('symbol')!r}"
            if d not in DISPOSITION_VOCABULARY:
                raise Refusal(f"{row_at}: disposition {d!r} is not one of {list(DISPOSITION_VOCABULARY)}")
            if list(r) != list(DISPOSITION_KEYS[d]):
                raise Refusal(f"{row_at}: a {d} row has the keys {list(DISPOSITION_KEYS[d])}, not {list(r)}")
            if r["target"] != inp["target"]:
                raise Refusal(f"{row_at}: keyed on target {r['target']!r} inside the {inp['target']} block")
            if (d == "unspecified") != (r["os_release"] == ANY_RELEASE):
                raise Refusal(f"{row_at}: os_release {r['os_release']!r}: an unspecified row is stated for every "
                              f"release ({ANY_RELEASE!r}) and a specified or refused row for one it names")
            if r["os_release"] in seen.setdefault(r["symbol"], set()):
                raise Refusal(f"{row_at}: two rows for OS release {r['os_release']!r}")
            seen[r["symbol"]].add(r["os_release"])
        names = sets[inp["id"]]
        if set(seen) != set(names):
            missing, extra = sorted(set(names) - set(seen)), sorted(set(seen) - set(names))
            raise Refusal(f"{where}: the rows and the import set differ: {len(missing)} imports with no row "
                          f"{missing[:5]}, {len(extra)} rows naming no import {extra[:5]}")
        for symbol, releases in seen.items():
            if ANY_RELEASE in releases and len(releases) > 1:
                raise Refusal(f"{where} row {symbol!r}: unspecified on every release and disposed of on "
                              f"{sorted(releases - {ANY_RELEASE})}")
        counts = disposition_counts(names, block["rows"])
        for key in DISPOSITION_COUNTS:
            if block.get(key) != counts[key]:
                raise Refusal(f"{where}: {key} = {block.get(key)!r}, but the rows give {counts[key]}")
        summary.append(f"{inp['id']}: {counts['numerator']}/{counts['imports']} specified or refused "
                       f"({counts['specified']} specified, {counts['refused']} refused, "
                       f"{counts['unspecified']} unspecified)")
    expected = render_dispositions(sets, table)
    if section != expected:
        diff = "".join(difflib.unified_diff(section.splitlines(True), expected.splitlines(True),
                                            "committed dispositions", "rendered", n=1))
        raise Refusal("the disposition column is not its rendering from the committed import sets and "
                      "DISPOSITIONS (do not hand-edit it; change DISPOSITIONS and run --write-dispositions):\n"
                      + diff)
    return summary


# --------------------------------------------------------------------------------------------
# TOML rendering (deterministic, no third-party writer).
# --------------------------------------------------------------------------------------------

def q(s: str) -> str:
    out = []
    for ch in s:
        if ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ord(ch) < 0x20 or ord(ch) == 0x7F:
            out.append(f"\\u{ord(ch):04x}")
        else:
            out.append(ch)
    return '"' + "".join(out) + '"'


def arr(items: list[str], indent: str = "  ") -> str:
    if not items:
        return "[]"
    return "[\n" + "".join(f"{indent}{q(i)},\n" for i in items) + "]"


def render(inputs: list[dict], measured: dict[str, dict], rows: list[dict], claims: list[dict], commit: str) -> str:
    L = []
    w = L.append
    w("# Stage 0.5 denominator: import sets per artifact and target (E0.12).")
    w(f"# GENERATED by `python3 {SCRIPT_REL} --write`; `--check` recomputes it from the pinned inputs")
    w("# and fails on any difference (measured_at_commit excepted). Do not hand-edit: change the script's")
    w("# tables and regenerate.")
    w(f"# Design of record: {DESIGN_REL} §5.2 Stage 0.5; consumers: D-10 (§3.10 denominators),")
    w("# E2.6.6, I-FFI-SPECIFIED, E1.10.2 / E5.1.1 (trustc-core's set must be a subset of std's).")
    w("")
    w(f"schema = {q(SCHEMA)}")
    w(f"key = {q(KEY)}")
    w(f"design = {q(DESIGN_REL)}")
    w(f"script = {q(SCRIPT_REL)}")
    w('exit = "E0.12"')
    w("consumers = " + arr(list(CONSUMERS)))
    w("# The pin: the superproject commit whose design text the [[design_claim]] rows read (every other")
    w("# input is pinned by its sha256 below). scripts/trust_core/denominators.py re-measures at it (--rev);")
    w("# this script's own --check reads the design at --rev (default HEAD) and ignores this line.")
    w(f"measured_at_commit = {q(commit)}")
    w("")
    w("[predicates]")
    w(f"macho = {q(PREDICATE_MACHO)}")
    w(f"elf = {q(PREDICATE_ELF)}")
    w(f"cxx_mangled = {q(PREDICATE_CXX)}")
    w(f"rust_mangled = {q(PREDICATE_RUST)}")
    w(f"c = {q(PREDICATE_C)}")
    w(f"bound_to = {q(PREDICATE_BOUND)}")
    w("")
    w("[roots]")
    w(f"build = {q('<superproject checkout>/build: the parent of the git common dir, + /build (--build-dir)')}")
    w(f"atpkg-store = {q('the atpkg package store: $ATPKG_BIN/../store, else ~/Library/Application Support/aterm/pkg/store (--atpkg-store)')}")
    for inp in inputs:
        m = measured[inp["id"]]
        w("")
        w(f"[inputs.{q(inp['id'])}]")
        w(f"artifact = {q(inp['artifact'])}")
        w(f"target = {q(inp['target'])}")
        w(f"canonical = {'true' if inp['canonical'] else 'false'}")
        w(f"root = {q(inp['root'])}")
        w(f"path = {q(inp['path'])}")
        w(f"sha256 = {q(m['sha256'])}")
        w(f"size = {m['size']}")
        w(f"format = {q(m['format'] + ' ' + m['arch'] + ' ' + m['filetype'])}")
        if m["install_name"]:
            w(f"install_name = {q(m['install_name'])}")
        if m["min_os"]:
            w(f"min_os = {q(m['min_os'])}")
            w(f"sdk = {q(m['sdk'])}")
        w(f"fixups = {q(m['fixups'])}")
        w(f"bind_cross_check = {'true' if m['bind_cross_check'] else 'false'}")
        w(f"commons_excluded = {m['commons_excluded']}")
        w(f"compiled_by = {arr(m['compiled_by'])}")
        w("version_strings = { " + ", ".join(f"{q(k)} = {v}" for k, v in m["version_strings"].items()) + " }")
        w(f"source_commit = {q(inp['source_commit'])}")
        w(f"source = {q(inp['source'])}")
        w(f"imports = {len(m['names'])}")
        w(f"import_set_sha256 = {q(m['set_digest'])}")
        w(f"weak_imports = {arr(m['weak'])}")
        w("linked = [")
        for d in m["dylibs"]:
            w(f"  {{ command = {q(d['command'])}, path = {q(d['path'])}, imports = {m['by_library'].get(d['path'], 0)} }},")
        w("]")
    for row in rows:
        w("")
        w("[[row]]")
        w(f"name = {q(row['name'])}")
        if "value" in row:
            w(f"value = {row['value']}")
        w(f"status = {q(row['status'])}")
        w(f"predicate = {q(row['predicate'])}")
        w("inputs = [" + ", ".join(q(i) for i in row["inputs"]) + "]")
        for field in ("added_vs_canonical", "removed_vs_canonical", "names"):
            if field in row:
                w(f"{field} = {arr(row[field])}")
        for field in ("blocked", "unblock"):
            if field in row:
                w(f"{field} = {q(row[field])}")
    for c in claims:
        w("")
        w("[[design_claim]]")
        w(f"id = {q(c['id'])}")
        w(f"line = {c['line']}")
        w(f"quote = {q(c['quote'])}")
        w("compare = [")
        for cmp in c["compare"]:
            w(f"  {{ row = {q(cmp['row'])}, design_value = {cmp['design_value']}, measured = {cmp['measured']}, "
              f"reproduces = {'true' if cmp['reproduces'] else 'false'}, reading = {q(cmp['reading'])} }},")
        w("]")
        w(f"explanation = {q(c['explanation'])}")
    # The published sets: one per canonical input, grouped by the library each name binds to.
    for inp in inputs:
        if not inp["canonical"]:
            continue
        m = measured[inp["id"]]
        w("")
        w("[[import_set]]")
        w(f"input = {q(inp['id'])}")
        w(f"count = {len(m['names'])}")
        w(f"sha256 = {q(m['set_digest'])}")
        same = [i["id"] for i in inputs if i["id"] != inp["id"] and measured[i["id"]]["set_digest"] == m["set_digest"]]
        w(f"identical_in = {arr(same)}")
        groups: dict[str, list[str]] = {}
        for n in m["names"]:
            groups.setdefault(m["imports"][n]["library"], []).append(n)
        w("[import_set.names]")
        for lib in sorted(groups):
            w(f"{q(lib)} = {arr(groups[lib])}")
    # The disposition column closes the table (committed_import_sets reads the sets above it).
    sets = {i["id"]: measured[i["id"]]["names"] for i in disposition_inputs()}
    return "\n".join(L) + "\n\n" + render_dispositions(sets)


# --------------------------------------------------------------------------------------------
# Main.
# --------------------------------------------------------------------------------------------

def resolve_commit(rev: str) -> str:
    return subprocess.run(["git", "-C", str(REPO), "rev-parse", "--verify", f"{rev}^{{commit}}"], check=True,
                          capture_output=True, text=True).stdout.strip()


def design_text(commit: str) -> str:
    return subprocess.run(["git", "-C", str(REPO), "show", f"{commit}:{DESIGN_REL}"], check=True,
                          capture_output=True).stdout.decode("utf-8")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--build-dir", type=Path, default=None)
    ap.add_argument("--atpkg-store", type=Path, default=None)
    ap.add_argument("--artifact-dir", type=Path, action="append", default=[],
                    help="a directory searched by digest for a pinned input that left its path")
    ap.add_argument("--workdir", type=Path, default=None, help="where copies are made (default: a fresh temp dir)")
    ap.add_argument("--check", action="store_true", help="compare the regenerated table with the committed one")
    ap.add_argument("--write", action="store_true", help="write the regenerated table")
    ap.add_argument("--artifact", type=Path, help="measure one unpinned file")
    ap.add_argument("--target", choices=sorted(TARGETS), help="the target of --artifact")
    ap.add_argument("--names", action="store_true", help="with --artifact: print every import")
    ap.add_argument("--rev", default="HEAD", help="the superproject revision whose design the claims read (default HEAD)")
    ap.add_argument("--record", type=Path, help=f"the table (default {TABLE_REL})")
    ap.add_argument("--check-dispositions", action="store_true",
                    help="validate the committed disposition column without re-measuring")
    ap.add_argument("--write-dispositions", action="store_true",
                    help="re-render only the disposition column from the committed import sets")
    args = ap.parse_args(argv)
    table = args.record or REPO / TABLE_REL

    if args.write_dispositions or args.check_dispositions or args.check:
        try:
            current = table.read_text(encoding="utf-8")
            if args.write_dispositions:
                at = current.find("\n" + DISPOSITION_BEGIN)
                head = current if at < 0 else current[:at + 1]
                current = head.rstrip("\n") + "\n\n" + render_dispositions(committed_import_sets(head))
                table.write_text(current, encoding="utf-8")
                print(f"imports: wrote the disposition column of {table}", file=sys.stderr)
            summary = check_dispositions(current)
        except OSError as err:
            print(f"imports: REFUSED dispositions: cannot read {table}: {err}", file=sys.stderr)
            return 1
        except Refusal as err:
            print(f"imports: REFUSED dispositions: {err}", file=sys.stderr)
            return 1
        print("imports: dispositions OK (" + "; ".join(summary) + ")", file=sys.stderr)
        if not args.check:
            return 0

    work = Path(tempfile.mkdtemp(prefix="imports-", dir=args.workdir))
    try:
        if args.artifact:
            if not args.target:
                ap.error("--artifact needs --target")
            try:
                m = measure_file(args.artifact, args.target, work)
            except (Refusal, struct.error, UnicodeDecodeError) as err:
                print(f"imports: REFUSED {args.artifact}: {err}", file=sys.stderr)
                return 1
            print(f"{args.artifact}: sha256 {m['sha256']}, {m['format']} {m['arch']} {m['filetype']}")
            print(f"imports = {len(m['names'])}  classes = {m['classes']}  set sha256 = {m['set_digest']}")
            for lib, n in m["by_library"].items():
                print(f"  {n:6d}  {lib}")
            if args.names:
                for n in m["names"]:
                    rec = m["imports"][n]
                    extra = f"@{rec['version']}" if rec.get("version") else ""
                    print(f"{n}{extra}\t{rec['library']}")
            return 0

        roots = {"build": args.build_dir or default_build_dir(), "atpkg-store": args.atpkg_store or default_atpkg_store()}
        measured: dict[str, dict] = {}
        failures, absent = [], []
        for inp in INPUTS:
            tried, pinned_bytes_seen = [], False
            for path, how in candidates(inp, roots, args.artifact_dir):
                try:
                    m = measure_file(path, inp["target"], work)
                except (Refusal, struct.error, UnicodeDecodeError) as err:
                    tried.append(f"{path}: {err}")
                    pinned_bytes_seen = pinned_bytes_seen or file_sha256(path) == inp["sha256"]
                    continue
                pinned_bytes_seen = pinned_bytes_seen or m["sha256"] == inp["sha256"]
                if m["sha256"] != inp["sha256"]:
                    tried.append(f"{path}: sha256 {m['sha256']} is not the pin {inp['sha256']} (input moved)")
                    continue
                if not any(inp["source_commit"] in k for k in m["version_strings"]):
                    tried.append(f"{path}: source_commit {inp['source_commit']} is not in the artifact's version "
                                 f"strings {sorted(m['version_strings'])}")
                    continue
                measured[inp["id"]] = m
                print(f"measured {inp['id']} ({how}): {len(m['names'])} imports", file=sys.stderr)
                break
            else:
                where = roots[inp["root"]] / inp["path"]
                failures.append(f"{inp['id']}: no candidate matches the pin (pinned path {where}); "
                                + ("; ".join(tried) if tried else "no file at the pinned path or in --artifact-dir"))
                if not pinned_bytes_seen:
                    absent.append(inp["id"])
        if failures:
            for f in failures:
                print(f"imports: REFUSED {f}", file=sys.stderr)
            if len(absent) == len(failures):
                # No failing input's pinned bytes are on this host: the table cannot be re-measured here.
                print(f"imports: UNAVAILABLE: {len(absent)} pinned input(s) are not on this host "
                      f"({', '.join(absent)}); re-measure where build/ or the artifact cache holds them "
                      "(scripts/trust_core/denominators.py --stash copies them, digest-checked)", file=sys.stderr)
                return 3
            return 1
        rows = build_rows(INPUTS, measured)
        try:
            commit = resolve_commit(args.rev)
        except (OSError, subprocess.CalledProcessError):
            print(f"imports: {args.rev} is not a commit of {REPO}", file=sys.stderr)
            return 2
        try:
            prose_facts(measured)
            claims = design_claims(rows, design_text(commit))
            text = render(INPUTS, measured, rows, claims, commit)
        except Refusal as err:
            print(f"imports: REFUSED {err}", file=sys.stderr)
            return 1
        for r in rows:
            print(f"{r['name']:<75} {str(r.get('value', '-')):>6}  {r['status']}")
        for c in claims:
            verdicts = ", ".join(f"{x['row'].split('imports.', 1)[1]}={x['measured']} vs {x['design_value']}"
                                 f" {'reproduces' if x['reproduces'] else 'DIFFERS'}"
                                 + (f" ({x['reading']})" if x["reading"] != "as worded" else "") for x in c["compare"])
            print(f"design:{c['line']} [{c['id']}] {verdicts or 'provenance only'}")
        if args.write:
            table.parent.mkdir(parents=True, exist_ok=True)
            table.write_text(text, encoding="utf-8")
            print(f"imports: wrote {TABLE_REL}", file=sys.stderr)
        if args.check:
            current = table.read_text(encoding="utf-8") if table.is_file() else ""
            # The pin line is what --rev names; every other byte must be reproduced.
            current = MEASURED_AT.sub(f'measured_at_commit = "{commit}"', current, count=1)
            if current != text:
                sys.stderr.writelines(difflib.unified_diff(current.splitlines(True), text.splitlines(True),
                                                           TABLE_REL, "regenerated", n=1))
                print(f"imports: {TABLE_REL} differs from the measurement", file=sys.stderr)
                return 1
            print(f"imports: OK ({len(measured)} inputs, {sum(r['status'] == 'measured' for r in rows)} measured rows, "
                  f"{sum(r['status'] == 'blocked' for r in rows)} blocked rows)", file=sys.stderr)
        return 0
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
