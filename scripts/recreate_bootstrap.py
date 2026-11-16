#!/usr/bin/env python3
"""Recreate the Trust bootstrap — authenticated local Trust first, genesis fallback.

Prefer the active atpkg Trust pack when its exact configured tools and local
offline tree-root authority verify. This is LOCAL CANDIDATE evidence, not fresh
release-signature admission. Its external stage0 tools do not consume archives.
Existing configurations retain their declared mode unless --force-config is used.

Archive path (SEED): materialize the checksum-pinned Trust stage0 seed that
`src/stage0` declares (fetching it from the `trust-stage0-<date>` release via
an authenticated `agh` when absent), validate every payload against the pins
(`scripts/check_seed_freshness.py --require-payloads`, fail-closed), write a
`bootstrap.toml` with NO stage0 override, and drive `./x.py build`. The result
is **trust-from-trust** — stock Rust nowhere in the loop — and no system
`rustc`/`cargo` is required at all.

Fallback path (GENESIS, `--genesis` or when the seed cannot be materialized):
wrap an installed `rustc`/`cargo` into a Trust-named local genesis stage0
adapter and point the stage0 tool keys at it. This is a developer /
first-build convenience only. The produced adapter is *not* release evidence —
see `scripts/create_local_genesis_stage0.py` for the admission boundary.

After a successful build, optionally re-seed `bootstrap/trust-stage0` via the
canonical `prepare.py` so future checkouts skip even the fetch.

For an immutable internal-lineage receipt, pass `--fresh-seed --require-seed`.
This explicitly selects the checksum-pinned archive mode, never local atpkg.
That option safely quarantines any previously extracted `build/<host>/stage0`
before bootstrap-lineage capture so x.py must hydrate the compiler from the
validated archives during the recorded build. A normal retry keeps the honest
`candidate-ready` classification because a pre-existing extracted compiler is
not, by itself, proof of fresh archive materialization.

The receipt of a Stage2+ build (`build/<host>/stage<N>/tool-provenance.json`)
also records the arguments this script was started with, as its
`recreator_invocation`; `scripts/promote-toolchain.sh` names them in the
PROVENANCE of the seal it cuts from that stage.

It also records which LLVM the stage carries, as its `llvm_identity`: the git
identity of the LLVM sources, whether the in-tree LLVM was built in this run or
reused from the build directory, and for a reused one the build record that
says what it was built from. The record is all that is new by default: the
build's exit, what x.py is asked to do and the receipt's status word are what
they were without it, and an LLVM whose identity could not be stated is said so
in the record, not refused. x.py rebuilds LLVM when HEAD:src/llvm-project moves
from the tree recorded beside it, but it keeps an LLVM that cannot say what it
was built from (one built before that record, whose own build header names no
commit this checkout has), and a change to its recipe or config rebuilds none,
so a build that must not carry an LLVM of unstated origin (a seal) passes
`--require-llvm-identity`: it is then refused before x.py starts when the
identity could not be stated, and fails at the end when it was not. An LLVM
linked through `--llvm-config` is recorded as external and its identity is
never stated: the build did not see it built, and nothing it binds says what
it was built from.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import lzma
import os
import platform
import posixpath
import re
import shlex
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace


# Trust: load the extraction-key owner by path, including under isolated -I -S.
_IDENTITY_SPEC = importlib.util.spec_from_file_location(
    "trust_stage0_identity", Path(__file__).resolve().parents[1] / "src/bootstrap/stage0_identity.py",
)
# Bind executable semantics to these source bytes, including under -B: that
# flag suppresses pyc writes but still admits a timestamp-valid cached image.
_IDENTITY_SOURCE = Path(_IDENTITY_SPEC.origin)
if "__trust_source_loader__" in globals():
    _IDENTITY_OWNER = __trust_source_loader__.module("trust_stage0_identity", _IDENTITY_SOURCE)
    _IDENTITY_SOURCE_SHA256 = _IDENTITY_OWNER.__source_sha256__
else:
    _IDENTITY_OWNER = importlib.util.module_from_spec(_IDENTITY_SPEC)
    _IDENTITY_BYTES = _IDENTITY_SOURCE.read_bytes()
    _IDENTITY_SOURCE_SHA256 = hashlib.sha256(_IDENTITY_BYTES).hexdigest()
    exec(compile(_IDENTITY_BYTES, str(_IDENTITY_SOURCE), "exec"),
         _IDENTITY_OWNER.__dict__)
if hashlib.sha256(_IDENTITY_SOURCE.read_bytes()).hexdigest() != _IDENTITY_SOURCE_SHA256:
    raise RuntimeError("stage0 identity source changed while loading")
stage0_extraction_stamp = _IDENTITY_OWNER.extraction_stamp

REEXEC_GUARD_ENV = "TRUST_RECREATE_BOOTSTRAP_REEXEC"

BOOTSTRAP_COMPILER_VERIFICATION = {
    "mode": "disabled",
    "flag": "-Ztrust-verify=off",
    "reason": "bootstrap stability",
    "counts_as_self_proof": False,
}

# The stage receipt's `recreator_invocation` record: the arguments this script
# was started with for the build the receipt describes. Until 2026-10-12 no
# sealed file named them. Three seals were cut that day from builds started
# with `--stage 2 --require-seed --fresh-seed --no-register`, and the only
# record of that line was each job's own unsealed log: the build stamp x.py
# writes says `argv=build --stage 2`, which is x.py's command line, not this
# script's.
#
# It is SELF-REPORTED. No later run can recompute a command line, so
# `--verify-stage-provenance` checks the record's form and nothing more, and
# says so in its help. A receipt without the record (every one written before
# it existed) verifies exactly as it did. The key set is closed: a record with
# another key is not this schema. An argument with a control character is not
# recordable (the seal's PROVENANCE quotes the arguments on one line), so a
# Stage2+ build started with one is refused before anything is built. Every
# other argument is recordable, whatever its length or script: promotion writes
# a non-ASCII character as its UTF-8 bytes in the shell's $'...' form, and
# points at this record when the quoted arguments are too long for a line.
RECREATOR_INVOCATION_SCHEMA = "trust.recreator-invocation.v1"
RECREATOR_INVOCATION_SCOPE = "self-reported"

# THE LLVM A STAGE CARRIES: the stage receipt's `llvm_identity` record.
#
# Until 2026-10-13 x.py did not rebuild the in-tree LLVM for a COMMITTED
# change to it. Its stamp, build/<host>/llvm/.llvm-stamp, is sha256(`git diff
# .` || `git status .` || the LLVM submodule's HEAD) taken in src/llvm-project
# (src/bootstrap/src/utils/build_stamp.rs generate_smart_stamp_hash, called
# from build_steps/llvm.rs prebuilt_llvm_config). Upstream's src/llvm-project
# is a submodule, so a bump moves the third input. Trust vendors the tree: it
# has no .git, the third input is the empty string (utils/channel.rs GitInfo),
# and on a clean checkout the stamp is the constant sha256("") whatever the
# tree holds (measured 2026-10-13: e3b0c442... in the build directory of the
# third seal of 2026-10-12, whose LLVM was built for the first).
# docs/KNOWN_HAZARDS.md, LLVM-STAMP-COMMITTED-1.
#
# Since then bootstrap keeps a record beside the stamp (.trust-llvm-sources;
# src/bootstrap/src/utils/trust_llvm_sources.rs): the git id of
# HEAD:src/llvm-project the build started from, and x.py rebuilds LLVM (and
# LLD) when HEAD's moves from it (through a symlink it stops with an error
# instead). A directory built before that record is
# asked LLVM's own build header: rebuilt when the header names a commit with
# other LLVM sources, KEPT when it names HEAD's or cannot say (no header, no
# commit, one this checkout does not have), and a kept one that cannot say is
# recorded with HEAD's id as `adopted`, which says nothing of what that LLVM
# was built from. Nor does x.py rebuild LLVM for a change to src/bootstrap,
# src/version, the bootstrap config or the native tools. So a seal still needs
# the record below, its own, and cannot take x.py's for it.
#
# On 2026-10-12 two of three seals reused the first one's build directory, and
# with it an LLVM built at another commit. The only guard was a git comparison
# an agent ran by hand; the receipt and the seal's PROVENANCE said nothing.
#
# So a Stage2+ provenance build records which LLVM it carries:
#
# * its SOURCE IDENTITY: the git object ids, at HEAD, of
#   LLVM_SOURCE_IDENTITY_PATHS, and one sha256 over them. It names no commit,
#   so two commits with the same LLVM inputs have the same identity;
# * whether the in-tree LLVM was BUILT IN THIS RUN (build/<host>/llvm did not
#   exist before x.py ran and holds a completed build after) or REUSED (it
#   existed and its installed files are byte for byte what they were);
# * for a reused one, the EVIDENCE: the build record
#   (LLVM_BUILD_RECORD_NAME, in that directory) that a run which watched the
#   directory being built from nothing wrote beside it: the source identity,
#   bootstrap config and native-tool authority LLVM was built with, and a
#   fingerprint of what the build installed. It is evidence only while all
#   four equal this run's.
#
# "The in-tree LLVM" is every directory of LLVM_OUTPUT_ROOTS that is there:
# LLD is built from the same tree into a directory of its own, and its stamp
# says even less (that a build completed once, whatever changed since).
#
# Only an in-tree LLVM can be stated. One linked through `--llvm-config` is
# recorded as mode "external", never stated, with no source identity beside
# it: LLVM_EXTERNAL_REASON, below, says why. Where the bootstrap config does
# not itself say which LLVM x.py links (_llvm_mode), the mode is "unknown",
# never stated, and nothing of this checkout stands beside it either: its
# src/llvm-project may not be what the stage links (since the follow-up of
# 2026-10-13; a record written from 381ac1ea0d until then holds its ids).
#
# BY DEFAULT THE RECORD IS ALL THAT IS NEW. A build whose LLVM identity cannot
# be stated goes ahead on the LLVM that is there, exits as it did, and gets the
# status word it got before the record existed (_classify_receipt_status does
# not read the record): the record says "not stated" and why. NOTHING HERE
# REMOVES OR REWRITES x.py's STAMP (it is only looked for), nothing here deletes
# build output, and nothing about the record can fail a build that did not ask
# for it (audit_stage_tool_provenance writes "not stated" where it could not
# form or leave one). So no ordinary build, the documented `--require-seed
# --fresh-seed` among them, is refused or made to rebuild LLVM by this record.
# NOR CAN ANY STATE OF THE BUILD DIRECTORY CRASH ONE: every step of the record
# that main() runs for a build that did not ask (the observation before x.py,
# the audit's settle_llvm_identity, the verifier's look at the directory)
# turns any exception into "not stated" or a finding, with the reason.
#
# `--require-llvm-identity` IS THE FAIL-CLOSED PART, for the build that makes a
# release claim about its LLVM (a seal): refused before x.py starts when the
# identity is known not to be statable (llvm_identity_refusal, with the command
# that fixes it or the statement that no single command does), and failed at the
# end when the receipt does not state it. `scripts/promote-toolchain.sh
# --require-llvm-identity` refuses to seal a stage whose receipt does not.
#
# WHAT A REUSE COMPARES is deliberately everything the receipt binds, the native
# authority WHOLE. The rows that take part in LLVM's build cannot be selected
# cleanly out of it: the authority is one digest over one object, which
# `--verify-stage-provenance` recomputes for every receipt already written, so
# nothing can be added to it; its dylib closure is one union over every tool's
# roots; and the rows a reader would leave out are not all idle. LLVM's cmake
# runs git for the checkout's HEAD commit and its remote's URL
# (llvm/cmake/modules/VersionFromVCS.cmake; measured 2026-10-13 in the build
# directory of the 10-12 seals: VCSRevision.h holds the first seal's commit and
# the origin URL, and the `llc` the third seal ships carries that commit), finds
# a Python by its own search (`find_package(Python3)`; the authority of those
# seals binds two), and names pkg-config in two of its find modules (read, not
# traced through a configure run). So a reuse is stated only while the
# whole authority is the recorded one, and a change that cannot matter to LLVM
# (Homebrew updating itself moves the `brew` row) un-states it: the cost, under
# the flag, is one LLVM build; without the flag it is a line in the record.
#
# WHAT THE BUILD COMMIT IS TO AN LLVM. Because of that VCSRevision.h, what a
# build installs differs between two commits with the same source identity, and
# `built_at_commit` in a build record is the commit those bytes themselves name.
#
# The paths of the source identity. src/llvm-project is what is compiled.
# src/bootstrap is the recipe: the cmake line is composed in
# build_steps/llvm.rs from configuration the rest of bootstrap parses, and x.py
# does not rebuild LLVM when the recipe changes (its record names only
# src/llvm-project). src/version is in
# LLVM's version suffix. The three are bootstrap's own LLVM_INVALIDATION_PATHS
# (llvm.rs) with the whole of src/bootstrap in place of the one file in it
# upstream bumps by hand. NOT here, because the LLVM build does not read them:
# compiler/rustc_llvm (cargo compiles that wrapper in every stage, against
# this LLVM's headers) and the first-party gitlinks.
LLVM_IDENTITY_SCHEMA = "trust.llvm-identity.v1"
LLVM_SOURCE_IDENTITY_SCHEMA = "trust.llvm-source-identity.v1"
LLVM_BUILD_RECORD_SCHEMA = "trust.llvm-build-record.v1"
LLVM_BUILD_RECORD_NAME = ".trust-llvm-build-record.json"
LLVM_SOURCE_IDENTITY_PATHS = ("src/bootstrap", "src/llvm-project", "src/version")
LLVM_SOURCE_TREE = "src/llvm-project"
# The directories under build/<host> that x.py's own cmake builds of
# src/llvm-project install into, and the stamp x.py leaves in each when the
# build completes (bootstrap `llvm_out` and `lld_out`; build_steps/llvm.rs,
# steps Llvm and Lld). One fingerprint and one build record cover those that
# are there; the first is the one an in-tree build always has.
LLVM_OUTPUT_ROOTS = (("llvm", ".llvm-stamp"), ("lld", ".lld-stamp"))
# What else x.py builds from src/llvm-project outside cargo, per target, in
# layouts this record does not fingerprint (the same file's OmpOffload,
# Sanitizers, CrtBeginEnd and Libunwind steps; their up-to-date checks are no
# better). The recreator's own config builds none of them. Where one is there
# the identity is not stated, rather than stated for part of what is carried.
LLVM_UNCOVERED_OUTPUTS = ("offload", "native/crt", "native/libunwind", "native/sanitizers")
# mode -> the provenance words a record of that mode can carry.
LLVM_PROVENANCE_OF_MODE = {
    "in-tree": ("built-in-this-run", "reused", "changed-in-this-run", "unknown"),
    "external": ("external",),
    "unknown": ("unknown",),
}
LLVM_IDENTITY_KEYS = frozenset({
    "schema", "mode", "provenance", "identity_stated", "reasons", "source_identity_sha256",
    "source_paths", "output_dirs", "output_fingerprint_sha256", "build_record",
})
LLVM_BUILD_RECORD_KEYS = frozenset({
    "schema", "built_at_commit", "host", "source_identity_sha256", "source_paths",
    "bootstrap_config_sha256", "native_authority_sha256", "output_fingerprint_sha256",
})
# The most bytes read_llvm_build_record parses. The record this script writes
# is under two kilobytes; a larger file at that name is not one, and is said to
# be unusable without being read into memory.
LLVM_BUILD_RECORD_MAX_BYTES = 64 * 1024
# AN EXTERNAL LLVM IS NEVER STATED. "Stated" means the build can say which
# sources its LLVM was built from: it watched the LLVM being built from
# nothing, or it reused one beside the record of such a build. Neither is true
# of an LLVM linked through `--llvm-config`. What the build authority binds of
# it is the llvm-config EXECUTABLE (bind_explicit_llvm_config: its path, sha256
# and `--version`) and that file's dylib closure, not the libraries and headers
# it points at; and this checkout's src/llvm-project is not what it was built
# from, so a record of mode external carries no source identity at all. (Until
# the independent re-read of 2026-10-13 such a record was stated whenever the
# authority had bound the llvm-config. The same old build/<host>/llvm that
# `--require-llvm-identity` refuses was then accepted when it was named through
# `--llvm-config`, with this checkout's LLVM source ids beside "stated".)
LLVM_EXTERNAL_REASON = (
    "the stage links an external LLVM through --llvm-config: this build did not watch that LLVM "
    "being built and it carries no record of such a build, and the build authority binds the "
    "llvm-config executable (its path, sha256 and version) and its dylib closure, not the "
    "libraries it points at; so which sources that LLVM was built from is not established, and "
    "this checkout's src/llvm-project does not describe it"
)

BUILD_AUTHORITY_ENV_NAMES = {
    # Mint admits these only with its validated source/Oracle/library closure.
    "CLEAN_OLEAN_PINNED_LEAN_LIB",
    "CLEAN_OLEAN_REQUIRE_PINNED_LEAN",
    "AR",
    "CC",
    "CFLAGS",
    "CPP",
    "CPPFLAGS",
    "CXX",
    "CXXFLAGS",
    "LD",
    "LDFLAGS",
    "LIBRARY_PATH",
    "CPATH",
    "C_INCLUDE_PATH",
    "CPLUS_INCLUDE_PATH",
    "OBJC_INCLUDE_PATH",
    "NM",
    "RANLIB",
    "STRIP",
    "MAKE",
    "MAKEFLAGS",
    "MFLAGS",
    "PKG_CONFIG",
    "PKG_CONFIG_PATH",
    "PKG_CONFIG_LIBDIR",
    "PKG_CONFIG_SYSROOT_DIR",
    # The HOST_/TARGET_ spelling of the pkg-config executable; every other
    # pkg-config spelling is a prefix (BUILD_AUTHORITY_ENV_PREFIXES, "pkg-config").
    "HOST_PKG_CONFIG",
    "TARGET_PKG_CONFIG",
    "CMAKE_GENERATOR",
    "CMAKE_GENERATOR_TOOLSET",
    "CMAKE_GENERATOR_PLATFORM",
    "CMAKE_PREFIX_PATH",
    "CMAKE_TOOLCHAIN_FILE",
    "NINJA_STATUS",
    "LLVM_CONFIG",
    "LLVM_ZSTD_PC_DIR",
    "LLVM_SYS_191_PREFIX",
    "LIBCLANG_PATH",
    "SDKROOT",
    "DEVELOPER_DIR",
    "MACOSX_DEPLOYMENT_TARGET",
    "IPHONEOS_DEPLOYMENT_TARGET",
    "RUSTC",
    "RUSTDOC",
    "RUSTFLAGS",
    "RUSTDOCFLAGS",
    "RUSTC_BOOTSTRAP",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO",
    "CARGOFLAGS",
    "CARGO_HOME",
    "CARGO_BUILD_RUSTC",
    "CARGO_BUILD_RUSTDOC",
    "CARGO_BUILD_RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS",
    "CARGO_TARGET_DIR",
    "RUSTUP_TOOLCHAIN",
    "RUSTUP_HOME",
    "DYLD_LIBRARY_PATH",
    "DYLD_FALLBACK_LIBRARY_PATH",
    "LD_LIBRARY_PATH",
    "SOURCE_DATE_EPOCH",
    "ZERO_AR_DATE",
    # Python, shell, dynamic-loader, and Git repository-discovery injection can
    # replace code or configuration before x.py reaches the compiler.  The Git
    # reads used by provenance are already separately sanitized; the build child
    # must not inherit a different authority surface.
    "PYTHONHOME",
    "PYTHONPATH",
    "VIRTUAL_ENV",
    "BASH_ENV",
    "ENV",
    "LD_PRELOAD",
    "DYLD_INSERT_LIBRARIES",
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_INDEX_FILE",
    "GIT_OBJECT_DIRECTORY",
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_COMMON_DIR",
    "GIT_NAMESPACE",
}

BUILD_AUTHORITY_ENV_PREFIXES = (
    "AR_",
    "CC_",
    "CFLAGS_",
    "CXX_",
    "CXXFLAGS_",
    "LDFLAGS_",
    "CARGO_TARGET_",
    "CCACHE_",
    "SCCACHE_",
    "DISTCC_",
    "GIT_CONFIG_",
    # Bootstrap, rustc, and Targo all have behavior-changing environment
    # switches beyond the small legacy allowlist above.  Release provenance
    # rejects the whole namespaces rather than letting a newly added switch
    # silently escape the receipt.
    "RUST",
    "CARGO_",
    "CARGOFLAGS_",
    "TRUST_",
    "BOOTSTRAP_",
    "DUMP_BOOTSTRAP_",
    # pkg-config, in every spelling a build script's probe reads. The
    # `pkg-config` crate the lockfiles pin (0.3.31 in src/bootstrap/Cargo.lock,
    # 0.3.33 in src/tools/miri/Cargo.lock, 0.3.34 in Cargo.lock and
    # src/tools/targo/Cargo.lock; `Config::targeted_env_var`, the same in all
    # three) looks each of PKG_CONFIG (the executable), PKG_CONFIG_PATH,
    # PKG_CONFIG_LIBDIR, PKG_CONFIG_SYSROOT_DIR (handed on to the executable:
    # its search path and sysroot) and PKG_CONFIG_ALLOW_CROSS (probing for a
    # cross target) up as <NAME>_<target>, then <NAME>_<target with `-` as
    # `_`>, then HOST_<NAME> or TARGET_<NAME>, then <NAME>. Until
    # 2026-10-12 only the four bare names above were refused and scrubbed, so
    # HOST_PKG_CONFIG_PATH or PKG_CONFIG_aarch64_apple_darwin passed the
    # capture and reached x.py, where it could move the search path of the
    # bound pkg-config or run another binary than the one the receipt names.
    # A target-scoped executable is spelled PKG_CONFIG_<target>, so no prefix
    # narrower than PKG_CONFIG_ covers the crate's spellings for every target;
    # the same prefix takes the switches the binary reads itself (pkgconf:
    # PKG_CONFIG_PRELOADED_FILES, PKG_CONFIG_<MODULE>_<VARIABLE>, ...).
    # NOT covered, because they are not pkg-config's: the per-library switches
    # the crate also reads (<LIB>_NO_PKG_CONFIG, <LIB>_STATIC, <LIB>_DYNAMIC),
    # SYSROOT, which the crate falls back to when PKG_CONFIG_SYSROOT_DIR is
    # unset (`parse_libs_cflags`, on a non-macOS host only: the directory whose
    # libraries count as system ones and are therefore never linked
    # statically), and the other knobs of individual -sys build scripts. Those
    # can skip a probe, ask it for static flags or change how its answer is
    # classified; they cannot change which binary runs or where it searches.
    "PKG_CONFIG_",
    "HOST_PKG_CONFIG_",
    "TARGET_PKG_CONFIG_",
)


def ensure_python_311() -> None:
    """Re-exec under a python >= 3.11 when invoked with an older interpreter.

    The recreator itself parses fine on 3.9 (stock macOS python3), but the
    sub-scripts it drives with sys.executable (check_seed_freshness.py, x.py)
    need `tomllib`. Re-execing here — the same pattern as
    fetch_trust_stage0_payloads.py — beats crashing minutes into the run.
    """
    # Apple's /usr/bin/python3 launcher injects these broad search roots before
    # user code starts. They are not user-selected build authority and must not
    # leak through the verified re-exec into native compilation. Normalize only
    # the exact documented CLT defaults; any differing/extended value remains
    # present and is rejected by capture_build_authority.
    executable_text = str(Path(sys.executable))
    apple_clt_python = executable_text in {
        "/usr/bin/python3",
        "/Library/Developer/CommandLineTools/usr/bin/python3",
        "/Applications/Xcode.app/Contents/Developer/usr/bin/python3",
    }
    if platform.system().lower() == "darwin" and apple_clt_python:
        clt_launcher_defaults = {
            "CPATH": "/usr/local/include",
            "LIBRARY_PATH": "/usr/local/lib",
            "SDKROOT": "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk",
        }
        for name, expected in clt_launcher_defaults.items():
            if os.environ.get(name) == expected:
                os.environ.pop(name, None)

    if sys.version_info >= (3, 11):
        return
    if os.environ.get(REEXEC_GUARD_ENV) != "1":
        newer = find_python_ge_311()
        if newer and Path(newer) != Path(sys.executable):
            os.environ[REEXEC_GUARD_ENV] = "1"
            os.execv(newer, [newer, *sys.argv])
    raise SystemExit(
        "recreate-bootstrap needs python >= 3.11 (tomllib) and found "
        f"{sys.version.split()[0]} with no newer interpreter on PATH. "
        "Install one (e.g. `brew install python@3.12`) and re-run."
    )


def line_buffer_output() -> None:
    """Keep parent prints ordered with child-process output when piped.

    Without this, python block-buffers our status lines while subprocesses
    write straight through, so a piped/logged run shows children first and
    the narration at the end.
    """
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(line_buffering=True)
        except (AttributeError, ValueError, OSError):
            pass


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def host_triple() -> str:
    machine = platform.machine().lower()
    system = platform.system().lower()
    if machine in {"arm64", "aarch64"}:
        arch = "aarch64"
    elif machine in {"amd64", "x64", "x86_64"}:
        arch = "x86_64"
    else:
        arch = machine
    if system == "darwin":
        return f"{arch}-apple-darwin"
    if system == "linux":
        return f"{arch}-unknown-linux-gnu"
    # Trust: Windows host support for the pure-bootstrap flow (machine() is
    # "AMD64" on x86_64 Windows, normalized to x86_64 above).
    if system == "windows":
        return f"{arch}-pc-windows-msvc"
    raise SystemExit(f"unsupported host platform: {system}/{machine}")


@dataclass
class Prereq:
    name: str
    path: str | None
    detail: str
    required: bool
    ok: bool
    # Longer guidance printed under the table when this row is what stops the
    # run (print_prereq_notes); the table cell itself stays one line.
    note: str = ""
    # True for a refusal of the native-authority capture that no tool row
    # stands for (native_authority_prereqs): `detail` is the capture's error,
    # verbatim, and print_prereqs() lists it under the table.
    capture_refusal: bool = False


def which(name: str) -> str | None:
    return shutil.which(name)


CONTROLLED_GIT_PATH = "/usr/bin:/bin:/usr/sbin:/sbin"
SUBMODULE_UPDATE_TIMEOUT_SECONDS = 10 * 60
SUBMODULE_UPDATE_OUTPUT_LIMIT_BYTES = 4 * 1024 * 1024
CONTROLLED_GIT_CONFIG_OVERRIDES = (
    f"core.hooksPath={os.devnull}",
    "core.fsmonitor=false",
    "core.untrackedCache=false",
    f"core.attributesFile={os.devnull}",
    f"core.excludesFile={os.devnull}",
    "credential.helper=",
    "credential.interactive=never",
    "http.extraHeader=",
    "http.cookieFile=",
    "http.saveCookies=false",
    "http.proxy=",
    "http.sslVerify=true",
    "protocol.allow=never",
    "protocol.ext.allow=never",
    "protocol.file.allow=never",
    "protocol.git.allow=never",
    "protocol.http.allow=never",
    "protocol.https.allow=always",
    "protocol.ssh.allow=never",
)


def _root_owned_executable_path_chain(path: Path) -> bool:
    """Require root ownership and cross-user immutability for a fixed OS tool."""
    if os.name == "nt" or not path.is_absolute():
        return os.name == "nt"
    current = Path(path.anchor)
    components = path.parts[1:]
    try:
        root_metadata = current.lstat()
    except OSError:
        return False
    if (
        not stat.S_ISDIR(root_metadata.st_mode)
        or root_metadata.st_uid != 0
        or stat.S_IMODE(root_metadata.st_mode) & 0o022
    ):
        return False
    for index, component in enumerate(components):
        current /= component
        try:
            metadata = current.lstat()
        except OSError:
            return False
        if metadata.st_uid != 0:
            return False
        leaf = index + 1 == len(components)
        if stat.S_ISLNK(metadata.st_mode):
            continue
        if leaf:
            if not stat.S_ISREG(metadata.st_mode):
                return False
        elif not stat.S_ISDIR(metadata.st_mode):
            return False
        if stat.S_IMODE(metadata.st_mode) & 0o022:
            return False
    return True


def fixed_git_executable() -> Path | None:
    """Resolve a fixed, OS-owned Git without consulting PATH or Git config.

    On Darwin, ``/usr/bin/git`` is an ``xcrun`` dispatcher whose selected
    developer directory can vary independently of the path being recorded.  Use
    the real CLT/Xcode binary instead.  Linux distributions install the real
    binary at one of the two fixed paths below.  Windows support is limited to
    the standard system-wide Git for Windows installation roots; a PATH-only
    installation is deliberately not provenance authority.
    """
    system = platform.system().lower()
    if system == "darwin":
        candidates = (
            Path("/Library/Developer/CommandLineTools/usr/bin/git"),
            Path("/Applications/Xcode.app/Contents/Developer/usr/bin/git"),
        )
    elif system == "linux":
        candidates = (Path("/usr/bin/git"), Path("/bin/git"))
    elif system == "windows":
        candidates = (
            Path("C:/Program Files/Git/cmd/git.exe"),
            Path("C:/Program Files/Git/bin/git.exe"),
            Path("C:/Program Files (x86)/Git/cmd/git.exe"),
        )
    else:
        candidates = ()

    for candidate in candidates:
        try:
            resolved = candidate.resolve(strict=True)
            metadata = resolved.stat()
        except OSError:
            continue
        if not stat.S_ISREG(metadata.st_mode) or not os.access(resolved, os.X_OK):
            continue
        if os.name != "nt" and (
            metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o022
        ):
            continue
        if os.name != "nt" and (
            not _root_owned_executable_path_chain(candidate)
            or not _root_owned_executable_path_chain(resolved)
        ):
            continue
        if system == "darwin" and resolved == Path("/usr/bin/git"):
            continue
        return resolved
    return None


def _require_fixed_git() -> Path:
    git = fixed_git_executable()
    if git is None:
        raise RuntimeError(
            "no fixed OS-owned Git is available (PATH-selected Git is not "
            "bootstrap/provenance authority)"
        )
    return git


def _controlled_git_command(arguments: list[str] | tuple[str, ...]) -> list[str]:
    command = [str(_require_fixed_git())]
    for override in CONTROLLED_GIT_CONFIG_OVERRIDES:
        command.extend(("-c", override))
    command.extend(arguments)
    return command


def tool_version(
    path: str,
    args: tuple[str, ...] = ("--version",),
    *,
    environment: dict[str, str] | None = None,
    cwd: str | None = None,
) -> str:
    try:
        out = subprocess.run(
            [path, *args],
            text=True,
            capture_output=True,
            check=False,
            env=environment,
            cwd=cwd,
            timeout=10,
        )
        return (out.stdout or out.stderr).splitlines()[0] if (out.stdout or out.stderr) else ""
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return ""


def _no_bytecode_environment() -> dict[str, str]:
    """This process's environment for a Python child that must not write bytecode.

    `--check` and `--verify-stage-provenance` are documented to leave the
    checkout as they found it, and a Python child that imports a module from
    the checkout does not:
    it writes or refreshes `scripts/__pycache__/<module>.cpython-<XY>.pyc`
    beside the module. Until 2026-10-12 a seed-mode `--check` did exactly that
    (check_seed_freshness.py imports scripts/mint_seed_support.py to read a
    bootstrap config). Every Python child this script starts where `--check`
    can reach gets this environment.

    The variable and not `-B` on the child's argv: check_seed_freshness.py
    replaces itself with a newer interpreter when its own has no TOML parser
    (prefer_real_toml_parser: `os.execv(candidate, [candidate, *sys.argv])`),
    and an interpreter option is not in sys.argv, so it would not survive that
    step; the environment does. The variable is not build authority
    (_ambient_build_authority_overrides does not name it) and no build child
    is started with it: run_xpy_build() builds its own environment.

    NOT given it, on purpose:
      * the interpreter ensure_python_311() re-execs into. It is this script
        again, and Python never caches the bytecode of the file it runs as
        `__main__`. The one module of the checkout this script imports into
        its own process is scripts/seed_host_ledger.py, which
        seed_host_ledger_module() loads without a cache
        (create_local_genesis_stage0.py is compiled from its source text by
        _load_genesis_adapter_generator(), and that caches nothing). The same
        holds when no re-exec happens at all;
      * the `--version` identity probes of the native-authority capture
        (`python` in NATIVE_BUILD_TOOLS, the xcrun-selected `python3`). The
        interpreter answers `--version` while it parses its arguments, before
        it imports anything, and their argument vectors are receipt content;
      * create_local_genesis_stage0.py and x.py: `--check` returns before
        either can start.
    """
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    return environment


def find_python_ge_311() -> str | None:
    """Find a python interpreter >= 3.11 (needed for tomllib)."""
    candidates = [
        sys.executable,
        which("python3.14"),
        which("python3.13"),
        which("python3.12"),
        which("python3.11"),
        which("python3"),
    ]
    for cand in candidates:
        if not cand:
            continue
        try:
            out = subprocess.run(
                [cand, "-c", "import sys; print(sys.version_info[:2])"],
                text=True,
                capture_output=True,
                check=True,
                timeout=5,
                # Reached by every `--check`: check_prereqs() asks for the
                # interpreter of its `python ≥ 3.11` row whatever runs this
                # script, and under python < 3.11 ensure_python_311() asks
                # first, before `--check` is parsed.
                env=_no_bytecode_environment(),
            ).stdout.strip()
            if out and tuple(int(x) for x in out.strip("()").split(",")) >= (3, 11):
                return cand
        except (FileNotFoundError, subprocess.CalledProcessError, subprocess.TimeoutExpired):
            continue
    return None


def provenance_build_requested(stage: int, *, no_build: bool) -> bool:
    """Whether these flags ask for a Stage2+ provenance build.

    Only such a build captures source lineage, bootstrap lineage and native
    tool/SDK authority (capture_build_authority) before x.py runs, refuses to
    start when a capture is rejected, and writes a stage receipt. Stage 0/1 and
    `--no-build` never reach a capture. `--check` is deliberately not an input:
    a check reports on the build the same flags would run. The stage0 mode is
    not one either: seed, atpkg and genesis builds all capture.
    """
    return stage >= 2 and not no_build


NATIVE_TOOL_ALWAYS = "always"
# Recorded in the receipt when present, never demanded.
NATIVE_TOOL_OPTIONAL = "optional"


@dataclass(frozen=True)
class NativeBuildTool:
    """One native tool a Stage2+ provenance build binds into its receipt."""

    name: str
    # PATH names tried in order. Empty for the two tools that are deliberately
    # not PATH lookups (_resolve_native_build_tool): git and python.
    candidates: tuple[str, ...]
    identity_args: tuple[str, ...]
    requirement: str
    # How to supply a missing one, as (macOS, Linux), for the prerequisite
    # table's `missing — ...` cell. No other host gets an install hint.
    supply: tuple[str, str] = ("", "")
    # Whether the identity probe's first line is a version worth printing in
    # the prerequisite table. Not every tool's is: macOS `ar --version` and
    # `strip --version` answer with a usage error, which the receipt records
    # verbatim but which must not be printed beside a check mark.
    reports_version: bool = False


_SUPPLY_C_TOOLCHAIN = (
    "`xcode-select --install`",
    "`apt-get install build-essential` (Debian/Ubuntu)",
)

# The `native_tools` rows of a Stage2+ provenance receipt: the PATH tools
# capture_build_authority() binds on every host, and the rows the prerequisite
# report prints for them (name, how to supply a missing one).
#
# It is NOT the whole of what that capture can refuse a build for. On macOS the
# capture also binds xcrun, xcode-select and the tools `xcrun --find` selects
# inside the active developer directory (_darwin_platform_toolchain), the SDK
# and the non-system dylib closure of every tool; on every host it refuses
# ambient build-authority overrides (BUILD_AUTHORITY_ENV_NAMES/_PREFIXES) and
# Cargo configuration it does not own (bootstrap_cargo_authority). The
# prerequisite report keeps no copy of any of that, and none of this table's
# verdicts either: for the invocations that capture
# (provenance_build_requested) it runs the capture itself, read-only, and
# prints what it answered (native_authority_prereqs).
#
# Until 2026-10-12 the report had a hand-kept list of its own, which had
# drifted: it asked for cmake, ninja, a C compiler, git and python, the capture
# also for c++, ar, ld, nm, ranlib, strip, make, perl, pkg-config and sh. So
# `--check` printed "prerequisites OK" for a Stage 2 build the capture then
# refused ("required native build tool is not bound: pkg-config", on a Mac
# without one), and the build itself got as far as that capture: past the seed
# fetch, the config write and the fresh-seed quarantine. Sharing this table
# closed that list and left the macOS one and every non-tool refusal
# unreported; asking the capture closes the class.
#
# NAMES, ORDER AND IDENTITY ARGUMENTS ARE RECEIPT CONTENT (native_tools in
# schema trust.build-authority.v1, hashed into authority_sha256). Changing one
# makes `--verify-stage-provenance` reject every receipt already written.
# Whether a row is required at all is policy, not bookkeeping: do not relax
# one here to make a prerequisite report green.
NATIVE_BUILD_TOOLS: tuple[NativeBuildTool, ...] = (
    NativeBuildTool("cc", ("cc", "clang", "gcc"), ("--version",), NATIVE_TOOL_ALWAYS,
                    _SUPPLY_C_TOOLCHAIN, True),
    NativeBuildTool("c++", ("c++", "clang++", "g++"), ("--version",), NATIVE_TOOL_ALWAYS,
                    _SUPPLY_C_TOOLCHAIN, True),
    NativeBuildTool("ar", ("ar",), ("--version",), NATIVE_TOOL_ALWAYS, _SUPPLY_C_TOOLCHAIN),
    NativeBuildTool("ld", ("ld",), ("-v",), NATIVE_TOOL_ALWAYS, _SUPPLY_C_TOOLCHAIN),
    NativeBuildTool("nm", ("nm",), ("--version",), NATIVE_TOOL_ALWAYS, _SUPPLY_C_TOOLCHAIN),
    NativeBuildTool("ranlib", ("ranlib",), ("--version",), NATIVE_TOOL_ALWAYS,
                    _SUPPLY_C_TOOLCHAIN),
    NativeBuildTool("strip", ("strip",), ("--version",), NATIVE_TOOL_ALWAYS,
                    _SUPPLY_C_TOOLCHAIN),
    NativeBuildTool("make", ("make",), ("--version",), NATIVE_TOOL_ALWAYS,
                    _SUPPLY_C_TOOLCHAIN, True),
    NativeBuildTool("perl", ("perl",), ("-v",), NATIVE_TOOL_ALWAYS,
                    ("macOS ships /usr/bin/perl: put /usr/bin on PATH",
                     "`apt-get install perl` (Debian/Ubuntu)")),
    NativeBuildTool("cmake", ("cmake",), ("--version",), NATIVE_TOOL_ALWAYS,
                    ("`brew install cmake`", "`apt-get install cmake` (Debian/Ubuntu)"), True),
    NativeBuildTool("ninja", ("ninja",), ("--version",), NATIVE_TOOL_ALWAYS,
                    ("`brew install ninja`", "`apt-get install ninja-build` (Debian/Ubuntu)"),
                    True),
    NativeBuildTool("pkg-config", ("pkg-config",), ("--version",), NATIVE_TOOL_ALWAYS,
                    ("`brew install pkgconf`, or a private pkgconf linked as `pkg-config` "
                     "in a directory LAST on PATH (commands in the note below)",
                     "`apt-get install pkg-config` (Debian/Ubuntu)"), True),
    NativeBuildTool("sh", ("sh",), ("--version",), NATIVE_TOOL_ALWAYS,
                    ("macOS ships /bin/sh: put /bin on PATH", "put /bin on PATH")),
    NativeBuildTool("git", (), ("--version",), NATIVE_TOOL_ALWAYS,
                    ("`xcode-select --install` (the fixed OS git; a PATH-only git is not "
                     "provenance authority)",
                     "install git at /usr/bin/git (a PATH-only git is not provenance "
                     "authority)"), True),
    NativeBuildTool("python", (), ("--version",), NATIVE_TOOL_ALWAYS, ("", ""), True),
    NativeBuildTool("brew", ("brew",), ("--version",), NATIVE_TOOL_OPTIONAL),
)

NATIVE_TOOL_RECEIPT_REASON = "the Stage2+ provenance receipt binds it"

# Printed under the prerequisite table when pkg-config is what stops a macOS
# run. It has to stand alone: the public snapshot ships scripts/ and INSTALL.md
# but not docs/ (publish/manifest.txt), so it carries the commands itself and
# points at no other file for them. Each sentence is read out of this file, the
# bootstrap sources or the tool's: the capture binds whatever file PATH
# resolves `pkg-config` to and never asks it for a library
# (_native_tool_record); every pkg-config variable is an ambient override
# (BUILD_AUTHORITY_ENV_PREFIXES, "pkg-config"), and pkgconf takes its search
# path from PKG_CONFIG_PATH, PKG_CONFIG_LIBDIR and otherwise its built-in list
# (libpkgconf/client.c, pkgconf_client_dir_list_build); Homebrew configures its
# pkgconf to search <prefix>/lib/pkgconfig and <prefix>/share/pkgconfig;
# tool.rs records what a probe that finds a Homebrew library did to targo; and
# pkgconf's own `make install` (3.0.8) creates bin/pkgconf, not bin/pkg-config.
PKG_CONFIG_DARWIN_NOTE = """\
pkg-config on macOS (the Command Line Tools do not ship one):
  A Stage2+ provenance build binds the first `pkg-config` on PATH into its receipt
  (path, sha256, non-system dylibs) and refuses to start without one. The capture only
  needs the file to resolve; it never asks it for a library. No PKG_CONFIG_* variable
  (PKG_CONFIG_PATH, PKG_CONFIG_LIBDIR, ...) and no HOST_PKG_CONFIG* or TARGET_PKG_CONFIG*
  one reaches the build: the spellings a build script reads, bare and target-scoped,
  are all refused as ambient build-authority overrides. So the environment can neither
  run another pkg-config nor move its search path, and a probe that passes no path of
  its own sees the .pc files on that binary's built-in search path.
    * `brew install pkgconf` is the short way. Its search path includes Homebrew's .pc
      files, so a build script that probes can resolve, and link, a Homebrew library
      (src/bootstrap/src/core/build_steps/tool.rs, "VENDOR LIBGIT2", records targo
      taking a runtime dependency on Homebrew's libgit2 that way).
    * A pkgconf built with its own `--prefix` searches only that prefix, so a probe for
      any other library still fails, as it does on a Mac that has no pkg-config. Its
      install creates `bin/pkgconf` and no file named `pkg-config`, so link one, alone
      in a directory, and put that directory LAST on PATH for the recreator only:
          ./configure --prefix="$P" --disable-shared && make && make install
          mkdir "$P/pathbin" && ln -s ../bin/pkgconf "$P/pathbin/pkg-config"
          PATH="$PATH:$P/pathbin" python3 scripts/recreate_bootstrap.py --check ...
  `--verify-stage-provenance` binds the tools on PATH again, so verify with the same
  `pkg-config` (same file, same path) in place."""


def _resolve_native_build_tool(tool: NativeBuildTool) -> str | None:
    if tool.name == "git":
        # PATH-selected Git is not provenance authority (fixed_git_executable).
        fixed_git = fixed_git_executable()
        return str(fixed_git) if fixed_git is not None else None
    if tool.name == "python":
        # The interpreter that runs this script is the one that runs x.py.
        return sys.executable
    for candidate in tool.candidates:
        path = which(candidate)
        if path:
            return path
    return None


@dataclass(frozen=True)
class NativeToolBinding:
    tool: NativeBuildTool
    required: bool
    # The receipt row: exactly what capture_build_authority() records.
    record: dict[str, object]

    @property
    def bound(self) -> bool:
        return self.record.get("status") == "bound"


def bind_native_build_tools() -> list[NativeToolBinding]:
    """Resolve and bind every NATIVE_BUILD_TOOLS row, in receipt order.

    The single reader of the table, called by capture_build_authority() only.
    "Present" means bound: resolved and hashable, not merely named on PATH.
    """
    bindings: list[NativeToolBinding] = []
    for tool in NATIVE_BUILD_TOOLS:
        required = tool.requirement == NATIVE_TOOL_ALWAYS
        record = _native_tool_record(
            tool.name, _resolve_native_build_tool(tool), tool.identity_args
        )
        record["required"] = required
        bindings.append(NativeToolBinding(tool, required, record))
    return bindings


EXPLICIT_LLVM_CONFIG = "llvm-config"


def bind_explicit_llvm_config(llvm_config: str | None) -> dict[str, object] | None:
    """The receipt row for `--llvm-config`, or None when LLVM is built in-tree."""
    if llvm_config is None:
        return None
    return _native_tool_record(EXPLICIT_LLVM_CONFIG, llvm_config, ("--version",))


def native_tool_refusal(name: str) -> str:
    """The capture's error for a required tool row, or `--llvm-config`, that is not bound.

    One spelling, two users: the capture writes it into its errors
    (native_tool_refusals) and the prerequisite report looks for it there to
    know which printed row a refusal belongs to (native_authority_prereqs). A
    capture error that is not one of these needs no entry anywhere: the report
    prints it under the table, verbatim.
    """
    if name == EXPLICIT_LLVM_CONFIG:
        return "explicit llvm-config is not bound"
    return f"required native build tool is not bound: {name}"


def native_tool_refusals(
    bindings: list[NativeToolBinding],
    selected_llvm: dict[str, object] | None,
) -> dict[str, str]:
    """Tool name -> the refusal its binding earns a Stage2+ provenance build."""
    refusals = {
        binding.tool.name: native_tool_refusal(binding.tool.name)
        for binding in bindings
        if binding.required and not binding.bound
    }
    if selected_llvm is not None and selected_llvm.get("status") != "bound":
        refusals[EXPLICIT_LLVM_CONFIG] = native_tool_refusal(EXPLICIT_LLVM_CONFIG)
    return refusals


# The `name` of a prerequisite row that carries a capture refusal no tool row
# stands for (Prereq.capture_refusal).
NATIVE_AUTHORITY_REFUSAL = "native authority"


def native_authority_prereqs(authority: dict[str, object]) -> list[Prereq]:
    """One capture_build_authority() answer as prerequisite rows.

    This function decides nothing. The rows are the capture's own
    `native_tools` records (and its `selected_llvm`), printed with the table's
    supply hints; a row fails exactly when the capture's errors hold that
    tool's refusal. Every other error the capture returned becomes a
    `capture_refusal` row whose detail is that error, verbatim. So the set of
    failing rows is the capture's error list: these rows fail exactly when,
    and for exactly the reasons, the capture refuses, and there is no list
    here that could drift from it, on any host.
    """
    system = platform.system().lower()
    table = {tool.name: tool for tool in NATIVE_BUILD_TOOLS}
    unclaimed = [str(error) for error in authority.get("errors", [])]

    def refused(name: str) -> bool:
        refusal = native_tool_refusal(name)
        if refusal in unclaimed:
            unclaimed.remove(refusal)
            return True
        return False

    rows: list[Prereq] = []
    native_tools = authority.get("native_tools")
    for record in native_tools if isinstance(native_tools, list) else []:
        name = str(record.get("name"))
        tool = table.get(name)
        if tool is not None and tool.requirement == NATIVE_TOOL_OPTIONAL:
            # Recorded in the receipt when present, never demanded.
            continue
        bound = record.get("status") == "bound"
        required = bool(record.get("required"))
        local_path = record.get("resolved_local_path")
        path = local_path if isinstance(local_path, str) and local_path else None
        note = ""
        if bound:
            identity = record.get("identity")
            detail = (
                identity
                if tool is not None
                and tool.reports_version
                and isinstance(identity, str)
                and identity
                else "bound"
            )
        elif not required:
            detail = "optional"
        elif path is None:
            supply = (
                {"darwin": tool.supply[0], "linux": tool.supply[1]}.get(system, "")
                if tool is not None
                else ""
            )
            detail = "missing — " + (f"{supply}; " if supply else "") + NATIVE_TOOL_RECEIPT_REASON
            if name == "pkg-config" and system == "darwin":
                note = PKG_CONFIG_DARWIN_NOTE
        else:
            detail = (
                f"found but cannot be bound ({record.get('error', 'unreadable')}); "
                + NATIVE_TOOL_RECEIPT_REASON
            )
        rows.append(Prereq(name, path, detail, required, not refused(name), note))
    selected_llvm = authority.get("selected_llvm")
    if isinstance(selected_llvm, dict):
        llvm_path = selected_llvm.get("resolved_local_path")
        llvm_refused = refused(EXPLICIT_LLVM_CONFIG)
        if llvm_refused:
            detail = (
                "not a readable llvm-config — fix the --llvm-config path; "
                + NATIVE_TOOL_RECEIPT_REASON
            )
        else:
            identity = selected_llvm.get("identity")
            detail = identity if isinstance(identity, str) and identity else "bound"
        rows.append(
            Prereq(
                EXPLICIT_LLVM_CONFIG,
                llvm_path if isinstance(llvm_path, str) and llvm_path else None,
                detail,
                True,
                not llvm_refused,
            )
        )
    rows.extend(
        Prereq(NATIVE_AUTHORITY_REFUSAL, None, error, True, False, capture_refusal=True)
        for error in unclaimed
    )
    if authority.get("status") != "ready" and all(row.ok for row in rows):
        # Unreachable while the capture derives its status from its errors;
        # kept so that a rejected capture can never read as a green report.
        rows.append(
            Prereq(
                NATIVE_AUTHORITY_REFUSAL,
                None,
                f"the capture answered status {authority.get('status')!r} without an error",
                True,
                False,
                capture_refusal=True,
            )
        )
    return rows


# Which rows check_prereqs() returns. A Stage2+ provenance build decides the
# rows that do not depend on the stage0 mode BEFORE it selects one, because
# selecting is where a build fetches the seed archives: a build that would be
# refused for a missing tool is refused before any download. Every other
# invocation keeps the one table it always printed, after the selection.
PREREQS_ALL = "all"
PREREQS_BEFORE_SELECTION = "before-selection"
PREREQS_OF_SELECTED_MODE = "selected-mode"


def check_prereqs(
    llvm_config: str | None = None,
    seed_mode: bool = False,
    require_rustup: bool = False,
    native_authority: bool = False,
    *,
    root: Path | None = None,
    host: str | None = None,
    phase: str = PREREQS_ALL,
    seed_selection: Stage0Selection | None = None,
) -> list[Prereq]:
    """Report what the invocation needs before it writes or builds anything.

    `native_authority` says the invocation is a Stage2+ provenance build
    (provenance_build_requested), which will run capture_build_authority()
    before x.py and refuse to start if it is rejected. The native rows are then
    that capture's own answer for `root`/`host`/`llvm_config`, obtained by
    running it here (it only reads: tools, SDK, environment, Cargo
    configuration paths), so they fail exactly when, and for the reasons, the
    build's capture would refuse (native_authority_prereqs). Any other
    invocation never runs the capture and keeps the short list x.py itself has
    always needed here: cmake, ninja, a C compiler and git.

    The capture answers for the machine as it is now. The build's two other
    pre-build captures are not previewed, because each needs a step a check
    does not perform: source lineage needs the first-party submodules
    materialized (ensure_submodules), bootstrap lineage needs the written
    bootstrap config (write_config) and, with --fresh-seed, the stage0
    quarantine.

    `phase` selects the rows: PREREQS_BEFORE_SELECTION is everything that does
    not depend on the stage0 mode (native rows, python, rustup),
    PREREQS_OF_SELECTED_MODE the rest (stock rustc/cargo in genesis mode,
    selected Trust seed runtime on macOS), PREREQS_ALL both.
    """
    checks: list[Prereq] = []
    mode_rows = phase in (PREREQS_ALL, PREREQS_OF_SELECTED_MODE)
    independent_rows = phase in (PREREQS_ALL, PREREQS_BEFORE_SELECTION)
    # A system Rust toolchain is only needed to mint the GENESIS adapter. Do
    # not even present stock rustc/cargo as prerequisites in seed mode: the
    # pinned Trust seed is the complete stage0 authority. GENESIS ADAPTER
    # (developer adapter, never release evidence; retiring it is an owner
    # decision, 2026-09-28).
    if mode_rows and not seed_mode:
        rustc = which("rustc")
        cargo = which("cargo")
        # Probed from the filesystem root: a rustup proxy run from the checkout would
        # read the dev tree's channel = "trust" pin instead of the host Rust.
        neutral = os.path.abspath(os.sep)
        checks.extend(
            [
                Prereq("rustc", rustc, tool_version(rustc, cwd=neutral) if rustc else "missing", True, bool(rustc)),
                Prereq("cargo", cargo, tool_version(cargo, cwd=neutral) if cargo else "missing", True, bool(cargo)),
            ]
        )
    if independent_rows and native_authority:
        checks.extend(
            native_authority_prereqs(
                capture_build_authority(
                    root if root is not None else repo_root(),
                    host if host is not None else host_triple(),
                    llvm_config,
                )
            )
        )
    elif independent_rows:
        cmake = which("cmake")
        ninja = which("ninja")
        # `cl` is MSVC's C/C++ compiler; on Windows it is the canonical toolchain
        # (put on PATH by a VS/Build-Tools environment, e.g. the portable envrun).
        cc = which("cc") or which("clang") or which("gcc") or which("cl")
        fixed_git = fixed_git_executable()
        git = str(fixed_git) if fixed_git is not None else None
        # The generated compiler profile builds LLD with CMake/Ninja even
        # when --llvm-config supplies an external LLVM provider.
        checks.extend([
            Prereq("cmake", cmake, (tool_version(cmake) if cmake else "missing — `brew install cmake`"), True, bool(cmake)),
            Prereq("ninja", ninja, (tool_version(ninja) if ninja else "missing — `brew install ninja`"), True, bool(ninja)),
            Prereq("C compiler", cc, tool_version(cc) if cc else "missing", True, bool(cc)),
            Prereq(
                "git",
                git,
                tool_version(git, environment=_provenance_git_environment())
                if git
                else "missing",
                True,
                bool(git),
            ),
        ])
    if independent_rows:
        py = find_python_ge_311()
        checks.append(
            Prereq(
                "python ≥ 3.11",
                py,
                tool_version(py) if py else "missing — install python@3.11 or newer",
                True,
                bool(py),
            )
        )
        rustup = find_rustup()
        checks.append(
            Prereq(
                "rustup",
                rustup,
                tool_version(rustup)
                if rustup
                else (
                    "missing — `brew install rustup` (required for toolchain registration)"
                    if require_rustup
                    else "not needed for this non-registering invocation"
                ),
                require_rustup,
                bool(rustup) or not require_rustup,
            )
        )
    if mode_rows and seed_mode and platform.system().lower() == "darwin":
        if seed_selection is not None and root is not None:
            checks.append(selected_seed_runtime_prereq(root, host or host_triple(), seed_selection))
        else:
            checks.append(Prereq("stage0 runtime", None,
                                 "select the Trust seed before inspecting its runtime", True, False))
    return checks


def selected_seed_runtime_prereq(root: Path, host: str, selection: Stage0Selection) -> Prereq:
    """Inspect the selected Targo's actual runtime, not a historical Homebrew dependency.

    Normal bootstrap always enables vendored-libgit2 (or all-static) for newly
    built Targo. The selected seed can be older, so its real dependency closure
    must still resolve. This preflight grants no seed or release authority.
    """
    source = None
    try:
        otool = which("otool")
        if otool is None:
            raise RuntimeError("otool is required to inspect the selected seed runtime")

        def inspect(binary: Path) -> str:
            if not binary.is_file() or not _is_macho(binary):
                raise RuntimeError("selected seed Targo is not a Mach-O executable")
            closure = _capture_darwin_dynamic_dependencies([binary], Path(otool))
            if closure.get("status") != "ready":
                raise RuntimeError("; ".join(str(e) for e in closure.get("errors", []))
                                   or "selected seed runtime closure was rejected")
            return f"selected Targo runtime resolved ({len(closure['dependencies'])} non-system libraries)"

        if selection.mode == "atpkg":
            pack = selection.atpkg_root
            if pack is None:
                raise RuntimeError("selected atpkg seed authority is unavailable")
            source = pack / "bin" / "targo"
            return Prereq("stage0 runtime", str(source), inspect(source), True, True)
        if selection.mode != "seed":
            raise RuntimeError("runtime preflight requires the selected Trust seed")
        pins, payloads = parse_stage0_pins(root)
        filename = f"targo-{pins.get('compiler_version', '')}-{host}.tar.xz"
        relative = f"dist/{pins.get('compiler_date', '')}/{filename}"
        expected = payloads.get(relative)
        if expected is None:
            raise RuntimeError("src/stage0 does not pin the selected Targo archive")
        source = root / "bootstrap" / "trust-stage0" / relative
        if source.is_symlink() or not source.is_file():
            raise RuntimeError("selected Targo archive is not a regular non-symlink file")
        # Hash and inspect the same copied bytes, without executing the seed or
        # modifying its installed/hydrated tree. Refuse unbounded archives and
        # links/duplicate entries instead of guessing a different executable.
        with tempfile.TemporaryFile() as snapshot:
            digest = hashlib.sha256()
            total = 0
            with source.open("rb") as archive:
                for chunk in iter(lambda: archive.read(1024 * 1024), b""):
                    total += len(chunk)
                    if total > 512 * 1024 * 1024:
                        raise RuntimeError("selected Targo archive exceeds runtime-probe bound")
                    digest.update(chunk)
                    snapshot.write(chunk)
            if digest.hexdigest() != expected:
                raise RuntimeError("selected Targo archive differs from its src/stage0 digest")
            snapshot.seek(0)
            with tarfile.open(fileobj=snapshot, mode="r:xz") as bundle:
                prefix = f"{filename.removesuffix('.tar.xz')}/targo"
                member_path = f"{prefix}/bin/targo"
                matches = []
                members = []
                names = set()
                expanded = 0
                for index, member in enumerate(bundle):
                    expanded += member.size
                    if index >= 100_000 or member.size < 0 or expanded > 512 * 1024 * 1024:
                        raise RuntimeError("selected Targo archive exceeds expanded runtime-probe bounds")
                    if member.name == member_path:
                        matches.append(member)
                    if member.name == prefix or member.name.startswith(prefix + "/"):
                        normalized = posixpath.normpath(member.name)
                        if (normalized != member.name or member.name in names
                                or not (member.isdir() or member.isfile()
                                        or member.issym() or member.islnk())):
                            raise RuntimeError("unsafe or duplicate selected Targo subtree entry")
                        names.add(member.name)
                        if member.issym() or member.islnk():
                            target = posixpath.normpath(
                                posixpath.join(posixpath.dirname(member.name), member.linkname)
                                if member.issym() else member.linkname
                            )
                            if target != prefix and not target.startswith(prefix + "/"):
                                raise RuntimeError("selected Targo subtree link escapes its component")
                        members.append(member)
                if len(matches) != 1 or not matches[0].isfile():
                    raise RuntimeError("selected Targo archive must contain one regular Targo executable")
                member = matches[0]
                if member.size > 256 * 1024 * 1024:
                    raise RuntimeError("selected Targo executable exceeds runtime-probe bound")
                if not hasattr(tarfile, "data_filter"):
                    raise RuntimeError("selected seed runtime requires Python's safe tar data filter")
                with tempfile.TemporaryDirectory(prefix="trust-seed-runtime-") as directory:
                    # Preserve the selected install layout: @loader_path and
                    # @executable_path can legitimately name bundled dylibs.
                    # Only this bounded, link-checked component is materialized.
                    bundle.extractall(directory, members=members, filter=tarfile.data_filter)
                    binary = Path(directory) / member_path
                    detail = inspect(binary)
        return Prereq("stage0 runtime", str(source), detail, True, True)
    except (OSError, RuntimeError, ValueError, KeyError, EOFError, tarfile.TarError, lzma.LZMAError) as error:
        return Prereq("stage0 runtime", str(source) if source else None, str(error), True, False)


def print_prereqs(prereqs: list[Prereq]) -> None:
    rows = [p for p in prereqs if not p.capture_refusal]
    width = max((len(p.name) for p in rows), default=0)
    for p in rows:
        mark = "✓" if p.ok else "✗"
        path = p.path or "(not found)"
        print(f"  {mark} {p.name:<{width}} {path}  — {p.detail}")
    refusals = [p for p in prereqs if p.capture_refusal]
    if refusals:
        # Not tool rows: whatever else the capture refuses for (ambient
        # overrides, unowned Cargo configuration, the macOS developer directory,
        # SDK and dylib closure), in the words the build itself would print.
        print("  Refused by the pre-build native tool and SDK authority capture, in its own words:")
        for p in refusals:
            print(f"  ✗ {p.detail}")


def print_prereq_notes(prereqs: list[Prereq]) -> None:
    """Print the longer guidance of the given (missing) prerequisites, once each."""
    for note in dict.fromkeys(p.note for p in prereqs if p.note):
        print()
        print(note)


def report_unmet_prereqs(prereqs: list[Prereq]) -> bool:
    """Say what in the printed prerequisite rows stops the run; True if anything does."""
    unmet = [p for p in prereqs if p.required and not p.ok]
    missing = [p for p in unmet if not p.capture_refusal]
    refused = [p for p in unmet if p.capture_refusal]
    if missing:
        print(f"\n{len(missing)} required prerequisite(s) missing. Install them and re-run.")
    if refused:
        print(
            f"\n{len(refused)} native-authority refusal(s). A Stage2+ build with these flags "
            "stops at that capture for each of them; clear them and re-run."
        )
    print_prereq_notes(missing)
    return bool(unmet)


def ensure_local_genesis_stage0(root: Path, host: str, force: bool) -> Path:
    """Run create_local_genesis_stage0.py to materialize build/<host>/genesis-stage0.

    The adapter must live OUTSIDE bootstrap.py's managed bin_root
    (build/<host>/stage0): download_toolchain() wipes and re-downloads any
    configured stage0 rustc/cargo under that root whenever the pinned stage0
    identity advances (rustc-stamp mismatch), which deletes the genesis adapter
    and reintroduces the missing-payload failure this script exists to solve.
    A stamped-empty stage0 dir also makes the no-force "reuse" path a trap, so
    reuse only a root that actually contains bin/trustc.
    """
    out = root / "build" / host / "genesis-stage0"
    if (out / "bin" / "trustc").exists() and not force:
        print(f"  reusing existing genesis stage0 at {out}")
        return out
    script = root / "scripts" / "create_local_genesis_stage0.py"
    args = [
        sys.executable, str(script), "--repo-root", str(root), "--host", host,
        "--out", str(out), "--force",
    ]
    subprocess.run(args, check=True)
    return out


def parse_stage0_pins(root: Path) -> tuple[dict[str, str], dict[str, str]]:
    """Parse `src/stage0` into (scalar pins, payload-path -> sha256 map)."""
    pins: dict[str, str] = {}
    payloads: dict[str, str] = {}
    stage0 = root / "src" / "stage0"
    if not stage0.is_file():
        return pins, payloads
    for line in stage0.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        key, _, value = line.partition("=")
        if key.startswith("dist/"):
            payloads[key] = value
        else:
            pins[key] = value
    return pins, payloads


def missing_seed_payloads(root: Path, payloads: dict[str, str]) -> list[str]:
    base = root / "bootstrap" / "trust-stage0"
    return [rel for rel in payloads if not (base / rel).is_file()]


def seed_ledger_release(root: Path) -> tuple[str, str] | None:
    """Read (repo, tag) from the seed ledger's `[release]` block.

    `bootstrap/trust-stage0/seed-ledger.toml` is the checked-in declaration of
    where the admitted-internal seed lives (the same source
    scripts/fetch_trust_stage0_payloads.py consumes), so fetching from it
    invents nothing.
    """
    import tomllib  # main() re-execs onto python >= 3.11 before this runs

    ledger = root / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
    if not ledger.is_file():
        return None
    try:
        data = tomllib.loads(ledger.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError):
        return None
    release = data.get("release")
    if not isinstance(release, dict):
        return None
    repo, tag = release.get("repo"), release.get("tag")
    if not isinstance(repo, str) or not isinstance(tag, str) or not repo or not tag:
        return None
    return repo, tag


SEED_LEDGER = Path("bootstrap") / "trust-stage0" / "seed-ledger.toml"


def minted_seed_pin(root: Path) -> str | None:
    """Why `src/stage0` is a minted pin, or None while it is not (D12 (d)).

    The seed ledger gains a `[release.mint]` table (`[release.hosts."<host>".mint]`
    in a multi-host ledger) only with a re-pin that `scripts/mint_and_prove_seed.sh`
    minted (docs/CUTTING-A-TOOLCHAIN.md §3.9); aterm's seed-pin gate switches on
    at the same table. A host table carrying `root_disclosure` (a first Linux seed
    admitted as a fixed point, docs/PLAN.md PKG-S6) pins the seed just as much,
    though it has no mint: a ledger whose only record is that one still retires
    both. From that commit on, the recreator's atpkg stage0 mode (a
    local seed override, which D12 refuses) is retired, and so is the stock-rust
    genesis fallback: the pin is the only seed and `--genesis` the only way to the
    adapter. Until then the mode stays: the owner's recorded choice for the
    pending pack cut (path P, §1.0 of
    docs/issues/2026-09-30-release-train-handoff-m2-m3.md) seeds from it.

    Only the table's presence is read: it decides what is offered, never what is
    proved, and the cut's own tools validate the record. A ledger that exists but
    cannot be read counts as minted (fail-closed: the pin is then the seed).
    """
    import tomllib  # main() re-execs onto python >= 3.11 before this runs

    ledger = root / SEED_LEDGER
    if not os.path.lexists(ledger):
        return None
    if ledger.is_symlink() or not ledger.is_file():
        return f"{SEED_LEDGER} is not a regular file, so it is read as a minted pin"
    try:
        data = tomllib.loads(ledger.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        return f"{SEED_LEDGER} cannot be read ({error}), so it is read as a minted pin"
    release = data.get("release")
    if not isinstance(release, dict):
        return None
    if "mint" in release:
        return f"{SEED_LEDGER} records the cut that minted the pin ([release.mint])"
    hosts = release.get("hosts")
    if isinstance(hosts, dict):
        for host in sorted(hosts):
            record = hosts[host]
            if not isinstance(record, dict):
                return (f'{SEED_LEDGER} [release.hosts."{host}"] is not a table, '
                        "so it is read as a minted pin")
            if "mint" in record:
                return (f"{SEED_LEDGER} records the cut that minted the pin "
                        f'([release.hosts."{host}".mint])')
            if "root_disclosure" in record:
                return (f"{SEED_LEDGER} records a seed admitted as a fixed point of an unpinned "
                        f'host chain ([release.hosts."{host}".root_disclosure])')
    elif hosts is not None:
        return f"{SEED_LEDGER} [release.hosts] is not a table, so it is read as a minted pin"
    return None


def fetch_seed_payloads(root: Path, date: str, attempts: int = 2) -> bool:
    """Fetch the exact pinned seed assets into the canonical dist dir via `agh`.

    The release coordinates come from the seed ledger
    (`bootstrap/trust-stage0/seed-ledger.toml` `[release]`), so the download
    uses agh's repository-specific credential routing. Integrity does NOT depend
    on this transport: every payload is re-hashed against the `src/stage0`
    SHA-256 pins by `validate_seed` afterwards.
    """
    agh = which("agh")
    aterm = None if agh else which("aterm")
    if not agh and not aterm:
        print("  agh or aterm not found — cannot fetch the pinned Trust seed release")
        return False
    client = [agh] if agh else [aterm, "agh"]
    release = seed_ledger_release(root)
    if release is None:
        print("  seed ledger declares no [release]; cannot fetch the pinned seed")
        return False
    repo, tag = release
    _, payloads = parse_stage0_pins(root)
    prefix = f"dist/{date}/"
    assets = []
    for relative in sorted(payloads):
        asset = relative.removeprefix(prefix)
        if not relative.startswith(prefix) or not re.fullmatch(
            r"[A-Za-z0-9][A-Za-z0-9._+-]*\.tar\.xz", asset
        ):
            print(f"  unsupported pinned seed asset path: {relative}")
            return False
        assets.extend(["--asset", asset])
    if not assets:
        print("  src/stage0 declares no pinned seed assets; refusing a wildcard download")
        return False
    dest = root / "bootstrap" / "trust-stage0" / "dist" / date
    dest.mkdir(parents=True, exist_ok=True)
    for attempt in range(1, attempts + 1):
        rc = subprocess.run(
            [
                *client, "release", "download", repo, tag,
                *assets, "--dir", str(dest), "--clobber",
            ],
            cwd=str(root),
        ).returncode
        if rc == 0:
            return True
        print(f"  agh release download {repo} {tag} failed (attempt {attempt}/{attempts})")
    return False


def _seed_transport():
    # Use the same reviewed admission/lifetime owner as the checker and land.
    # This path comes from this script, including under isolated Python.
    library = str(Path(__file__).resolve().parent / "lib")
    if library not in sys.path:
        sys.path.insert(0, library)
    import native_serial
    return native_serial


def _run_seed_checker(command, *, env, cwd, capture_output=True, text=True):
    """Run the maintained checker without inventing a native Windows owner."""
    transport = _seed_transport()
    if sys.platform == "win32":
        if transport.landing_targo.resource_fds(env):
            raise RuntimeError("Windows seed checker cannot inherit native POSIX custody")
        # The checker refuses actual Windows compiler execution separately;
        # this preserves its supported metadata/payload-only subprocess path.
        return subprocess.run(command, env=env, cwd=cwd,
                              capture_output=capture_output, text=text)
    return transport.run_custodied_command(command, env=env, cwd=cwd,
                                           capture_output=capture_output, text=text)


def validate_seed(root: Path, host: str | None = None) -> bool:
    """Fail-closed digest validation of the materialized seed payloads."""
    rc = _run_seed_checker(
        [sys.executable, str(root / "scripts" / "check_seed_freshness.py"),
         "--require-payloads", "--host", host or host_triple()],
        cwd=str(root),
        # Reached by `--check` whenever the pinned payloads are on disk.
        env=_no_bytecode_environment(),
        capture_output=False,
    ).returncode
    return rc == 0


def resolve_seed(root: Path, allow_fetch: bool, host: str | None = None) -> bool:
    """Materialize + validate the pinned Trust stage0 seed. True = usable."""
    pins, payloads = parse_stage0_pins(root)
    date = pins.get("compiler_date")
    if not date or not payloads:
        print("  src/stage0 declares no pinned Trust seed payloads")
        return False
    missing = missing_seed_payloads(root, payloads)
    if missing:
        print(f"  {len(missing)}/{len(payloads)} pinned payloads not materialized")
        if not allow_fetch:
            return False
        print("  fetching the seed release declared in the seed ledger ...")
        if not fetch_seed_payloads(root, date):
            return False
        missing = missing_seed_payloads(root, payloads)
        if missing:
            print(f"  still missing after fetch: {missing}")
            return False
    print("  validating payload digests against src/stage0 (fail-closed) ...")
    return validate_seed(root, host)


# The one symlink `build` may be: a link to the sibling REAL directory
# `build.noindex`, whose name keeps Spotlight from indexing hundreds of GiB of
# build output (docs/BUILD_AND_INSTALL.md, "Keeping Spotlight out of build/").
# Every other link is still refused. Same predicate as mint_seed_support.py;
# scripts/tests/build_dir_symlink_test.py drives every copy over one fixture.
BUILD_NOINDEX = "build.noindex"


def is_sanctioned_build_link(root: Path) -> bool:
    """True iff `root/build` is a symlink resolving to the real `root/build.noindex`."""
    lexical = root / "build"
    try:
        if not stat.S_ISLNK(os.lstat(lexical).st_mode):
            return False
        physical = root.resolve(strict=True) / BUILD_NOINDEX
        if not stat.S_ISDIR(os.lstat(physical).st_mode):
            return False
        return lexical.resolve(strict=True) == physical
    except (OSError, RuntimeError):
        return False


def quarantine_seed_stage0(root: Path, host: str) -> Path | None:
    """Move an extracted seed aside so provenance can observe fresh hydration.

    The move is same-filesystem and recoverable.  It deliberately targets only
    the exact generated `build/<host>/stage0` directory; pinned archives remain
    untouched.  The caller removes the quarantine only after the stage-tool
    receipt passes direct immutable-lineage verification.
    """
    host_component = Path(host)
    if (
        not host
        or host_component.is_absolute()
        or host_component.parts != (host,)
        or host in {".", ".."}
    ):
        raise RuntimeError(f"unsafe host component for fresh seed materialization: {host!r}")
    build_root = root / "build"
    if build_root.is_symlink() and not is_sanctioned_build_link(root):
        raise RuntimeError(f"fresh seed build directory must not be a symlink: {build_root}")
    host_root = build_root / host
    if host_root.is_symlink():
        raise RuntimeError(f"fresh seed host directory must not be a symlink: {host_root}")
    try:
        host_root.resolve(strict=False).relative_to(build_root.resolve(strict=False))
    except (OSError, ValueError) as error:
        raise RuntimeError(
            f"fresh seed host directory escapes the checkout build root: {host_root}"
        ) from error
    stage0 = host_root / "stage0"
    quarantine = stage0.with_name("stage0.preexisting-fresh-seed")
    if os.path.lexists(quarantine):
        if quarantine.is_symlink() or not quarantine.is_dir():
            raise RuntimeError(f"fresh seed backup is not a real directory: {quarantine}")
        if os.path.lexists(stage0):
            raise RuntimeError(
                "an interrupted fresh-seed run left both the replacement and backup; "
                f"refusing to choose or delete either: {stage0}, {quarantine}"
            )
        print(f"  resuming interrupted fresh-seed quarantine -> {quarantine}")
        print("  x.py must now hydrate stage0 from the checksum-validated archives")
        return quarantine
    if not os.path.lexists(stage0):
        print(f"  fresh seed requested; {stage0} is already absent")
        return None
    if stage0.is_symlink() or not stage0.is_dir():
        raise RuntimeError(f"fresh seed target must be a real directory: {stage0}")

    try:
        os.replace(stage0, quarantine)
    except OSError as error:
        raise RuntimeError(
            f"could not quarantine pre-existing seed compiler {stage0}: {error}"
        ) from error
    print(f"  quarantined pre-existing seed compiler -> {quarantine}")
    print("  x.py must now hydrate stage0 from the checksum-validated archives")
    return quarantine


def recover_seed_stage0_quarantine(
    root: Path,
    host: str,
    quarantine: Path | None,
) -> None:
    """Restore the quarantine only when no replacement stage0 was materialized."""
    if quarantine is None or not os.path.lexists(quarantine):
        return
    stage0 = root / "build" / host / "stage0"
    if os.path.lexists(stage0):
        print(f"  preserved failed-run seed backup at {quarantine}")
        return
    try:
        os.replace(quarantine, stage0)
    except OSError as error:
        print(f"  WARNING: could not restore seed backup {quarantine}: {error}")
        return
    print(f"  restored pre-existing seed compiler after failed setup -> {stage0}")


def discard_seed_stage0_quarantine(
    root: Path,
    host: str,
    quarantine: Path | None,
) -> None:
    """Remove the generated backup after fresh hydration passes provenance."""
    if quarantine is None or not os.path.lexists(quarantine):
        return
    stage0 = root / "build" / host / "stage0"
    expected_parent = stage0.parent
    if (
        quarantine.parent != expected_parent
        or quarantine.name != "stage0.preexisting-fresh-seed"
        or quarantine.is_symlink()
        or not quarantine.is_dir()
    ):
        raise RuntimeError(f"refusing unsafe seed backup cleanup target: {quarantine}")
    if not stage0.is_dir() or stage0.is_symlink():
        raise RuntimeError(
            f"refusing seed backup cleanup without a fresh real stage0 directory: {stage0}"
        )
    try:
        shutil.rmtree(quarantine)
    except OSError as error:
        raise RuntimeError(
            f"could not remove superseded seed backup {quarantine}: {error}"
        ) from error
    print(f"  removed superseded seed backup -> {quarantine}")


@dataclass(frozen=True)
class SubmoduleState:
    """One direct gitlink, resolved relative to its containing repository."""

    repository: Path
    path: Path
    display_path: str
    marker: str
    needs_registration: bool = False


@dataclass(frozen=True)
class IndexedSubmodule:
    """One submodule declaration read from the indexed .gitmodules blob."""

    name: str
    path: Path
    url: str
    oid: str
    modules_blob: str


def _submodule_url_is_allowed(value: str) -> bool:
    """Admit only canonical, credential-free GitHub repository URLs.

    The first-party graph and its currently indexed recursive dependencies are
    all hosted on github.com.  Keeping this grammar deliberately smaller than a
    general URL parser prevents userinfo, query/fragment credentials, alternate
    ports, percent-decoding ambiguities, and command-scoped URL rewrites from
    becoming pre-verification transport authority.
    """
    prefix = "https://github.com/"
    suffix = ".git"
    if not value.startswith(prefix) or not value.endswith(suffix):
        return False
    repository = value[len(prefix) : -len(suffix)]
    parts = repository.split("/")
    if len(parts) != 2 or any(not part for part in parts):
        return False
    allowed = frozenset(
        "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_."
    )
    return all(
        part not in {".", ".."} and all(character in allowed for character in part)
        for part in parts
    )


def _agh_source_identity(executable: Path) -> dict[str, object]:
    """Bind the selected multicall spelling as well as its physical program."""
    if not executable.is_absolute():
        raise RuntimeError("Agh source transport requires an absolute executable")
    resolved = executable.resolve(strict=True)
    metadata = resolved.stat()
    if not stat.S_ISREG(metadata.st_mode) or not os.access(resolved, os.X_OK):
        raise RuntimeError("Agh source transport is not a regular executable")
    return {
        "executable": str(executable),
        "resolved": str(resolved),
        "device": metadata.st_dev,
        "inode": metadata.st_ino,
        "mode": stat.S_IMODE(metadata.st_mode),
        "bytes": metadata.st_size,
        "mtime_ns": metadata.st_mtime_ns,
        "sha256": _sha256_file(resolved),
    }


def _agh_source_environment() -> dict[str, str]:
    """Give only Agh its caller identity; ordinary Git keeps its closed HOME."""
    environment = _provenance_git_environment()
    for name in ("HOME", "USERPROFILE", "APPDATA", "LOCALAPPDATA"):
        value = os.environ.get(name)
        if value and "\0" not in value and Path(value).is_absolute():
            environment[name] = value
    environment["GIT_TERMINAL_PROMPT"] = "0"
    return environment


def _agh_source_fetch(
    url: str,
    destination: Path,
    source_ref: str,
    private_ref: str,
    *,
    execute=None,
    checkout_cache: Path | None = None,
    checkout_closure: bool = False,
) -> dict[str, object]:
    """Fetch through Agh's owner routing, then independently read its exact ref.

    No credential is extracted and no GitHub Git/anonymous fallback exists.
    Keep the lexical `agh` executable: it may be a multicall symlink to aterm.
    Callers own destination custody and any subsequent checkout transaction.
    """
    canonical_url = url if url.endswith(".git") else url + ".git"
    if not _submodule_url_is_allowed(canonical_url):
        raise RuntimeError("Agh source fetch requires a canonical GitHub repository URL")
    if not (
        re.fullmatch(r"[0-9a-f]{40}", source_ref)
        or re.fullmatch(r"refs/(heads|tags)/[A-Za-z0-9_./-]+", source_ref)
    ) or any(part in source_ref for part in ("..", "//", "@{")) or source_ref.endswith(("/", ".")) or any(
        part.startswith(".") or part.endswith(".lock") for part in source_ref.split("/")
    ):
        raise RuntimeError("Agh source fetch requires a literal commit or full source ref")
    if not re.fullmatch(r"refs/agh/[A-Za-z0-9_./-]+", private_ref) or any(
        part in private_ref for part in ("..", "//", "@{")
    ) or private_ref.endswith(("/", ".")) or any(
        part.startswith(".") or part.endswith(".lock") for part in private_ref.split("/")
    ):
        raise RuntimeError("Agh source destination must be a literal private refs/agh ref")
    selected = which("agh")
    if selected is None:
        raise RuntimeError("owner-routed Agh is required for GitHub source acquisition")
    executable = Path(os.path.abspath(selected))
    identity = _agh_source_identity(executable)
    repository = canonical_url[len("https://github.com/") : -len(".git")]
    command = [str(executable), "repo", "fetch", repository, str(destination),
               "--ref", source_ref, "--into", private_ref]
    exact_source = re.fullmatch(r"[0-9a-f]{40}", source_ref) is not None
    if checkout_closure and not exact_source:
        raise RuntimeError("Agh checkout closure requires an exact immutable source commit")
    if checkout_cache is not None and not exact_source:
        raise RuntimeError("Agh checkout cache requires an exact immutable source commit")
    # Exact pinned compilers need the complete selected checkout, with or
    # without a cache. Explicit closure requests never accept a mutable ref.
    if exact_source:
        command.append("--checkout-closure")
    if checkout_cache is not None:
        command.extend(("--checkout-cache", str(checkout_cache)))
    environment = _agh_source_environment()
    try:
        if execute is None:
            result = _run_submodule_update_process(
                command, environment=environment,
                timeout_seconds=SUBMODULE_UPDATE_TIMEOUT_SECONDS, credential_gh=None,
            )
            if result.returncode != 0:
                raise RuntimeError(f"owner-routed Agh source fetch failed (exit {result.returncode})")
        else:
            execute(command, environment)
    finally:
        if _agh_source_identity(executable) != identity:
            raise RuntimeError("Agh source transport changed during acquisition")
    result = subprocess.run(
        _controlled_git_command(["-C", str(destination), "rev-parse", "--verify",
                                 private_ref + "^{commit}"]),
        env=_provenance_git_environment(), capture_output=True, text=True,
        check=True, timeout=30,
    )
    commit = result.stdout.strip()
    if not re.fullmatch(r"[0-9a-f]{40,64}", commit):
        raise RuntimeError("Agh source ref did not resolve to a commit")
    if re.fullmatch(r"[0-9a-f]{40}", source_ref) and commit != source_ref:
        raise RuntimeError("Agh source ref differs from the requested immutable commit")
    return {"program": identity, "repository": repository, "source": source_ref,
            "private_ref": private_ref, "commit": commit}


def fetch_source_pin_main(argv: list[str]) -> int:
    """Explicit object repair; share the bootstrap's existing Agh owner."""
    parser = argparse.ArgumentParser(
        prog="recreate_bootstrap.py fetch-source-pin",
        description="Fetch one exact GitHub source pin through owner-routed Agh; no checkout or build.",
    )
    parser.add_argument("--url", required=True)
    parser.add_argument("--directory", required=True, type=Path)
    parser.add_argument("--pin", required=True)
    args = parser.parse_args(argv)
    if not re.fullmatch(r"[0-9a-f]{40}", args.pin):
        parser.error("--pin requires one exact forty-digit commit ID")
    private_ref = "refs/agh/trust-source-pins/" + args.pin
    # Postconditions are local observations, not additional acquisitions. Even
    # a promisor store must not hide absent data by fetching during readback.
    environment = _provenance_git_environment()
    environment["GIT_NO_LAZY_FETCH"] = "1"
    environment["GIT_ALLOW_PROTOCOL"] = ""
    try:
        existing = subprocess.run(
            _controlled_git_command(["-C", str(args.directory), "show-ref", "--verify", "--quiet", private_ref]),
            env=environment, capture_output=True, text=True, check=False, timeout=30,
        )
        if existing.returncode not in (0, 1):
            raise RuntimeError("selected private source-pin ref is unreadable or names another commit")
        if existing.returncode == 0:
            selected = subprocess.run(
                _controlled_git_command(["-C", str(args.directory), "rev-parse", "--verify", private_ref]),
                env=environment, capture_output=True, text=True, check=True, timeout=30,
            )
            if selected.stdout.strip() != args.pin:
                raise RuntimeError("selected private source-pin ref is unreadable or names another commit")
        # Source repair needs the exact selected checkout and ancestry metadata,
        # not every historical checkout's blobs. Keep Agh's authenticated owner,
        # immutable/private-ref readback and the same bounded refusal behavior.
        _agh_source_fetch(args.url, args.directory, args.pin, private_ref,
                          checkout_closure=True)
        tree = subprocess.run(
            _controlled_git_command(["-C", str(args.directory), "cat-file", "-t", args.pin + "^{tree}"]),
            env=environment, capture_output=True, text=True, check=False, timeout=30,
        )
        if tree.returncode != 0 or tree.stdout.strip() != "tree":
            raise RuntimeError("Agh returned but the exact source pin's root tree is not locally readable")
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"source pin fetch refused: {error}", file=sys.stderr)
        return 2
    return 0


def _credential_gh_executable(
    snapshot_directory: Path | None = None,
) -> Path | None:
    """Resolve the caller's explicit GitHub CLI credential facility.

    ``gh`` is not source/provenance authority: the fixed OS Git and pinned
    gitlinks remain the integrity boundary.  It is allowed only as a scoped
    credential reader for the one materialization operation below.  Resolve
    its path before entering the closed Git environment so a helper cannot be
    selected through the controlled PATH.
    """
    candidate = which("gh")
    if not candidate:
        return None
    candidate_path = Path(candidate)
    trusted = _trusted_credential_executable(candidate_path)
    if trusted is not None and not _homebrew_credential_layout(
        candidate_path, trusted
    ):
        return trusted
    if snapshot_directory is None or os.name == "nt":
        return trusted
    return _snapshot_homebrew_credential_executable(
        candidate_path, snapshot_directory
    )


_ROOT_CREDENTIAL_EXECUTABLE_PREFIXES = (
    Path("/usr"),
    Path("/bin"),
    Path("/sbin"),
)

_HOMEBREW_CREDENTIAL_LAYOUTS = (
    (Path("/opt/homebrew/bin/gh"), Path("/opt/homebrew/Cellar/gh")),
    (Path("/usr/local/bin/gh"), Path("/usr/local/Cellar/gh")),
)
_MAX_CREDENTIAL_HELPER_BYTES = 256 * 1024 * 1024


def _path_is_within(path: Path, prefix: Path) -> bool:
    return path == prefix or prefix in path.parents


def _trusted_posix_path_chain(path: Path, effective_uid: int) -> bool:
    """Validate every lexical component without silently following an alias.

    Directory write authority controls whether another user can redirect a
    later path lookup.  Symlink mode bits are not meaningful on macOS, so a
    symlink is admitted only when its owner is the current euid or root; both
    its lexical containing chain and its fully resolved target chain are
    validated separately by ``_trusted_credential_executable``.
    """
    if not path.is_absolute():
        return False
    current = Path(path.anchor)
    try:
        root_metadata = current.lstat()
    except OSError:
        return False
    root_mode = stat.S_IMODE(root_metadata.st_mode)
    if (
        not stat.S_ISDIR(root_metadata.st_mode)
        or root_metadata.st_uid not in {0, effective_uid}
        or (
            root_mode & 0o022
            and not (
                root_metadata.st_uid == 0
                and root_mode & stat.S_ISVTX
                and root_mode & 0o002
            )
        )
    ):
        return False
    components = path.parts[1:]
    for index, component in enumerate(components):
        current /= component
        try:
            metadata = current.lstat()
        except OSError:
            return False
        recognized_owner = metadata.st_uid in {0, effective_uid}
        if not recognized_owner:
            return False
        leaf = index + 1 == len(components)
        if stat.S_ISLNK(metadata.st_mode):
            continue
        if leaf:
            if not stat.S_ISREG(metadata.st_mode):
                return False
        elif not stat.S_ISDIR(metadata.st_mode):
            return False
        mode = stat.S_IMODE(metadata.st_mode)
        if mode & 0o022:
            # A root-owned sticky temporary directory (normally /tmp) does not
            # let another uid rename or unlink our private child.  This narrow
            # exception is needed for the 0700 helper snapshot below; ordinary
            # group-writable Homebrew directories remain untrusted.
            root_sticky_directory = (
                not leaf
                and stat.S_ISDIR(metadata.st_mode)
                and metadata.st_uid == 0
                and mode & stat.S_ISVTX
                and mode & 0o002
            )
            if not root_sticky_directory:
                return False
    return True


def _homebrew_credential_layout(candidate: Path, resolved: Path) -> bool:
    """Recognize only the fixed Homebrew gh alias-to-Cellar shape."""
    try:
        lexical = Path(os.path.abspath(os.fspath(candidate)))
    except (OSError, TypeError, ValueError):
        return False
    for alias, cellar in _HOMEBREW_CREDENTIAL_LAYOUTS:
        if lexical != alias:
            continue
        try:
            relative = resolved.relative_to(cellar)
        except ValueError:
            continue
        parts = relative.parts
        if (
            len(parts) == 3
            and parts[0] not in {"", ".", ".."}
            and parts[1:] == ("bin", "gh")
        ):
            return True
    return False


def _credential_source_metadata_is_allowed(
    metadata: os.stat_result, resolved: Path, effective_uid: int
) -> bool:
    """Admit an opened helper leaf, independently of mutable ancestors."""
    mode = stat.S_IMODE(metadata.st_mode)
    if (
        not stat.S_ISREG(metadata.st_mode)
        or metadata.st_nlink != 1
        or metadata.st_size <= 0
        or metadata.st_size > _MAX_CREDENTIAL_HELPER_BYTES
        or mode & 0o022
        or mode & 0o111 == 0
    ):
        return False
    if metadata.st_uid == effective_uid:
        return True
    return metadata.st_uid == 0 and any(
        _path_is_within(resolved, prefix)
        for prefix in _ROOT_CREDENTIAL_EXECUTABLE_PREFIXES
    )


def _credential_source_identity(metadata: os.stat_result) -> tuple[int, ...]:
    """Fields that must remain stable for the duration of an fd copy."""
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_uid,
        metadata.st_gid,
        metadata.st_mode,
        metadata.st_nlink,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def _snapshot_homebrew_credential_executable(
    candidate: Path, snapshot_directory: Path
) -> Path | None:
    """Copy an opened Homebrew gh inode into a private executable snapshot.

    Homebrew's top-level ``bin`` and ``Cellar`` directories are commonly 0775.
    They therefore cannot remain execution authority even when the gh leaf is
    owned by this uid.  Resolve only the fixed gh layout, open its leaf with
    ``O_NOFOLLOW``, validate the opened inode, and execute a 0700 copy beneath
    a freshly-created 0700 directory.  A later alias or Cellar swap cannot
    change the bytes Git runs.
    """
    try:
        effective_uid = os.geteuid()
        lexical = Path(os.path.abspath(os.fspath(candidate)))
        resolved = lexical.resolve(strict=True)
        if not _homebrew_credential_layout(lexical, resolved):
            return None

        directory_metadata = snapshot_directory.lstat()
        if (
            not stat.S_ISDIR(directory_metadata.st_mode)
            or directory_metadata.st_uid != effective_uid
            or stat.S_IMODE(directory_metadata.st_mode) != 0o700
            or snapshot_directory.resolve(strict=True) != snapshot_directory
        ):
            return None
    except (AttributeError, OSError, TypeError, ValueError):
        return None

    source_flags = os.O_RDONLY
    source_flags |= getattr(os, "O_CLOEXEC", 0)
    source_flags |= getattr(os, "O_NOFOLLOW", 0)
    destination = snapshot_directory / "gh-credential-helper"
    destination_flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    destination_flags |= getattr(os, "O_CLOEXEC", 0)
    destination_flags |= getattr(os, "O_NOFOLLOW", 0)
    source_descriptor: int | None = None
    destination_descriptor: int | None = None
    directory_descriptor: int | None = None
    destination_created = False
    snapshot_complete = False
    try:
        source_descriptor = os.open(resolved, source_flags)
        before = os.fstat(source_descriptor)
        if not _credential_source_metadata_is_allowed(
            before, resolved, effective_uid
        ):
            return None

        destination_descriptor = os.open(
            destination, destination_flags, 0o700
        )
        destination_created = True
        os.fchmod(destination_descriptor, 0o700)
        copied = 0
        while True:
            chunk = os.read(source_descriptor, 1024 * 1024)
            if not chunk:
                break
            copied += len(chunk)
            if copied > before.st_size or copied > _MAX_CREDENTIAL_HELPER_BYTES:
                return None
            view = memoryview(chunk)
            while view:
                written = os.write(destination_descriptor, view)
                if written <= 0:
                    raise OSError("short credential helper snapshot write")
                view = view[written:]
        os.fsync(destination_descriptor)

        after = os.fstat(source_descriptor)
        snapshot_metadata = os.fstat(destination_descriptor)
        if (
            copied != before.st_size
            or _credential_source_identity(after)
            != _credential_source_identity(before)
            or not stat.S_ISREG(snapshot_metadata.st_mode)
            or snapshot_metadata.st_uid != effective_uid
            or snapshot_metadata.st_nlink != 1
            or snapshot_metadata.st_size != copied
            or stat.S_IMODE(snapshot_metadata.st_mode) != 0o700
        ):
            return None

        directory_flags = os.O_RDONLY
        directory_flags |= getattr(os, "O_CLOEXEC", 0)
        directory_flags |= getattr(os, "O_DIRECTORY", 0)
        directory_flags |= getattr(os, "O_NOFOLLOW", 0)
        directory_descriptor = os.open(snapshot_directory, directory_flags)
        os.fsync(directory_descriptor)
        snapshot_complete = True
    except OSError:
        return None
    finally:
        for descriptor in (
            directory_descriptor,
            destination_descriptor,
            source_descriptor,
        ):
            if descriptor is not None:
                try:
                    os.close(descriptor)
                except OSError:
                    pass
        if destination_created and not snapshot_complete:
            try:
                destination.unlink(missing_ok=True)
            except OSError:
                pass

    trusted_snapshot = _trusted_credential_executable(destination)
    if trusted_snapshot != destination:
        try:
            destination.unlink(missing_ok=True)
        except OSError:
            pass
        return None
    return trusted_snapshot


def _trusted_credential_executable(candidate: Path) -> Path | None:
    """Return one canonical, cross-user-immutable credential helper path.

    Check the complete lexical alias chain, resolve it, then check the complete
    canonical chain and the opened leaf.  Homebrew's commonly group-writable
    top-level directories intentionally fail this direct-path gate and are
    handled by the private fd-bound snapshot above.  The returned canonical
    path is what Git executes, so replacing a trusted alias afterward has no
    effect.

    Same-euid replacement is the local-principal boundary.  A root-owned leaf
    is accepted only in the conventional immutable system prefixes; an
    attacker-owned mode-0755 binary is not made trustworthy by lacking write
    bits for group/other.
    """
    if os.name == "nt":
        # Windows ownership/ACL validation is not expressible through st_uid.
        # Accept only the standard system-wide GitHub CLI installation, never a
        # PATH-only executable in a caller-controlled directory.
        standard = (
            Path("C:/Program Files/GitHub CLI/gh.exe"),
            Path("C:/Program Files (x86)/GitHub CLI/gh.exe"),
        )
        try:
            resolved = candidate.resolve(strict=True)
        except OSError:
            return None
        if not any(resolved == path.resolve(strict=False) for path in standard):
            return None
        try:
            metadata = resolved.stat()
        except OSError:
            return None
        return resolved if stat.S_ISREG(metadata.st_mode) and os.access(resolved, os.X_OK) else None

    try:
        effective_uid = os.geteuid()
        lexical = Path(os.path.abspath(os.fspath(candidate)))
        if not _trusted_posix_path_chain(lexical, effective_uid):
            return None
        resolved = lexical.resolve(strict=True)
        if not _trusted_posix_path_chain(resolved, effective_uid):
            return None
        metadata = resolved.lstat()
    except (AttributeError, OSError, ValueError):
        return None

    if (
        not stat.S_ISREG(metadata.st_mode)
        or not os.access(resolved, os.X_OK)
        or stat.S_IMODE(metadata.st_mode) & 0o111 == 0
        or stat.S_IMODE(metadata.st_mode) & 0o022
    ):
        return None
    if metadata.st_uid != effective_uid:
        root_system_leaf = metadata.st_uid == 0 and any(
            _path_is_within(resolved, prefix)
            for prefix in _ROOT_CREDENTIAL_EXECUTABLE_PREFIXES
        )
        if not root_system_leaf:
            return None

    flags = os.O_RDONLY
    flags |= getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(resolved, flags)
        try:
            opened = os.fstat(descriptor)
        finally:
            os.close(descriptor)
    except OSError:
        return None
    if (
        not stat.S_ISREG(opened.st_mode)
        or opened.st_dev != metadata.st_dev
        or opened.st_ino != metadata.st_ino
        or opened.st_uid != metadata.st_uid
        or stat.S_IMODE(opened.st_mode) & 0o111 == 0
        or stat.S_IMODE(opened.st_mode) & 0o022
    ):
        return None
    return resolved


def _revalidate_credential_gh_executable(path: Path) -> None:
    """Recheck the canonical helper immediately before Git may execute it."""
    if _trusted_credential_executable(path) != path:
        raise RuntimeError(
            f"GitHub credential helper lost executable authority before use: {path}"
        )


def _read_only_gh_credential_helper(gh: Path) -> str:
    """Return a command-scoped helper that forwards only credential ``get``.

    Git calls helpers again with ``store`` after a successful authentication.
    Deliberately ignoring every operation except ``get`` keeps this bootstrap
    path unable to persist a prompted token or mutate ``gh`` authentication.
    """
    executable = shlex.quote(gh.as_posix())
    scoped_environment = " ".join(
        f"{name}={shlex.quote(value)}"
        for name, value in _credential_gh_environment().items()
    )
    if scoped_environment:
        scoped_environment += " "
    return (
        "credential.helper=!f() { if test \"$1\" = get; then "
        f"{scoped_environment}exec {executable} auth git-credential get; fi; "
        "exit 0; }; f"
    )


def _caller_gh_config_directory() -> str | None:
    """Resolve gh's config directory without exposing the caller's HOME to Git."""
    explicit = os.environ.get("GH_CONFIG_DIR")
    if explicit:
        candidate = Path(explicit)
    elif os.environ.get("XDG_CONFIG_HOME"):
        candidate = Path(os.environ["XDG_CONFIG_HOME"]) / "gh"
    elif os.name == "nt" and os.environ.get("APPDATA"):
        candidate = Path(os.environ["APPDATA"]) / "GitHub CLI"
    elif os.environ.get("HOME"):
        candidate = Path(os.environ["HOME"]) / ".config" / "gh"
    else:
        return None
    rendered = os.fspath(candidate)
    if "\0" in rendered or not candidate.is_absolute():
        return None
    return rendered


def _credential_gh_environment() -> dict[str, str]:
    """Ambient paths visible to gh itself, never to the transport Git child."""
    scoped: dict[str, str] = {}
    gh_config_directory = _caller_gh_config_directory()
    if gh_config_directory is not None:
        scoped["GH_CONFIG_DIR"] = gh_config_directory
    names = ["HOME"]
    if os.name == "nt":
        names.extend(("APPDATA", "LOCALAPPDATA", "USERPROFILE"))
    for name in names:
        value = os.environ.get(name)
        if not value or "\0" in value:
            continue
        candidate = Path(value)
        if candidate.is_absolute():
            scoped[name] = value
    return scoped


def _submodule_materialization_environment() -> dict[str, str]:
    """Open only the user credential lookup needed by submodule transport.

    All Git config, executable, protocol, proxy, and repository controls stay
    closed exactly as they are for provenance reads.  The caller's home/config
    configuration and home paths are embedded only as shell assignments on the
    absolute ``gh`` helper command, so the Git child keeps this closed mapping
    and libcurl cannot consult the caller's ``~/.netrc``. Ambient tokens,
    askpass programs, Git config, proxies, and dynamic-loader settings are never
    inherited.
    """
    env = _provenance_git_environment()
    env.pop("GIT_ASKPASS", None)
    env["GIT_TERMINAL_PROMPT"] = "1" if sys.stdin.isatty() else "0"
    return env


def _submodule_auth_config(
    snapshot_directory: Path,
) -> tuple[list[str], Path | None]:
    """Return late ``-c`` options for read-only gh/terminal authentication."""
    gh = _credential_gh_executable(snapshot_directory)
    options = ["-c", "credential.interactive=always"]
    if gh is not None:
        options.extend(("-c", _read_only_gh_credential_helper(gh)))
    return options, gh


def _credential_snapshot_parent() -> Path | None:
    """Return a fixed parent where another uid cannot replace our temp dir."""
    if os.name == "nt":
        return None
    candidates = (
        (Path("/private/tmp"), Path("/tmp"))
        if platform.system().lower() == "darwin"
        else (Path("/tmp"), Path("/var/tmp"))
    )
    for candidate in candidates:
        try:
            resolved = candidate.resolve(strict=True)
            metadata = resolved.lstat()
        except OSError:
            continue
        mode = stat.S_IMODE(metadata.st_mode)
        immutable_parent = mode & 0o022 == 0
        sticky_world_parent = mode & 0o002 and mode & stat.S_ISVTX
        if (
            stat.S_ISDIR(metadata.st_mode)
            and metadata.st_uid == 0
            and (immutable_parent or sticky_world_parent)
        ):
            return resolved
    raise RuntimeError(
        "no fixed root-owned immutable or sticky temporary directory is "
        "available for the private GitHub credential-helper snapshot"
    )


def _add_exception_note(error: BaseException, note: str) -> None:
    """Keep the primary failure on runtimes predating BaseException.add_note."""
    attach = getattr(error, "add_note", None)
    if callable(attach):
        attach(note)
        return
    try:
        print(note, file=sys.stderr)
    except (OSError, ValueError, AttributeError):
        pass


def _submodule_wait_custody_available() -> bool:
    return callable(getattr(os, "waitid", None)) and all(
        hasattr(os, name) for name in ("P_PID", "WEXITED", "WNOWAIT", "WNOHANG")
    )


def _terminate_submodule_process_tree(
    process: subprocess.Popen[bytes], *, leader_already_exited: bool = False
) -> None:
    """Hard-stop the transport/helper process group and confirm it is gone."""
    # A prior cleanup may have reaped the leader before reporting an unresolved
    # group. Its numeric identifier is then reusable, not another signal right.
    if os.name != "nt":
        if process.returncode is not None:
            raise RuntimeError("submodule leader wait custody was already consumed")
        if not _submodule_wait_custody_available():
            raise RuntimeError("submodule termination requires unreaped leader custody")
        try:
            os.waitid(os.P_PID, process.pid, os.WEXITED | os.WNOWAIT | os.WNOHANG)
        except ChildProcessError as error:
            raise RuntimeError("submodule leader wait custody is unavailable") from error
    tree_signal_succeeded = False
    if os.name == "nt":
        taskkill = Path("C:/Windows/System32/taskkill.exe")
        if taskkill.is_file():
            try:
                result = subprocess.run(
                    [str(taskkill), "/PID", str(process.pid), "/T", "/F"],
                    check=False,
                    stdin=subprocess.DEVNULL,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    timeout=10,
                )
                tree_signal_succeeded = result.returncode == 0
            except (OSError, subprocess.TimeoutExpired):
                pass
    else:
        try:
            os.killpg(process.pid, signal.SIGKILL)
            tree_signal_succeeded = True
        except (ProcessLookupError, PermissionError, OSError):
            pass
    if process.poll() is None:
        try:
            process.kill()
        except OSError:
            pass
    try:
        process.wait(timeout=10)
    except (OSError, subprocess.TimeoutExpired):
        pass
    if process.poll() is None:
        raise RuntimeError(
            f"submodule Git process {process.pid} survived forced termination"
        )
    if os.name == "nt":
        if not tree_signal_succeeded:
            if leader_already_exited:
                # taskkill cannot reliably rediscover a descendant after its
                # parent has already exited. Fixed Git is expected to wait for
                # normal transports; deliberately detached same-user helpers
                # remain the documented non-Job-Object Windows boundary.
                return
            raise RuntimeError(
                "could not confirm Windows submodule descendant-tree termination"
            )
        return

    # The session/process-group leader can exit before its descendants. Probe
    # the original group for a short bounded interval instead of equating a
    # reaped leader with complete transport/helper cleanup.
    deadline = time.monotonic() + 2
    while True:
        try:
            os.killpg(process.pid, 0)
        except ProcessLookupError:
            return
        except PermissionError:
            # Darwin can report EPERM briefly while a killed descendant is a
            # reparented zombie. Treat it as "not yet confirmed" and require
            # ESRCH before the bounded deadline rather than accepting it.
            pass
        if time.monotonic() >= deadline:
            raise RuntimeError(
                f"submodule process group {process.pid} survived forced termination"
            )
        time.sleep(0.02)


def _wait_submodule_process_group(
    process: subprocess.Popen[bytes], timeout_seconds: int | float
) -> int:
    """Observe a POSIX leader without reaping it, then retire its whole group.

    ``Popen.wait`` reaps the leader immediately, allowing its PID/process-group
    identifier to be reused before a post-success descendant check. POSIX
    ``waitid(..., WNOWAIT)`` keeps the exited leader waitable until the group is
    killed and confirmed. Windows has no equivalent in the standard library;
    its fixed Git is expected to wait for normal transports and taskkill is
    attempted after the leader returns.
    """
    if os.name == "nt":
        return_code = process.wait(timeout=timeout_seconds)
        _terminate_submodule_process_tree(
            process, leader_already_exited=True
        )
        return return_code
    if not _submodule_wait_custody_available():
        raise RuntimeError("submodule transport requires nonreaping child wait support")

    deadline = time.monotonic() + timeout_seconds
    while True:
        result = os.waitid(
            os.P_PID,
            process.pid,
            os.WEXITED | os.WNOWAIT | os.WNOHANG,
        )
        if result is not None:
            _terminate_submodule_process_tree(
                process, leader_already_exited=True
            )
            if process.returncode is None:
                raise RuntimeError(
                    "submodule Git leader was not reaped after group termination"
                )
            return process.returncode
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise subprocess.TimeoutExpired(process.args, timeout_seconds)
        time.sleep(min(0.02, remaining))


def _relay_bounded_submodule_output(stream: object) -> None:
    """Drain child output completely while bounding terminal/CI disclosure."""
    emitted = 0
    truncated = False

    def write_diagnostic(data: bytes) -> None:
        try:
            binary = getattr(sys.stderr, "buffer", None)
            if binary is not None:
                binary.write(data)
                binary.flush()
            else:
                sys.stderr.write(data.decode("utf-8", errors="replace"))
                sys.stderr.flush()
        except (BrokenPipeError, OSError, ValueError):
            pass

    try:
        while True:
            chunk = stream.read(64 * 1024)  # type: ignore[attr-defined]
            if not chunk:
                break
            remaining = max(0, SUBMODULE_UPDATE_OUTPUT_LIMIT_BYTES - emitted)
            if remaining:
                visible = chunk[:remaining]
                write_diagnostic(visible)
                emitted += len(visible)
            if len(chunk) > remaining and not truncated:
                truncated = True
                write_diagnostic(
                    b"\n[trust bootstrap: submodule diagnostic output truncated "
                    + f"after {SUBMODULE_UPDATE_OUTPUT_LIMIT_BYTES} bytes]\n".encode()
                )
    except (OSError, ValueError):
        pass
    finally:
        try:
            stream.close()  # type: ignore[attr-defined]
        except (OSError, ValueError):
            pass


def _run_submodule_update_process(
    command: list[str],
    *,
    environment: dict[str, str],
    timeout_seconds: int | float,
    credential_gh: Path | None,
) -> subprocess.CompletedProcess[bytes]:
    """Run one targeted update with a process-tree deadline.

    Output is drained concurrently and relayed to the invoking terminal/CI log
    up to a fixed byte ceiling.  It is never accumulated in Python memory or a
    temporary file, while stdin remains attached for the explicitly enabled
    terminal credential prompt.
    """
    if credential_gh is not None:
        _revalidate_credential_gh_executable(credential_gh)
    if os.name != "nt" and signal.getsignal(signal.SIGCHLD) != signal.SIG_DFL:
        raise RuntimeError("submodule process custody requires the default SIGCHLD disposition")
    if os.name != "nt" and not _submodule_wait_custody_available():
        raise RuntimeError("submodule transport requires nonreaping child wait support")
    options: dict[str, object] = {
        "env": environment,
        "stdin": None,
        "stdout": subprocess.PIPE,
        "stderr": subprocess.STDOUT,
    }
    if os.name == "nt":
        options["creationflags"] = getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0)
    else:
        options["start_new_session"] = True
    process: subprocess.Popen[bytes] | None = None
    relay: threading.Thread | None = None
    try:
        process = subprocess.Popen(command, **options)
        if process.stdout is None:
            raise RuntimeError("submodule process omitted its owned output pipe")
        relay = threading.Thread(
            target=_relay_bounded_submodule_output,
            args=(process.stdout,),
            name="trust-submodule-output",
            daemon=True,
        )
        relay.start()
        return_code = _wait_submodule_process_group(process, timeout_seconds)
    except BaseException as error:
        try:
            if process is not None:
                _terminate_submodule_process_tree(process)
        except BaseException as termination_error:
            _add_exception_note(
                error,
                f"submodule process-tree termination also failed: {termination_error}"
            )
        if isinstance(error, subprocess.TimeoutExpired):
            raise subprocess.TimeoutExpired(command, timeout_seconds) from error
        raise
    finally:
        if relay is not None and relay.ident is not None:
            relay.join(timeout=10)
            if relay.is_alive():
                # An escaped descendant may still hold the inherited pipe.
                # Keep the existing bounded relay cleanup after tree retirement.
                try:
                    process.stdout.close()
                except (OSError, ValueError):
                    pass
                relay.join(timeout=1)
        elif process is not None and process.stdout is not None:
            # Constructor/start failure never transferred this pipe to a relay.
            process.stdout.close()
    if credential_gh is not None:
        _revalidate_credential_gh_executable(credential_gh)
    return subprocess.CompletedProcess(command, return_code)


def _parse_git_config_records(
    raw: bytes, repository: Path, scope: str
) -> list[tuple[str, str]]:
    """Decode one NUL-framed Git config scope without exposing its values."""
    records: list[tuple[str, str]] = []
    for raw_record in raw.split(b"\0"):
        if not raw_record:
            continue
        raw_key, separator, raw_value = raw_record.partition(b"\n")
        if not separator:
            raise RuntimeError(
                f"malformed {scope} Git config record in {repository}"
            )
        try:
            key = raw_key.decode("utf-8", errors="strict").lower()
            value = raw_value.decode("utf-8", errors="strict").strip()
        except UnicodeDecodeError as error:
            raise RuntimeError(
                f"non-UTF-8 {scope} Git config in {repository}"
            ) from error
        records.append((key, value))
    return records


def _worktree_config_snapshot(
    repository: Path,
) -> tuple[Path, tuple[int, ...]] | None:
    """Locate Git's optional worktree scope without confusing absence with errors."""
    try:
        result = subprocess.run(
            _controlled_git_command([
                "-C", str(repository), "rev-parse", "--absolute-git-dir",
            ]),
            capture_output=True, check=False,
            env=_provenance_git_environment(), timeout=30,
        )
        if result.returncode != 0:
            raise RuntimeError(f"could not locate worktree Git config in {repository}")
        # --git-path may dereference the final symlink. Append the fixed leaf
        # to this worktree's own Git directory so lstat inspects that leaf.
        config_path = Path(os.fsdecode(result.stdout).rstrip("\n")) / "config.worktree"
        if not config_path.is_absolute():
            raise RuntimeError(f"worktree Git config path was not absolute in {repository}")
        try:
            metadata = config_path.lstat()
        except FileNotFoundError:
            return None
        if not stat.S_ISREG(metadata.st_mode):
            raise RuntimeError(f"worktree Git config is not a regular file in {repository}")
        return config_path, (
            metadata.st_dev, metadata.st_ino, metadata.st_mode, metadata.st_size,
            metadata.st_mtime_ns, metadata.st_ctime_ns,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise RuntimeError(
            f"could not inspect worktree Git config in {repository}: {error}"
        ) from error


def _read_repository_git_config_scope(
    repository: Path, scope: str
) -> list[tuple[str, str]]:
    """Read exactly one repository-owned config scope with includes disabled."""
    if scope not in {"local", "worktree"}:
        raise ValueError(f"unsupported Git config scope: {scope}")
    worktree_snapshot = None
    if scope == "worktree":
        # Git exits nonzero for a missing config.worktree even though this
        # optional scope has no values. Check the actual Git-resolved path;
        # never infer absence from localized stderr or swallow access errors.
        worktree_snapshot = _worktree_config_snapshot(repository)
        if worktree_snapshot is None:
            return []
    command = _controlled_git_command(
        [
            "-C",
            str(repository),
            "config",
            f"--{scope}",
            "--no-includes",
            "--null",
            "--list",
        ]
    )
    try:
        result = subprocess.run(
            command,
            capture_output=True,
            check=False,
            env=_provenance_git_environment(),
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise RuntimeError(
            f"could not inspect {scope} Git authority in {repository}: {error}"
        ) from error
    if result.returncode != 0:
        detail = (
            result.stderr.decode("utf-8", errors="replace").strip()
            or "unknown Git error"
        )
        raise RuntimeError(
            f"could not inspect {scope} Git authority in {repository}: {detail}"
        )
    if scope == "worktree" and _worktree_config_snapshot(repository) != worktree_snapshot:
        raise RuntimeError(f"worktree Git config changed while being read in {repository}")
    return _parse_git_config_records(result.stdout, repository, scope)


def _git_config_bool(value: str) -> bool | None:
    lowered = value.lower()
    if lowered in {"", "true", "yes", "on", "1"}:
        return True
    if lowered in {"false", "no", "off", "0"}:
        return False
    return None


def _repository_git_config_records(
    repository: Path,
) -> list[tuple[str, str, str]]:
    """Return every effective repository-owned scope, excluding includes."""
    local = _read_repository_git_config_scope(repository, "local")
    records = [("local", key, value) for key, value in local]
    worktree_values = [
        value for key, value in local if key == "extensions.worktreeconfig"
    ]
    if worktree_values:
        enabled = _git_config_bool(worktree_values[-1])
        if enabled is None:
            raise RuntimeError(
                f"invalid extensions.worktreeConfig value in {repository}"
            )
        if enabled:
            records.extend(
                ("worktree", key, value)
                for key, value in _read_repository_git_config_scope(
                    repository, "worktree"
                )
            )
    return records


def _git_config_key_for_diagnostic(key: str) -> str:
    """Render a config key without echoing URL-subsection credentials."""
    if not any(token in key for token in ("://", "@", "?", "#")):
        return key
    parts = key.split(".")
    if len(parts) < 2:
        return "<redacted-config-key>"
    return f"{parts[0]}.<redacted>.{parts[-1]}"


_ADMITTED_TRUST_CHECKOUTS: set[Path] = set()


@contextmanager
def admitted_trust_checkout(root: Path):
    """Within the block, judge `root` as this recreator's own source root is judged.

    For a caller's other checkout of the Trust source whose pushes must run its
    tracked hooks: the fleet train's landing worktree, a linked worktree of its
    --repo, keeps that clone's maintained hooks path. Its children are judged as
    any other repository.
    """
    resolved = root.resolve(strict=True)
    if resolved in _ADMITTED_TRUST_CHECKOUTS:
        raise RuntimeError(f"{root} is already an admitted Trust checkout")
    _ADMITTED_TRUST_CHECKOUTS.add(resolved)
    try:
        yield
    finally:
        _ADMITTED_TRUST_CHECKOUTS.discard(resolved)


def _maintained_absolute_hooks_path(repository: Path, value: str) -> bool:
    """Whether an absolute core.hooksPath names the maintained hooks of `repository`.

    The two that scripts/prewarm_push.sh's `hooks_verdict` accepts, compared
    physically: the checkout's own scripts/hooks, or, for a linked worktree, the
    scripts/hooks of the main worktree of the same repository (the shared
    absolute path scripts/install-git-hooks.sh writes).
    """
    hooks = Path(value)
    if not hooks.is_dir():
        return False
    hooks = hooks.resolve()
    own = repository / "scripts/hooks"
    if own.is_dir() and own.resolve() == hooks:
        return True

    def read(*arguments: str, at: Path = repository) -> str | None:
        result = subprocess.run(
            _controlled_git_command(["-C", str(at), *arguments]),
            capture_output=True,
            check=False,
            env=_provenance_git_environment(),
            timeout=30,
        )
        return os.fsdecode(result.stdout).rstrip("\n") if result.returncode == 0 else None

    git_dir = read("rev-parse", "--path-format=absolute", "--git-dir")
    common = read("rev-parse", "--path-format=absolute", "--git-common-dir")
    if not git_dir or not common or Path(git_dir).resolve() == Path(common).resolve():
        return False
    # `git worktree list` names the main worktree first.
    listing = read("worktree", "list", "--porcelain") or ""
    first = listing.split("\n", 1)[0]
    if not first.startswith("worktree "):
        return False
    main = Path(first[len("worktree "):])
    main_hooks = main / "scripts/hooks"
    main_common = read("rev-parse", "--path-format=absolute", "--git-common-dir", at=main) if main.is_dir() else None
    return (main_hooks.is_dir() and main_hooks.resolve() == hooks
            and main_common is not None and Path(main_common).resolve() == Path(common).resolve())


def _reject_local_git_execution_authority(
    repository: Path, *, require_https_submodules: bool = False
) -> None:
    """Reject repo-local Git settings that can execute or redirect code.

    Global/system configuration and the process environment are removed by
    `_provenance_git_environment`. Local config is required for worktree and
    submodule bookkeeping, so inspect it with includes disabled before any
    status/update/provenance command can consume it. Only this recreator's
    source root may retain the maintained hooks path (`scripts/hooks`,
    `scripts/hooks-pin`, or an absolute path `_maintained_absolute_hooks_path`
    admits) and an empty worktree scope or disabled sparse controls, as may a
    checkout admitted by `admitted_trust_checkout`. Every other worktree scope is rejected
    after inspection; command-line overrides remain the final boundary.
    """
    records = _repository_git_config_records(repository)
    source_root = repository.resolve() in {repo_root().resolve(), *_ADMITTED_TRUST_CHECKOUTS}
    harmless_worktree_scope = source_root and all(
        scope != "worktree"
        or (
            key in {"core.sparsecheckout", "core.sparsecheckoutcone", "index.sparse"}
            and _git_config_bool(value) is False
        )
        for scope, key, value in records
    )
    hostile: list[str] = []
    for scope, key, value in records:
        lowered = value.lower()
        section = key.split(".", 1)[0]

        executable_setting = (
            key.startswith("include.")
            or key.startswith("includeif.")
            or key == "core.sshcommand"
            or key == "core.gitproxy"
            or key == "core.askpass"
            or key == "core.attributesfile"
            or (
                key == "extensions.worktreeconfig"
                and _git_config_bool(value) is not False
                and not harmless_worktree_scope
            )
            or (key == "core.fsmonitor" and lowered not in {"", "false"})
            or (
                key == "core.hookspath"
                and value not in {"", "/dev/null"}
                and not (
                    source_root
                    and scope == "local"
                    and (value in {"scripts/hooks", "scripts/hooks-pin"} or os.path.isabs(value))
                )
            )
            # Git gives URL-specific HTTP/credential keys precedence over a
            # generic command-line value.  Reject the complete sections in
            # both local and worktree scope; enumerating suffixes is unsafe.
            or section in {"credential", "http", "https", "protocol", "url"}
            or key in {"core.alternaterefscommand", "diff.external", "gc.recentobjectshook"}
            or (
                key.startswith("filter.")
                and key.rsplit(".", 1)[-1] in {"clean", "smudge", "process"}
            )
            or (
                key.startswith("diff.")
                and key.rsplit(".", 1)[-1] in {"command", "textconv"}
            )
            or (key.startswith("merge.") and key.endswith(".driver"))
            or (
                key.startswith("remote.")
                and key.rsplit(".", 1)[-1]
                in {"uploadpack", "receivepack", "vcs", "proxy"}
            )
            or key == "init.templatedir"
        )
        hostile_update = (
            key.startswith("submodule.")
            and key.endswith(".update")
            and lowered != "checkout"
        )
        unsafe_submodule_url = (
            require_https_submodules
            and key.startswith("submodule.")
            and key.endswith(".url")
            and not _submodule_url_is_allowed(value)
        )
        if executable_setting or hostile_update or unsafe_submodule_url:
            hostile.append(
                f"{scope}:{_git_config_key_for_diagnostic(key)}"
            )

    # An absolute hooks path is judged once nothing else in the scope can run:
    # it must name the hooks a push from this checkout runs under
    # scripts/prewarm_push.sh's verdict.
    if source_root and not hostile and any(
        scope == "local" and key == "core.hookspath" and value not in {"", "/dev/null"}
        and os.path.isabs(value) and not _maintained_absolute_hooks_path(repository, value)
        for scope, key, value in records
    ):
        hostile.append("local:core.hookspath")
    if hostile:
        raise RuntimeError(
            "repository-local Git configuration contains hidden execution, update, "
            f"or transport authority in {repository}: {', '.join(sorted(set(hostile)))}"
        )

    top = subprocess.run(
        _controlled_git_command(["-C", str(repository), "rev-parse", "--show-toplevel"]),
        capture_output=True,
        check=False,
        env=_provenance_git_environment(),
        timeout=30,
    )
    if top.returncode != 0:
        detail = top.stderr.decode("utf-8", errors="replace").strip() or "unknown Git error"
        raise RuntimeError(f"could not resolve repository worktree {repository}: {detail}")
    try:
        resolved_top = Path(os.fsdecode(top.stdout).strip()).resolve(strict=True)
        resolved_repository = repository.resolve(strict=True)
    except OSError as error:
        raise RuntimeError(f"could not resolve repository worktree {repository}: {error}") from error
    if resolved_top != resolved_repository:
        raise RuntimeError(
            f"local Git worktree authority redirects {repository} to {resolved_top}"
        )


def _run_git_read(
    repository: Path, arguments: list[str]
) -> subprocess.CompletedProcess[str]:
    _reject_local_git_execution_authority(
        repository, require_https_submodules=True
    )
    result = subprocess.run(
        _controlled_git_command(["-C", str(repository), *arguments]),
        capture_output=True,
        text=True,
        check=False,
        env=_provenance_git_environment(),
        timeout=30,
    )
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip() or "unknown Git error"
        raise RuntimeError(
            f"could not inspect submodules in {repository}: {detail}"
        )
    return result


def _indexed_submodules(repository: Path) -> list[IndexedSubmodule]:
    """Validate and return direct declarations from the indexed blob.

    This gate intentionally reads ``:.gitmodules``, not the working-tree file,
    and runs before any credential helper or network process.  Git otherwise
    copies an indexed URL into local config during ``submodule update --init``;
    validating it afterward is too late to prevent credential persistence and
    diagnostic disclosure.
    """
    indexed_modules = _run_git_read(
        repository, ["ls-files", "--stage", "-z", "--", ".gitmodules"]
    )
    index_rows = _run_git_read(repository, ["ls-files", "--stage", "-z"]).stdout.split("\0")
    gitlinks = []
    for row in index_rows:
        if not row.startswith("160000 "):
            continue
        match_link = re.fullmatch(r"160000 ([0-9a-f]{40}) 0\t(.+)", row)
        if match_link is None:
            raise RuntimeError(f"unmerged or unsupported indexed gitlink in {repository}")
        gitlinks.append((match_link.group(2), match_link.group(1)))
    if not indexed_modules.stdout.strip():
        if gitlinks:
            raise RuntimeError(f"indexed gitlinks have no indexed .gitmodules mapping in {repository}")
        return []

    module_rows = indexed_modules.stdout.rstrip("\0").split("\0")
    match = re.fullmatch(r"100(?:644|755) ([0-9a-f]{40}) 0\t\.gitmodules", module_rows[0]) if len(module_rows) == 1 else None
    if match is None:
        raise RuntimeError(f"indexed .gitmodules is not one regular stage0 SHA1 blob in {repository}")
    modules_blob = match.group(1)

    try:
        configured = subprocess.run(
            _controlled_git_command(
                [
                    "-C",
                    str(repository),
                    "config",
                    "--no-includes",
                    "-z",
                    "--blob",
                    ":.gitmodules",
                    "--list",
                ]
            ),
            capture_output=True,
            check=False,
            env=_provenance_git_environment(),
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise RuntimeError(
            f"could not inspect indexed .gitmodules in {repository}"
        ) from error
    if configured.returncode != 0:
        raise RuntimeError(
            f"could not inspect indexed .gitmodules in {repository}; "
            "its contents were not printed because they may contain credentials"
        )

    declarations: dict[str, dict[str, str]] = {}
    for record_number, record in enumerate(configured.stdout.split(b"\0"), start=1):
        if not record:
            continue
        raw_key, separator, raw_value = record.partition(b"\n")
        if not separator:
            raise RuntimeError(
                f"invalid indexed .gitmodules record {record_number} in {repository}"
            )
        try:
            key = raw_key.decode("utf-8", errors="strict")
            value = raw_value.decode("utf-8", errors="strict").strip()
        except UnicodeDecodeError as error:
            raise RuntimeError(
                f"non-UTF-8 indexed .gitmodules record {record_number} in {repository}"
            ) from error
        if not key.lower().startswith("submodule.") or "." not in key[len("submodule.") :]:
            raise RuntimeError(
                f"unsupported indexed .gitmodules record {record_number} in {repository}"
            )
        declaration, variable = key.rsplit(".", 1)
        variable = variable.lower()
        name = declaration[len("submodule.") :]
        if not name or any(ord(character) < 32 or ord(character) == 127 for character in name):
            raise RuntimeError(
                f"unsafe indexed .gitmodules name in record {record_number} of {repository}"
            )
        if variable not in {"path", "url", "update"}:
            raise RuntimeError(
                f"unsupported indexed .gitmodules key in record {record_number} of {repository}"
            )
        if variable == "update" and value.lower() != "checkout":
            raise RuntimeError(
                f"custom indexed submodule update authority is forbidden in {repository}"
            )
        fields = declarations.setdefault(name, {})
        if variable in fields:
            raise RuntimeError(
                f"duplicate indexed .gitmodules {variable} record in {repository}"
            )
        fields[variable] = value

    if len(declarations) > 4096:
        raise RuntimeError("indexed submodule declaration population exceeds4096")
    entries: list[IndexedSubmodule] = []
    seen_paths: set[str] = set()
    for declaration_number, (name, fields) in enumerate(
        declarations.items(), start=1
    ):
        value = fields.get("path", "")
        url = fields.get("url", "")
        if not value or not url:
            raise RuntimeError(
                f"indexed submodule declaration {declaration_number} in {repository} "
                "must have exactly one path and one URL"
            )
        path = Path(value)
        if (
            path.is_absolute()
            or ".." in path.parts
            or path == Path(".")
            or path.as_posix() != value
            or any(part.lower() == ".git" for part in path.parts)
            or "\\" in value
            or any(
                ord(character) < 32 or ord(character) == 127
                for character in value
            )
        ):
            raise RuntimeError(
                f"unsafe indexed submodule path in declaration "
                f"{declaration_number} of {repository}"
            )
        if value in seen_paths:
            raise RuntimeError(
                f"duplicate indexed submodule path in {repository}"
            )
        seen_paths.add(value)
        if not _submodule_url_is_allowed(url):
            raise RuntimeError(
                f"unsafe indexed submodule URL in declaration "
                f"{declaration_number} of {repository}; expected a canonical, "
                "credential-free https://github.com/<owner>/<repo>.git URL"
            )

        gitlink = _run_git_read(
            repository, ["ls-files", "--stage", "-z", "--", value]
        ).stdout.rstrip("\0").split("\0")
        match = re.fullmatch(r"160000 ([0-9a-f]{40}) 0\t" + re.escape(value), gitlink[0]) if len(gitlink) == 1 else None
        if match is None:
            raise RuntimeError(
                f"indexed .gitmodules path is not one stage0 SHA1 gitlink in {repository}: {value}"
            )
        entries.append(IndexedSubmodule(name=name, path=path, url=url,
                                       oid=match.group(1), modules_blob=modules_blob))

    if sorted(gitlinks) != sorted((entry.path.as_posix(), entry.oid) for entry in entries):
        raise RuntimeError(f"indexed gitlink inventory differs from .gitmodules in {repository}")
    return entries


def _submodule_config_values(repository: Path, key: str, *, boolean: bool = False) -> list[str]:
    arguments = ["-C", str(repository), "config", "--local", "--no-includes", "--null"]
    if boolean:
        arguments.append("--bool")
    result = _local_submodule_git([*arguments, "--get-all", key], absent_ok=True)
    if result.returncode == 1:
        return []
    decoded = result.stdout.decode("utf-8", errors="strict")
    if not decoded.endswith("\0"):
        raise RuntimeError("submodule config lacks its record terminator")
    # Empty final values remain policy input, not framing to strip away.
    return decoded[:-1].split("\0")


def _submodule_activation(repository: Path, indexed: IndexedSubmodule, registration) -> tuple[bool, bool]:
    """Read Git's active selection without submodule-status's describe subprocess.

    A per-name Boolean wins, then all parent-wide pathspecs, then URL presence.
    Keep Git's native pathspec matcher and the registration's fixed config
    snapshot; the second result distinguishes a policy exclusion from an
    existing child that only needs its missing URL registered.
    """
    config, identity, data, missing_url = registration

    def unchanged() -> None:
        if _submodule_file_identity(config) != identity or config.read_bytes() != data:
            raise RuntimeError("parent registration changed while determining submodule activity")

    unchanged()
    named = _submodule_config_values(repository, f"submodule.{indexed.name}.active", boolean=True)
    if named:
        if len(named) != 1 or _git_config_bool(named[0]) is None:
            raise RuntimeError(f"invalid indexed submodule active setting: {indexed.path}")
        active, explicit = _git_config_bool(named[0]) is True, True
    else:
        pathspecs = _submodule_config_values(repository, "submodule.active")
        if pathspecs:
            selected = _run_git_read(
                repository, ["ls-files", "--stage", "-z", "--", *pathspecs]
            ).stdout.split("\0")
            entry = f"160000 {indexed.oid} 0\t{indexed.path.as_posix()}"
            active, explicit = entry in selected, True
        else:
            active, explicit = not missing_url, False
    unchanged()
    return active, explicit


def _direct_submodule_states(
    repository: Path, display_prefix: str = ""
) -> list[SubmoduleState]:
    states: list[SubmoduleState] = []
    for indexed in _indexed_submodules(repository):
        path = indexed.path
        registration = _submodule_registration(repository, indexed)
        active, explicit_activation = _submodule_activation(repository, indexed, registration)
        if not active and explicit_activation:
            raise RuntimeError(f"indexed submodule is excluded by active selection: {path}")
        current = repository
        for component in path.parts:
            current /= component
            if current.is_symlink() or (os.path.lexists(current) and not current.is_dir()):
                raise RuntimeError(f"indexed submodule path has aliased or unknown existing contents: {current}")
        child = repository / path
        if os.path.lexists(child / ".git"):
            if (child / ".git").is_symlink():
                raise RuntimeError(f"existing submodule .git is a symlink: {child}")
            _reject_local_git_execution_authority(child, require_https_submodules=True)
            head = _run_git_read(child, ["rev-parse", "--verify", "HEAD^{commit}"]).stdout.strip()
            marker = " " if head == indexed.oid else "+"
            needs_registration = not active
        elif child.is_dir() and any(child.iterdir()):
            raise RuntimeError(f"indexed submodule path contains unknown existing data: {child}")
        else:
            marker, needs_registration = "-", False
        display_path = (
            f"{display_prefix}/{path.as_posix()}"
            if display_prefix
            else path.as_posix()
        )
        states.append(SubmoduleState(repository, path, display_path, marker, needs_registration))
    return states


def _inspect_submodule_tree(root: Path) -> list[SubmoduleState]:
    states: list[SubmoduleState] = []

    def inspect(repository: Path, display_prefix: str, depth: int = 0) -> None:
        if depth > 64 or len(states) > 4096:
            raise RuntimeError("indexed submodule graph exceeds its depth/population bound")
        for state in _direct_submodule_states(repository, display_prefix):
            states.append(state)
            if len(states) > 4096:
                raise RuntimeError("indexed submodule graph exceeds4096 entries")
            if state.marker == "U":
                raise RuntimeError(
                    f"unmerged indexed submodule state at {state.display_path}; "
                    "resolve the gitlink conflict before recreating bootstrap"
                )
            if state.marker != "-":
                inspect(repository / state.path, state.display_path, depth + 1)

    inspect(root, "")
    return states


def refuse_dirty_submodule_lockfiles(states: list[SubmoduleState]) -> None:
    """Refuse tracked lockfile loss; this gate never changes a worktree."""
    dirty: list[str] = []
    for state in states:
        if state.marker == "-":
            continue
        result = _run_git_read(
            state.repository / state.path,
            ["status", "--porcelain=v1", "--untracked-files=no", "--", "Cargo.lock"],
        )
        if result.stdout.strip():
            dirty.append(state.display_path)
    if dirty:
        locations = "\n".join(f"    - {path}/Cargo.lock" for path in dirty)
        raise RuntimeError(
            "refusing to initialize submodules because tracked Cargo.lock changes "
            "would make the source state ambiguous. No lockfile was changed.\n"
            f"{locations}\n"
            "Commit the changes, stash them with `git -C <submodule> stash push -- "
            "Cargo.lock`, or deliberately discard them with `git -C <submodule> "
            "restore -- Cargo.lock`; then rerun this command."
        )


def _submodule_file_identity(path: Path) -> tuple[int, ...]:
    metadata = path.lstat()
    return (metadata.st_dev, metadata.st_ino, metadata.st_mode, metadata.st_size,
            metadata.st_mtime_ns, metadata.st_ctime_ns)


def _submodule_index_identity(repository: Path) -> tuple[Path, tuple[int, ...], str]:
    value = _run_git_read(repository, ["rev-parse", "--git-path", "index"]).stdout.strip()
    path = Path(value) if Path(value).is_absolute() else repository / value
    if path.is_symlink() or not path.is_file() or os.path.lexists(path.with_name("index.lock")):
        raise RuntimeError(f"submodule parent index is aliased, missing or locked: {repository}")
    before = _submodule_file_identity(path)
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if _submodule_file_identity(path) != before:
        raise RuntimeError(f"submodule parent index changed while read: {repository}")
    return path, before, digest


def _local_submodule_git(arguments: list[str], *, bounded: bool = False, absent_ok: bool = False):
    # Even accidental missing-object reads/checkout cannot perform a raw fetch.
    environment = _provenance_git_environment()
    environment.update(GIT_NO_LAZY_FETCH="1", GIT_OPTIONAL_LOCKS="0", GIT_TERMINAL_PROMPT="0")
    command = _controlled_git_command(["-c", "protocol.https.allow=never",
                                      "-c", "submodule.recurse=false", *arguments])
    if bounded:
        result = _run_submodule_update_process(command, environment=environment,
                     timeout_seconds=SUBMODULE_UPDATE_TIMEOUT_SECONDS, credential_gh=None)
    else:
        result = subprocess.run(command, env=environment, capture_output=True,
                                check=False, timeout=30)
    if result.returncode and not (absent_ok and result.returncode == 1):
        raise RuntimeError(f"fixed local Git submodule operation failed (exit {result.returncode})")
    return result


def _prepare_source_working_cache(repository: Path, commit: str, donor: Path | None):
    if donor is None or sys.platform != "darwin":
        return SimpleNamespace(verify=lambda: {"schema": 1, "method": "normal-checkout", "cloned": 0})
    # Load support source explicitly, without importing a donor or cached bytecode.
    namespace = {"__name__": "trust_source_working_cache", "__file__": str(Path(__file__).with_name("source_working_cache.py"))}
    support = Path(namespace["__file__"])
    if "__trust_source_loader__" in globals():
        namespace = vars(__trust_source_loader__.module("trust_source_working_cache", support))
    else:
        source = support.read_bytes()
        exec(compile(source, str(support), "exec"), namespace)
        if support.read_bytes() != source:
            raise RuntimeError("source working cache support changed while loading")
    environment = _provenance_git_environment()
    environment.update(GIT_NO_LAZY_FETCH="1", GIT_ALLOW_PROTOCOL="")
    return namespace["prepare_checkout"](
        repository, commit, donor,
        git_command=_controlled_git_command(["-c", "submodule.recurse=false"]),
        environment=environment, timeout=SUBMODULE_UPDATE_TIMEOUT_SECONDS,
        verify_physical=_source_working_cache_physical)


def _source_working_cache_physical(repository: Path) -> dict:
    # Reuse the producer's existing complete physical-byte/mode/normalization
    # owner. Index stat caches cannot establish complete source bytes.
    errors = []
    entries = _parse_index_entries(_local_submodule_git(
        ["-C", str(repository), "ls-files", "--stage", "-z"]).stdout, errors, "working DATA cache")
    object_format = _local_submodule_git(["-C", str(repository), "rev-parse", "--show-object-format"]).stdout.decode().strip()
    digest, mismatches, normalized = _capture_working_tree_snapshot(
        repository, entries, object_format, errors, "working DATA cache")
    if errors or mismatches:
        raise RuntimeError("complete working DATA cache physical source audit refused: " + repr(errors + mismatches))
    return {"sha256": digest, "entries": len(entries), "attribute_normalized": normalized}


def _submodule_destination(repository: Path, path: Path):
    current = repository
    parents = [(repository, _submodule_file_identity(repository))]
    for component in path.parts[:-1]:
        current /= component
        if not os.path.lexists(current):
            current.mkdir()
        if current.is_symlink() or not current.is_dir():
            raise RuntimeError(f"submodule parent path is not a real directory: {current}")
        parents.append((current, _submodule_file_identity(current)))
    destination = repository / path
    if not os.path.lexists(destination):
        return destination, None, parents
    if destination.is_symlink() or not destination.is_dir() or any(destination.iterdir()):
        raise RuntimeError(f"missing submodule destination contains unknown existing data: {destination}")
    return destination, _submodule_file_identity(destination), parents


def _revalidate_submodule_destination(destination: Path, identity, parents) -> None:
    for directory, expected in parents:
        if directory.is_symlink() or not directory.is_dir() or _submodule_file_identity(directory)[:3] != expected[:3]:
            raise RuntimeError(f"submodule destination ancestor changed: {directory}")
    if identity is None:
        if os.path.lexists(destination):
            raise RuntimeError(f"missing submodule destination appeared during acquisition: {destination}")
    elif (not destination.is_dir() or destination.is_symlink()
          or _submodule_file_identity(destination) != identity or any(destination.iterdir())):
        raise RuntimeError(f"missing submodule destination changed during acquisition: {destination}")


def _submodule_registration(repository: Path, indexed: IndexedSubmodule):
    value = _run_git_read(repository, ["rev-parse", "--git-path", "config"]).stdout.strip()
    config = Path(value) if Path(value).is_absolute() else repository / value
    if config.is_symlink() or not config.is_file() or os.path.lexists(config.with_name("config.lock")):
        raise RuntimeError(f"submodule parent configuration is aliased or locked: {repository}")
    identity = _submodule_file_identity(config)
    data = config.read_bytes()
    values = _submodule_config_values(repository, f"submodule.{indexed.name}.url")
    if values and values != [indexed.url]:
        raise RuntimeError(f"missing submodule registration differs from indexed URL: {indexed.path}")
    active = _submodule_config_values(repository, f"submodule.{indexed.name}.active", boolean=True)
    if active and (len(active) != 1 or _git_config_bool(active[0]) is not True):
        raise RuntimeError(f"missing submodule is explicitly inactive: {indexed.path}")
    if _submodule_file_identity(config) != identity or config.read_bytes() != data:
        raise RuntimeError("parent registration changed while read")
    return config, identity, data, not values


def _restore_submodule_registration(config: Path, expected, original: bytes, mode: int) -> None:
    if _submodule_file_identity(config) != expected:
        raise RuntimeError("submodule registration changed concurrently; refusing rollback")
    lock = config.with_name("config.lock")
    descriptor = os.open(lock, os.O_WRONLY | os.O_CREAT | os.O_EXCL, stat.S_IMODE(mode))
    lock_identity = _submodule_file_identity(lock)
    try:
        with os.fdopen(descriptor, "wb") as output:
            output.write(original); output.flush(); os.fsync(output.fileno())
        if _submodule_file_identity(config) != expected:
            raise RuntimeError("submodule registration changed before rollback")
        os.replace(lock, config)
    finally:
        if os.path.lexists(lock) and lock.lstat().st_ino == lock_identity[1]:
            lock.unlink()


def _register_indexed_submodule(repository: Path, indexed: IndexedSubmodule, registration):
    config, identity, data, missing = registration
    if _submodule_file_identity(config) != identity or config.read_bytes() != data:
        raise RuntimeError("parent submodule registration changed during acquisition")
    if not missing:
        return None
    _local_submodule_git(["-C", str(repository), "config", "--local", "--add",
                          f"submodule.{indexed.name}.url", indexed.url])
    return _submodule_file_identity(config)


def _validate_staged_submodule(stage: Path, identity) -> None:
    if stage.is_symlink() or _submodule_file_identity(stage)[:2] != identity[:2]:
        raise RuntimeError("owned submodule staging directory was replaced")
    git = stage / ".git"
    if git.is_symlink() or not git.is_dir() or os.path.lexists(git / "commondir"):
        raise RuntimeError("staged child must own one real .git directory")
    for leaf in [git / "objects/info/alternates", git / "objects/info/http-alternates"]:
        if os.path.lexists(leaf):
            raise RuntimeError("staged child object alternates are forbidden")
    population = 0
    for root, directories, files in os.walk(git, followlinks=False):
        for name in directories + files:
            population += 1
            leaf = Path(root) / name
            if (population > 1_000_000 or leaf.is_symlink()
                    or not (leaf.is_dir() or leaf.is_file())
                    or (leaf.is_file() and leaf.stat().st_nlink != 1)):
                raise RuntimeError("staged child Git custody contains aliases/special files or exceeds its bound")
    _reject_local_git_execution_authority(stage, require_https_submodules=True)
    if any(key in {"extensions.partialclone", "extensions.worktreeconfig", "core.worktree"} or key.endswith((".promisor", ".partialclonefilter"))
           for key, _ in _read_repository_git_config_scope(stage, "local")):
        raise RuntimeError("staged child may not defer objects or redirect worktree custody")
    directory = _local_submodule_git(["-C", str(stage), "rev-parse", "--absolute-git-dir"]).stdout.decode().strip()
    common = _local_submodule_git(["-C", str(stage), "rev-parse", "--git-common-dir"]).stdout.decode().strip()
    if Path(directory).resolve() != git.resolve() or (stage / common).resolve() != git.resolve():
        raise RuntimeError("staged child Git custody redirects outside its owned directory")


def _submodule_exclusive_move(parent: Path, container: Path):
    """Pin both owned directories; atomic install never replaces any destination."""
    if os.name == "nt":
        # Windows rename refuses existing destinations; bookend both ancestors.
        identities = {path: _submodule_file_identity(path)[:3] for path in (parent, container)}
        def move(source: Path, destination: Path) -> None:
            for path, expected in identities.items():
                if path.is_symlink() or _submodule_file_identity(path)[:3] != expected:
                    raise RuntimeError("submodule rename directory changed")
            os.rename(source, destination)
            for path, expected in identities.items():
                if path.is_symlink() or _submodule_file_identity(path)[:3] != expected:
                    raise RuntimeError("submodule rename directory changed")
        return move, lambda: None
    import ctypes
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    parent_fd = os.open(parent, flags)
    container_fd = None
    try:
        container_fd = os.open(container.name, flags, dir_fd=parent_fd)
        descriptors = {parent: parent_fd, container: container_fd}
        library = ctypes.CDLL(None, use_errno=True)
        if sys.platform == "darwin":
            # Existing volume capability query only; its LLVM mover is unused.
            _empty_llvm_exclusive_rename(parent_fd)
            rename = library.renameatx_np
            rename.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
            exclusive = 4
        elif sys.platform.startswith("linux"):
            rename = library.renameat2
            rename.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
            exclusive = 1
        else:
            raise RuntimeError("submodule installation requires supported atomic no-replace rename")
        rename.restype = ctypes.c_int
        def bind_directories() -> None:
            for path, descriptor in descriptors.items():
                metadata = os.fstat(descriptor)
                if (path.is_symlink() or _submodule_file_identity(path)[:3] !=
                        (metadata.st_dev, metadata.st_ino, metadata.st_mode)):
                    raise RuntimeError("pinned submodule rename directory changed")
        def move(source: Path, destination: Path) -> None:
            if source.parent not in descriptors or destination.parent not in descriptors:
                raise RuntimeError("submodule rename escapes owned directories")
            bind_directories()
            if rename(descriptors[source.parent], os.fsencode(source.name),
                      descriptors[destination.parent], os.fsencode(destination.name), exclusive) != 0:
                error = ctypes.get_errno()
                raise OSError(error, "exclusive submodule rename: " + os.strerror(error))
            bind_directories()
        def close() -> None:
            os.close(container_fd)
            os.close(parent_fd)
        bind_directories()
        return move, close
    except BaseException:
        if container_fd is not None:
            os.close(container_fd)
        os.close(parent_fd)
        raise


@contextmanager
def _submodule_owner_lock(root: Path):
    value = _run_git_read(root, ["rev-parse", "--git-path", "trust-bootstrap-submodules.lock"]).stdout.strip()
    lock = Path(value) if Path(value).is_absolute() else root / value
    try:
        descriptor = os.open(lock, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError as error:
        raise RuntimeError("another submodule materialization owns the existing lock") from error
    identity = _submodule_file_identity(lock)
    try:
        os.write(descriptor, f"owned by bootstrap pid {os.getpid()}\n".encode())
        yield
    finally:
        os.close(descriptor)
        if os.path.lexists(lock):
            if _submodule_file_identity(lock)[:2] != identity[:2]:
                raise RuntimeError("submodule owner lock changed; preserving unknown replacement")
            lock.unlink()


def _materialize_bridge_source_witnesses(root: Path) -> int:
    """Restore exact historical object DATA under the existing submodule owner.

    The normal selected checkout supplies the producer subtree. A rewritten
    source publication can omit the original commit and root tree that bind
    that subtree to the unchanged bridge provenance. These tiny raw witnesses
    supply only those objects; the existing bridge verifier remains authority
    for the original anchor, full producer/reader closure and artifact bytes.
    """
    import tomllib

    environment = _provenance_git_environment()
    environment.update(GIT_NO_LAZY_FETCH="1", GIT_ALLOW_PROTOCOL="", GIT_GRAFT_FILE=os.devnull)

    def git(repository: Path, *args: str, data: bytes | None = None) -> bytes:
        result = subprocess.run(
            _controlled_git_command(["-C", str(repository), *args]),
            input=data, capture_output=True, check=False, env=environment, timeout=30,
        )
        if result.returncode:
            raise RuntimeError(f"bridge source DATA Git operation refused (exit {result.returncode})")
        return result.stdout

    prefix = "data/bridge-source-witnesses/trust-ir/objects"
    if not git(root, "ls-files", "--", prefix).strip():
        return 0
    _reject_local_git_execution_authority(root, require_https_submodules=True)
    index = _submodule_index_identity(root)

    def indexed_blob(path: str) -> bytes:
        # write-tree updates the index's cache-tree extension even with
        # optional locks disabled. Read its exact stage-0 blob instead, with
        # the original index identity held across every read and object write.
        listing = git(root, "ls-files", "--stage", "-z", "--", path)
        match = re.fullmatch(rb"100(?:644|755) ([0-9a-f]{40}) 0\t" + re.escape(path.encode()) + b"\0", listing)
        if match is None:
            raise RuntimeError("bridge source witness must be one exact indexed regular blob")
        raw = git(root, "cat-file", "blob", match[1].decode("ascii"))
        if len(raw) > 1024 * 1024 or hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest().encode() != match[1]:
            raise RuntimeError("bridge source witness blob has a different original hash or exceeds its bound")
        return raw

    manifest = tomllib.loads(indexed_blob("crates/trust-clean/fixtures/trustir-oleans/MANIFEST.toml").decode("utf-8"))
    if "source_reuse" not in manifest:
        return 0
    original = manifest.get("provenance", {}).get("trustir_commit")
    selected = manifest["source_reuse"].get("selected_trustir_commit")
    if not all(isinstance(value, str) and re.fullmatch("[0-9a-f]{40}", value) for value in (original, selected)):
        raise RuntimeError("bridge source witness requires exact original and selected IR identities")
    commit_path = f"{prefix}/commit/{original}"
    # A witness is optional source DATA, never a substitute for a missing
    # verifier input. Other source revisions retain their normal acquisition.
    if not git(root, "ls-files", "--stage", "-z", "--", commit_path):
        return 0
    commit = indexed_blob(commit_path)
    header = re.match(rb"tree ([0-9a-f]{40})\n", commit)
    if header is None:
        raise RuntimeError("bridge source witness commit has no exact root tree")
    root_tree = header[1].decode("ascii")
    objects = [("commit", original, commit), ("tree", root_tree, indexed_blob(f"{prefix}/tree/{root_tree}"))]
    for kind, oid, raw in objects:
        if hashlib.sha1(f"{kind} {len(raw)}\0".encode() + raw).hexdigest() != oid:
            raise RuntimeError("bridge source witness canonical type/object hash differs")
    declarations = {entry.path.as_posix(): entry for entry in _indexed_submodules(root)}
    entry = declarations.get("first-party/trust-ir")
    if entry is None or entry.oid != selected:
        raise RuntimeError("bridge source witness selection differs from indexed IR gitlink")
    child = root / "first-party/trust-ir"
    if child.resolve(strict=True) != child:
        raise RuntimeError("bridge source witness destination must be its exact physical root")
    _reject_local_git_execution_authority(child, require_https_submodules=True)
    if Path(os.fsdecode(git(child, "rev-parse", "--show-toplevel")).strip()).resolve() != child:
        raise RuntimeError("bridge source witness destination is not the selected IR repository")
    if git(child, "rev-parse", "HEAD").decode().strip() != selected:
        raise RuntimeError("bridge source witness requires the exact selected IR checkout")

    def book(repository: Path):
        config_name = os.fsdecode(git(repository, "rev-parse", "--git-path", "config")).strip()
        config = Path(config_name)
        if not config.is_absolute():
            config = repository / config
        if config.is_symlink() or not config.is_file():
            raise RuntimeError("bridge source witness configuration is not a regular file")
        return (git(repository, "rev-parse", "HEAD"), git(repository, "for-each-ref"),
                config.read_bytes(), _submodule_index_identity(repository),
                git(repository, "status", "--porcelain=v1", "--untracked-files=no"))

    before = (book(root), book(child))
    if _submodule_index_identity(root) != index:
        raise RuntimeError("bridge source witness index changed before object writes")
    added = 0
    try:
        for kind, oid, raw in objects:
            observed = git(child, "cat-file", "--batch-check", data=(oid + "\n").encode())
            if observed == (oid + " missing\n").encode():
                written = git(child, "hash-object", "-w", "-t", kind, "--stdin", data=raw).decode().strip()
                if written != oid:
                    raise RuntimeError("bridge source witness wrote a different object")
                added += 1
            elif observed != f"{oid} {kind} {len(raw)}\n".encode():
                raise RuntimeError("bridge source witness existing object has a different type or size")
            if git(child, "cat-file", kind, oid) != raw:
                raise RuntimeError("bridge source witness original object bytes differ")
    finally:
        if _submodule_index_identity(root) != index or (book(root), book(child)) != before:
            raise RuntimeError("bridge source witness source/destination bookends changed")
    if added:
        print(f"  restored {added} exact bridge provenance source DATA object(s); no history or refs")
    return added


def materialize_bridge_source_witnesses(root: Path) -> int:
    """Explicit local source-DATA restoration, sharing submodule exclusion."""
    root = root.resolve(strict=True)
    with _submodule_owner_lock(root):
        return _materialize_bridge_source_witnesses(root)


def _install_missing_submodule(repository: Path, indexed: IndexedSubmodule,
                               *, checkout_cache: Path | None = None,
                               working_cache: Path | None = None) -> None:
    index = _submodule_index_identity(repository)
    indexed_before = _indexed_submodules(repository)
    if indexed not in indexed_before:
        raise RuntimeError("selected indexed submodule changed before acquisition")
    destination, destination_identity, parents = _submodule_destination(repository, indexed.path)
    registration = _submodule_registration(repository, indexed)
    container = Path(tempfile.mkdtemp(prefix=".trust-submodule-", dir=destination.parent))
    container_identity = _submodule_file_identity(container)
    stage = container / "source"
    stage.mkdir(mode=0o700)
    identity = _submodule_file_identity(stage)
    preserved = container / "original-empty"
    registered = None
    installed = False
    failure = None
    close_move = lambda: None
    try:
        move, close_move = _submodule_exclusive_move(destination.parent, container)
        _local_submodule_git(["init", "--quiet", "--template=", "--object-format=sha1", str(stage)])
        if _submodule_index_identity(repository) != index or _indexed_submodules(repository) != indexed_before:
            raise RuntimeError("parent submodule index changed before acquisition")
        try:
            if checkout_cache is None:
                _agh_source_fetch(indexed.url, stage, indexed.oid,
                                  "refs/agh/bootstrap-submodule/" + indexed.oid)
            else:
                _agh_source_fetch(indexed.url, stage, indexed.oid,
                                  "refs/agh/bootstrap-submodule/" + indexed.oid,
                                  checkout_cache=checkout_cache)
        except subprocess.TimeoutExpired as error:
            raise RuntimeError(f"owner-routed Agh submodule acquisition timed out after {SUBMODULE_UPDATE_TIMEOUT_SECONDS}s") from error
        _validate_staged_submodule(stage, identity)
        private_ref = "refs/agh/bootstrap-submodule/" + indexed.oid
        fetched = _local_submodule_git(["-C", str(stage), "rev-parse", "--verify", private_ref]).stdout.decode().strip()
        if fetched != indexed.oid:
            raise RuntimeError("Agh private ref differs from the exact indexed commit")
        # Registration/checkout are fixed local operations; only Agh fetched.
        _local_submodule_git(["-C", str(stage), "config", "--local", "--replace-all", "remote.origin.url", indexed.url])
        _local_submodule_git(["-C", str(stage), "config", "--local", "--replace-all", "remote.origin.fetch", "+refs/heads/*:refs/remotes/origin/*"])
        kind = _local_submodule_git(["-C", str(stage), "cat-file", "-t", indexed.oid]).stdout.strip()
        if kind != b"commit":
            raise RuntimeError("indexed submodule OID is not the exact commit object")
        working = _prepare_source_working_cache(
            stage, indexed.oid, working_cache if working_cache is not None else checkout_cache)
        _local_submodule_git(["-C", str(stage), "checkout", "--quiet", "--detach",
                              "--no-recurse-submodules", indexed.oid, "--"], bounded=True)
        working.verify()
        _validate_staged_submodule(stage, identity)
        head = _local_submodule_git(["-C", str(stage), "rev-parse", "HEAD"]).stdout.decode().strip()
        detached = _local_submodule_git(["-C", str(stage), "symbolic-ref", "--quiet", "HEAD"], absent_ok=True)
        if head != indexed.oid or detached.returncode != 1:
            raise RuntimeError("staged submodule is not detached at the indexed commit")
        status = _local_submodule_git(["-C", str(stage), "status", "--porcelain=v1", "--untracked-files=all", "--ignored", "--ignore-submodules=all"])
        if status.stdout.strip():
            raise RuntimeError("staged submodule has changed or unknown source files")
        _indexed_submodules(stage)  # Validate nested indexed URL/OID before installation.
        if _submodule_index_identity(repository) != index or _indexed_submodules(repository) != indexed_before:
            raise RuntimeError("parent submodule index changed during acquisition")
        _revalidate_submodule_destination(destination, destination_identity, parents)
        registered = _register_indexed_submodule(repository, indexed, registration)
        if _submodule_index_identity(repository) != index:
            raise RuntimeError("parent submodule index changed before installation")
        _revalidate_submodule_destination(destination, destination_identity, parents)
        if destination_identity is not None:
            move(destination, preserved)
            if (not preserved.is_dir() or preserved.is_symlink() or any(preserved.iterdir())
                    or _submodule_file_identity(preserved)[:3] != destination_identity[:3]):
                raise RuntimeError("empty submodule destination changed before preservation")
            stage.chmod(stat.S_IMODE(destination_identity[2]))
        move(stage, destination)  # Never overwrite even a newly appeared EMPTY directory.
        installed = True
        if os.path.lexists(preserved):
            if (preserved.is_symlink() or not preserved.is_dir() or any(preserved.iterdir())
                    or _submodule_file_identity(preserved)[:3] != destination_identity[:3]):
                raise RuntimeError("preserved submodule placeholder changed; retaining its contents")
            preserved.rmdir()
    except BaseException as error:
        failure = error
        if not installed and os.path.lexists(preserved):
            try:
                move(preserved, destination)
            except BaseException as cleanup:
                _add_exception_note(error, f"original submodule destination retained at {preserved}; exclusive restore refused: {cleanup}")
        if registered is not None and not installed:
            try:
                _restore_submodule_registration(registration[0], registered, registration[2], registration[1][2])
            except BaseException as cleanup:
                _add_exception_note(error, f"submodule registration rollback also refused: {cleanup}")
        raise
    finally:
        try:
            if container.is_symlink() or _submodule_file_identity(container)[:2] != container_identity[:2]:
                raise RuntimeError("refusing cleanup of replaced submodule staging container")
            if os.path.lexists(stage):
                if stage.is_symlink() or _submodule_file_identity(stage)[:2] != identity[:2]:
                    raise RuntimeError("refusing cleanup of replaced submodule staging directory")
                if getattr(failure, "retain_source_working_cache", False):
                    _add_exception_note(failure, f"ambiguous working DATA cache custody retained at {stage}")
                else:
                    shutil.rmtree(stage)
            if not any(container.iterdir()):
                container.rmdir()  # Unknown/preserved entries are NEVER removed.
        except BaseException as cleanup:
            if failure is None:
                raise
            _add_exception_note(failure, f"owned submodule staging cleanup also refused: {cleanup}")
        finally:
            close_move()


def _initialize_missing_submodules(repository: Path, display_prefix: str = "", *, depth: int = 0,
                                   population: list[int] | None = None,
                                   checkout_caches: dict[str, Path] | None = None,
                                   working_caches: dict[str, Path] | None = None) -> int:
    """Agh-acquire only truly missing children; never move an existing worktree."""
    if depth > 64:
        raise RuntimeError("indexed submodule recursion exceeds64 levels")
    if population is None:
        population = [0]
    initialized = 0
    indexed = {entry.path: entry for entry in _indexed_submodules(repository)}
    for state in _direct_submodule_states(repository, display_prefix):
        population[0] += 1
        if population[0] > 4096:
            raise RuntimeError("indexed submodule population exceeds4096")
        if state.marker == "U":
            raise RuntimeError(f"unmerged indexed submodule state at {state.display_path}")
        if state.marker == "-":
            print(f"  Agh acquiring exact indexed commit for {state.display_path}")
            cache = (checkout_caches or {}).get(state.display_path)
            options = {}
            if cache is not None:
                print("    using Agh exact checkout closure with an explicit immutable object cache")
                options["checkout_cache"] = cache
            working = (working_caches or {}).get(state.display_path)
            if working is not None:
                print("    using a separate byte-checked native CoW working DATA donor")
                options["working_cache"] = working
            _install_missing_submodule(repository, indexed[state.path], **options)
            initialized += 1
        elif state.needs_registration:
            before = _submodule_index_identity(repository)
            _register_indexed_submodule(repository, indexed[state.path],
                                       _submodule_registration(repository, indexed[state.path]))
            if _submodule_index_identity(repository) != before:
                raise RuntimeError("parent index changed while registering an existing child")
        initialized += _initialize_missing_submodules(repository / state.path, state.display_path,
                         depth=depth + 1, population=population,
                         checkout_caches=checkout_caches,
                         **({"working_caches": working_caches} if working_caches else {}))
    return initialized


def ensure_submodules(root: Path, *, checkout_caches: dict[str, Path] | None = None,
                      working_caches: dict[str, Path] | None = None) -> None:
    """Acquire missing indexed commits through Agh only, preserving existing children.

    Every known indexed URL/OID is validated before acquisition. New children
    are independently staged and checked out by closed fixed-OS Git; no GitHub
    Git transport, credential helper, token extraction or terminal fallback runs.
    """
    before = _inspect_submodule_tree(root)
    refuse_dirty_submodule_lockfiles(before)
    if not any(state.marker == "-" or state.needs_registration for state in before):
        print("  complete indexed recursive submodule graph already materialized")
        scrub_pat_from_remotes(root)
        materialize_bridge_source_witnesses(root)
        return
    _materialize_missing_submodules(root, checkout_caches=checkout_caches,
                                   **({"working_caches": working_caches} if working_caches else {}))


def submodule_registrations_off_index(root: Path) -> list[tuple[str, list[str], str]]:
    """Each registration of `root`'s direct submodules that is not its indexed URL: name, values, URL.

    Reads only. A linked worktree shares these registrations with its clone and
    every other worktree of it, and ensure_submodules acquires only the indexed
    URL through Agh, so a caller that must not change its clone's configuration
    asks first. An absent registration is not listed: ensure_submodules adds it
    with the indexed URL, as `git submodule init` does.
    """
    # The registrations are read as recorded: the URL policy of the reads that
    # validate the indexed declarations would refuse a local path before naming it.
    _reject_local_git_execution_authority(root)
    if not _local_submodule_git(["-C", str(root), "ls-files", "--", ".gitmodules"]).stdout.strip():
        return []
    registered: dict[str, list[str]] = {}
    for scope, key, value in _repository_git_config_records(root):
        if scope == "local" and key.startswith("submodule.") and key.endswith(".url"):
            registered.setdefault(key, []).append(value)
    off: list[tuple[str, list[str], str]] = []
    for key, values in registered.items():
        indexed = _local_submodule_git(["-C", str(root), "config", "--no-includes", "--null", "--blob",
                                        ":.gitmodules", "--get-all", key], absent_ok=True)
        urls = indexed.stdout.decode("utf-8", errors="strict").split("\0")[:-1] if indexed.returncode == 0 else []
        # A registration with no single indexed URL is left for ensure_submodules to judge.
        if len(urls) == 1 and values != urls:
            off.append((key[len("submodule."):-len(".url")], values, urls[0]))
    return off


def _materialize_missing_submodules(root: Path, *, checkout_caches: dict[str, Path] | None = None,
                                   working_caches: dict[str, Path] | None = None) -> None:
    """Hold one owner through acquisition, cleanup and complete reinspection."""
    with _submodule_owner_lock(root):
        try:
            refuse_dirty_submodule_lockfiles(_inspect_submodule_tree(root))
            initialized = _initialize_missing_submodules(root, checkout_caches=checkout_caches,
                             **({"working_caches": working_caches} if working_caches else {}))
        except BaseException as materialization_error:
            try:
                scrub_pat_from_remotes(root)
            except BaseException as scrub_error:
                _add_exception_note(materialization_error, f"post-failure credential cleanup also failed closed: {scrub_error}")
            raise
        scrub_pat_from_remotes(root)
        after = _inspect_submodule_tree(root)
        refuse_dirty_submodule_lockfiles(after)
        if any(state.marker == "-" or state.needs_registration for state in after):
            raise RuntimeError("recursive indexed submodule acquisition did not complete")
        _materialize_bridge_source_witnesses(root)
        print(f"  materialized {initialized} missing indexed submodule(s) through Agh")


def _clean_remote_url_credentials(url: str) -> str:
    """Remove HTTP userinfo without reproducing it in a diagnostic."""
    if any(ord(character) < 32 or ord(character) == 127 for character in url):
        raise RuntimeError("origin remote URL contains control characters")
    lowered = url.lower()
    if not (lowered.startswith("https://") or lowered.startswith("http://")):
        return url
    if "?" in url or "#" in url:
        raise RuntimeError(
            "origin HTTP remote URL contains a query or fragment that may carry "
            "credentials; replace it with a credential-free URL"
        )
    scheme_end = url.index("://") + 3
    path_start = url.find("/", scheme_end)
    if path_start < 0:
        path_start = len(url)
    authority = url[scheme_end:path_start]
    if "@" not in authority:
        return url
    clean_authority = authority.rsplit("@", 1)[1]
    if not clean_authority:
        raise RuntimeError("origin HTTP remote URL has an invalid authority")
    return url[:scheme_end] + clean_authority + url[path_start:]


def _replace_git_config_values(
    repository: Path, scope: str, key: str, values: list[str]
) -> None:
    """Replace every value for one known key in one audited config scope."""
    if not values:
        return
    commands = [
        ["config", f"--{scope}", "--replace-all", key, values[0]],
        *(
            ["config", f"--{scope}", "--add", key, value]
            for value in values[1:]
        ),
    ]
    for arguments in commands:
        try:
            result = subprocess.run(
                _controlled_git_command(["-C", str(repository), *arguments]),
                capture_output=True,
                check=False,
                env=_provenance_git_environment(),
                timeout=30,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise RuntimeError(
                f"could not scrub embedded credentials from {repository}/origin"
            ) from error
        if result.returncode != 0:
            raise RuntimeError(
                f"could not scrub embedded credentials from {repository}/origin "
                f"(Git exit {result.returncode})"
            )


def _scrub_repository_origin_credentials(repository: Path) -> None:
    """Scrub every fetch/push URL in the accepted local config, or fail."""
    _reject_local_git_execution_authority(
        repository, require_https_submodules=True
    )
    grouped: dict[tuple[str, str], list[str]] = {}
    for scope, key, value in _repository_git_config_records(repository):
        if key in {"remote.origin.url", "remote.origin.pushurl"}:
            grouped.setdefault((scope, key), []).append(value)

    changed = False
    for (scope, key), values in grouped.items():
        cleaned = [_clean_remote_url_credentials(value) for value in values]
        if cleaned != values:
            _replace_git_config_values(repository, scope, key, cleaned)
            changed = True
    if changed:
        print(f"  scrubbed embedded credentials from {repository}/origin")

    # Re-read the edited scopes and reapply the complete authority gate. Any
    # read/edit failure is fatal; absence of an origin is represented by no key,
    # not by swallowing an arbitrary Git error.
    for _scope, key, value in _repository_git_config_records(repository):
        if key in {"remote.origin.url", "remote.origin.pushurl"}:
            if _clean_remote_url_credentials(value) != value:
                raise RuntimeError(
                    f"embedded credentials remain in {repository}/origin"
                )
    _reject_local_git_execution_authority(
        repository, require_https_submodules=True
    )


def scrub_pat_from_remotes(root: Path) -> None:
    """Scrub embedded HTTP credentials from every materialized origin.

    Visit and scrub a repository before asking Git to inspect its children. This
    ordering prevents a partial/promisor checkout from consuming an embedded
    origin credential while discovering its indexed submodules.
    """

    def scrub_tree(repository: Path, display_prefix: str) -> None:
        _scrub_repository_origin_credentials(repository)
        for state in _direct_submodule_states(repository, display_prefix):
            if state.marker == "U":
                raise RuntimeError(
                    f"unmerged indexed submodule state at {state.display_path}; "
                    "resolve the gitlink conflict before recreating bootstrap"
                )
            if state.marker != "-":
                scrub_tree(repository / state.path, state.display_path)

    scrub_tree(root, "")


CONFIG_TEMPLATE = """\
# Generated by scripts/recreate_bootstrap.py ({mode} stage0 mode).
# Edit freely; rerunning the recreator will not overwrite an existing
# config.toml / bootstrap.toml unless you pass --force-config.

profile = "compiler"
change-id = "ignore"

[build]
python = "{python}"
# Trust: first-party/ submodules are managed by this script / the developer
# ("most pulled forward" toolchain policy). Disable bootstrap's unconditional
# `git submodule update` so it can never reset deliberately-advanced pins back
# to the committed gitlink SHA. Standard upstream submodules are vendored as
# plain source trees (not in .gitmodules), so nothing else is affected;
# recreate_bootstrap.py materializes first-party/ itself on a fresh clone.
submodules = false
docs = false
compiler-docs = false
extended = true
# The profiler runtime (compiler-rt, vendored in src/llvm-project) backs
# -Cinstrument-coverage; without it the suite.coverage rows run nothing.
profiler = true
{targets_block}# Inherit the tool allowlist from bootstrap.compiler.toml. Omitting `tools`
# here does not clear the profile's list. That profile selects the public Trust
# tools, including trustup, clean and ty; AY is also a source-backed compiler
# battery. Keep the complete selection in the shared profile so generated and
# hand-written compiler-profile configurations build the same tool surface.
# An explicit `tools = [...]` replaces the inherited list, rather than adding
# to it, and can omit required tools.
{stage0_block}
[llvm]
download-ci-llvm = false
ninja = true
optimize = true
# Inherit bootstrap's supported LLVM targets, including experimental targets.
# The complete compiletest suite queries other architectures even when the
# shipped std targets above are limited to the two Apple architectures.

[rust]
download-rustc = false
channel = "trust"
# The compiler profile turns on debug assertions and overflow checks; keep them
# out of std so it carries the Asserts the sealed channel's release std does
# (KNOWN_HAZARDS: a debug std turns ~43 tests/ui/trust revisions red).
debug-assertions-std = false
overflow-checks-std = false
# Production-shaped std paths: panic locations and diagnostics embed
# /rustc/<ver>/library/... exactly like upstream dist builds, so upstream ui
# test expectations (library/core/src/... after test normalization) match
# without local blessing.
remap-debuginfo = true
# Trust: build the verified trust-cg codegen backend alongside LLVM so
# `-Zcodegen-backend=trust_cg` works out of the box. Without this the shipped
# trustc fails with "failed to find a codegen-backends folder" — the backend's
# availability must never silently depend on a machine-local config.
codegen-backends = ["llvm", "trust-cg"]
# The receipts bind every compiler this script builds, and the producer of each, to
# the root HEAD through `trustc -vV`'s commit-hash. A dev stage-1 build names its
# sources there instead (TB1), so name the commit at every stage, as a stage-2 build
# always does; the config's digest binds the choice.
trust-source-identity = false
# Submodules under first-party/ drift behind current nightly and surface
# legitimate warnings (deprecated hidden lifetimes, non-camel-case enum
# variants from a rust_mc → trust_mc rename, dead code). Trust's release
# build enforces zero warnings via a ratchet; for a fresh-checkout dev
# build we relax to warn-only so the toolchain comes up. Fix the warnings
# in the affected submodules, then flip this back on.
deny-warnings = false
{rust_lld_block}
[install]
prefix = "{prefix}"
sysconfdir = "etc"
"""


GENESIS_STAGE0_BLOCK = """\
# Point each stage0 tool at the genesis adapter so bootstrap never tries to
# download a `trust-*` tarball from the empty local dist server.
# Trust: config KEYS keep their upstream-compatible names. Bootstrap uses the
# Cargo-compatible identity because branded Targo accepts only authenticated
# verification or a human-visible --unverified argument.
rustc = "{stage0}/bin/trustc"
cargo = "{stage0}/bin/cargo"
rustdoc = "{stage0}/bin/trustdoc"
rustfmt = "{stage0}/bin/trustfmt"
cargo-clippy = "{stage0}/bin/targo-tippy"
"""

ATPKG_STAGE0_TOOLS = {
    "rustc": "trustc",
    "cargo": "cargo",
    "rustdoc": "trustdoc",
    "rustfmt": "trustfmt",
    "cargo-clippy": "targo-tippy",
}
STAGE0_OVERRIDE_KEYS = frozenset({"rustc", "cargo", "rustdoc", "rustfmt", "cargo-clippy"})


def _atpkg_prefix() -> Path:
    # Mirror atpkg's default per-user prefix on supported native mint hosts.
    # Never infer pack authority from PATH, ATPKG_BIN, or a staged directory.
    system = platform.system()
    if system == "Darwin":
        return Path.home() / "Library/Application Support/aterm/pkg"
    if system == "Linux":
        return Path.home() / ".local/share/aterm/pkg"
    raise ValueError(f"unsupported native atpkg bootstrap platform: {system}")


def _atpkg_file_identity(path: Path, *, within: Path | None = None) -> dict[str, object]:
    real = path.resolve(strict=True)
    if within is not None and not real.is_relative_to(within):
        raise ValueError(f"atpkg tool escapes selected pack: {path} -> {real}")
    mode = real.stat().st_mode
    if not stat.S_ISREG(mode) or not mode & 0o111:
        raise ValueError(f"atpkg tool is not an executable regular file: {path}")
    return {
        "selected_local_path": str(path),
        "resolved_real_path": str(real),
        "mode": stat.S_IMODE(mode),
        "sha256": _sha256_file(real),
    }


def _atpkg_shim_target(path: Path) -> Path | None:
    # Mirror atpkg's Unix shim reader without executing shell input. Old installs
    # use symlinks; current installs use a bounded, single-quoted exec stub.
    if path.is_symlink():
        return Path(os.readlink(path))
    if not path.is_file():
        return None
    with path.open("rb") as source:
        content = source.read(64 * 1024 + 1)
    if len(content) > 64 * 1024:
        return None
    try:
        lines = content.decode("utf-8").splitlines()
    except UnicodeError:
        return None
    for line in lines:
        line = line.strip()
        if line.startswith("exec '") and line.endswith("' \"$@\""):
            return Path(line[6:-6].replace("'\\''", "'"))
    return None


def _capture_atpkg_pack(build_table: dict[str, object] | None = None) -> dict[str, object]:
    import tomllib

    prefix = _atpkg_prefix().resolve(strict=True)
    store = prefix / "store/trust"
    current = store / "current"
    if not current.is_symlink():
        raise ValueError(f"atpkg trust current must name the active pack: {current}")
    pack = current.resolve(strict=True)
    if (
        not pack.name.isascii()
        or not pack.name.isdigit()
        or str(int(pack.name)) != pack.name
        or int(pack.name) > (1 << 64) - 1
        or pack.parent != store.resolve(strict=True)
        or (store / pack.name).is_symlink()
    ):
        raise ValueError(f"atpkg trust current is not a direct numbered store pack: {pack}")
    if (pack / "toolchain").is_symlink():
        raise ValueError("atpkg WiredSysroot is not exact-tree-attestable")
    tools = {}
    for key, name in ATPKG_STAGE0_TOOLS.items():
        expected = pack / "bin" / name
        if build_table is not None and build_table.get(key) != str(expected):
            raise ValueError(f"atpkg stage0 {key} must name exactly {expected}")
        tools[key] = _atpkg_file_identity(expected, within=pack)

    # active_builds() is last-writer-wins if managed shims name different builds.
    # Refuse that ambiguity, including extra Trust shims outside the five tools.
    # Cargo itself is a private compatibility identity; the managed shim is targo.
    required_shims = {"trustc", "targo", "trustdoc", "trustfmt", "targo-tippy"}
    active_shims = {}
    for shim in sorted((prefix / "bin").iterdir()):
        target = _atpkg_shim_target(shim)
        if shim.name in required_shims and target != pack / "bin" / shim.name:
            raise ValueError(f"atpkg active shim disagrees with current pack: {shim}")
        if target is None or not any(
            target.parts[index:index + 2] == ("store", "trust")
            for index in range(len(target.parts) - 1)
        ):
            continue
        if (
            not target.is_relative_to(pack)
            or ".." in target.parts
            or not target.resolve(strict=True).is_relative_to(pack)
        ):
            raise ValueError(f"atpkg mixed or missing active Trust shim target: {shim} -> {target}")
        active_shims[shim.name] = {
            "target": str(target),
            "identity": _atpkg_file_identity(shim),
        }
    if not required_shims.issubset(active_shims):
        raise ValueError("atpkg active Trust shim roster is incomplete")

    status_path = prefix / "status.toml"
    if status_path.is_symlink() or not status_path.is_file():
        raise ValueError(f"atpkg local status must be a regular file: {status_path}")
    with status_path.open("rb") as source:
        status_bytes = source.read(2 * 1024 * 1024 + 1)
    if len(status_bytes) > 2 * 1024 * 1024:
        raise ValueError("atpkg local status exceeds the 2 MiB metadata limit")
    status = tomllib.loads(status_bytes.decode("utf-8"))
    programs = status.get("programs")
    if (
        type(status.get("schema")) is not int
        or status["schema"] != 1
        or not isinstance(programs, dict)
        or len(programs) > 2048
    ):
        raise ValueError("atpkg local status schema/program roster is invalid")
    trust = programs.get("trust")
    if not isinstance(trust, dict) or type(trust.get("installed_build")) is not int:
        raise ValueError("atpkg local status is missing the installed Trust build")
    tree_root = trust.get("tree_root")
    if (
        trust["installed_build"] != int(pack.name)
        or not isinstance(tree_root, str)
        or len(tree_root) != 64
        or any(char not in "0123456789abcdefABCDEF" for char in tree_root)
    ):
        raise ValueError("atpkg local status build/tree_root does not bind the active pack")
    return {
        "pack_local_path": str(pack),
        "build": int(pack.name),
        "current_link_target": os.readlink(current),
        "configured_tools": tools,
        "active_shims": active_shims,
        # Only the selected record is load-bearing; unrelated package updates and
        # diagnostic timestamps do not change this pack's candidate identity.
        "local_status_path": str(status_path),
        "local_status_schema": 1,
        "recorded_tree_root": tree_root.lower(),
    }


def _capture_atpkg_stage0_authority(build_table):
    """Measure a local atpkg candidate, not a fresh signed release admission.

    `atpkg verify trust` is an offline comparison with a root in local status.toml;
    it does NOT replay signatures and can exit zero for an unattestable WiredSysroot.
    Require the exact Match outcome, independently hash the explicitly configured
    pack through the same identified verifier, and bind tools/activation/verifier
    before and after those checks. The local status and verifier remain explicit TCB.
    """
    try:
        before = _capture_atpkg_pack(build_table)
        selected = shutil.which("atpkg")
        if selected is None:
            raise ValueError("atpkg stage0 requires an explicit `atpkg` verifier on PATH")
        verifier_before = _atpkg_file_identity(Path(selected))
        # atpkg may be a symlink to the aterm multicall binary. Hash the resolved
        # bytes, but preserve the identified invocation path/argv[0] dispatch.
        verifier = selected
        proof = subprocess.run(
            [verifier, "verify", "trust"], capture_output=True, text=True, timeout=120
        )
        expected = f"atpkg: trust build {before['build']} OK (matches signed tree_root)"
        if proof.returncode != 0 or proof.stdout.strip() != expected or proof.stderr.strip():
            raise ValueError(
                "atpkg verify did not report the exact selected-build tree Match "
                f"(exit {proof.returncode}): {(proof.stdout + proof.stderr).strip()}"
            )
        measured = subprocess.run(
            [verifier, "tree-root", str(before["pack_local_path"])],
            capture_output=True, text=True, timeout=120,
        )
        if (
            measured.returncode != 0
            or measured.stderr.strip()
            or measured.stdout.strip().lower() != before["recorded_tree_root"]
        ):
            raise ValueError("atpkg explicit selected-pack tree-root does not match local status")
        after = _capture_atpkg_pack(build_table)
        verifier_after = _atpkg_file_identity(Path(selected))
        if before != after or verifier_before != verifier_after or shutil.which("atpkg") != selected:
            raise ValueError("atpkg pack, activation, status root, or verifier changed during capture")
        authority = {
            "evidence_class": "local-offline-tree-match",
            "fresh_signature_replay": False,
            "release_authority": False,
            "trusted_computing_base": ["local-atpkg-verifier", "local-status.toml-tree-root"],
            "pack": after,
            "verifier": verifier_after,
            "measured_tree_root": measured.stdout.strip().lower(),
        }
        return {
            "schema": "trust.atpkg-stage0-authority.v1",
            "status": "local-verified",
            "authority": authority,
            "authority_sha256": hashlib.sha256(
                json.dumps(authority, sort_keys=True, separators=(",", ":")).encode("utf-8")
            ).hexdigest(),
            "errors": [],
        }
    except (OSError, ValueError, RuntimeError, UnicodeError, ImportError, subprocess.SubprocessError) as error:
        return {
            "schema": "trust.atpkg-stage0-authority.v1",
            "status": "rejected",
            "authority": None,
            "authority_sha256": None,
            "errors": [str(error)],
        }


def _atpkg_authority_ready(snapshot: object) -> bool:
    if not isinstance(snapshot, dict):
        return False
    authority = snapshot.get("authority")
    canonical = (
        snapshot.get("schema") == "trust.atpkg-stage0-authority.v1"
        and snapshot.get("status") == "local-verified"
        and snapshot.get("errors") == []
        and isinstance(authority, dict)
        and authority.get("evidence_class") == "local-offline-tree-match"
        and authority.get("fresh_signature_replay") is False
        and authority.get("release_authority") is False
        and authority.get("trusted_computing_base")
        == ["local-atpkg-verifier", "local-status.toml-tree-root"]
    )
    if not canonical:
        return False
    try:
        digest = hashlib.sha256(
            json.dumps(authority, sort_keys=True, separators=(",", ":")).encode("utf-8")
        ).hexdigest()
    except (TypeError, ValueError, RecursionError, UnicodeError):
        return False
    return snapshot.get("authority_sha256") == digest


ATPKG_STAGE0_BLOCK = """\
# STAGE0 = THE ATPKG-PUBLISHED TRUST TOOLCHAIN.
#
# Trust seeds itself from the toolchain atpkg already delivers, instead of from a
# separately-published `trust-stage0-<date>` tarball. One published toolchain, one
# pipeline, and no rebuilding a compiler from source just to obtain a compiler.
#
# This is LOCAL CANDIDATE provenance, not immutable release admission. The active
# pack, five configured tools, verifier, and exact tree root are bound before/after
# the build. The verifier compares against local status.toml OFFLINE; no fresh
# signature replay occurs, and both verifier and local status remain explicit TCB.
# Concurrent activation/replacement invalidates this build's provenance snapshot.
#
# Bootstrap remains deliberately NOT a self-proving session; the compiler-verification
# policy in src/bootstrap/bootstrap.py is unchanged and still governs it.
rustc = "{stage0}/bin/trustc"
cargo = "{stage0}/bin/cargo"
rustdoc = "{stage0}/bin/trustdoc"
rustfmt = "{stage0}/bin/trustfmt"
cargo-clippy = "{stage0}/bin/targo-tippy"
"""


# A manifest-schema refusal says the candidate stage0 predates a `[trust]` key this
# tree uses. Any OTHER failure (network, lockfile, permissions) says nothing about
# the candidate's schema and must not reject it.
STAGE0_SCHEMA_REFUSAL_MARKERS = ("unknown field", "expected one of")


def stage0_bootstrap_manifest_roots(root: Path) -> list[Path]:
    """Use the same recipe manifest authority as the obligatory offline gate."""
    path = Path(__file__).resolve().with_name("bootstrap_dependency_closure.py")
    # Execute the authenticated checkout's actual source bytes, never an
    # unchecked timestamp-valid __pycache__ shadow (even under Python -B).
    namespace = {"__name__": "trust_bootstrap_dependency_closure", "__file__": str(path)}
    exec(compile(path.read_bytes(), str(path), "exec"), namespace)
    return namespace["stage0_bootstrap_manifest_roots"](root)


class _Stage0ManifestGraph:
    """Declared local manifest closure; never recurse by directory name.

    Cargo's successful membership output takes precedence. The fallback visits
    explicit members/globs and declared path edges only: offline failure must
    not hide an active [trust] table. It is NOT a Cargo feature/version resolver
    or evidence that the build's dependency resolution succeeded.
    """

    def __init__(self, root: Path, membership: dict[Path, list[Path]] | None = None, *, source_view=None):
        self.source_view = source_view
        self.root = source_view.path(root) if source_view is not None else root.resolve()
        self.membership = membership or {}
        self.documents: dict[Path, dict] = {}
        self.members_by_owner: dict[Path, set[Path]] = {}
        self.reached: set[Path] = set()
        self.inconclusive: set[str] = set()
        self.dependency_specs: list[tuple[str, object]] = []
        # Every probe runs at the checkout root. Cargo prefers the extensionless
        # spelling when both exist, and resolves these paths relative to root.
        configs = [self.root / ".cargo" / name for name in ("config", "config.toml")]
        self.config = next((self.read(path) for path in configs if self.is_file(path)), {})
        if "include" in self.config:
            self.inconclusive.add("Cargo config includes are not resolved by the local schema census")

    def is_file(self, path: Path) -> bool:
        return self.source_view.is_file(path) if self.source_view is not None else path.is_file()

    def resolve_path(self, path: Path) -> Path:
        return self.source_view.path(path) if self.source_view is not None else path.resolve()

    def manifest(self, path: Path) -> Path:
        path = self.resolve_path(path)
        if not path.is_relative_to(self.root):
            raise RuntimeError(f"stage0 manifest path escapes checkout: {path}")
        return path

    def read(self, path: Path) -> dict:
        import tomllib

        path = self.manifest(path)
        if path not in self.documents:
            try:
                self.documents[path] = tomllib.loads(self.source_view.read_text(path) if self.source_view is not None
                                                   else path.read_text(encoding="utf-8"))
            except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
                self.inconclusive.add(f"{path.relative_to(self.root)}: {error}")
                self.documents[path] = {}
        return self.documents[path]

    def owner(self, path: Path) -> Path:
        document = self.read(path)
        explicit = document.get("package", {}).get("workspace")
        if isinstance(explicit, str):
            return self.manifest(path.parent / explicit / "Cargo.toml")
        for directory in (path.parent, *path.parent.parents):
            if not directory.is_relative_to(self.root):
                break
            candidate = directory / "Cargo.toml"
            if self.is_file(candidate) and "workspace" in self.read(candidate):
                return candidate
        return path

    def members(self, workspace: Path) -> list[Path]:
        if workspace in self.membership:
            return self.membership[workspace]
        document = self.read(workspace)
        result = {workspace} if "package" in document else set()
        table = document.get("workspace", {})
        patterns = table.get("members", [])
        excluded = table.get("exclude", [])
        if not isinstance(patterns, list) or not isinstance(excluded, list):
            self.inconclusive.add(f"{workspace}: invalid workspace membership")
            return sorted(result)
        # These are only per-call path observations. Re-resolve every observed
        # spelling before returning; no path/status cache survives this census.
        prefixes: dict[str, Path] = {}

        def below_any(items, ancestors):
            for item in items:
                if not isinstance(item, str):
                    continue
                if item not in prefixes:
                    prefixes[item] = self.resolve_path(workspace.parent / item)
                if prefixes[item] in ancestors:
                    return True
            return False

        for pattern in patterns:
            if not isinstance(pattern, str):
                self.inconclusive.add(f"{workspace}: nonliteral workspace member")
                continue
            # Cargo gives an explicitly named member precedence over exclusion.
            # Excludes are directory prefixes (workspace.rs::is_excluded).
            for directory in sorted(self.source_view.glob(workspace.parent, pattern) if self.source_view is not None
                                    else workspace.parent.glob(pattern)):
                if not (self.source_view.is_dir(directory) if self.source_view is not None else directory.is_dir()):
                    continue
                manifest = self.manifest(directory / "Cargo.toml")
                ancestors = {manifest, *manifest.parents}
                explicitly_named = below_any(patterns, ancestors)
                is_excluded = below_any(excluded, ancestors)
                if not is_excluded or explicitly_named:
                    result.add(manifest)
        for spelling, original in prefixes.items():
            if self.resolve_path(workspace.parent / spelling) != original:
                raise RuntimeError(
                    f"stage0 workspace member/exclusion path changed during source census: {spelling}"
                )
        return sorted(result)

    def collect(self, roots: list[Path], *, dependency_roots: bool = False) -> set[Path]:
        self.members_by_owner.clear()
        self.dependency_specs.clear()
        # One local-source census, not a cache across requests. A
        # recipe list can name many entries in the same declared workspace;
        # re-enumerating all members per entry makes the census quadratic.
        declared_members: dict[Path, tuple[Path, ...]] = {}
        pending: list[tuple[Path, Path, bool]] = []
        for entry in roots:
            owner = self.owner(entry)
            if dependency_roots:
                # A Git/path dependency supplies one selected package and its
                # ordinary/build path edges, not its workspace's unrelated
                # members, root package, dev-dependencies or patch policy.
                self.members_by_owner.setdefault(owner, set())
                pending.append((entry, owner, False))
            else:
                if owner not in declared_members:
                    declared_members[owner] = tuple(self.members(owner))
                    self.members_by_owner[owner] = set(declared_members[owner])
                members = declared_members[owner]
                pending.append((owner, owner, True))
                pending.extend((member, owner, True) for member in members)
                pending.append((entry, owner, True))
        active_workspaces = set() if dependency_roots else {owner for _, owner, _ in pending}
        visited: set[tuple[Path, Path, bool]] = set()
        while pending:
            path, owner, is_member = pending.pop()
            path, owner = self.manifest(path), self.manifest(owner)
            key = (path, owner, is_member)
            if key in visited:
                continue
            visited.add(key)
            self.reached.update((path, owner))
            document, workspace = self.read(path), self.read(owner)
            sections = ["dependencies", "build-dependencies"]
            if is_member:
                sections.append("dev-dependencies")
            tables = [document]
            tables.extend(value for value in document.get("target", {}).values()
                          if isinstance(value, dict))
            edges = []
            for table in tables:
                for section in sections:
                    for name, specification in table.get(section, {}).items():
                        base = path.parent
                        if isinstance(specification, dict) and specification.get("workspace") is True:
                            specification = workspace.get("workspace", {}).get("dependencies", {}).get(name)
                            base = owner.parent
                            if specification is None:
                                self.inconclusive.add(f"{path}: undefined workspace dependency {name}")
                        edges.append((base, specification, True, name))
            if path == owner and is_member:
                sources = set(document.get("patch", {})) | set(self.config.get("patch", {}))
                for source in sources:
                    patches = {name: (path.parent, value) for name, value in
                               document.get("patch", {}).get(source, {}).items()}
                    patches.update({name: (self.root, value) for name, value in
                                    self.config.get("patch", {}).get(source, {}).items()})
                    edges.extend((base, value, False, name) for name, (base, value) in patches.items())
                edges.extend((path.parent, value, False, name) for name, value in document.get("replace", {}).items())
                edges.extend((self.root, {"path": value}, False, "") for value in self.config.get("paths", [])
                             if isinstance(value, str))
            for base, specification, member_edge, dependency_name in edges:
                self.dependency_specs.append((dependency_name, specification))
                if isinstance(specification, dict) and isinstance(specification.get("path"), str):
                    target = self.manifest(base / specification["path"] / "Cargo.toml")
                    # The compiler root and crates/ workspace deliberately share
                    # member files. Their inherited paths belong to the current
                    # Cargo context, not to one global path -> owner cache.
                    target_owner = owner if target in self.members_by_owner.get(owner, set()) else self.owner(target)
                    member = not dependency_roots and target in self.members_by_owner.get(target_owner, set())
                    if (member_edge and target_owner in active_workspaces
                            and target_owner not in self.membership):
                        table = self.read(target_owner).get("workspace", {})
                        excluded = any(target.is_relative_to(self.resolve_path(target_owner.parent / item))
                                       for item in table.get("exclude", []) if isinstance(item, str))
                        # Cargo also admits implicit local path members. This
                        # fallback matters when the membership query itself was
                        # inconclusive; patch sources do NOT become members.
                        member = member or not excluded
                        if member:
                            self.members_by_owner.setdefault(target_owner, set()).add(target)
                    # Dependency workspaces supply inheritance, not an invitation
                    # to probe their unrelated members or their dev-dependencies.
                    pending.append((target, target_owner, member))
        # Re-read actual membership before accepting this collection. Sharing
        # its initial census cannot hide a changed glob, alias or exclusion;
        # the next managed bookend constructs an entirely fresh graph again.
        for owner, before in declared_members.items():
            if tuple(self.members(owner)) != before:
                raise RuntimeError(
                    f"stage0 manifest workspace membership changed during source census: {owner}"
                )
        return self.reached


def stage0_trust_manifest_probes(root: Path) -> list[Path]:
    """[trust]-bearing manifests in the declared local bootstrap closure."""
    graph = _Stage0ManifestGraph(root)
    reached = graph.collect(stage0_bootstrap_manifest_roots(root))
    return sorted(path for path in reached if "trust" in graph.read(path))


def stage0_refuses_tree_manifest(sysroot: Path, root: Path) -> tuple[Path, str] | None:
    """The first `[trust]`-bearing manifest this stage0 cannot PARSE, or None.

    Returns `(manifest, first stderr line)` only when the candidate's own cargo
    rejects the manifest SCHEMA. Every other outcome — success, a network error,
    a missing lockfile, a timeout — returns None, because none of them is
    evidence about the candidate's manifest schema and a false rejection here
    leaves the machine with no stage0 at all.
    """
    cargo = sysroot / "bin" / "cargo"
    if not cargo.exists():
        return None
    _authority, errors = bootstrap_cargo_authority(root)
    if errors:
        raise RuntimeError("schema probe Cargo authority rejected: " + "; ".join(errors))
    env = os.environ.copy()
    for name in _ambient_build_authority_overrides(env):
        env.pop(name, None)
    roots = stage0_bootstrap_manifest_roots(root)
    graph = _Stage0ManifestGraph(root)
    graph.collect(roots)
    entries = sorted({graph.owner(path) for path in roots})
    pending = list(entries)
    probed: set[Path] = set()
    expanded = False
    while pending or not expanded:
        if not pending:
            # Successful Cargo membership is authoritative. On an offline or
            # other non-schema error, the declared closure still finds active
            # Trust tables; it never promotes an unreferenced nested fixture.
            graph.reached.clear()
            graph.collect(roots)
            pending = sorted(path for path in graph.reached
                             if path not in probed and "trust" in graph.read(path))
            expanded = True
            continue
        manifest = pending.pop(0)
        if manifest in probed:
            continue
        probed.add(manifest)
        try:
            # --check must not populate the build-owned home or rewrite locks.
            # Use a disposable probe home; this capability observation is not
            # the subsequent source/config/tool provenance capture.
            with tempfile.TemporaryDirectory(prefix="trust-stage0-schema-") as probe_home:
                env["CARGO_HOME"] = probe_home
                probe = subprocess.run(
                    [
                        str(cargo),
                        "metadata",
                        "--no-deps",
                        "--locked",
                        "--offline",
                        "--format-version",
                        "1",
                        "--manifest-path",
                        str(manifest),
                    ],
                    capture_output=True,
                    text=True,
                    timeout=180,
                    env=env,
                    cwd=root,
                )
        except (OSError, subprocess.SubprocessError) as error:
            graph.inconclusive.add(f"{manifest.relative_to(graph.root)}: {error}")
            continue
        if probe.returncode == 0:
            if manifest in entries:
                try:
                    metadata = json.loads(probe.stdout)
                    workspace = graph.manifest(Path(metadata["workspace_root"]) / "Cargo.toml")
                    ids = set(metadata["workspace_members"])
                    members = [graph.manifest(Path(package["manifest_path"]))
                               for package in metadata["packages"] if package["id"] in ids]
                    if len(members) != len(ids):
                        raise ValueError("incomplete Cargo membership")
                    graph.membership[workspace] = members
                except (AttributeError, KeyError, TypeError, ValueError) as error:
                    graph.inconclusive.add(f"{manifest.relative_to(graph.root)}: membership unavailable ({error})")
            continue
        stderr = probe.stderr or ""
        if not any(marker in stderr for marker in STAGE0_SCHEMA_REFUSAL_MARKERS):
            graph.inconclusive.add(f"{manifest.relative_to(graph.root)}: Cargo metadata failed without a schema refusal")
            continue
        # A dependency manifest's metadata command can inspect OTHER members
        # of its workspace. A diagnostic there is not evidence about this build.
        locations = re.findall(r"-->\s+(.+?Cargo\.toml):\d+(?::\d+)?", stderr)
        diagnosed = manifest
        if locations:
            diagnosed = (root / locations[0]).resolve()
            if diagnosed not in graph.reached:
                graph.inconclusive.add(f"{manifest.relative_to(graph.root)}: schema diagnostic outside reached closure: {diagnosed}")
                continue
        elif "trust" not in graph.read(manifest):
            graph.inconclusive.add(f"{manifest.relative_to(graph.root)}: unlocated schema diagnostic")
            continue
        first = next(
            (line.strip() for line in stderr.splitlines() if line.strip()),
            "manifest rejected with no message",
        )
        return (diagnosed, first)
    if graph.inconclusive:
        print("  stage0 schema observation INCONCLUSIVE (not a compatibility proof):")
        for diagnostic in sorted(graph.inconclusive):
            print(f"    {diagnostic}")
    return None


def _report_atpkg_schema_refusal(pack: Path, root: Path, refusal: tuple[Path, str]) -> None:
    manifest, message = refusal
    try:
        manifest = manifest.relative_to(root)
    except ValueError:
        pass
    print(f"  active atpkg pack {pack.name} REFUSES this tree's manifests: {manifest}")
    print(f"    {message}")
    print("  No staged or older pack is substituted for the active/current identity.")
    print("  options: repair the selected config; `atpkg update` then re-run; or")
    print("    `--no-atpkg --require-seed` for pinned archives (use --force-config")
    print("    when replacing an existing atpkg config).")


def atpkg_trust_sysroot(root: Path | None = None):
    """Select the active/current complete local candidate, never a newer staged pack."""
    try:
        pack = Path(_capture_atpkg_pack()["pack_local_path"])
    except (OSError, ValueError, RuntimeError, UnicodeError, ImportError):
        return None
    if root is not None:
        refusal = stage0_refuses_tree_manifest(pack, root)
        if refusal is not None:
            _report_atpkg_schema_refusal(pack, root, refusal)
            return None
    return pack


SEED_STAGE0_BLOCK = """\
# No stage0 override: x.py resolves the checksum-pinned Trust seed declared in
# src/stage0 from the repo-local bootstrap/trust-stage0 dist (trust-from-trust;
# stock rust nowhere in the loop). Both bootstrap layers select the seed's
# sibling bin/cargo compatibility identity, never branded Targo authority.
"""


APPLE_TARGETS = ("aarch64-apple-darwin", "x86_64-apple-darwin")


def build_targets_block(host: str) -> str:
    """The `[build] target` line for this host, or nothing.

    On an Apple host both Apple architectures are built (CLAUDE.md, "Targets —
    build BOTH Apple architectures"): Trust ships an x86_64 std that the ALab
    programs' Intel artifacts are built against, so a sysroot with only the
    host std is incomplete for them. Other hosts keep bootstrap's default
    (host only) — nothing on the shipping side asks for more there yet.
    """
    if not host.endswith("-apple-darwin"):
        return ""
    targets = ", ".join(f'"{t}"' for t in APPLE_TARGETS)
    return (
        "# Trust: build BOTH Apple architectures. The x86_64 std is what the\n"
        "# shipping ALab programs' Intel artifacts build against (CLAUDE.md).\n"
        f"target = [{targets}]\n"
    )


def _declared_bootstrap_mode(content: bytes, build_table: dict) -> str:
    """Share the existing lineage classifier; markers alone never grant authority."""
    seed = b"(seed stage0 mode)" in content
    genesis = b"(genesis stage0 mode)" in content
    atpkg = b"(atpkg stage0 mode)" in content
    adapter = b"genesis-stage0" in content
    if seed and not genesis and not atpkg and not adapter and not (
        STAGE0_OVERRIDE_KEYS & set(build_table)
    ):
        return "seed"
    if atpkg and not seed and not genesis and not adapter:
        return "atpkg"
    if genesis and not seed and not atpkg and adapter:
        return "genesis"
    return "unknown"


def _existing_bootstrap_config(root: Path) -> tuple[Path | None, bytes | None]:
    paths = [path for path in (root / "bootstrap.toml", root / "config.toml")
             if os.path.lexists(path)]
    if len(paths) > 1:
        raise RuntimeError("both bootstrap.toml and config.toml exist; resolve the ambiguous config explicitly")
    if not paths:
        return None, None
    path = paths[0]
    if path.is_symlink() or not path.is_file():
        raise RuntimeError(f"{path} must be a regular, non-symlink bootstrap config")
    return path, path.read_bytes()


@dataclass(frozen=True)
class Stage0Selection:
    """One retained decision, not release evidence or a substitute for pre/post audit."""

    mode: str
    config_path: Path | None
    config_content: bytes | None
    atpkg_authority: dict[str, object] | None = None

    @property
    def atpkg_root(self) -> Path | None:
        if self.mode != "atpkg" or not _atpkg_authority_ready(self.atpkg_authority):
            return None
        return Path(self.atpkg_authority["authority"]["pack"]["pack_local_path"])


def resolve_stage0_selection(root: Path, args: argparse.Namespace) -> Stage0Selection:
    """Select once before archive resolution; never silently replace an existing mode."""
    path, content = _existing_bootstrap_config(root)
    # D12 (d): once src/stage0 is a minted pin, the atpkg stage0 mode and the
    # genesis fallback are retired (minted_seed_pin).
    minted = minted_seed_pin(root)
    existing_mode = None
    build_table = {}
    if path is not None and not args.force_config:
        import tomllib

        try:
            build_table = tomllib.loads(content.decode("utf-8")).get("build", {})
        except (UnicodeError, tomllib.TOMLDecodeError) as error:
            raise RuntimeError(f"{path} is not valid UTF-8 TOML; repair it or use --force-config: {error}") from error
        if not isinstance(build_table, dict):
            raise RuntimeError(f"{path} [build] must be a table; repair it or use --force-config")
        existing_mode = _declared_bootstrap_mode(content, build_table)
        if existing_mode == "unknown":
            raise RuntimeError(f"{path} has ambiguous stage0 mode; repair it or use --force-config")
        if existing_mode == "atpkg" and minted is not None:
            raise RuntimeError(
                f"{path} selects the atpkg stage0 mode, which D12 (d) retires now that src/stage0 is a "
                f"minted pin: {minted}; regenerate the config with --force-config to seed from the pin"
            )
        requested = "genesis" if args.genesis else "seed" if args.fresh_seed else None
        if requested is not None and existing_mode != requested:
            raise RuntimeError(f"{path} selects {existing_mode}, but this invocation requires {requested}; use --force-config to change it")
        if existing_mode == "genesis" and not args.genesis:
            raise RuntimeError(f"{path} selects stock-rust genesis; use --genesis deliberately or --force-config to select Trust")
        if existing_mode == "atpkg" and args.no_atpkg:
            raise RuntimeError(f"{path} selects atpkg, but --no-atpkg excludes it; use --force-config to change it")

    def selected(mode: str, authority=None) -> Stage0Selection:
        return Stage0Selection(mode, path, content, authority)

    if args.genesis:
        return selected("genesis")
    # --fresh-seed and an existing seed config force the archive lane even when
    # a complete local pack exists. In particular fresh provenance cannot be
    # satisfied by an atpkg candidate's offline local-status tree match.
    atpkg_wanted = not args.fresh_seed and not args.no_atpkg and existing_mode != "seed"
    if atpkg_wanted and minted is not None:
        print(f"  atpkg stage0 mode retired (D12 (d)): {minted}")
    elif atpkg_wanted:
        pack = atpkg_trust_sysroot() if existing_mode is None else None
        if existing_mode == "atpkg" or pack is not None:
            table = build_table if existing_mode == "atpkg" else {
                key: str(pack / "bin" / tool) for key, tool in ATPKG_STAGE0_TOOLS.items()
            }
            authority = _capture_atpkg_stage0_authority(table)
            if _atpkg_authority_ready(authority):
                candidate = selected("atpkg", authority)
                refusal = stage0_refuses_tree_manifest(candidate.atpkg_root, root)
                if refusal is None:
                    print("  active atpkg Trust verified — local offline candidate, NOT release authority")
                    return candidate
                _report_atpkg_schema_refusal(candidate.atpkg_root, root, refusal)
                if existing_mode == "atpkg":
                    raise RuntimeError(f"{path} selects an atpkg pack that refuses this tree's manifest schema; use --force-config to change it")
                print("  trying pinned archives after the active pack's schema refusal")
            else:
                details = "; ".join(str(error) for error in authority.get("errors", []))
                if existing_mode == "atpkg":
                    raise RuntimeError(f"{path} atpkg authority rejected: {details}; repair the selected local pack or use --force-config")
                print(f"  local atpkg candidate rejected: {details}; trying pinned archives")

    print("  resolving pinned Trust stage0 archives (src/stage0)")
    if resolve_seed(root, allow_fetch=not args.no_fetch and not args.check,
                    host=getattr(args, "host", None) or host_triple()):
        print("  pinned archives validated — bootstrapping Trust without stock rust")
        return selected("seed")
    if args.require_seed or existing_mode == "seed":
        raise RuntimeError("pinned Trust seed unavailable; refusing genesis fallback (materialize the pinned archives or explicitly change the config)")
    if minted is not None:
        raise RuntimeError(
            "pinned Trust seed unavailable; refusing genesis fallback: D12 (d) retired it now that "
            f"src/stage0 is a minted pin ({minted}); materialize the pinned archives, or pass --genesis "
            "for the stock-rust adapter deliberately"
        )
    print("  Trust seed unavailable — stock-rust genesis fallback (development only; NOT release evidence)")
    return selected("genesis")


@dataclass(frozen=True)
class WrittenBootstrapConfig:
    path: Path
    sha256: str

    def require_normal_source_identity(self) -> None:
        """Check the selected bytes; this grants no release/provenance authority."""
        import tomllib

        if not self.path.is_absolute() or self.path.is_symlink() or not self.path.is_file():
            raise RuntimeError("selected normal bootstrap config must be an absolute regular, non-symlink file")
        content = self.path.read_bytes()
        if hashlib.sha256(content).hexdigest() != self.sha256:
            raise RuntimeError("selected normal bootstrap config bytes changed")
        config = tomllib.loads(content.decode("utf-8"))
        rust = config.get("rust", {})
        if not isinstance(rust, dict) or rust.get("trust-source-identity") is not False:
            raise RuntimeError("selected normal bootstrap config must explicitly bind rust.trust-source-identity=false")
        # Native config.rs merges include/profile with IgnoreDuplicate: this
        # explicit top-level false dominates inherited values. CLI overrides
        # must still be excluded by the shared normal argument owner below.


# Trust: on Linux every Rust link of the build goes through the building compiler's own
# rust-lld (`-Clink-self-contained=+linker`: the stage0's for what it builds, the in-tree one
# after), never GNU ld. Measured on the GB10 (aarch64, binutils 2.42) on 2026-11-14: a seed-mode
# stage-2 build of main da4bd9f2c4 from the pinned Linux seed stopped after 2 h 05 min linking
# librustc_driver with /usr/bin/gcc, "relocation truncated to fit: R_AARCH64_CALL26" against the
# outline-atomics helpers __aarch64_ldadd8_rel and __aarch64_cas8_acq_rel, called from
# .text.unlikely sections more than 128 MiB away (docs/OPEN_ISSUES.md LINUX-GNU-LD-CALL26-1).
# Every build of main on that host linked with this lld already (linux_refresh_toolchain.py
# --lld). docs/DECISION_QUEUE.md LINUX-SEED-LLD-1.
LINUX_LLD_BLOCK = """\
# Trust: every Rust link goes through the building compiler's own rust-lld, never GNU ld,
# which cannot link the stage-2 librustc_driver on aarch64 Linux (LINUX-SEED-LLD-1).
bootstrap-override-lld = "self-contained"
"""


def links_with_own_lld(stage0_mode: str, atpkg_root: Path | None, host: str) -> bool:
    """Whether the generated config links Rust with the building compiler's own rust-lld:
    on a Linux host, in seed mode (the pinned seed ships rust-lld and gcc-ld/ld.lld), and
    in atpkg mode when that stage0 ships both; never on another host or in genesis mode."""
    if platform.system().lower() != "linux" or "-linux-" not in host:
        return False
    if stage0_mode == "seed":
        return True
    if stage0_mode == "atpkg" and atpkg_root is not None:
        tools = atpkg_root / "lib" / "rustlib" / host / "bin"
        return (tools / "rust-lld").is_file() and (tools / "gcc-ld" / "ld.lld").is_file()
    return False


def write_config(
    root: Path, host: str, force: bool, llvm_config: str | None = None, seed_mode: bool = False,
    *, selection: Stage0Selection | None = None,
) -> WrittenBootstrapConfig:
    """Return the exact reused/generated byte identity, not a later reread."""
    existing, existing_content = _existing_bootstrap_config(root)
    if selection is None:
        # Compatibility callers select their explicit boolean mode; no hidden
        # rediscovery of atpkg in a config writer.
        selection = Stage0Selection("seed" if seed_mode else "genesis", existing, existing_content)
    if (existing, existing_content) != (selection.config_path, selection.config_content):
        raise RuntimeError("bootstrap config changed after stage0 selection; rerun without overwriting the concurrent edit")
    target = existing or root / "bootstrap.toml"
    if existing and not force:
        import tomllib

        table = tomllib.loads(existing_content.decode("utf-8")).get("build", {})
        if not isinstance(table, dict) or _declared_bootstrap_mode(existing_content, table) != selection.mode:
            raise RuntimeError(f"{existing} disagrees with selected {selection.mode} mode; use --force-config to change it")
        print(f"  reusing existing config at {existing}")
        return WrittenBootstrapConfig(existing, hashlib.sha256(existing_content).hexdigest())
    py = find_python_ge_311() or sys.executable
    stage0_mode = selection.mode
    if stage0_mode == "atpkg":
        atpkg_stage0 = selection.atpkg_root
        if atpkg_stage0 is None:
            raise RuntimeError("selected atpkg mode lacks exact local candidate authority")
        print(f"  stage0: atpkg-delivered trust toolchain at {atpkg_stage0}")
        stage0_block = ATPKG_STAGE0_BLOCK.format(stage0=str(atpkg_stage0))
    elif stage0_mode == "seed":
        stage0_block = SEED_STAGE0_BLOCK
    elif stage0_mode == "genesis":
        stage0_block = GENESIS_STAGE0_BLOCK.format(
            stage0=str(root / "build" / host / "genesis-stage0")
        )
    else:
        raise RuntimeError(f"unknown selected stage0 mode: {stage0_mode}")
    content = CONFIG_TEMPLATE.format(
        mode=stage0_mode,
        python=py,
        prefix=str(root / "install"),
        stage0_block=stage0_block,
        targets_block=build_targets_block(host),
        rust_lld_block=LINUX_LLD_BLOCK if links_with_own_lld(stage0_mode, selection.atpkg_root, host) else "",
    )
    target_lines: list[str] = []
    apple_tool_lines: list[str] = []
    if llvm_config:
        # Link an external LLVM instead of building LLVM in-tree. The compiler
        # profile still builds LLD with CMake/Ninja. The LLVM major version must
        # match what rustc_llvm expects.
        target_lines.append(f'llvm-config = "{llvm_config}"')
    if platform.system().lower() == "linux":
        # The OS toolchain is the native build authority on Linux — the same
        # doctrine as the root-owned fixed git. A PATH `cc` can be any shim
        # (a zig-cc shim's bundled glibc stubs broke the LLVM host link, its
        # PATH probe poisoned CMAKE_ASM_FLAGS, and its -lstdc++ mapped to
        # libc++, all on the first Linux host), so pin compile and link to
        # the distro compiler when it exists; ambient CC/CXX stay refused.
        gcc = Path("/usr/bin/gcc")
        gxx = Path("/usr/bin/g++")
        if gcc.is_file() and gxx.is_file():
            target_lines.append(f'cc = "{gcc}"')
            target_lines.append(f'cxx = "{gxx}"')
            target_lines.append(f'linker = "{gcc}"')
    elif platform.system().lower() == "darwin" and host.endswith("-apple-darwin"):
        # The normal producer scrubs ambient CC/CXX/SDKROOT. The Python
        # bootstrap exports these target settings before compiling its native
        # dependencies; an implicit PATH `cc` can miss Apple's SDK headers.
        # Every selected Apple Std target needs the same explicit tools, not
        # just the compiler host: profiler_builtins also compiles C there.
        # Select Apple's native entrypoints, as the explicit compiler config
        # does, rather than reintroducing ambient compiler or include flags.
        for name, path in (("cc", "/usr/bin/clang"), ("cxx", "/usr/bin/clang++"),
                           ("linker", "/usr/bin/clang"), ("ar", "/usr/bin/ar"),
                           ("ranlib", "/usr/bin/ranlib")):
            apple_tool_lines.append(f'{name} = "{path}"')
        target_lines.extend(apple_tool_lines)
    if target_lines:
        content += f'\n[target.{host}]\n' + "\n".join(target_lines) + "\n"
    if apple_tool_lines:
        for std_target in APPLE_TARGETS:
            if std_target != host:
                content += f'\n[target.{std_target}]\n' + "\n".join(apple_tool_lines) + "\n"
    encoded = content.encode("utf-8")
    target.write_bytes(encoded)
    print(f"  wrote {target}")
    return WrittenBootstrapConfig(target, hashlib.sha256(encoded).hexdigest())


def ay_bcp_cargo_features(ay_dir: Path) -> str:
    """`--features` for an ay bootstrap build, per the spelling ay declares.

    Mirrors `ay_bootstrap_cargo_args_for_manifest` in
    src/bootstrap/src/core/build_steps/tool.rs, deliberately including its
    fail-safe, so this fallback rebuild and x.py's own cannot select different
    capabilities from the same pin. The bcp feature has been renamed in BOTH
    directions (raw-pointer-bcp <-> unsafe-bcp); hardcoding either spelling
    breaks every checkout whose ay pin sits on the other side of the rename.
    Measured 2026-08-23: the pinned ay declares `raw-pointer-bcp` only, so the
    hardcoded `cli,unsafe-bcp` this function used to pass made the rebuild fail
    with "none of the selected packages contains these features" — and
    `install_ay_solver` then reports that verification will answer `unknown`.
    """
    try:
        manifest = (ay_dir / "crates" / "ay" / "Cargo.toml").read_text(encoding="utf-8")
    except OSError:
        manifest = ""

    def declares(feature: str) -> bool:
        in_features = False
        for line in manifest.splitlines():
            trimmed = line.split("#", 1)[0].strip()
            if trimmed.startswith("["):
                in_features = trimmed == "[features]"
                continue
            if in_features and trimmed.startswith(feature):
                if trimmed[len(feature):].lstrip().startswith("="):
                    return True
        return False

    if declares("unsafe-bcp") or not declares("raw-pointer-bcp"):
        return "cli,unsafe-bcp"
    return "cli,raw-pointer-bcp"


def install_ay_solver(root: Path, host: str, stage: int) -> bool:
    """Ensure the x.py-built `ay` (trust-from-trust) sits beside `trustc`.

    The `ay` beside `trustc` is the solver CLI the toolchain ships: `targo trust
    verify-binary` spawns it (`ay_beside_current_exe`), and the release gates
    refuse a toolchain without it, so without it the toolchain is not
    "batteries on". trustc itself links its ay and spawns none since plan P4 /
    T4.1 (2026-10-10), so source verification does not read this file. Until
    then trustc's Liskov router spawned it. `./x.py build` already
    builds `ay` as an in-tree tool (`--no-default-features --features
    cli,<bcp>`, the spelling probed from ay's manifest — see
    `ay_bcp_cargo_features`; `ensure_default_verifier_tool_bins` in
    src/bootstrap/src/core/build_steps/tool.rs) and installs it in the sysroot,
    so the job here is only to restore that artifact if anything displaced it.
    Rebuilding with a PATH `cargo` — what this function once did — silently
    replaced the trust-from-trust binary with a stock-Rust build carrying
    different features. If the artifact is somehow absent, fall back to
    building with the just-built targo/trustc; stock rust is never used.
    Returns false when installation cannot be completed; the one-command
    caller treats that as an installation failure even if x.py itself built.
    """
    bindir = root / "build" / host / f"stage{stage}" / "bin"
    trustc = bindir / "trustc"
    if not trustc.exists():
        print(f"  (skip ay install: no {trustc})")
        return False
    installed = bindir / "ay"
    # ToolBuild copies using its output compiler (stage N), not its build
    # compiler (stage N-1). Session::tools_dir adds one to that output stage
    # and appends the tool's target triple. For these native sysroot tools the
    # target is host; adjacent generations and the retired flat layout are not
    # producers, even if they still contain executable files from an older cut.
    tool_artifact = root / "build" / host / f"stage{stage + 1}-tools-bin" / host / "ay"
    if tool_artifact.is_file():
        if installed.exists() and os.path.samefile(tool_artifact, installed):
            # bootstrap installs via hard link; the common post-build state is
            # already correct and copying a file onto itself would fail.
            print(f"  x.py-built ay already installed at {installed}  (trust-from-trust)")
            return True
        # Never write THROUGH the destination: bootstrap hard-links the sysroot
        # bin to its tools-bin cache and cargo's output, and an in-place copy
        # truncates every path sharing the inode. Unlink first.
        installed.unlink(missing_ok=True)
        shutil.copy2(tool_artifact, installed)
        print(f"  installed x.py-built ay -> {installed}  (trust-from-trust)")
        return True
    if installed.exists():
        print(f"  keeping x.py-installed ay at {installed}")
        return True
    targo = bindir / "targo"
    if not targo.exists():
        print(
            "  ERROR: no x.py-built ay artifact and no targo to rebuild one — "
            "`targo trust verify-binary` will report `unknown` until `ay` is beside "
            "trustc (run ./x.py build --stage 2, which installs it there)."
        )
        return False
    ay_dir = root / "first-party" / "ay"
    features = ay_bcp_cargo_features(ay_dir)
    print(f"\n  building ay with the just-built toolchain (release, {features}) ...")
    env = os.environ.copy()
    env.pop("RUSTC_BOOTSTRAP", None)
    env["RUSTC"] = str(trustc)
    env["PATH"] = f"{bindir}:{env.get('PATH', '')}"
    prepare_bootstrap_cargo_environment(root, env)
    add_homebrew_library_path(env)
    rc = subprocess.run(
        [
            str(targo), "--unverified", "build", "--locked", "--release", "--bin", "ay",
            "--no-default-features", "--features", features,
        ],
        cwd=str(ay_dir),
        env=env,
    ).returncode
    ay_bin = ay_dir / "target" / "release" / "ay"
    if rc != 0 or not ay_bin.exists():
        print(
            "  ERROR: ay build failed — `targo trust verify-binary` will report "
            "`unknown` until `ay` is beside trustc (run ./x.py build --stage 2, which "
            "installs it there)."
        )
        return False
    installed.unlink(missing_ok=True)  # never write through bootstrap's hard links
    shutil.copy2(ay_bin, installed)
    print(
        f"  installed ay -> {installed}  "
        "(targo trust front doors activate verification explicitly)"
    )
    return True


# Public stage-N entrypoint -> target-qualified x.py stage-(N+1) tools-bin artifact,
# produced by compiler N-1. ToolBuild passes its output compiler (N) to
# Session::tools_dir, which adds one to that stage and appends the target triple. Trust's
# branded front doors intentionally replace most inherited public spellings;
# rustc/cargo remain same-sysroot compatibility aliases only.  Keeping this
# map beside the post-build installer makes it impossible to silently add a
# public tool without naming the exact bootstrap artifact that produced it.
STAGE_TOOL_PRODUCERS = {
    # Trust: the Trust Cargo's package, library and binary are all `targo`
    # (src/tools/targo/Cargo.toml), so its tools-bin artifact is the file
    # `targo`, and `bin/cargo` is that same artifact under the compatibility
    # name (bootstrap's `upstream_compat_bin_for_tool_source`). A tools-bin
    # file named `cargo` is not a producer of anything: binding either public
    # name to it would accept a stale pre-rename build as the stage's Targo.
    "cargo": "targo",
    "targo": "targo",
    # Trust: NOT OPTIONAL (2026-07-31). A public tool named in `tools = [...]`
    # must also name the bootstrap artifact that produced it, or the post-build
    # installer cannot place it and the stage tool provenance audit reports it
    # missing — exactly the failure `clean` and `ty` hit in fef5414c1fa.
    "trustup": "trustup",
    "targo-trust": "targo-trust",
    "trustd": "trustd",
    "ay": "ay",
    "ty": "ty",
    "clean": "clean",
    "trustdoc": "rustdoc_tool_binary",
    "trustfmt": "rustfmt",
    "targo-fmt": "cargo-fmt",
    "tippy": "cargo-clippy",
    "targo-tippy": "cargo-clippy",
    "tippy-driver": "clippy-driver",
    "trust-analyzer": "rust-analyzer",
}

# Public bin/ names that are COMPAT ALIASES of a Trust producer rather than
# producers themselves: `rustc` is `trustc` and `rustdoc` is `trustdoc` (cargo
# spawns `rustdoc` by name for doctests, 76d408e1cd), so every stage >= 1
# sysroot ships both names. ONE definition, consumed by the write-time audit
# AND the read-only verifier. They used to carry separate copies of this set,
# and the verifier's copy lacked `rustdoc`: a stage2 that passed the audit at
# build time was then refused on re-verification with "current public stage
# tool inventory differs from the closed producer map" — a receipt that could
# never be re-checked against the sysroot it described.
COMPAT_ALIAS_PUBLIC_TOOLS = frozenset({"rustc", "trustc", "rustdoc"})

# Public tools a complete stage bin/ MAY carry, each bound to its x.py producer
# exactly like a required one whenever it is present. These are the optional
# canonical Miri tools of scripts/lib/trust_toolchain_surface.sh, the same
# carve-out scripts/check_toolchain_coherence.py derives (and checks this map
# against). The compiler profile selects `trust-miri`, so bootstrap installs
# both names into stage2/bin (tool.rs `install_private_bins`). With the map
# closed over the required tools only, a complete seed-first stage2 built at
# 81fd6cee789 failed this audit after its build succeeded: "unmapped public
# stage tools: targo-miri, trust-miri" (2026-09-30).
OPTIONAL_STAGE_TOOL_PRODUCERS = {
    "trust-miri": "miri",
    "targo-miri": "cargo-miri",
}

# `copy_lld_artifacts` installs LLVM's native LLD into both the target libdir
# and root bin/. It was not compiled by a Rust stage-(N-1) compiler and must
# never be represented as a tools-bin artifact.
NATIVE_STAGE_TOOL_PRODUCERS = {"rust-lld": ("lld", "lld")}


def expected_public_stage_tools() -> set[str]:
    """The executables a stage bin/ must contain: every producer in
    `STAGE_TOOL_PRODUCERS` plus the compat aliases. Beside them it may carry
    the optional Rust and separately LLVM-bound native tools."""
    return set(STAGE_TOOL_PRODUCERS) | set(COMPAT_ALIAS_PUBLIC_TOOLS)


def stage_tool_producers_for(actual_public: set[str]) -> dict[str, str]:
    """The producer map a stage bin/ holding `actual_public` is bound by: every
    required producer, plus each optional tool that is present."""
    producers = dict(STAGE_TOOL_PRODUCERS)
    for public_name, producer_name in OPTIONAL_STAGE_TOOL_PRODUCERS.items():
        if public_name in actual_public:
            producers[public_name] = producer_name
    return producers


def capture_native_stage_tools(
    root: Path, host: str, build: Path, bin_dir: Path,
    actual_public: set[str], llvm_identity: object,
) -> tuple[list[dict[str, object]], list[str]]:
    """Bind native front doors to their exact installed, stated LLVM output."""
    rows: list[dict[str, object]] = []
    errors: list[str] = []
    identity = llvm_identity if isinstance(llvm_identity, dict) else {}
    for name in sorted(actual_public & set(NATIVE_STAGE_TOOL_PRODUCERS)):
        component, producer_name = NATIVE_STAGE_TOOL_PRODUCERS[name]
        prefix = build / host / component
        producer = prefix / "bin" / _host_executable(producer_name, host)
        installed = bin_dir / _host_executable(name, host)
        row: dict[str, object] = {
            "name": name, "producer_kind": "in-tree-llvm-project",
            "path": _repository_relative_path(root, installed),
            "producer_path": _repository_relative_path(root, producer),
            "llvm_source_identity_sha256": identity.get("source_identity_sha256"),
            "llvm_output_fingerprint_sha256": identity.get("output_fingerprint_sha256"),
        }
        output_dirs = identity.get("output_dirs")
        if (identity.get("mode") != "in-tree" or identity.get("identity_stated") is not True
                or not isinstance(output_dirs, list)
                or _repository_relative_path(root, prefix) not in output_dirs):
            errors.append(f"native stage tool {name} requires its stated in-tree LLVM output")
        regular = all(
            p.is_file() and not p.is_symlink() and os.access(p, os.X_OK)
            for p in (installed, producer)
        )
        if (not regular or prefix.is_symlink()
                or not producer.resolve().is_relative_to(build.resolve())
                or not installed.resolve().is_relative_to(bin_dir.parent.resolve())):
            row["status"] = "producer_missing_or_not_regular"
            errors.append(f"native stage tool {name} or its exact regular producer is missing")
        else:
            installed_sha, producer_sha = _sha256_file(installed), _sha256_file(producer)
            row.update(sha256=installed_sha, producer_sha256=producer_sha,
                       same_inode=os.path.samefile(installed, producer),
                       status="bound" if installed_sha == producer_sha else "mismatch")
            if installed_sha != producer_sha:
                errors.append(f"native stage tool {name} does not match its exact LLVM producer")
            ok, version = _capture_identity(installed, ("-flavor", "gnu", "--version"))
            row.update(version_probe_ok=ok, version=version.splitlines()[0] if version else "")
            if not ok:
                errors.append(f"native stage tool {name} cannot report its version")
        rows.append(row)
    return rows, errors


SEED_STAGE0_REQUIRED_BINS = (
    "trustc",
    "rustc",
    "trustdoc",
    "targo",
    "cargo",
    "targo-trust",
    "trustfmt",
    "targo-fmt",
    "tippy",
    "targo-tippy",
    "tippy-driver",
    "trust-analyzer",
)

SEED_STAGE0_REQUIRED_LIBEXEC_BINS = ("trust-analyzer-proc-macro-srv",)

SEED_STAGE0_FORBIDDEN_BINS = (
    "cargo-trust",
    "tcargo",
    "tcargo-trust",
    "tcargo-fmt",
    "rustdoc",
    "rustfmt",
    "cargo-fmt",
    "cargo-clippy",
    "clippy-driver",
    "targo-clippy",
    "trust-clippy",
    "trust-clippy-driver",
    "rust-analyzer",
    "miri",
    "trust-miri",
    "cargo-miri",
    "targo-miri",
    "rust-gdb",
    "rust-gdbgui",
    "rust-lldb",
    "rust-windbg.cmd",
)

SEED_STAGE0_FORBIDDEN_LIBEXEC_BINS = ("rust-analyzer-proc-macro-srv",)

GENESIS_WRAPPER_SOURCES = {
    "trustc": "rustc",
    "rustc": "rustc",
    "trustdoc": "rustdoc",
    "targo": "cargo",
    "cargo": "cargo",
    "trustfmt": "rustfmt",
    "targo-fmt": "cargo-fmt",
    "tippy": "cargo-clippy",
    "targo-tippy": "cargo-clippy",
    "tippy-driver": "clippy-driver",
    "trust-analyzer": "rust-analyzer",
}

GENESIS_STUB_BINS = ("targo-trust",)
GENESIS_STUB_LIBEXEC_BINS = ("trust-analyzer-proc-macro-srv",)


def _host_executable(name: str, host: str) -> str:
    return f"{name}.exe" if "windows" in host else name


def _stage0_bin_filename(name: str, host: str) -> str:
    return name if name.endswith(".cmd") else _host_executable(name, host)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _capture_identity(path: Path, args: tuple[str, ...]) -> tuple[bool, str]:
    try:
        completed = subprocess.run(
            [str(path), *args],
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        return False, str(error)
    output = (completed.stdout or completed.stderr).strip()
    return completed.returncode == 0, output


def _repository_relative_path(root: Path, path: Path) -> str:
    """Return a portable repository-root-relative path or fail closed.

    The path is resolved, so under the sanctioned `build -> build.noindex` link
    (docs/BUILD_AND_INSTALL.md, "Keeping Spotlight out of build/") a build
    product resolves to `build.noindex/...`. That component is folded back to
    `build`: the link is a storage detail, and a receipt written before the move
    must name the same paths as one written after it. Only the sanctioned link
    is folded; any other layout keeps its physical spelling.
    """
    try:
        relative = path.resolve().relative_to(root.resolve())
    except (OSError, ValueError) as error:
        raise ValueError(f"path is outside the Trust repository: {path}: {error}") from error
    if relative.parts and relative.parts[0] == BUILD_NOINDEX and is_sanctioned_build_link(root):
        relative = Path("build", *relative.parts[1:])
    rendered = relative.as_posix()
    return rendered if rendered else "."


def _repository_lexical_relative_path(root: Path, path: Path) -> str:
    """Record an in-tree symlink entry without resolving its external target."""
    root_absolute = Path(os.path.abspath(root))
    path_absolute = Path(os.path.abspath(path))
    try:
        relative = path_absolute.relative_to(root_absolute)
    except ValueError as error:
        raise ValueError(f"lexical path is outside the Trust repository: {path}") from error
    rendered = relative.as_posix()
    return rendered if rendered else "."


def _provenance_git_environment() -> dict[str, str]:
    """Return a closed environment for source/provenance Git operations.

    Constructing this mapping from scratch is intentional.  Git and its
    transports honor a large execution surface (`GIT_EXEC_PATH`, askpass/SSH
    commands, dynamic-loader variables, proxy variables, repository redirects,
    and counted config in the environment).  A deny-list is therefore not a
    stable authority boundary.
    """
    if os.name == "nt":
        controlled_path = r"C:\Windows\System32;C:\Windows"
        empty_home = r"C:\Windows\Temp"
        false_program = None
    else:
        controlled_path = CONTROLLED_GIT_PATH
        empty_home = "/var/empty" if Path("/var/empty").is_dir() else "/"
        false_program = (
            "/usr/bin/false" if Path("/usr/bin/false").is_file() else "/bin/false"
        )

    env = {
        "PATH": controlled_path,
        "HOME": empty_home,
        "LANG": "C",
        "LC_ALL": "C",
        "TZ": "UTC",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_SYSTEM": os.devnull,
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_ATTR_NOSYSTEM": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_TERMINAL_PROMPT": "0",
        "GIT_PAGER": "",
        "PAGER": "",
    }
    if false_program is not None:
        env.update(
            {
                "GIT_ASKPASS": false_program,
                "SSH_ASKPASS": false_program,
                "SSH_ASKPASS_REQUIRE": "never",
            }
        )
    return env


def _git_bytes(
    repository: Path,
    args: tuple[str, ...],
    errors: list[str],
    label: str,
) -> bytes | None:
    env = _provenance_git_environment()
    try:
        _reject_local_git_execution_authority(repository)
        completed = subprocess.run(
            _controlled_git_command(["-C", str(repository), *args]),
            capture_output=True,
            check=False,
            env=env,
            timeout=30,
        )
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        errors.append(f"could not record {label}: {error}")
        return None
    if completed.returncode != 0:
        stderr = completed.stderr.decode("utf-8", errors="replace").strip()
        errors.append(
            f"could not record {label} (git exit {completed.returncode}): "
            f"{stderr or 'no diagnostic'}"
        )
        return None
    return completed.stdout


def _git_oid(
    repository: Path,
    args: tuple[str, ...],
    errors: list[str],
    label: str,
) -> str | None:
    raw = _git_bytes(repository, args, errors, label)
    if raw is None:
        return None
    value = raw.decode("ascii", errors="replace").strip()
    if len(value) not in (40, 64) or any(
        byte not in "0123456789abcdef" for byte in value
    ):
        errors.append(f"{label} did not produce one canonical Git object ID")
        return None
    return value


def _git_has_changes(
    repository: Path,
    args: tuple[str, ...],
    errors: list[str],
    label: str,
) -> bool:
    """Run a quiet Git plumbing comparison (0 = same, 1 = changed)."""
    env = _provenance_git_environment()
    try:
        _reject_local_git_execution_authority(repository)
        completed = subprocess.run(
            _controlled_git_command(["-C", str(repository), *args]),
            capture_output=True,
            check=False,
            env=env,
            timeout=30,
        )
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        errors.append(f"could not record {label}: {error}")
        return False
    if completed.returncode in (0, 1):
        return completed.returncode == 1
    stderr = completed.stderr.decode("utf-8", errors="replace").strip()
    errors.append(
        f"could not record {label} (git exit {completed.returncode}): "
        f"{stderr or 'no diagnostic'}"
    )
    return False


def _git_optional_config(
    repository: Path,
    key: str,
    errors: list[str],
    label: str,
) -> str | None:
    try:
        _reject_local_git_execution_authority(repository)
        completed = subprocess.run(
            _controlled_git_command(
                [
                    "-C",
                    str(repository),
                    "config",
                    "--local",
                    "--no-includes",
                    "--get",
                    key,
                ]
            ),
            capture_output=True,
            check=False,
            env=_provenance_git_environment(),
            timeout=30,
        )
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        errors.append(f"could not record {label}: {error}")
        return None
    if completed.returncode == 1:
        return None
    if completed.returncode != 0:
        stderr = completed.stderr.decode("utf-8", errors="replace").strip()
        errors.append(
            f"could not record {label} (git exit {completed.returncode}): "
            f"{stderr or 'no diagnostic'}"
        )
        return None
    try:
        return completed.stdout.decode("utf-8").strip().lower()
    except UnicodeError:
        errors.append(f"{label} is not valid UTF-8")
        return None


def _parse_index_entries(
    raw: bytes | None,
    errors: list[str],
    label: str,
) -> list[dict[str, object]]:
    """Parse canonical `git ls-files --stage -z` rows without path quoting."""
    if raw is None:
        return []
    if raw and not raw.endswith(b"\0"):
        errors.append(f"{label} did not use a complete NUL-delimited index")
        return []
    entries: list[dict[str, object]] = []
    for raw_entry in raw.split(b"\0"):
        if not raw_entry:
            continue
        metadata, separator, raw_path = raw_entry.partition(b"\t")
        fields = metadata.split()
        if not separator or len(fields) != 3 or not raw_path:
            errors.append(f"{label} contains a malformed index row")
            continue
        mode_raw, oid_raw, stage_raw = fields
        try:
            mode = mode_raw.decode("ascii")
            oid = oid_raw.decode("ascii")
            stage = int(stage_raw)
        except (UnicodeError, ValueError):
            errors.append(f"{label} contains non-canonical index metadata")
            continue
        relative = Path(os.fsdecode(raw_path))
        if (
            mode not in {"100644", "100755", "120000", "160000"}
            or len(oid) not in (40, 64)
            or any(character not in "0123456789abcdef" for character in oid)
            or stage not in (0, 1, 2, 3)
            or relative.is_absolute()
            or ".." in relative.parts
        ):
            errors.append(f"{label} contains a non-canonical index row")
            continue
        entries.append(
            {
                "mode": mode,
                "oid": oid,
                "stage": stage,
                "path": relative,
                "raw_path": raw_path,
            }
        )
    return entries


def _discover_repository_graph(
    root: Path,
    errors: list[str],
) -> dict[Path, dict[str, object]]:
    """Discover every recursive gitlink from canonical indexes, not local config."""
    graph: dict[Path, dict[str, object]] = {
        Path("."): {
            "parent": None,
            "child_from_parent": None,
            "parent_index_gitlink": None,
        }
    }
    queue = [Path(".")]
    while queue:
        relative_repository = queue.pop(0)
        repository = root if relative_repository == Path(".") else root / relative_repository
        repository_id = relative_repository.as_posix()
        index_snapshot = _git_bytes(
            repository,
            ("ls-files", "--stage", "-z"),
            errors,
            f"{repository_id} index snapshot",
        )
        entries = _parse_index_entries(
            index_snapshot, errors, f"{repository_id} index snapshot"
        )
        graph[relative_repository]["index_snapshot"] = index_snapshot
        graph[relative_repository]["index_entries"] = entries
        for entry in entries:
            if entry["mode"] != "160000" or entry["stage"] != 0:
                continue
            child_from_parent = entry["path"]
            assert isinstance(child_from_parent, Path)
            child = (
                child_from_parent
                if relative_repository == Path(".")
                else relative_repository / child_from_parent
            )
            if child in graph:
                errors.append(f"recursive gitlink discovery repeats {child.as_posix()}")
                continue
            child_repository = root / child
            top_level = _git_bytes(
                child_repository,
                ("rev-parse", "--show-toplevel"),
                errors,
                f"{child.as_posix()} initialized repository root",
            )
            initialized = False
            if top_level is not None:
                try:
                    initialized = (
                        Path(os.fsdecode(top_level).strip()).resolve()
                        == child_repository.resolve()
                    )
                except OSError:
                    initialized = False
            if not initialized:
                errors.append(f"recursive gitlink is not initialized: {child.as_posix()}")
                continue
            graph[child] = {
                "parent": relative_repository,
                "child_from_parent": child_from_parent,
                "parent_index_gitlink": entry["oid"],
            }
            queue.append(child)
    return graph


def _parse_index_tags(
    raw: bytes | None,
    errors: list[str],
    label: str,
) -> dict[Path, str]:
    """Parse the one-byte tags from `git ls-files -v/-f -z`."""
    if raw is None:
        return {}
    if raw and not raw.endswith(b"\0"):
        errors.append(f"{label} did not use a complete NUL-delimited path list")
        return {}
    tags: dict[Path, str] = {}
    for item in raw.split(b"\0"):
        if not item:
            continue
        if len(item) < 3 or item[1:2] != b" ":
            errors.append(f"{label} contains a malformed tagged path")
            continue
        try:
            tag = item[:1].decode("ascii")
        except UnicodeError:
            errors.append(f"{label} contains a non-ASCII tag")
            continue
        path = Path(os.fsdecode(item[2:]))
        if path.is_absolute() or ".." in path.parts or path in tags:
            errors.append(f"{label} contains a duplicate or unsafe path")
            continue
        tags[path] = tag
    return tags


def _git_blob_identities(
    path: Path,
    index_mode: str,
    object_format: str,
) -> tuple[str, str, str]:
    """Return (Git blob OID, SHA-256, working mode) for exact consumed bytes."""
    before = path.lstat()
    if stat.S_ISLNK(before.st_mode):
        content = os.fsencode(os.readlink(path))
        actual_mode = "120000"
        git_digest = hashlib.new(object_format)
        git_digest.update(f"blob {len(content)}\0".encode("ascii"))
        git_digest.update(content)
        return git_digest.hexdigest(), hashlib.sha256(content).hexdigest(), actual_mode
    if not stat.S_ISREG(before.st_mode):
        raise OSError("tracked path is not a regular file or symlink")
    actual_mode = "100755" if before.st_mode & 0o111 else "100644"
    git_digest = hashlib.new(object_format)
    git_digest.update(f"blob {before.st_size}\0".encode("ascii"))
    content_digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            git_digest.update(chunk)
            content_digest.update(chunk)
    after = path.lstat()
    if (
        before.st_dev,
        before.st_ino,
        before.st_size,
        before.st_mtime_ns,
        before.st_mode,
    ) != (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
        after.st_mode,
    ):
        raise OSError("tracked file changed while it was being hashed")
    return git_digest.hexdigest(), content_digest.hexdigest(), actual_mode


def _capture_working_tree_snapshot(
    repository: Path,
    entries: list[dict[str, object]],
    object_format: str,
    errors: list[str],
    repository_id: str,
) -> tuple[str, list[str], list[str]]:
    """Hash and compare every tracked working-tree byte independently of index flags."""
    snapshot = hashlib.sha256()
    mismatches: list[str] = []
    attribute_normalized_paths: list[str] = []
    seen_stage0_paths: set[Path] = set()
    for entry in entries:
        mode = str(entry["mode"])
        oid = str(entry["oid"])
        stage = int(entry["stage"])
        relative = entry["path"]
        raw_path = entry["raw_path"]
        assert isinstance(relative, Path) and isinstance(raw_path, bytes)
        snapshot.update(mode.encode("ascii") + b"\0")
        snapshot.update(oid.encode("ascii") + b"\0")
        snapshot.update(str(stage).encode("ascii") + b"\0")
        snapshot.update(len(raw_path).to_bytes(8, "big") + raw_path)
        if stage != 0:
            mismatches.append(relative.as_posix())
            snapshot.update(b"unmerged\0")
            continue
        if relative in seen_stage0_paths:
            errors.append(f"{repository_id} index repeats stage-0 path {relative.as_posix()}")
            mismatches.append(relative.as_posix())
            continue
        seen_stage0_paths.add(relative)
        if mode == "160000":
            snapshot.update(b"gitlink\0")
            continue
        candidate = repository / relative
        try:
            actual_oid, content_sha256, actual_mode = _git_blob_identities(
                candidate, mode, object_format
            )
        except OSError as error:
            errors.append(
                f"could not bind tracked path in {repository_id} "
                f"{relative.as_posix()}: {error}"
            )
            mismatches.append(relative.as_posix())
            snapshot.update(b"unreadable\0")
            continue
        snapshot.update(actual_mode.encode("ascii") + b"\0")
        snapshot.update(actual_oid.encode("ascii") + b"\0")
        snapshot.update(content_sha256.encode("ascii") + b"\0")
        if actual_mode != mode:
            mismatches.append(relative.as_posix())
            continue
        if actual_oid != oid:
            attributes_raw = _git_bytes(
                repository,
                (
                    "check-attr",
                    "-z",
                    "text",
                    "eol",
                    "filter",
                    "working-tree-encoding",
                    "--",
                    relative.as_posix(),
                ),
                errors,
                f"{repository_id} checkout attributes for {relative.as_posix()}",
            )
            attributes: dict[str, str] = {}
            if attributes_raw is not None:
                fields = attributes_raw.split(b"\0")
                if fields and fields[-1] == b"":
                    fields.pop()
                if len(fields) % 3 != 0:
                    errors.append(
                        f"{repository_id} checkout attributes are malformed for "
                        f"{relative.as_posix()}"
                    )
                else:
                    for offset in range(0, len(fields), 3):
                        path_field, attribute_field, value_field = fields[offset : offset + 3]
                        if os.fsdecode(path_field) != relative.as_posix():
                            errors.append(
                                f"{repository_id} checkout attributes returned a foreign path"
                            )
                            continue
                        attributes[attribute_field.decode("ascii", errors="replace")] = (
                            value_field.decode("utf-8", errors="replace")
                        )
            unsafe_attribute = any(
                attributes.get(name) not in {None, "unspecified", "unset"}
                for name in ("filter", "working-tree-encoding")
            )
            if unsafe_attribute:
                errors.append(
                    f"{repository_id} tracked path uses unsupported checkout filters: "
                    f"{relative.as_posix()}"
                )
            normalized_raw = (
                None
                if unsafe_attribute
                else _git_bytes(
                    repository,
                    (
                        "hash-object",
                        f"--path={relative.as_posix()}",
                        "--",
                        relative.as_posix(),
                    ),
                    errors,
                    f"{repository_id} attribute-normalized bytes for "
                    f"{relative.as_posix()}",
                )
            )
            normalized_oid = (
                normalized_raw.decode("ascii", errors="replace").strip()
                if normalized_raw is not None
                else ""
            )
            try:
                repeated_oid, repeated_sha256, repeated_mode = _git_blob_identities(
                    candidate, mode, object_format
                )
            except OSError as error:
                errors.append(
                    f"could not rebind attribute-normalized path in {repository_id} "
                    f"{relative.as_posix()}: {error}"
                )
                repeated_oid = repeated_sha256 = repeated_mode = ""
            stable_bytes = (
                repeated_oid == actual_oid
                and repeated_sha256 == content_sha256
                and repeated_mode == actual_mode
            )
            snapshot.update(
                json.dumps(
                    {
                        "attributes": dict(sorted(attributes.items())),
                        "normalized_oid": normalized_oid,
                        "stable_bytes": stable_bytes,
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
                + b"\0"
            )
            if normalized_oid == oid and not unsafe_attribute and stable_bytes:
                attribute_normalized_paths.append(relative.as_posix())
            else:
                mismatches.append(relative.as_posix())
    return (
        snapshot.hexdigest(),
        sorted(set(mismatches)),
        sorted(set(attribute_normalized_paths)),
    )


def _nul_paths(raw: bytes | None, errors: list[str], label: str) -> list[Path]:
    if raw is None:
        return []
    if raw and not raw.endswith(b"\0"):
        errors.append(f"{label} did not use a complete NUL-delimited path list")
        return []
    paths: list[Path] = []
    for item in raw.split(b"\0"):
        if not item:
            continue
        path = Path(os.fsdecode(item))
        if path.is_absolute() or ".." in path.parts:
            errors.append(f"{label} returned a non-repository-relative path")
            continue
        paths.append(path)
    return paths


def _untracked_file_records(
    repository: Path,
    paths: list[Path],
    errors: list[str],
    repository_id: str,
) -> list[dict[str, str]]:
    records: list[dict[str, str]] = []
    for relative in sorted(paths, key=lambda path: path.as_posix()):
        candidate = repository / relative
        try:
            if candidate.is_symlink():
                target = os.fsencode(os.readlink(candidate))
                digest = hashlib.sha256(target).hexdigest()
                kind = "symlink-target"
            elif candidate.is_file():
                digest = _sha256_file(candidate)
                kind = "file"
            else:
                errors.append(
                    f"untracked path in {repository_id} is not a regular file or symlink: "
                    f"{relative.as_posix()}"
                )
                continue
        except OSError as error:
            errors.append(
                f"could not hash untracked path in {repository_id} "
                f"{relative.as_posix()}: {error}"
            )
            continue
        records.append({"path": relative.as_posix(), "kind": kind, "sha256": digest})
    return records


def _index_gitlink(
    parent: Path,
    relative: Path,
    errors: list[str],
    label: str,
) -> str | None:
    raw = _git_bytes(
        parent,
        ("ls-files", "--stage", "-z", "--", relative.as_posix()),
        errors,
        label,
    )
    if raw is None:
        return None
    matches: list[str] = []
    for entry in raw.split(b"\0"):
        if not entry:
            continue
        metadata, separator, _path = entry.partition(b"\t")
        fields = metadata.split()
        if separator and len(fields) == 3 and fields[0] == b"160000" and fields[2] == b"0":
            matches.append(fields[1].decode("ascii", errors="replace"))
    if len(matches) != 1:
        errors.append(f"{label} did not resolve exactly one stage-0 gitlink")
        return None
    value = matches[0]
    if len(value) not in (40, 64) or any(
        byte not in "0123456789abcdef" for byte in value
    ):
        errors.append(f"{label} returned a non-canonical Git object ID")
        return None
    return value


def capture_source_lineage(root: Path) -> dict[str, object]:
    """Capture the exact recursive Git state used by a bootstrap build.

    Clean committed trees are eligible for immutable release lineage. A tree
    whose only changes are staged is recorded as a non-release proposal.
    Unstaged, untracked, conflicted, uninitialized, ambiguous, or mismatched
    recursive state is rejected instead of being summarized optimistically.
    """
    errors: list[str] = []
    root = root.resolve()
    repository_graph = _discover_repository_graph(root, errors)
    repository_paths = list(repository_graph)

    repositories: list[dict[str, object]] = []
    for relative_repository in sorted(
        repository_paths, key=lambda path: (path.as_posix() != ".", path.as_posix())
    ):
        repository = root if relative_repository == Path(".") else root / relative_repository
        repository_id = relative_repository.as_posix()
        head = _git_oid(
            repository,
            ("rev-parse", "--verify", "HEAD"),
            errors,
            f"{repository_id} HEAD",
        )
        head_tree = _git_oid(
            repository,
            ("rev-parse", "--verify", "HEAD^{tree}"),
            errors,
            f"{repository_id} HEAD tree",
        )
        graph_row = repository_graph[relative_repository]
        index_snapshot = graph_row.get("index_snapshot")
        index_entries = graph_row.get("index_entries")
        if not isinstance(index_entries, list):
            errors.append(f"{repository_id} has no canonical index snapshot")
            index_entries = []
        object_format_raw = _git_bytes(
            repository,
            ("rev-parse", "--show-object-format"),
            errors,
            f"{repository_id} object format",
        )
        object_format = (
            object_format_raw.decode("ascii", errors="replace").strip()
            if object_format_raw is not None
            else ""
        )
        if object_format not in {"sha1", "sha256"}:
            errors.append(f"{repository_id} uses an unsupported Git object format")
            object_format = "sha256"
        checkout_policy = {
            key: _git_optional_config(
                repository,
                key,
                errors,
                f"{repository_id} {key}",
            )
            for key in (
                "core.autocrlf",
                "core.symlinks",
                "core.filemode",
                "core.ignorestat",
                "core.sparsecheckout",
                "core.attributesfile",
            )
        }
        if checkout_policy["core.autocrlf"] not in (None, "false"):
            errors.append(f"{repository_id} enables unsupported core.autocrlf")
        if checkout_policy["core.symlinks"] == "false":
            errors.append(f"{repository_id} disables tracked symlink materialization")
        if checkout_policy["core.filemode"] == "false":
            errors.append(f"{repository_id} disables tracked executable-mode authority")
        if checkout_policy["core.ignorestat"] not in (None, "false"):
            errors.append(f"{repository_id} enables unsupported core.ignoreStat")
        if checkout_policy["core.sparsecheckout"] not in (None, "false"):
            errors.append(f"{repository_id} enables unsupported sparse checkout")
        if checkout_policy["core.attributesfile"] is not None:
            errors.append(f"{repository_id} configures an external attributes file")
        info_attributes_raw = _git_bytes(
            repository,
            ("rev-parse", "--git-path", "info/attributes"),
            errors,
            f"{repository_id} repository-local attributes path",
        )
        info_attributes_value = (
            os.fsdecode(info_attributes_raw).strip()
            if info_attributes_raw is not None
            else ""
        )
        info_attributes_path = Path(info_attributes_value)
        if not info_attributes_path.is_absolute():
            info_attributes_path = repository / info_attributes_path
        info_attributes_present = os.path.lexists(info_attributes_path)
        if info_attributes_present:
            errors.append(f"{repository_id} has untracked repository-local attributes")
        index_tags = _parse_index_tags(
            _git_bytes(
                repository,
                ("ls-files", "-v", "-z"),
                errors,
                f"{repository_id} index flags",
            ),
            errors,
            f"{repository_id} index flags",
        )
        fsmonitor_tags = _parse_index_tags(
            _git_bytes(
                repository,
                ("ls-files", "-f", "-z"),
                errors,
                f"{repository_id} fsmonitor flags",
            ),
            errors,
            f"{repository_id} fsmonitor flags",
        )
        assume_unchanged_paths = sorted(
            path.as_posix() for path, tag in index_tags.items() if tag.islower()
        )
        skip_worktree_paths = sorted(
            path.as_posix() for path, tag in index_tags.items() if tag.upper() == "S"
        )
        fsmonitor_valid_paths = sorted(
            path.as_posix() for path, tag in fsmonitor_tags.items() if tag.islower()
        )
        if assume_unchanged_paths:
            errors.append(f"{repository_id} has assume-unchanged index entries")
        if skip_worktree_paths:
            errors.append(f"{repository_id} has skip-worktree index entries")
        if fsmonitor_valid_paths:
            errors.append(f"{repository_id} has fsmonitor-valid index entries")
        has_staged_changes = _git_has_changes(
            repository,
            (
                "diff-index",
                "--cached",
                "--quiet",
                "--ignore-submodules=dirty",
                "HEAD",
                "--",
            ),
            errors,
            f"{repository_id} staged state",
        )
        (
            working_tree_snapshot_sha256,
            working_tree_mismatch_paths,
            attribute_normalized_paths,
        ) = (
            _capture_working_tree_snapshot(
                repository,
                index_entries,
                object_format,
                errors,
                repository_id,
            )
        )
        has_unstaged_changes = bool(working_tree_mismatch_paths)
        untracked_paths = _nul_paths(
            _git_bytes(
                repository,
                (
                    "ls-files",
                    "--others",
                    "--exclude-per-directory=.gitignore",
                    "-z",
                ),
                errors,
                f"{repository_id} untracked paths",
            ),
            errors,
            f"{repository_id} untracked paths",
        )
        conflict_paths = sorted(
            {
                entry["path"]
                for entry in index_entries
                if int(entry["stage"]) != 0 and isinstance(entry["path"], Path)
            },
            key=lambda path: path.as_posix(),
        )
        untracked_files = _untracked_file_records(
            repository, untracked_paths, errors, repository_id
        )

        parent_repository: str | None = None
        parent_head_gitlink: str | None = None
        parent_index_gitlink: str | None = None
        head_matches_parent_head: bool | None = None
        head_matches_parent_index: bool | None = None
        if relative_repository != Path("."):
            parent_relative = graph_row.get("parent")
            child_from_parent = graph_row.get("child_from_parent")
            parent_index_value = graph_row.get("parent_index_gitlink")
            if not isinstance(parent_relative, Path) or not isinstance(
                child_from_parent, Path
            ) or not isinstance(parent_index_value, str):
                errors.append(f"could not resolve parent gitlink for {repository_id}")
            else:
                parent = root if parent_relative == Path(".") else root / parent_relative
                parent_repository = parent_relative.as_posix()
                parent_head_gitlink = _git_oid(
                    parent,
                    ("rev-parse", "--verify", f"HEAD:{child_from_parent.as_posix()}"),
                    errors,
                    f"{repository_id} parent HEAD gitlink",
                )
                parent_index_gitlink = parent_index_value
                if head is not None and parent_head_gitlink is not None:
                    head_matches_parent_head = head == parent_head_gitlink
                if head is not None:
                    head_matches_parent_index = head == parent_index_gitlink
                    if not head_matches_parent_index:
                        errors.append(
                            f"{repository_id} HEAD does not match its parent index gitlink"
                        )

        repositories.append(
            {
                "path": repository_id,
                "head": head,
                "head_tree": head_tree,
                "object_format": object_format,
                "checkout_policy": checkout_policy,
                "info_attributes_present": info_attributes_present,
                "index_snapshot_sha256": hashlib.sha256(index_snapshot or b"").hexdigest(),
                "working_tree_snapshot_sha256": working_tree_snapshot_sha256,
                "has_staged_changes": has_staged_changes,
                "has_unstaged_changes": has_unstaged_changes,
                "working_tree_mismatch_paths": working_tree_mismatch_paths,
                "attribute_normalized_paths": attribute_normalized_paths,
                "assume_unchanged_paths": assume_unchanged_paths,
                "skip_worktree_paths": skip_worktree_paths,
                "fsmonitor_valid_paths": fsmonitor_valid_paths,
                "untracked_files": untracked_files,
                "conflict_paths": [path.as_posix() for path in conflict_paths],
                "parent_repository": parent_repository,
                "parent_head_gitlink": parent_head_gitlink,
                "parent_index_gitlink": parent_index_gitlink,
                "head_matches_parent_head": head_matches_parent_head,
                "head_matches_parent_index": head_matches_parent_index,
            }
        )

    for repository in repositories:
        repository_id = str(repository["path"])
        if repository["has_unstaged_changes"]:
            errors.append(f"{repository_id} has unstaged tracked changes")
        if repository["untracked_files"]:
            errors.append(f"{repository_id} has untracked files")
        if repository["conflict_paths"]:
            errors.append(f"{repository_id} has unresolved conflicts")

    closure = {
        "schema": "trust.source-lineage-closure.v1",
        "repositories": repositories,
    }
    closure_sha256 = hashlib.sha256(
        json.dumps(closure, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    has_staged_changes = any(bool(repository["has_staged_changes"]) for repository in repositories)
    parent_head_mismatch = any(
        repository["head_matches_parent_head"] is False for repository in repositories
    )
    if errors:
        status = "rejected"
    elif has_staged_changes or parent_head_mismatch:
        status = "staged_proposal"
    else:
        status = "immutable_release"
    return {
        "schema": "trust.source-lineage.v1",
        "status": status,
        "source_tree_clean": status == "immutable_release",
        "closure_sha256": closure_sha256,
        "repositories": repositories,
        "errors": sorted(set(errors)),
    }


def _bind_source_lineage(
    before: dict[str, object] | None,
    after: dict[str, object],
) -> dict[str, object]:
    lineage = dict(after)
    errors = [str(error) for error in after.get("errors", [])]
    before_sha = before.get("closure_sha256") if before is not None else None
    after_sha = after.get("closure_sha256")
    stable = before is not None and before_sha == after_sha
    if before is None:
        errors.append("missing pre-build source-lineage snapshot")
    else:
        errors.extend(str(error) for error in before.get("errors", []))
        if before.get("status") == "rejected":
            errors.append("pre-build source lineage was rejected")
        if not stable:
            errors.append("recursive source lineage changed during the bootstrap build")
    if errors:
        status = "rejected"
    else:
        status = str(after.get("status"))
    lineage.update(
        {
            "status": status,
            "source_tree_clean": status == "immutable_release",
            "stable_across_build": stable,
            "pre_build_closure_sha256": before_sha,
            "post_build_closure_sha256": after_sha,
            "errors": sorted(set(errors)),
        }
    )
    return lineage


@contextmanager
def _open_seekable_seed_archive(archive: Path):
    """Decode once; tar member and link lookups may seek in the temporary tar."""
    # An XZ seek backwards replays decompression from the beginning. getmembers()
    # followed by extractfile() does this for every archive, and aliases can do
    # it again. Keep the same tarfile resolution and validation on a temporary
    # seekable copy, with bounded copy buffers and no persistent authority cache.
    with tempfile.TemporaryFile() as decoded:
        with lzma.open(archive, "rb") as compressed:
            shutil.copyfileobj(compressed, decoded, length=1024 * 1024)
        decoded.seek(0)
        with tarfile.open(fileobj=decoded, mode="r:") as bundle:
            yield bundle


def _capture_seed_archive_members(
    root: Path,
    host: str,
    pins: dict[str, str],
    payloads: list[dict[str, object]],
    errors: list[str],
) -> tuple[list[dict[str, object]], dict[str, dict[str, object]]]:
    """Hash every required stage0 entrypoint in its exact pinned archive."""
    compiler_version = pins.get("compiler_version", "")
    rustfmt_version = pins.get("rustfmt_version", "")
    date = pins.get("compiler_date", "")
    archive_specs = (
        (
            "trustc",
            compiler_version,
            (
                ("bin", "trustc"),
                ("bin", "rustc"),
                ("bin", "trustdoc"),
                ("libexec", "trust-analyzer-proc-macro-srv"),
            ),
        ),
        ("targo", compiler_version, (("bin", "targo"), ("bin", "cargo"))),
        ("targo-trust", compiler_version, (("bin", "targo-trust"),)),
        (
            "trustfmt",
            rustfmt_version,
            (("bin", "trustfmt"), ("bin", "targo-fmt")),
        ),
        (
            "tippy",
            compiler_version,
            (("bin", "tippy"), ("bin", "targo-tippy"), ("bin", "tippy-driver")),
        ),
        (
            "trust-analyzer",
            compiler_version,
            (("bin", "trust-analyzer"),),
        ),
    )
    declared_payload_paths = [str(payload.get("path", "")) for payload in payloads]
    records: list[dict[str, object]] = []
    member_bindings: dict[str, dict[str, object]] = {}
    for component, version, wanted_members in archive_specs:
        if not date or not version:
            errors.append(f"seed pins cannot name the exact {component} archive")
            continue
        filename = f"{component}-{version}-{host}.tar.xz"
        archive_relative = Path("bootstrap") / "trust-stage0" / "dist" / date / filename
        if declared_payload_paths.count(archive_relative.as_posix()) != 1:
            errors.append(
                f"src/stage0 does not declare the exact required archive: "
                f"{archive_relative.as_posix()}"
            )
            continue
        archive = root / archive_relative
        try:
            with _open_seekable_seed_archive(archive) as bundle:
                archive_prefix = filename.removesuffix(".tar.xz")
                all_members = bundle.getmembers()
                paired_source = f"lib/rustlib/{host}/bin/rust-lld"
                paired_root = "bin/rust-lld"
                paired = component == "trustc" and host.endswith("-apple-darwin")
                if paired:
                    # Trust: these are archive members, never arbitrary files
                    # discovered in a previously hydrated SDK. Older archives
                    # omit the root role; fresh extraction derives it from the
                    # exact authenticated host image, preserving the closed
                    # compiler/Host SDK/bin/rust-lld locator.
                    available = {member.name for member in all_members}
                    for relative in (paired_source, paired_root):
                        if f"{archive_prefix}/{component}/{relative}" in available:
                            parent, leaf = relative.rsplit("/", 1)
                            wanted_members += ((parent, leaf),)
                for destination_dir, tool in wanted_members:
                    executable = _host_executable(tool, host)
                    member_path = (
                        f"{archive_prefix}/{component}/{destination_dir}/{executable}"
                    )
                    matches = [member for member in all_members if member.name == member_path]
                    if len(matches) != 1:
                        errors.append(
                            f"seed {component} archive does not contain exactly one "
                            f"{component}/{destination_dir}/{executable} member"
                        )
                        continue
                    member = matches[0]
                    if tool == "rust-lld" and (not member.isfile() or not member.mode & 0o111):
                        errors.append(f"paired linker archive member is not regular executable: {member.name}")
                        continue
                    if not (member.isfile() or member.islnk() or member.issym()):
                        errors.append(
                            f"seed archive member is not a file or link: {member.name}"
                        )
                        continue
                    extracted = bundle.extractfile(member)
                    if extracted is None:
                        errors.append(f"seed archive member could not be read: {member.name}")
                        continue
                    digest = hashlib.sha256()
                    for chunk in iter(lambda: extracted.read(1024 * 1024), b""):
                        digest.update(chunk)
                    sha256 = digest.hexdigest()
                    destination = f"{destination_dir}/{executable}"
                    member_type = (
                        "regular"
                        if member.isfile()
                        else "hardlink"
                        if member.islnk()
                        else "symlink"
                    )
                    archive_record = {
                        "tool": tool,
                        "destination": destination,
                        "archive_path": archive_relative.as_posix(),
                        "member_path": member.name,
                        "member_type": member_type,
                        "member_mode": member.mode,
                        "member_linkname": member.linkname or None,
                        "member_sha256": sha256,
                    }
                    records.append(archive_record)
                    if destination in member_bindings:
                        errors.append(f"duplicate seed destination across archives: {destination}")
                    member_bindings[destination] = archive_record
                if paired:
                    source_binding = member_bindings.get(paired_source)
                    root_binding = member_bindings.get(paired_root)
                    if source_binding is None and root_binding is not None:
                        errors.append("paired linker root archive role lacks its exact host image")
                    elif source_binding is not None:
                        if root_binding is None:
                            root_binding = {**source_binding, "destination": paired_root,
                                            "materialization": "paired-linker-copy-v1",
                                            "derived_from": paired_source}
                            records.append(root_binding)
                            member_bindings[paired_root] = root_binding
                        elif any(root_binding[key] != source_binding[key]
                                 for key in ("member_sha256", "member_mode")):
                            errors.append("paired linker archive roles differ in bytes or mode")
        except (OSError, EOFError, lzma.LZMAError, KeyError, tarfile.TarError) as error:
            errors.append(f"could not inspect seed {component} archive: {error}")
            continue
    return sorted(records, key=lambda record: str(record["destination"])), member_bindings


def _capture_stage0_tree(root: Path, stage0: Path) -> dict[str, object]:
    """Hash the complete hydrated stage0 tree without following directory links."""
    entries: list[dict[str, object]] = []
    errors: list[str] = []
    stage0_resolved = stage0.resolve()
    walk_errors: list[OSError] = []
    for current_root, directory_names, file_names in os.walk(
        stage0,
        followlinks=False,
        onerror=walk_errors.append,
    ):
        current = Path(current_root)
        for name in sorted((*directory_names, *file_names)):
            path = current / name
            relative = path.relative_to(stage0).as_posix()
            try:
                metadata = path.lstat()
            except OSError as error:
                errors.append(f"could not stat hydrated stage0 entry {relative}: {error}")
                continue
            row: dict[str, object] = {
                "path": relative,
                "mode": stat.S_IMODE(metadata.st_mode),
            }
            if stat.S_ISDIR(metadata.st_mode):
                row["type"] = "directory"
            elif stat.S_ISREG(metadata.st_mode):
                try:
                    sha256 = _sha256_file(path)
                except OSError as error:
                    errors.append(f"could not hash hydrated stage0 entry {relative}: {error}")
                    sha256 = None
                row.update(
                    {
                        "type": "regular",
                        "size": metadata.st_size,
                        "sha256": sha256,
                    }
                )
            elif stat.S_ISLNK(metadata.st_mode):
                link_target: str | None = None
                try:
                    link_target = os.readlink(path)
                    resolved_target = path.resolve(strict=True)
                    resolved_target.relative_to(stage0_resolved)
                except (OSError, ValueError) as error:
                    errors.append(
                        f"hydrated seed stage0 link escapes or is unreadable: {relative}: {error}"
                    )
                    resolved_target_text = None
                else:
                    resolved_target_text = _repository_relative_path(root, resolved_target)
                row.update(
                    {
                        "type": "symlink",
                        "link_target": link_target,
                        "resolved_target": resolved_target_text,
                    }
                )
            else:
                row["type"] = "unsupported"
                errors.append(f"hydrated seed stage0 has unsupported entry type: {relative}")
            entries.append(row)
    errors.extend(f"could not walk hydrated stage0 tree: {error}" for error in walk_errors)
    closure = {
        "schema": "trust.seed-stage0-tree.v1",
        "root": _repository_relative_path(root, stage0),
        "entries": sorted(entries, key=lambda row: str(row["path"])),
    }
    closure_sha256 = hashlib.sha256(
        json.dumps(closure, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return {
        **closure,
        "status": "validated" if not errors else "rejected",
        "closure_sha256": closure_sha256,
        "errors": sorted(set(errors)),
    }


def _capture_external_tree(
    tree: Path,
    allowed_root: Path,
    *,
    bind_external_symlink_targets: bool = False,
) -> dict[str, object]:
    """Canonical byte manifest for an external producer tree on this machine."""
    errors: list[str] = []
    entries: list[dict[str, object]] = []
    try:
        tree_real = tree.resolve(strict=True)
        allowed_real = allowed_root.resolve(strict=True)
        tree_real.relative_to(allowed_real)
    except (OSError, ValueError) as error:
        return {
            "schema": "trust.external-producer-tree.v1",
            "selected_local_path": str(tree),
            "real_path": None,
            "status": "rejected",
            "closure_sha256": None,
            "entries": [],
            "errors": [f"external producer tree is outside its admitted root: {error}"],
        }
    if tree.is_symlink() or not tree.is_dir():
        errors.append("external producer tree root is not a real directory")

    walk_errors: list[OSError] = []
    for current_root, directory_names, file_names in os.walk(
        tree_real,
        followlinks=False,
        onerror=walk_errors.append,
    ):
        current = Path(current_root)
        for name in sorted((*directory_names, *file_names)):
            path = current / name
            relative = path.relative_to(tree_real).as_posix()
            try:
                metadata = path.lstat()
            except OSError as error:
                errors.append(f"could not stat external producer entry {relative}: {error}")
                continue
            row: dict[str, object] = {
                "path": relative,
                "mode": stat.S_IMODE(metadata.st_mode),
            }
            if stat.S_ISDIR(metadata.st_mode):
                row["type"] = "directory"
            elif stat.S_ISREG(metadata.st_mode):
                try:
                    sha256 = _sha256_file(path)
                except OSError as error:
                    errors.append(f"could not hash external producer entry {relative}: {error}")
                    sha256 = None
                row.update(
                    {
                        "type": "regular",
                        "size": metadata.st_size,
                        "sha256": sha256,
                    }
                )
            elif stat.S_ISLNK(metadata.st_mode):
                link_target: str | None = None
                try:
                    link_target = os.readlink(path)
                    resolved_target = path.resolve(strict=True)
                    resolved_target.relative_to(allowed_real)
                except (OSError, ValueError) as error:
                    errors.append(
                        f"external producer link escapes or is unreadable: {relative}: {error}"
                    )
                    resolved_target_text = None
                else:
                    resolved_target_text = str(resolved_target)
                    try:
                        resolved_target.relative_to(tree_real)
                    except ValueError:
                        if bind_external_symlink_targets and resolved_target.is_file():
                            try:
                                target_metadata = resolved_target.lstat()
                                row.update(
                                    {
                                        "resolved_target_type": "regular",
                                        "resolved_target_mode": stat.S_IMODE(
                                            target_metadata.st_mode
                                        ),
                                        "resolved_target_size": target_metadata.st_size,
                                        "resolved_target_sha256": _sha256_file(
                                            resolved_target
                                        ),
                                    }
                                )
                            except OSError as error:
                                errors.append(
                                    f"could not bind external producer link target "
                                    f"{relative}: {error}"
                                )
                        else:
                            errors.append(
                                "external producer link target is outside the walked tree: "
                                f"{relative}"
                            )
                row.update(
                    {
                        "type": "symlink",
                        "link_target": link_target,
                        "resolved_target": resolved_target_text,
                    }
                )
            else:
                row["type"] = "unsupported"
                errors.append(f"external producer tree has unsupported entry: {relative}")
            entries.append(row)
    errors.extend(f"could not walk external producer tree: {error}" for error in walk_errors)
    closure = {
        "schema": "trust.external-producer-tree.v1",
        "selected_local_path": str(tree),
        "real_path": str(tree_real),
        "entries": sorted(entries, key=lambda row: str(row["path"])),
    }
    closure_sha256 = hashlib.sha256(
        json.dumps(closure, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return {
        **closure,
        "status": "validated" if not errors else "rejected",
        "closure_sha256": closure_sha256,
        "errors": sorted(set(errors)),
    }


def _capture_seed_compiler_identity(
    root: Path,
    host: str,
    pins: dict[str, str],
    archive_member_bindings: dict[str, dict[str, object]],
    reported_product_identities: dict[str, str],
    *,
    build_root: Path | None = None,
) -> dict[str, object]:
    """Bind the complete hydrated stage0 tree and canonical entrypoint surface.

    ``compiler_version`` and ``rustfmt_version`` in ``src/stage0`` are archive
    labels used by rustup's distribution protocol.  They are not necessarily
    the versions printed by the products inside those archives (for example,
    a ``1.99.0-trust`` archive can contain a compiler reporting
    ``1.99.0-dev``).  The exact product identities are admitted separately in
    the seed ledger so neither namespace is silently conflated here.
    """
    stage0 = (build_root if build_root is not None else root / "build") / host / "stage0"
    bin_dir = stage0 / "bin"
    stage0_root_present = os.path.lexists(stage0)
    if not stage0_root_present:
        return {
            "schema": "trust.seed-compiler-identity.v1",
            "status": "not-materialized",
            "stage0_root": _repository_relative_path(root, stage0),
            "stage0_root_present": False,
            "tools": [],
            "forbidden_paths_present": [],
            "stage0_tree": None,
            "errors": [],
        }

    errors: list[str] = []
    paired_linker_binding = None
    if stage0.is_symlink() or not stage0.is_dir():
        errors.append("hydrated seed stage0 root is not a real directory")
        stage0_tree: dict[str, object] | None = None
    else:
        stage0_tree = _capture_stage0_tree(root, stage0)
        errors.extend(str(error) for error in stage0_tree.get("errors", []))
        try:
            paired_linker_binding = _IDENTITY_OWNER.paired_linker(stage0, host)
            archived_linker = archive_member_bindings.get("bin/rust-lld")
            if paired_linker_binding is not None:
                if (archived_linker is None or
                        archived_linker["member_sha256"] != paired_linker_binding["sha256"] or
                        archived_linker["member_mode"] != paired_linker_binding["mode"]):
                    errors.append("hydrated paired linker differs from its pinned archive member")
                else:
                    paired_linker_binding["archive_binding"] = archived_linker
            elif archived_linker is not None:
                errors.append("hydrated seed lacks its archived paired linker roles")
        except (OSError, ValueError) as error:
            errors.append(f"hydrated paired linker binding failed: {error}")

    required_paths = [
        (name, "bin", bin_dir / _host_executable(name, host))
        for name in SEED_STAGE0_REQUIRED_BINS
    ] + [
        (
            name,
            "libexec",
            stage0 / "libexec" / _host_executable(name, host),
        )
        for name in SEED_STAGE0_REQUIRED_LIBEXEC_BINS
    ]
    tools: list[dict[str, object]] = []
    paths: dict[str, Path] = {}
    for name, destination_dir, path in required_paths:
        paths[name] = path
        destination = f"{destination_dir}/{path.name}"
        archive_binding = archive_member_bindings.get(destination)
        row: dict[str, object] = {
            "name": name,
            "path": _repository_relative_path(root, path),
            "destination": destination,
            "archive_member_sha256": (
                archive_binding.get("member_sha256")
                if archive_binding is not None
                else None
            ),
            "archive_member_type": (
                archive_binding.get("member_type")
                if archive_binding is not None
                else None
            ),
            "archive_member_mode": (
                archive_binding.get("member_mode")
                if archive_binding is not None
                else None
            ),
        }
        if path.is_file():
            metadata = path.lstat()
            row["destination_type"] = (
                "symlink" if stat.S_ISLNK(metadata.st_mode) else "regular"
            )
            row["destination_mode"] = stat.S_IMODE(metadata.st_mode)
            row["executable"] = os.access(path, os.X_OK)
            row["sha256"] = _sha256_file(path)
            if row["archive_member_sha256"] != row["sha256"]:
                errors.append(
                    f"hydrated seed {destination} does not match its pinned archive member"
                )
            archive_type = row["archive_member_type"]
            if archive_type == "symlink":
                if row["destination_type"] != "symlink":
                    errors.append(
                        f"hydrated seed {destination} is not the archived symlink type"
                    )
                else:
                    destination_linkname = os.readlink(path)
                    row["destination_linkname"] = destination_linkname
                    if destination_linkname != archive_binding.get("member_linkname"):
                        errors.append(
                            f"hydrated seed {destination} link target differs from its archive"
                        )
            elif archive_type in {"regular", "hardlink"}:
                if row["destination_type"] != "regular":
                    errors.append(
                        f"hydrated seed {destination} is not a regular extracted file"
                    )
                elif (
                    "windows" not in host
                    and row["destination_mode"] != row["archive_member_mode"]
                ):
                    errors.append(
                        f"hydrated seed {destination} mode differs from its archive member"
                    )
            if not row["executable"]:
                errors.append(f"hydrated seed {destination} is not executable")
            if name in {"trustc", "targo", "trustfmt"}:
                args = ("-Vv",) if name == "trustc" else ("--version",)
                ok, identity = _capture_identity(path, args)
                row["identity"] = identity
                row["identity_probe_ok"] = ok
                if not ok:
                    errors.append(f"hydrated seed {name} identity probe failed")
        else:
            errors.append(f"hydrated seed stage0 is missing required {destination}")
        if archive_binding is None:
            errors.append(f"pinned seed archive member is missing for {destination}")
        tools.append(row)

    rows = {str(row["name"]): row for row in tools}
    for owned, compatibility in (
        ("trustc", "rustc"),
        ("targo", "cargo"),
    ):
        if paths[owned].is_file() and paths[compatibility].is_file():
            if rows[owned].get("sha256") != rows[compatibility].get("sha256"):
                errors.append(f"hydrated seed {compatibility} alias differs from {owned}")
            rows[compatibility]["same_inode_as_owned"] = os.path.samefile(
                paths[owned], paths[compatibility]
            )

    forbidden_paths = [
        bin_dir / _stage0_bin_filename(name, host)
        for name in SEED_STAGE0_FORBIDDEN_BINS
    ] + [
        stage0 / "libexec" / _host_executable(name, host)
        for name in SEED_STAGE0_FORBIDDEN_LIBEXEC_BINS
    ]
    forbidden_present = sorted(
        _repository_relative_path(root, path)
        for path in forbidden_paths
        if os.path.lexists(path)
    )
    if forbidden_present:
        errors.append(
            "hydrated seed stage0 contains forbidden entrypoints: "
            + ", ".join(forbidden_present)
        )

    expected_identity_keys = {"trustc", "targo", "trustfmt"}
    if set(reported_product_identities) != expected_identity_keys:
        errors.append(
            "seed admission ledger does not declare the exact reported product identity set"
        )

    compiler_identity = str(rows.get("trustc", {}).get("identity", ""))
    compiler_commit = pins.get("compiler_git_commit_hash", "")
    if not compiler_commit or f"commit-hash: {compiler_commit}" not in compiler_identity:
        errors.append("hydrated seed trustc is not bound to compiler_git_commit_hash")
    compiler_first_line = compiler_identity.splitlines()[0] if compiler_identity else ""
    if compiler_first_line != reported_product_identities.get("trustc"):
        errors.append("hydrated seed trustc does not match its admitted product identity")
    targo_identity = str(rows.get("targo", {}).get("identity", ""))
    if targo_identity != reported_product_identities.get("targo"):
        errors.append("hydrated seed targo does not match its admitted product identity")
    trustfmt_identity = str(rows.get("trustfmt", {}).get("identity", ""))
    if trustfmt_identity != reported_product_identities.get("trustfmt"):
        errors.append("hydrated seed trustfmt does not match its admitted product identity")
    trustc = paths["trustc"]
    sysroot_matches = False
    if trustc.is_file():
        sysroot_ok, reported_sysroot = _capture_identity(trustc, ("--print", "sysroot"))
        try:
            sysroot_matches = sysroot_ok and Path(reported_sysroot).resolve() == stage0.resolve()
        except OSError:
            sysroot_matches = False
        if not sysroot_matches:
            errors.append("hydrated seed trustc reports a foreign sysroot")

    return {
        "schema": "trust.seed-compiler-identity.v1",
        "status": "validated" if not errors else "rejected",
        "stage0_root": _repository_relative_path(root, stage0),
        "stage0_root_present": stage0_root_present,
        "tools": tools,
        "reported_product_identities": dict(sorted(reported_product_identities.items())),
        "forbidden_paths_present": forbidden_present,
        "stage0_tree": stage0_tree,
        "paired_linker": paired_linker_binding,
        "reported_sysroot_matches": sysroot_matches,
        "errors": sorted(set(errors)),
    }


def seed_host_ledger_module():
    """Load the repository helper even under the mint launcher's isolated Python.

    Without a bytecode cache: the read-only `--verify-stage-provenance` reaches
    this load, and the import system would otherwise write
    scripts/__pycache__/seed_host_ledger.cpython-<XY>.pyc beside the helper on
    the first load after each edit of it. The explicit mint configuration
    context loads its own sibling helper with the same read-only discipline.
    """
    import importlib.util

    path = Path(__file__).resolve().with_name("seed_host_ledger.py")
    spec = importlib.util.spec_from_file_location("trust_seed_host_ledger", path)
    if spec is None or spec.loader is None:
        raise ValueError(f"cannot load seed host ledger helper: {path}")
    module = importlib.util.module_from_spec(spec)
    wrote_bytecode = not sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = not wrote_bytecode
    return module


@contextmanager
def _without_bytecode_cache():
    """The helper's own siblings, which it loads lazily (seed_fixed_point.py,
    seed_root_initialization.py, mint_seed_support.py), under the same discipline
    as the helper: no bytecode cache is written beside them, and the caller's
    setting is put back."""
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        yield
    finally:
        sys.dont_write_bytecode = previous


# seed_root_initialization.LINUX_HOSTS (recreate_bootstrap_test holds the two
# equal). The single-host ledger format (no [release.hosts]) carries no host
# record, so nothing in it can say which kind of evidence admitted the seed; it
# only ever admitted aarch64-apple-darwin (the one legacy admission,
# bootstrap/trust-linux-root-initialization.json). A Linux seed is admitted only
# through its own host record, where a fixed point is graded below every
# release (docs/PLAN.md PKG-S6), never through that format.
LINUX_SEED_HOSTS = frozenset({"aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"})


def capture_validated_seed_lineage(
    root: Path, host: str, *, build_root: Path | None = None, config_path: Path | None = None,
) -> dict[str, object]:
    """Bind seed pins, payload bytes, admission ledger, and hydrated compiler."""
    try:
        import tomllib
    except ModuleNotFoundError:
        tomllib = None

    root = root.resolve()
    errors: list[str] = []
    stage0_path = root / "src" / "stage0"
    ledger_path = root / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
    pins, payload_pins = parse_stage0_pins(root)
    required_pins = {
        "compiler_channel_manifest_hash",
        "compiler_git_commit_hash",
        "compiler_date",
        "compiler_version",
        "rustfmt_channel_manifest_hash",
        "rustfmt_git_commit_hash",
        "rustfmt_date",
        "rustfmt_version",
    }
    missing_pins = sorted(required_pins - set(pins))
    if missing_pins:
        errors.append(f"src/stage0 is missing seed pins: {', '.join(missing_pins)}")
    if not payload_pins:
        errors.append("src/stage0 declares no seed payloads")
    if pins.get("compiler_date") != pins.get("rustfmt_date"):
        errors.append("compiler and rustfmt seed dates disagree")
    if pins.get("compiler_channel_manifest_hash") != pins.get(
        "rustfmt_channel_manifest_hash"
    ):
        errors.append("compiler and rustfmt channel-manifest pins disagree")
    try:
        stage0_sha256 = _sha256_file(stage0_path)
    except OSError as error:
        errors.append(f"could not hash src/stage0: {error}")
        stage0_sha256 = None

    payloads: list[dict[str, object]] = []
    seed_root = root / "bootstrap" / "trust-stage0"
    for declared_path, pinned_sha256 in sorted(payload_pins.items()):
        relative = Path(declared_path)
        safe = (
            not relative.is_absolute()
            and ".." not in relative.parts
            and relative.parts[:1] == ("dist",)
        )
        if not safe:
            errors.append(f"unsafe seed payload path in src/stage0: {declared_path}")
            continue
        if len(pinned_sha256) != 64 or any(
            character not in "0123456789abcdef" for character in pinned_sha256
        ):
            errors.append(f"non-canonical seed payload SHA-256: {declared_path}")
        payload = seed_root / relative
        actual_sha256: str | None = None
        if not payload.is_file() or payload.is_symlink():
            errors.append(f"seed payload is missing or not a regular file: {declared_path}")
        else:
            try:
                actual_sha256 = _sha256_file(payload)
            except OSError as error:
                errors.append(f"could not hash seed payload {declared_path}: {error}")
        matches = actual_sha256 == pinned_sha256
        if not matches:
            errors.append(f"seed payload does not match src/stage0 pin: {declared_path}")
        payloads.append(
            {
                "path": _repository_relative_path(root, payload),
                "pinned_sha256": pinned_sha256,
                "actual_sha256": actual_sha256,
                "matches_pin": matches,
            }
        )

    manifest_date = pins.get("compiler_date", "")
    manifest_path = seed_root / "dist" / manifest_date / "channel-rust-trust.toml"
    manifest_sha256: str | None = None
    if not manifest_path.is_file() or manifest_path.is_symlink():
        errors.append("pinned Trust channel manifest is missing or not a regular file")
    else:
        try:
            manifest_sha256 = _sha256_file(manifest_path)
        except OSError as error:
            errors.append(f"could not hash pinned Trust channel manifest: {error}")
    for pin_name in (
        "compiler_channel_manifest_hash",
        "rustfmt_channel_manifest_hash",
    ):
        if manifest_sha256 != pins.get(pin_name):
            errors.append(f"Trust channel manifest does not match {pin_name}")

    freshness_script = root / "scripts" / "check_seed_freshness.py"
    freshness_record: dict[str, object] = {
        "script_path": _repository_relative_path(root, freshness_script),
    }
    try:
        freshness_record["script_sha256"] = _sha256_file(freshness_script)
        freshness = _run_seed_checker(
            [sys.executable, str(freshness_script), "--require-payloads"],
            cwd=str(root),
            capture_output=True,
            text=False,
            # The checker bounds its actual native probe and reaps its owner;
            # no outer kill timeout may cut that custody chain.
            # Reached by the read-only `--verify-stage-provenance`, which
            # `--check` on the same command line does not replace.
            env={**_no_bytecode_environment(), **(
                {"RUST_BOOTSTRAP_CONFIG": str(config_path)} if config_path is not None else {}
            )},
        )
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        errors.append(f"canonical seed freshness check could not run: {error}")
        freshness_record.update({"status": "rejected", "exit_code": None})
    else:
        freshness_record.update(
            {
                "status": "validated" if freshness.returncode == 0 else "rejected",
                "exit_code": freshness.returncode,
            }
        )
        if freshness.returncode != 0:
            errors.append("canonical seed freshness/required-component check failed")

    ledger_sha256: str | None = None
    ledger_document: dict[str, object] = {}
    if not ledger_path.is_file() or ledger_path.is_symlink():
        errors.append("seed admission ledger is missing or not a regular file")
    else:
        try:
            ledger_bytes = ledger_path.read_bytes()
            ledger_sha256 = hashlib.sha256(ledger_bytes).hexdigest()
        except OSError as error:
            errors.append(f"could not read seed admission ledger: {error}")
            ledger_bytes = b""
        if tomllib is None:
            errors.append("Python 3.11+ tomllib is required to validate seed admission")
        else:
            try:
                parsed_ledger = tomllib.loads(ledger_bytes.decode("utf-8"))
            except (UnicodeError, tomllib.TOMLDecodeError) as error:
                errors.append(f"seed admission ledger is not valid UTF-8 TOML: {error}")
            else:
                if isinstance(parsed_ledger, dict):
                    ledger_document = parsed_ledger
                else:
                    errors.append("seed admission ledger is not a TOML table")

    scope = ledger_document.get("scope")
    promotion_decision = ledger_document.get("promotion_decision")
    signatures = ledger_document.get("signatures")
    checksums = ledger_document.get("checksums")
    release = ledger_document.get("release")
    artifact_root = ledger_document.get("artifact_root")
    if not isinstance(signatures, list) or not all(isinstance(item, str) for item in signatures):
        errors.append("seed admission ledger signatures are malformed")
        signatures = []
    if not isinstance(checksums, list) or not all(isinstance(item, str) for item in checksums):
        errors.append("seed admission ledger checksums are malformed")
        checksums = []
    if not isinstance(release, dict):
        errors.append("seed admission ledger release table is missing")
        release = {}
    if not isinstance(artifact_root, dict):
        errors.append("seed admission ledger artifact_root table is missing")
        artifact_root = {}
    declared_checksums = set(checksums)
    for payload in payloads:
        if f"sha256:{payload['pinned_sha256']}" not in declared_checksums:
            errors.append(f"seed admission ledger omits payload {payload['path']}")
    ledger_pin_fields = {
        "date": "compiler_date",
        "compiler_version": "compiler_version",
        "compiler_git_commit_hash": "compiler_git_commit_hash",
        "channel_manifest_hash": "compiler_channel_manifest_hash",
    }
    for ledger_field, pin_field in ledger_pin_fields.items():
        if release.get(ledger_field) != pins.get(pin_field):
            errors.append(f"seed admission ledger {ledger_field} disagrees with src/stage0")
    host_record_authority = None
    selected_release = release
    if "hosts" in release:
        try:
            helper = seed_host_ledger_module()
            selected = helper.select_host_record(release, host)
            declared_hosts = release["hosts"]
            if set(declared_hosts) != set(helper.pinned_hosts({**pins, **payload_pins})):
                raise ValueError("seed admission host records do not cover the exact pinned cohort")
            records = {}
            metadata_sha256 = {}
            # A fixed-point record's evidence is judged by validators the helper
            # loads only now (seed_fixed_point.py and its siblings); a capture
            # writes no bytecode cache beside them, as for the helper itself.
            with _without_bytecode_cache():
                for name, record in sorted(declared_hosts.items()):
                    records[name], metadata_sha256[name] = helper.capture_host_record(
                        ledger_path.parent, {**pins, **payload_pins}, name, record
                    )
            selected_release = records[host]
            if len(records) == 1:
                for key in ("host_triple", "reported_product_identities", "mint"):
                    expected = host if key == "host_triple" else selected_release.get(key)
                    if key in release and release[key] != expected:
                        raise ValueError("single-host compatibility fields disagree with the host record")
            host_record_authority = {
                "helper_sha256": _sha256_file(Path(__file__).resolve().with_name("seed_host_ledger.py")),
                "selected_host": host, "records": records,
                "record_metadata_sha256": metadata_sha256,
            }
            if any(record.get("schema") == helper.FIXED_POINT_SCHEMA for record in records.values()):
                # scripts/seed_fixed_point.py judged that record's evidence in this
                # capture (seed_host_ledger.fixed_point_actual), so the authority
                # names its bytes beside the helper's. Only then: a ledger without
                # such a record keeps its authority, and its receipts, unchanged.
                host_record_authority["fixed_point_validator_sha256"] = _sha256_file(
                    Path(__file__).resolve().with_name("seed_fixed_point.py")
                )
            del selected
        except (OSError, UnicodeError, ValueError, TypeError) as error:
            errors.append(f"seed admission host mint record is invalid: {error}")
            selected_release = {}
    elif release.get("host_triple") != host:
        errors.append("seed admission ledger host_triple does not match the build host")
    elif host in LINUX_SEED_HOSTS:
        errors.append(
            f"seed admission ledger is in the single-host format (no [release.hosts]), which admits no "
            f"Linux host: {host}'s seed is admitted only through its own "
            f'[release.hosts."{host}"] host record (docs/PLAN.md PKG-S6)'
        )

    reported_product_identities = selected_release.get("reported_product_identities")
    if not isinstance(reported_product_identities, dict) or not all(
        isinstance(key, str) and isinstance(value, str) and value
        for key, value in (
            reported_product_identities.items()
            if isinstance(reported_product_identities, dict)
            else ()
        )
    ):
        errors.append("seed admission ledger reported product identities are malformed")
        reported_product_identities = {}
    else:
        reported_product_identities = dict(reported_product_identities)

    placeholder_signature = any(
        marker in signature.lower()
        for signature in signatures
        for marker in ("placeholder", "not-public", "internal-admission-only")
    )
    visibility = release.get("visibility")
    if (
        scope == "public"
        and promotion_decision == "promote"
        and visibility == "public"
        and signatures
        and not placeholder_signature
    ):
        admission_status = "rejected"
        errors.append(
            "public seed promotion lacks an implemented pinned-key cryptographic verifier"
        )
    elif scope == "internal" and promotion_decision == "admit-internal":
        admission_status = "internal-admitted"
    else:
        admission_status = "rejected"
        errors.append("seed admission ledger does not declare an accepted admission class")

    admission = {
        "scope": scope,
        "promotion_decision": promotion_decision,
        "signatures": signatures,
        "checksums": checksums,
        "release": dict(sorted(release.items())),
        "artifact_root": dict(sorted(artifact_root.items())),
        "status": admission_status,
    }
    authority = {
        "schema": "trust.seed-authority.v1",
        "src_stage0": {
            "path": _repository_relative_path(root, stage0_path),
            "sha256": stage0_sha256,
        },
        "pins": dict(sorted(pins.items())),
        "payloads": payloads,
        "channel_manifest": {
            "path": _repository_relative_path(root, manifest_path),
            "sha256": manifest_sha256,
            "compiler_pin": pins.get("compiler_channel_manifest_hash"),
            "rustfmt_pin": pins.get("rustfmt_channel_manifest_hash"),
        },
        "freshness_check": freshness_record,
        "seed_ledger": {
            "path": _repository_relative_path(root, ledger_path),
            "sha256": ledger_sha256,
            "admission": admission,
        },
    }
    if host_record_authority is not None:
        authority["seed_ledger"]["host_records"] = host_record_authority
    archive_members, archive_member_bindings = _capture_seed_archive_members(
        root, host, pins, payloads, errors
    )
    if host_record_authority is not None:
        try:
            helper.check_entrypoint_bindings(selected_release, archive_member_bindings)
        except (ValueError, TypeError) as error:
            errors.append(f"seed admission native host surface does not match archives: {error}")
        if selected_release.get("schema") == helper.FIXED_POINT_SCHEMA:
            # A fixed point has no DDC receipt naming the archives' members: every
            # member hashed above must be its receipt's compiler_file row
            # (seed_host_ledger.check_fixed_point_member_bindings; design E).
            try:
                with _without_bytecode_cache():
                    helper.check_fixed_point_member_bindings(
                        ledger_path.parent, host, selected_release, archive_member_bindings
                    )
            except (OSError, UnicodeError, ValueError, TypeError) as error:
                errors.append(
                    f"seed admission fixed-point receipt does not bind the pinned archive members: {error}"
                )
    authority["archive_members"] = archive_members
    authority_sha256 = hashlib.sha256(
        json.dumps(authority, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    compiler = _capture_seed_compiler_identity(
        root,
        host,
        pins,
        archive_member_bindings,
        reported_product_identities,
        **({"build_root": build_root} if build_root is not None else {}),
    )
    errors.extend(str(error) for error in compiler.get("errors", []))
    if errors:
        status = "rejected"
    elif compiler.get("status") == "validated":
        status = "validated"
    else:
        status = "validated-payloads"
    return {
        "schema": "trust.validated-seed-lineage.v1",
        "status": status,
        "admission_status": admission_status,
        "authority_sha256": authority_sha256,
        "authority": authority,
        "compiler": compiler,
        "errors": sorted(set(errors)),
    }


def _parse_verbose_identity(identity: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for line in identity.splitlines():
        key, separator, value = line.partition(": ")
        if separator and key not in fields:
            fields[key] = value
    return fields


def _load_genesis_adapter_generator(root: Path) -> object:
    script = root / "scripts" / "create_local_genesis_stage0.py"
    source = script.read_text(encoding="utf-8")
    namespace: dict[str, object] = {
        "__file__": str(script),
        "__name__": "trust_genesis_adapter_generator",
    }
    exec(compile(source, str(script), "exec"), namespace)
    return SimpleNamespace(**namespace)


def _capture_genesis_adapter_authority(
    root: Path,
    host: str,
    build_table: dict[str, object],
) -> dict[str, object]:
    """Bind the complete local-genesis adapter and its external producer root."""
    errors: list[str] = []
    adapter = root / "build" / host / "genesis-stage0"
    bin_dir = adapter / "bin"
    libexec_dir = adapter / "libexec"
    manifest_path = adapter / "trust-local-genesis-stage0.json"
    expected_config_paths = {
        "rustc": adapter / "bin" / _host_executable("trustc", host),
        "cargo": adapter / "bin" / _host_executable("cargo", host),
        "rustdoc": adapter / "bin" / _host_executable("trustdoc", host),
        "rustfmt": adapter / "bin" / _host_executable("trustfmt", host),
        "cargo-clippy": adapter / "bin" / _host_executable("targo-tippy", host),
    }
    config_bindings: dict[str, object] = {}
    for key, expected_path in expected_config_paths.items():
        value = build_table.get(key)
        config_bindings[key] = value
        if value != str(expected_path):
            errors.append(f"genesis bootstrap config {key} does not name the exact adapter")
    if set(key for key in build_table if key in expected_config_paths) != set(
        expected_config_paths
    ):
        errors.append("genesis bootstrap config does not declare the exact stage0 key set")
    if "windows" in host:
        errors.append("Windows genesis adapter authority requires the native Windows schema")

    expected_root_names = {
        "bin",
        "lib",
        "libexec",
        ".trustc-stamp",
        ".rustc-stamp",
        "trust-local-genesis-stage0.json",
    }
    expected_bin_names = {
        _host_executable(name, host) for name in SEED_STAGE0_REQUIRED_BINS
    }
    expected_libexec_names = {
        _host_executable(name, host) for name in SEED_STAGE0_REQUIRED_LIBEXEC_BINS
    }
    surface_rows: list[dict[str, object]] = []
    if adapter.is_symlink() or not adapter.is_dir():
        errors.append("genesis adapter root is not a real directory")
        root_names: set[str] = set()
    else:
        root_names = {path.name for path in adapter.iterdir()}
    if root_names != expected_root_names:
        errors.append("genesis adapter root inventory is not closed")
    for directory, expected_names in (
        (bin_dir, expected_bin_names),
        (libexec_dir, expected_libexec_names),
    ):
        if directory.is_symlink() or not directory.is_dir():
            errors.append(f"genesis adapter directory is missing or symlinked: {directory.name}")
            actual_names: set[str] = set()
        else:
            actual_names = {path.name for path in directory.iterdir()}
        if actual_names != expected_names:
            errors.append(f"genesis adapter {directory.name} inventory is not closed")
        for name in sorted(expected_names):
            path = directory / name
            row: dict[str, object] = {
                "path": _repository_lexical_relative_path(root, path),
            }
            if not os.path.lexists(path):
                errors.append(f"genesis adapter entry is missing: {path}")
                row["type"] = "missing"
            else:
                metadata = path.lstat()
                row.update(
                    {
                        "type": "regular" if stat.S_ISREG(metadata.st_mode) else "invalid",
                        "mode": stat.S_IMODE(metadata.st_mode),
                        "nlink": metadata.st_nlink,
                        "executable": os.access(path, os.X_OK),
                    }
                )
                if not stat.S_ISREG(metadata.st_mode) or path.is_symlink():
                    errors.append(f"genesis adapter entry is not an independent regular file: {path}")
                else:
                    try:
                        row["sha256"] = _sha256_file(path)
                    except OSError as error:
                        errors.append(f"could not hash genesis adapter entry {path}: {error}")
                if metadata.st_nlink != 1:
                    errors.append(f"genesis adapter entry is hard-linked: {path}")
                if stat.S_IMODE(metadata.st_mode) != 0o755 or not os.access(path, os.X_OK):
                    errors.append(f"genesis adapter entry is not executable mode 0755: {path}")
            surface_rows.append(row)

    for name in (".trustc-stamp", ".rustc-stamp", "trust-local-genesis-stage0.json"):
        path = adapter / name
        row = {"path": _repository_lexical_relative_path(root, path)}
        if not path.is_file() or path.is_symlink():
            errors.append(f"genesis adapter metadata is not a regular file: {path}")
            row["type"] = "missing-or-invalid"
        else:
            metadata = path.lstat()
            row.update(
                {
                    "type": "regular",
                    "mode": stat.S_IMODE(metadata.st_mode),
                    "nlink": metadata.st_nlink,
                    "size": metadata.st_size,
                    "sha256": _sha256_file(path),
                }
            )
            if metadata.st_nlink != 1:
                errors.append(f"genesis adapter metadata is hard-linked: {path}")
        surface_rows.append(row)

    lib_link = adapter / "lib"
    lib_link_target: str | None = None
    lib_real: Path | None = None
    lib_row: dict[str, object] = {
        "path": _repository_lexical_relative_path(root, lib_link)
    }
    if not lib_link.is_symlink():
        errors.append("genesis adapter lib is not the designated sysroot symlink")
        lib_row["type"] = "missing-or-invalid"
    else:
        try:
            lib_link_target = os.readlink(lib_link)
            lib_real = lib_link.resolve(strict=True)
        except OSError as error:
            errors.append(f"genesis adapter lib link is unreadable: {error}")
        lib_row.update(
            {
                "type": "symlink",
                "link_target": lib_link_target,
                "resolved_local_path": str(lib_real) if lib_real is not None else None,
            }
        )
    surface_rows.append(lib_row)
    surface = {
        "schema": "trust.genesis-adapter-surface.v1",
        "entries": sorted(surface_rows, key=lambda row: str(row["path"])),
    }
    surface["closure_sha256"] = hashlib.sha256(
        json.dumps(surface, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()

    pins, payloads = parse_stage0_pins(root)
    expected_stamp = stage0_extraction_stamp({**pins, **payloads})
    stamp_values: dict[str, str | None] = {}
    for name in (".trustc-stamp", ".rustc-stamp"):
        path = adapter / name
        try:
            value = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            errors.append(f"could not read genesis adapter stamp {name}: {error}")
            value = None
        stamp_values[name] = value
        if value != expected_stamp:
            errors.append(f"genesis adapter {name} does not equal the pinned extraction identity")

    manifest: dict[str, object] = {}
    manifest_sha256: str | None = None
    if manifest_path.is_file() and not manifest_path.is_symlink():
        try:
            manifest_bytes = manifest_path.read_bytes()
            manifest_sha256 = hashlib.sha256(manifest_bytes).hexdigest()
            parsed_manifest = json.loads(manifest_bytes.decode("utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            errors.append(f"could not parse genesis adapter manifest: {error}")
        else:
            if isinstance(parsed_manifest, dict):
                manifest = parsed_manifest
            else:
                errors.append("genesis adapter manifest is not a JSON object")
    manifest_identity = {
        "schema": manifest.get("schema"),
        "admission": manifest.get("admission"),
        "public_upload": manifest.get("public_upload"),
        "counts_as_trust_stage0_evidence": manifest.get(
            "counts_as_trust_stage0_evidence"
        ),
        "repo_root": manifest.get("repo_root"),
        "stage0_root": manifest.get("stage0_root"),
        "host": manifest.get("host"),
        "stamp": manifest.get("stamp"),
        "compiler_version_target": manifest.get("compiler_version_target"),
    }
    expected_manifest_identity = {
        "schema": "trust.local-genesis-stage0-adapter.v1",
        "admission": "local-genesis-only",
        "public_upload": False,
        "counts_as_trust_stage0_evidence": False,
        "repo_root": str(root),
        "stage0_root": str(adapter),
        "host": host,
        "stamp": expected_stamp,
        "compiler_version_target": pins.get("compiler_version"),
    }
    if manifest_identity != expected_manifest_identity:
        errors.append("genesis adapter manifest identity fields are not canonical")
    expected_generated_bins = {
        name: str(bin_dir / _host_executable(name, host))
        for name in SEED_STAGE0_REQUIRED_BINS
    }
    expected_generated_libexec = {
        name: str(libexec_dir / _host_executable(name, host))
        for name in SEED_STAGE0_REQUIRED_LIBEXEC_BINS
    }
    if manifest.get("generated_bins") != expected_generated_bins:
        errors.append("genesis adapter manifest generated_bins is not exact")
    if manifest.get("generated_libexec_bins") != expected_generated_libexec:
        errors.append("genesis adapter manifest generated_libexec_bins is not exact")

    source_values = manifest.get("wrapper_sources")
    if not isinstance(source_values, dict):
        errors.append("genesis adapter manifest wrapper_sources is missing")
        source_values = {}
    expected_source_keys = (
        set(GENESIS_WRAPPER_SOURCES)
        | set(GENESIS_STUB_BINS)
        | set(GENESIS_STUB_LIBEXEC_BINS)
    )
    if set(source_values) != expected_source_keys:
        errors.append("genesis adapter wrapper_sources key set is not exact")
    for name in (*GENESIS_STUB_BINS, *GENESIS_STUB_LIBEXEC_BINS):
        if source_values.get(name) is not None:
            errors.append(f"genesis adapter always-stub {name} unexpectedly names a producer")

    root_manifest_path = root / "bootstrap" / "trust-genesis-roots.json"
    root_manifest: dict[str, object] = {}
    root_manifest_sha256: str | None = None
    if not root_manifest_path.is_file() or root_manifest_path.is_symlink():
        errors.append("genesis root-pin manifest is missing, non-regular, or symlinked")
    else:
        try:
            root_manifest_bytes = root_manifest_path.read_bytes()
            root_manifest_sha256 = hashlib.sha256(root_manifest_bytes).hexdigest()
            parsed_root_manifest = json.loads(root_manifest_bytes.decode("utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            errors.append(f"could not parse genesis root-pin manifest: {error}")
        else:
            if isinstance(parsed_root_manifest, dict):
                root_manifest = parsed_root_manifest
            else:
                errors.append("genesis root-pin manifest is not a JSON object")
    if (
        root_manifest.get("schema") != "trust.genesis-roots.v1"
        or root_manifest.get("admission") != "external-bootstrap-root-only"
        or root_manifest.get("counts_as_trust_stage0_evidence") is not False
    ):
        errors.append("genesis root-pin manifest admission is not canonical")
    channel_manifest = root_manifest.get("channel_manifest")
    roots = root_manifest.get("roots")
    selected_pin = roots.get(host) if isinstance(roots, dict) else None
    if not isinstance(channel_manifest, dict) or not isinstance(selected_pin, dict):
        errors.append("genesis root-pin manifest lacks channel or selected host authority")
        channel_manifest = {}
        selected_pin = {}
    if selected_pin.get("host") != host:
        errors.append("genesis selected host pin does not match the build host")
    if selected_pin.get("rustup_toolchain") != f"nightly-{channel_manifest.get('date')}":
        errors.append("genesis root pin does not match its channel date")

    rustc_value = source_values.get("trustc")
    rustc_path = Path(rustc_value) if isinstance(rustc_value, str) else None
    rustc_identity = ""
    rustc_fields: dict[str, str] = {}
    rustc_sha256: str | None = None
    sysroot_selected: Path | None = None
    sysroot_real: Path | None = None
    if rustc_path is None or not rustc_path.is_absolute() or not rustc_path.is_file():
        errors.append("genesis adapter does not name a usable direct backing rustc")
    else:
        try:
            rustc_path = rustc_path.resolve(strict=True)
            rustc_sha256 = _sha256_file(rustc_path)
        except OSError as error:
            errors.append(f"could not bind backing rustc: {error}")
        identity_ok, rustc_identity = _capture_identity(rustc_path, ("-Vv",))
        if not identity_ok:
            errors.append("backing genesis rustc rejected -Vv")
        rustc_fields = _parse_verbose_identity(rustc_identity)
        sysroot_ok, sysroot_value = _capture_identity(
            rustc_path, ("--print", "sysroot")
        )
        if not sysroot_ok:
            errors.append("backing genesis rustc rejected --print sysroot")
        else:
            sysroot_selected = Path(sysroot_value)
            try:
                sysroot_real = sysroot_selected.resolve(strict=True)
            except OSError as error:
                errors.append(f"could not resolve backing rustc sysroot: {error}")
    pin_identity = {
        "binary": "rustc",
        "release": selected_pin.get("release"),
        "commit-hash": selected_pin.get("commit_hash"),
        "commit-date": selected_pin.get("commit_date"),
        "host": selected_pin.get("host"),
    }
    if any(rustc_fields.get(field) != value for field, value in pin_identity.items()):
        errors.append("backing rustc identity does not match the selected genesis root pin")

    producers: list[dict[str, object]] = []
    producer_by_program: dict[str, dict[str, object]] = {}
    if sysroot_real is not None:
        for wrapper_name, program in GENESIS_WRAPPER_SOURCES.items():
            declared = source_values.get(wrapper_name)
            expected_candidate = sysroot_real / "bin" / _host_executable(program, host)
            expected_real: Path | None = None
            if expected_candidate.is_file():
                try:
                    expected_real = expected_candidate.resolve(strict=True)
                except OSError as error:
                    errors.append(f"could not resolve backing genesis {program}: {error}")
            if declared is None:
                if wrapper_name in {"trustc", "rustc", "trustdoc", "targo", "cargo"}:
                    errors.append(f"core genesis wrapper {wrapper_name} has no producer")
                if expected_real is not None:
                    errors.append(
                        f"genesis wrapper {wrapper_name} is stubbed despite an installed producer"
                    )
                continue
            if not isinstance(declared, str) or expected_real is None or declared != str(
                expected_real
            ):
                errors.append(
                    f"genesis wrapper {wrapper_name} does not name canonical sysroot {program}"
                )
                continue
            producer = producer_by_program.get(program)
            if producer is None:
                metadata = expected_real.lstat()
                producer = {
                    "name": program,
                    "path_scope": "local-diagnostic",
                    "selected_local_path": declared,
                    "resolved_real_path": str(expected_real),
                    "mode": stat.S_IMODE(metadata.st_mode),
                    "nlink": metadata.st_nlink,
                    "executable": os.access(expected_real, os.X_OK),
                    "referenced_by": [],
                }
                if not stat.S_ISREG(metadata.st_mode) or not os.access(expected_real, os.X_OK):
                    errors.append(f"backing genesis producer is not regular/executable: {program}")
                try:
                    before_sha256 = _sha256_file(expected_real)
                except OSError as error:
                    errors.append(f"could not hash backing genesis producer {program}: {error}")
                    before_sha256 = None
                args = ("-Vv",) if program in {"rustc", "rustdoc", "cargo"} else ("--version",)
                identity_ok, identity = _capture_identity(expected_real, args)
                try:
                    after_sha256 = _sha256_file(expected_real)
                except OSError as error:
                    errors.append(f"could not rehash backing genesis producer {program}: {error}")
                    after_sha256 = None
                producer.update(
                    {
                        "sha256": after_sha256,
                        "stable_during_probe": before_sha256 == after_sha256,
                        "identity_probe_ok": identity_ok,
                        "identity": identity,
                        "identity_fields": _parse_verbose_identity(identity),
                    }
                )
                if before_sha256 != after_sha256:
                    errors.append(f"backing genesis producer changed during capture: {program}")
                if not identity_ok:
                    errors.append(f"backing genesis producer identity probe failed: {program}")
                producer_by_program[program] = producer
                producers.append(producer)
            referenced_by = producer["referenced_by"]
            if isinstance(referenced_by, list):
                referenced_by.append(wrapper_name)
    producers.sort(key=lambda row: str(row["name"]))
    for producer in producers:
        referenced_by = producer.get("referenced_by")
        if isinstance(referenced_by, list):
            referenced_by.sort()
    producer_rows = {str(row["name"]): row for row in producers}
    rustdoc_fields = producer_rows.get("rustdoc", {}).get("identity_fields", {})
    if isinstance(rustdoc_fields, dict):
        expected_rustdoc = {**pin_identity, "binary": "rustdoc"}
        if any(rustdoc_fields.get(field) != value for field, value in expected_rustdoc.items()):
            errors.append("backing rustdoc identity does not match the genesis compiler root")
    cargo_fields = producer_rows.get("cargo", {}).get("identity_fields", {})
    if isinstance(cargo_fields, dict):
        for field in ("release", "host"):
            if cargo_fields.get(field) != rustc_fields.get(field):
                errors.append(f"backing cargo {field} differs from backing rustc")

    if sysroot_real is not None:
        expected_lib_real = (sysroot_real / "lib").resolve()
        if lib_real != expected_lib_real:
            errors.append("genesis adapter lib link does not resolve to backing sysroot/lib")
        lib_tree = _capture_external_tree(expected_lib_real, sysroot_real)
        errors.extend(str(error) for error in lib_tree.get("errors", []))
    else:
        expected_lib_real = None
        lib_tree = {
            "schema": "trust.external-producer-tree.v1",
            "status": "rejected",
            "entries": [],
            "closure_sha256": None,
            "errors": ["backing sysroot is unavailable"],
        }
        errors.extend(str(error) for error in lib_tree["errors"])

    if rustc_path is not None and rustc_sha256 is not None:
        reconstructed_genesis_root = {
            "manifest": "bootstrap/trust-genesis-roots.json",
            "channel_manifest": channel_manifest,
            "pin": selected_pin,
            "observed": rustc_fields,
            "rustc_path": str(rustc_path),
            "rustc_sha256": rustc_sha256,
        }
        if manifest.get("genesis_root") != reconstructed_genesis_root:
            errors.append("genesis adapter manifest root evidence differs from current authority")
    source_tools = manifest.get("source_tools")
    if not isinstance(source_tools, dict):
        errors.append("genesis adapter manifest source_tools is missing")
        source_tools = {}
    rustc_version_ok, rustc_version = (
        _capture_identity(rustc_path, ("--version",))
        if rustc_path is not None and rustc_path.is_file()
        else (False, "")
    )
    cargo_path_value = source_values.get("targo")
    cargo_path = Path(cargo_path_value) if isinstance(cargo_path_value, str) else None
    cargo_version_ok, cargo_version = (
        _capture_identity(cargo_path, ("--version",))
        if cargo_path is not None and cargo_path.is_file()
        else (False, "")
    )
    expected_source_tools = {
        "rustc": str(rustc_path) if rustc_path is not None else None,
        "rustc_version": rustc_version.splitlines()[0] if rustc_version_ok else None,
        "rustc_sysroot": str(sysroot_real) if sysroot_real is not None else None,
        "cargo": str(cargo_path) if cargo_path is not None else None,
        "cargo_version": cargo_version.splitlines()[0] if cargo_version_ok else None,
    }
    if source_tools != expected_source_tools:
        errors.append("genesis adapter manifest source_tools differs from current producers")

    try:
        generator = _load_genesis_adapter_generator(root)
    except (ImportError, OSError) as error:
        errors.append(f"could not load genesis adapter generator for byte validation: {error}")
        generator = None
    if generator is not None:
        if (
            tuple(generator.REQUIRED_BINS) != SEED_STAGE0_REQUIRED_BINS
            or tuple(generator.REQUIRED_LIBEXEC_BINS) != SEED_STAGE0_REQUIRED_LIBEXEC_BINS
            or set(generator.FORBIDDEN_BINS) != set(SEED_STAGE0_FORBIDDEN_BINS)
            or set(generator.FORBIDDEN_LIBEXEC_BINS)
            != set(SEED_STAGE0_FORBIDDEN_LIBEXEC_BINS)
        ):
            errors.append("genesis generator and provenance surface contracts disagree")
        for trust_name, (source_program, source_name) in generator.WRAPPER_SOURCES.items():
            real = source_values.get(trust_name)
            if real is None:
                expected_text = generator.stub_script(
                    name=trust_name,
                    message=f"{source_program} was not found in PATH",
                )
            elif isinstance(real, str):
                expected_text = generator.wrapper_script(
                    real=real,
                    source_name=source_name,
                    trust_name=trust_name,
                    argument_prefix=generator.WRAPPER_ARG_PREFIXES.get(trust_name),
                    argument_marker=generator.WRAPPER_ARG_MARKERS.get(trust_name),
                    version_name=generator.TIPPY_VERSION_NAMES.get(trust_name),
                    version_argument_prefix=generator.TIPPY_VERSION_ARG_PREFIXES.get(
                        trust_name
                    ),
                    argument_rename=generator.WRAPPER_ARG_RENAMES.get(trust_name),
                )
            else:
                errors.append(f"genesis wrapper source is malformed: {trust_name}")
                continue
            wrapper = bin_dir / _host_executable(trust_name, host)
            try:
                actual_bytes = wrapper.read_bytes()
            except OSError as error:
                errors.append(f"could not read genesis wrapper {trust_name}: {error}")
            else:
                if actual_bytes != expected_text.encode("utf-8"):
                    errors.append(f"genesis wrapper bytes do not match generator: {trust_name}")
        for name, message in generator.STUB_BINS.items():
            expected_text = generator.stub_script(name=name, message=message)
            path = bin_dir / _host_executable(name, host)
            if path.is_file() and path.read_bytes() != expected_text.encode("utf-8"):
                errors.append(f"genesis stub bytes do not match generator: {name}")
        for name, message in generator.STUB_LIBEXEC_BINS.items():
            expected_text = generator.stub_script(name=name, message=message)
            path = libexec_dir / _host_executable(name, host)
            if path.is_file() and path.read_bytes() != expected_text.encode("utf-8"):
                errors.append(f"genesis libexec stub bytes do not match generator: {name}")

    authority = {
        "schema": "trust.genesis-adapter-authority.v1",
        "admission": "local-genesis-only",
        "counts_as_trust_stage0_evidence": False,
        "host": host,
        "adapter_root": _repository_lexical_relative_path(root, adapter),
        "config_bindings": dict(sorted(config_bindings.items())),
        "root_pin": {
            "manifest_path": _repository_relative_path(root, root_manifest_path),
            "manifest_sha256": root_manifest_sha256,
            "channel_manifest": channel_manifest,
            "selected_host_pin": selected_pin,
        },
        "adapter_manifest": {
            "path": _repository_lexical_relative_path(root, manifest_path),
            "sha256": manifest_sha256,
            "identity": manifest_identity,
        },
        "stamps": stamp_values,
        "surface": surface,
        "backing_sysroot": {
            "path_scope": "local-diagnostic",
            "selected_local_path": str(sysroot_selected) if sysroot_selected else None,
            "resolved_real_path": str(sysroot_real) if sysroot_real else None,
            "lib_link_target": lib_link_target,
            "lib_resolved_local_path": (
                str(expected_lib_real) if expected_lib_real is not None else None
            ),
            "lib_tree": lib_tree,
        },
        "producers": producers,
    }
    authority_sha256 = hashlib.sha256(
        json.dumps(authority, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return {
        "schema": "trust.genesis-adapter-authority.v1",
        "status": "ready" if not errors else "rejected",
        "authority_sha256": authority_sha256,
        "authority": authority,
        "errors": sorted(set(errors)),
    }


def _nixos_host() -> bool:
    try:
        os_release = Path("/etc/os-release").read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        return False
    return any(
        line.strip() in {"ID=nixos", "ID='nixos'", 'ID="nixos"'}
        for line in os_release.splitlines()
    )


def _validated_mint_configuration(
    root: Path, host: str | None, config: Path, expected: dict[str, object],
) -> dict[str, object]:
    """Re-evaluate the mint owner's explicit context; defaults never infer it.

    Load the same configuration/closure owner under isolated Python, without
    leaving bytecode during a read-only receipt verification.
    """
    import importlib.util

    if not isinstance(expected, dict):
        raise ValueError("mint configuration context is not an object")
    if host is None:
        raise ValueError("host triple is required for a mint configuration context")
    path = Path(__file__).resolve().with_name("mint_seed_support.py")
    spec = importlib.util.spec_from_file_location("trust_mint_configuration", path)
    if spec is None or spec.loader is None:
        raise ValueError(f"cannot load mint configuration owner: {path}")
    module = importlib.util.module_from_spec(spec)
    wrote_bytecode = not sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = not wrote_bytecode
    overrides = expected.get("xpy_config_overrides", {})
    if not isinstance(overrides, dict):
        raise ValueError("mint x.py configuration overrides are not an object")
    lean = expected.get("clean_lean_inputs")
    lean_options = {}
    if lean is not None:
        if not isinstance(lean, dict) or not isinstance(lean.get("library_path"), str):
            raise ValueError("mint Clean Lean input context is malformed")
        lean_options["clean_lean_lib"] = Path(lean["library_path"])
    current = module.mint_configuration_context(root, config, host, jobs=overrides.get("build.jobs"),
                                                **lean_options)
    if (json.dumps(current, sort_keys=True, separators=(",", ":"), allow_nan=False)
            != json.dumps(expected, sort_keys=True, separators=(",", ":"), allow_nan=False)):
        raise ValueError("mint configuration context differs from its current effective configuration/closure")
    return current


def _python_root_config_disables_seed_patching(root: Path, content: bytes) -> bool:
    """Ask the actual pre-Rust reader; includes/TOML comments are not guessed."""
    import importlib.util

    path = root / "src/bootstrap/bootstrap.py"
    spec = importlib.util.spec_from_file_location("trust_python_seed_config", path)
    if spec is None or spec.loader is None:
        return False
    module = importlib.util.module_from_spec(spec)
    wrote_bytecode = not sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec.loader.exec_module(module)
        return module.RustBuild.get_toml_static(
            content.decode("utf-8"), "patch-binaries-for-nix", "build",
        ) == "false"
    except Exception:  # A missing/unreadable owner supplies no authority to skip patching.
        return False
    finally:
        sys.dont_write_bytecode = not wrote_bytecode


def capture_bootstrap_lineage(
    root: Path, host: str | None = None, *, config_path: Path | None = None,
    build_root: Path | None = None,
    mint_configuration: dict[str, object] | None = None,
) -> dict[str, object]:
    """Record the bootstrap config without embedding host-local paths.

    Defaults classify the recreator's declared mode. The mint alone supplies
    its validated effective configuration/closure, re-evaluated here; its
    config_sha256 covers that whole context and config_file_sha256 the root file.
    """
    try:
        import tomllib
    except ModuleNotFoundError:
        tomllib = None

    if config_path is None:
        candidates = [
            path for path in (root / "bootstrap.toml", root / "config.toml") if path.is_file()
        ]
    else:
        candidates = [config_path] if config_path.is_file() else []
    errors: list[str] = []
    if len(candidates) != 1:
        errors.append("expected exactly one bootstrap.toml or config.toml")
        return {
            "schema": "trust.bootstrap-lineage.v1",
            "status": "rejected",
            "mode": "unknown",
            "trust_from_trust": False,
            "config_path": None,
            "config_sha256": None,
            "declared_stage0_overrides": [],
            "validated_seed": None,
            "genesis_adapter": None,
            "atpkg_authority": None,
            "errors": errors,
        }
    config = candidates[0]
    try:
        content = config.read_bytes()
    except OSError as error:
        errors.append(f"could not read bootstrap config: {error}")
        content = b""
    if tomllib is None:
        errors.append("Python 3.11+ tomllib is required to classify bootstrap lineage")
        parsed = {}
    else:
        try:
            parsed = tomllib.loads(content.decode("utf-8"))
        except (UnicodeError, tomllib.TOMLDecodeError) as error:
            errors.append(f"bootstrap config is not valid UTF-8 TOML: {error}")
            parsed = {}
    build_table = parsed.get("build", {})
    if not isinstance(build_table, dict):
        errors.append("bootstrap config [build] value is not a table")
        build_table = {}
    mint_context = None
    if mint_configuration is not None:
        try:
            mint_context = _validated_mint_configuration(root, host, config, mint_configuration)
            build_table = mint_context["effective_build"]
        except (OSError, RuntimeError, ValueError) as error:
            errors.append(f"mint bootstrap configuration was rejected: {error}")
    declared_stage0_overrides = sorted(STAGE0_OVERRIDE_KEYS & set(build_table))
    if mint_configuration is None:
        mode = _declared_bootstrap_mode(content, build_table)
    else:
        mode = "seed" if mint_context is not None else "unknown"
    validated_seed: dict[str, object] | None = None
    genesis_adapter: dict[str, object] | None = None
    atpkg_authority: dict[str, object] | None = None
    if mode == "seed":
        if host is None:
            errors.append("host triple is required to validate seed lineage")
            status = "rejected"
        else:
            validated_seed = capture_validated_seed_lineage(root, host, **{
                **({"build_root": build_root} if build_root is not None else {}),
                **({"config_path": config_path} if config_path is not None else {}),
            })
            errors.extend(str(error) for error in validated_seed.get("errors", []))
            nix_patch_setting = build_table.get("patch-binaries-for-nix")
            if mint_context is not None and _nixos_host() and not _python_root_config_disables_seed_patching(root, content):
                # Python extracts stage0 before Rust merges recursive includes.
                # Fail closed even if the Rust-effective value is false: only
                # an explicit root setting is known to disable that rewriting.
                errors.append(
                    "mint seed provenance on NixOS requires explicit root-config "
                    "build.patch-binaries-for-nix = false; Python stage0 does not merge includes"
                )
            if nix_patch_setting is True or (
                nix_patch_setting is None and _nixos_host()
            ):
                errors.append(
                    "immutable seed release provenance does not model bootstrap's "
                    "Nix patchelf transformation"
                )
            if validated_seed.get("status") == "validated":
                status = "trust_from_trust"
            elif validated_seed.get("status") == "validated-payloads":
                status = "seed-validated-pending-hydration"
            else:
                status = "rejected"
    elif mode == "atpkg":
        # Offline local-status integrity is candidate evidence, not signature replay.
        atpkg_authority = _capture_atpkg_stage0_authority(build_table)
        errors.extend(str(error) for error in atpkg_authority.get("errors", []))
        status = "local_atpkg" if _atpkg_authority_ready(atpkg_authority) else "rejected"
        if status == "rejected" and not errors:
            errors.append("atpkg authority is not canonical local candidate evidence")
    elif mode == "genesis":
        if host is None:
            errors.append("host triple is required to validate genesis authority")
            status = "rejected"
        else:
            genesis_adapter = _capture_genesis_adapter_authority(root, host, build_table)
            errors.extend(str(error) for error in genesis_adapter.get("errors", []))
            status = (
                "local_genesis"
                if genesis_adapter.get("status") == "ready"
                else "rejected"
            )
    else:
        mode = "unknown"
        status = "rejected"
        errors.append("bootstrap config does not unambiguously declare seed, atpkg, or genesis mode")
    return {
        "schema": "trust.bootstrap-lineage.v1",
        "status": status if not errors else "rejected",
        "mode": mode,
        "trust_from_trust": status in {"trust_from_trust", "local_atpkg"} and not errors,
        "config_path": _repository_relative_path(root, config),
        # For a mint this digest binds includes, profile and fixed CLI settings;
        # LLVM's build record must bind that whole configuration, not one file.
        "config_sha256": (
            mint_context["fingerprint"] if mint_context is not None
            else hashlib.sha256(content).hexdigest()
        ),
        **({
            "config_file_sha256": hashlib.sha256(content).hexdigest(),
            "mint_configuration": mint_context,
        } if mint_context is not None else {}),
        "declared_stage0_overrides": declared_stage0_overrides,
        "validated_seed": validated_seed,
        "genesis_adapter": genesis_adapter,
        "atpkg_authority": atpkg_authority,
        "errors": sorted(set(errors)),
    }


def _bind_bootstrap_lineage(
    before: dict[str, object] | None,
    after: dict[str, object],
) -> dict[str, object]:
    lineage = dict(after)
    errors = [str(error) for error in after.get("errors", [])]
    config_stable = before is not None and all(
        before.get(field) == after.get(field)
        for field in (
            "schema",
            "mode",
            "config_path",
            "config_sha256",
            "declared_stage0_overrides",
            "config_file_sha256",
            "mint_configuration",
        )
    )
    if before is not None and (
        json.dumps(before.get("mint_configuration"), sort_keys=True, allow_nan=False)
        != json.dumps(after.get("mint_configuration"), sort_keys=True, allow_nan=False)
    ):
        config_stable = False
    if before is None:
        errors.append("missing pre-build bootstrap-lineage snapshot")
    else:
        errors.extend(str(error) for error in before.get("errors", []))
        if before.get("status") == "rejected":
            errors.append("pre-build bootstrap lineage was rejected")
        if not config_stable:
            errors.append("bootstrap configuration changed during the build")
    stable = config_stable
    mode = after.get("mode")
    if before is not None and before.get("mode") != mode:
        errors.append("bootstrap mode changed during the build")
    if mode != "atpkg" and (
        after.get("atpkg_authority") is not None
        or (before is not None and before.get("atpkg_authority") is not None)
    ):
        errors.append("non-atpkg bootstrap unexpectedly carries atpkg authority")
    if mode == "seed":
        if before is not None and (
            before.get("genesis_adapter") is not None
            or after.get("genesis_adapter") is not None
        ):
            errors.append("seed bootstrap unexpectedly carries genesis adapter authority")
        before_seed = before.get("validated_seed") if before is not None else None
        after_seed = after.get("validated_seed")
        if not isinstance(before_seed, dict) or not isinstance(after_seed, dict):
            errors.append("validated seed lineage is missing")
            stable = False
        else:
            before_errors = before_seed.get("errors")
            after_errors = after_seed.get("errors")
            if before_errors != [] or after_errors != []:
                errors.append("validated seed lineage contains errors")
            before_authority = before_seed.get("authority_sha256")
            after_authority = after_seed.get("authority_sha256")
            authority_stable = before_authority == after_authority
            if not authority_stable:
                errors.append("seed pins, payloads, or admission changed during the build")
            before_compiler = before_seed.get("compiler")
            after_compiler = after_seed.get("compiler")
            if not isinstance(before_compiler, dict) or not isinstance(after_compiler, dict):
                errors.append("seed compiler identity is missing")
                compiler_stable: bool | None = False
                compiler_materialized = False
            else:
                before_compiler_status = before_compiler.get("status")
                after_compiler_status = after_compiler.get("status")
                compiler_materialized = before_compiler_status == "not-materialized"
                before_compiler_sha256 = (
                    None
                    if compiler_materialized
                    else hashlib.sha256(
                        json.dumps(
                            before_compiler,
                            sort_keys=True,
                            separators=(",", ":"),
                        ).encode("utf-8")
                    ).hexdigest()
                )
                after_compiler_sha256 = hashlib.sha256(
                    json.dumps(
                        after_compiler,
                        sort_keys=True,
                        separators=(",", ":"),
                    ).encode("utf-8")
                ).hexdigest()
                compiler_stable = (
                    None
                    if compiler_materialized
                    else before_compiler == after_compiler
                )
                if before_compiler_status not in {"not-materialized", "validated"}:
                    errors.append("pre-build seed compiler identity was rejected")
                if after_compiler_status != "validated":
                    errors.append("post-build seed compiler identity is not validated")
                if compiler_stable is False:
                    errors.append("hydrated seed compiler changed during the build")
            bound_seed = dict(after_seed)
            bound_seed.update(
                {
                    "stable_across_build": authority_stable
                    and compiler_stable is not False,
                    "pre_build_authority_sha256": before_authority,
                    "post_build_authority_sha256": after_authority,
                    "compiler_materialized_during_build": compiler_materialized,
                    "compiler_stable_across_build": compiler_stable,
                    "materialization_status": (
                        "fresh-from-validated-archives"
                        if compiler_materialized
                        else "preexisting-unproven"
                    ),
                    "pre_build_compiler_identity_sha256": before_compiler_sha256,
                    "post_build_compiler_identity_sha256": after_compiler_sha256,
                }
            )
            lineage["validated_seed"] = bound_seed
            stable = stable and bool(bound_seed["stable_across_build"])
        if after.get("status") != "trust_from_trust":
            errors.append("post-build bootstrap is not bound to a validated seed compiler")
    elif mode == "genesis":
        if before is None or before.get("status") != "local_genesis" or after.get(
            "status"
        ) != "local_genesis":
            errors.append("genesis bootstrap classification changed during the build")
        if before is not None and (
            before.get("validated_seed") is not None or after.get("validated_seed") is not None
        ):
            errors.append("genesis bootstrap unexpectedly carries validated seed authority")
        before_genesis = before.get("genesis_adapter") if before is not None else None
        after_genesis = after.get("genesis_adapter")
        if not isinstance(before_genesis, dict) or not isinstance(after_genesis, dict):
            errors.append("genesis adapter authority is missing")
            genesis_stable = False
        else:
            if (
                before_genesis.get("schema") != "trust.genesis-adapter-authority.v1"
                or after_genesis.get("schema") != "trust.genesis-adapter-authority.v1"
                or before_genesis.get("status") != "ready"
                or after_genesis.get("status") != "ready"
                or before_genesis.get("errors") != []
                or after_genesis.get("errors") != []
            ):
                errors.append("genesis adapter authority is not canonical and ready")
            before_genesis_sha = before_genesis.get("authority_sha256")
            after_genesis_sha = after_genesis.get("authority_sha256")
            genesis_stable = (
                before_genesis_sha == after_genesis_sha
                and before_genesis.get("authority") == after_genesis.get("authority")
            )
            if not genesis_stable:
                errors.append("genesis adapter or backing producer authority changed during build")
            bound_genesis = dict(after_genesis)
            bound_genesis.update(
                {
                    "stable_across_build": genesis_stable,
                    "pre_build_authority_sha256": before_genesis_sha,
                    "post_build_authority_sha256": after_genesis_sha,
                }
            )
            lineage["genesis_adapter"] = bound_genesis
        stable = stable and genesis_stable
    elif mode == "atpkg":
        before_atpkg = before.get("atpkg_authority") if before is not None else None
        after_atpkg = after.get("atpkg_authority")
        if before is None or before.get("status") != "local_atpkg" or after.get("status") != "local_atpkg":
            errors.append("atpkg bootstrap classification changed during the build")
        if any(
            snapshot is not None and (
                snapshot.get("validated_seed") is not None
                or snapshot.get("genesis_adapter") is not None
            )
            for snapshot in (before, after)
        ):
            errors.append("atpkg bootstrap unexpectedly carries seed/genesis authority")
        atpkg_stable = False
        if not _atpkg_authority_ready(before_atpkg) or not _atpkg_authority_ready(after_atpkg):
            errors.append("atpkg authority is not canonical local candidate evidence")
        else:
            atpkg_stable = (
                before_atpkg["authority_sha256"] == after_atpkg["authority_sha256"]
                and before_atpkg["authority"] == after_atpkg["authority"]
            )
            if not atpkg_stable:
                errors.append("atpkg pack, activation, status root, or verifier changed during build")
            lineage["atpkg_authority"] = {
                **after_atpkg,
                "stable_across_build": atpkg_stable,
                "pre_build_authority_sha256": before_atpkg["authority_sha256"],
                "post_build_authority_sha256": after_atpkg["authority_sha256"],
            }
        stable = stable and atpkg_stable
    else:
        errors.append("bootstrap mode is neither seed, atpkg, nor genesis")
    if errors:
        lineage["status"] = "rejected"
        lineage["trust_from_trust"] = False
    elif mode == "seed":
        lineage["status"] = "trust_from_trust"
        lineage["trust_from_trust"] = True
    elif mode == "atpkg":
        lineage["status"] = "local_atpkg"
        lineage["trust_from_trust"] = True
    else:
        lineage["status"] = "local_genesis"
        lineage["trust_from_trust"] = False
    lineage["stable_across_build"] = stable
    lineage["pre_build_config_sha256"] = (
        before.get("config_sha256") if before is not None else None
    )
    lineage["post_build_config_sha256"] = after.get("config_sha256")
    lineage["errors"] = sorted(set(errors))
    return lineage


# seed_host_ledger.FIXED_POINT_SCHEMA (recreate_bootstrap_test holds the two equal):
# a first Linux seed admitted as a fixed point of an unpinned host chain, with no
# pinned predecessor and no diverse double compile (docs/PLAN.md PKG-S6). A build
# from it is graded UNPINNED_ROOT_SEED_READY, below internal-release-ready: no
# release status names it, so --require-immutable-lineage, compat_check.py and
# every reader that asks for a release status refuse it unchanged.
FIXED_POINT_HOST_RECORD_SCHEMA = "trust-seed-fixed-point-host-record-v1"
UNPINNED_ROOT_SEED_READY = "unpinned-root-seed-ready"


def _selected_host_record_schema(validated_seed: dict[str, object]) -> str | None:
    """The schema of the host record the seed capture selected for this build.

    None when the capture holds no host records (a single-host ledger in the
    legacy format); "" when it holds them but names no readable selected record,
    which the classification refuses rather than guess its kind.
    """
    authority = validated_seed.get("authority")
    ledger = authority.get("seed_ledger") if isinstance(authority, dict) else None
    host_records = ledger.get("host_records") if isinstance(ledger, dict) else None
    if host_records is None:
        return None
    if not isinstance(host_records, dict):
        return ""
    records, selected = host_records.get("records"), host_records.get("selected_host")
    record = records.get(selected) if isinstance(records, dict) and isinstance(selected, str) else None
    schema = record.get("schema") if isinstance(record, dict) else None
    return schema if isinstance(schema, str) and schema else ""


def _classify_receipt_status(
    source_status: object,
    bootstrap_lineage: dict[str, object],
) -> str:
    if source_status != "immutable_release" or bootstrap_lineage.get(
        "status"
    ) != "trust_from_trust":
        return "candidate-ready"
    validated_seed = bootstrap_lineage.get("validated_seed")
    if not isinstance(validated_seed, dict) or validated_seed.get("status") != "validated":
        return "rejected"
    if validated_seed.get("materialization_status") != "fresh-from-validated-archives":
        return "candidate-ready"
    admission_status = validated_seed.get("admission_status")
    schema = _selected_host_record_schema(validated_seed)
    if schema == "":
        return "rejected"
    if schema == FIXED_POINT_HOST_RECORD_SCHEMA:
        # Never a release status, by any admission: an internal admission is the
        # lower grade, and a public promotion of an unpinned root is refused.
        return UNPINNED_ROOT_SEED_READY if admission_status == "internal-admitted" else "rejected"
    if admission_status == "public-promoted":
        return "release-ready"
    if admission_status == "internal-admitted":
        return "internal-release-ready"
    return "rejected"


def _build_slot_cpu_share(env: dict[str, str] | os._Environ[str]) -> str | None:
    """The existing machine admission's resource ceiling, never tool selection."""
    if env.get("BUILD_SLOT_HELD") != "1":
        return None
    share = env.get("CARGO_BUILD_JOBS", "")
    significant = share.lstrip("0")
    if (not re.fullmatch(r"[0-9]+", share) or not significant
            or len(significant) > 10 or int(significant) > 0xFFFFFFFF):
        raise RuntimeError("BUILD_SLOT_HELD=1 requires a positive u32 CARGO_BUILD_JOBS share")
    # Keep the validated resource value short for downstream Python/Rust
    # parsers and argv, even when the launcher supplied many leading zeroes.
    return str(int(significant))


def _ambient_build_authority_overrides(
    env: dict[str, str] | os._Environ[str],
) -> dict[str, str]:
    overrides: dict[str, str] = {}
    try:
        admitted_share = _build_slot_cpu_share(env)
    except RuntimeError:
        admitted_share = None  # Invalid/missing shares are refused by capture and producer.
    for name, value in env.items():
        # This private marker only prevents an old-Python re-exec loop.  It is
        # consumed by this driver and scrubbed before x.py; treating it as build
        # authority would make the supported interpreter upgrade path unusable.
        if name == REEXEC_GUARD_ENV:
            continue
        # Trust: a validated admission ceiling selects no compiler, SDK,
        # library, source or flag. Bootstrap independently clamps CLI/config
        # jobs to it. Do not make machine admission itself a forbidden Cargo
        # override; all other CARGO_* settings still refuse. Resource ceilings
        # do not enter native-tool identity, so provenance can be rechecked
        # outside the original scheduling slot.
        if name == "CARGO_BUILD_JOBS" and admitted_share is not None:
            continue
        if name in BUILD_AUTHORITY_ENV_NAMES or any(
            name.startswith(prefix) for prefix in BUILD_AUTHORITY_ENV_PREFIXES
        ):
            overrides[name] = hashlib.sha256(value.encode("utf-8")).hexdigest()
    return dict(sorted(overrides.items()))


def _native_tool_record(name: str, path: str | None, args: tuple[str, ...]) -> dict[str, object]:
    record: dict[str, object] = {"name": name, "resolved_local_path": path}
    if path is None:
        record["status"] = "missing"
        return record
    candidate = Path(path)
    try:
        record.update(
            {
                "status": "bound",
                "resolved_real_path": str(candidate.resolve()),
                "sha256": _sha256_file(candidate),
                "identity": tool_version(
                    path,
                    args,
                    environment=(
                        _provenance_git_environment() if name == "git" else None
                    ),
                ),
            }
        )
    except OSError as error:
        record.update({"status": "rejected", "error": str(error)})
    return record


def _darwin_platform_toolchain() -> tuple[dict[str, object], list[str]]:
    """Resolve the actual Apple toolchain selected behind /usr/bin dispatchers."""
    errors: list[str] = []
    xcrun = which("xcrun")
    xcode_select = which("xcode-select")
    record: dict[str, object] = {
        "schema": "trust.darwin-platform-toolchain.v1",
        "xcrun": _native_tool_record("xcrun", xcrun, ("--version",)),
        "xcode_select": _native_tool_record(
            "xcode-select", xcode_select, ("--version",)
        ),
    }
    if xcrun is None or xcode_select is None:
        errors.append("xcrun or xcode-select is missing")
        record.update({"status": "rejected", "tools": [], "errors": errors})
        return record, errors

    developer_ok, developer_value = _capture_identity(Path(xcode_select), ("-p",))
    developer_path = Path(developer_value) if developer_ok else None
    developer_real: Path | None = None
    if developer_path is None or not developer_path.is_absolute() or not developer_path.is_dir():
        errors.append("xcode-select did not identify an absolute developer directory")
    else:
        try:
            developer_real = developer_path.resolve(strict=True)
        except OSError as error:
            errors.append(f"could not resolve the active developer directory: {error}")
    allowed_developer_roots = {
        Path("/Applications/Xcode.app/Contents/Developer"),
        Path("/Library/Developer/CommandLineTools"),
    }
    if developer_real not in allowed_developer_roots:
        errors.append("active Apple developer directory is outside the admitted roots")
    record.update(
        {
            "developer_selected_path": str(developer_path) if developer_path else None,
            "developer_real_path": str(developer_real) if developer_real else None,
        }
    )

    selected_tools: list[dict[str, object]] = []
    identity_args = {
        "clang": ("--version",),
        "clang++": ("--version",),
        "ar": ("-V",),
        "ld": ("-v",),
        "nm": ("--version",),
        "ranlib": ("-V",),
        "strip": ("-V",),
        "git": ("--version",),
        "make": ("--version",),
        "otool": ("--version",),
        "python3": ("--version",),
    }
    for name, args in identity_args.items():
        selected_ok, selected_value = _capture_identity(
            Path(xcrun), ("--find", name)
        )
        selected_path = Path(selected_value) if selected_ok else None
        tool_record = _native_tool_record(
            name,
            str(selected_path) if selected_path is not None else None,
            args,
        )
        tool_record["xcrun_selected_path"] = (
            str(selected_path) if selected_path is not None else None
        )
        selected_real_value = tool_record.get("resolved_real_path")
        selected_within_developer = False
        if developer_real is not None and isinstance(selected_real_value, str):
            try:
                Path(selected_real_value).relative_to(developer_real)
            except ValueError:
                selected_within_developer = False
            else:
                selected_within_developer = True
        tool_record["within_active_developer_dir"] = selected_within_developer
        if tool_record.get("status") != "bound" or not selected_within_developer:
            errors.append(f"xcrun-selected {name} is not bound inside the developer directory")
        selected_tools.append(tool_record)
    record["tools"] = selected_tools

    sdk_ok, sdk_value = _capture_identity(Path(xcrun), ("--show-sdk-path",))
    version_ok, sdk_version = _capture_identity(Path(xcrun), ("--show-sdk-version",))
    sdk_selected = Path(sdk_value) if sdk_ok else None
    sdk_real: Path | None = None
    if sdk_selected is None or not sdk_selected.is_absolute() or not sdk_selected.is_dir():
        errors.append("xcrun did not identify an absolute SDK directory")
    else:
        try:
            sdk_real = sdk_selected.resolve(strict=True)
        except OSError as error:
            errors.append(f"could not resolve the selected Darwin SDK: {error}")
    sdk_within_developer = False
    if developer_real is not None and sdk_real is not None:
        try:
            sdk_real.relative_to(developer_real)
        except ValueError:
            sdk_within_developer = False
        else:
            sdk_within_developer = True
    if not sdk_within_developer:
        errors.append("selected Darwin SDK is outside the active developer directory")
    settings = sdk_real / "SDKSettings.json" if sdk_real is not None else None
    settings_sha256: str | None = None
    if settings is None or not settings.is_file() or settings.is_symlink():
        errors.append("Darwin SDKSettings.json is missing, non-regular, or a symlink")
    else:
        try:
            settings_sha256 = _sha256_file(settings)
        except OSError as error:
            errors.append(f"could not hash Darwin SDK settings: {error}")
    sdk_link_target: str | None = None
    if sdk_selected is not None and sdk_selected.is_symlink():
        try:
            sdk_link_target = os.readlink(sdk_selected)
        except OSError as error:
            errors.append(f"could not read selected Darwin SDK symlink: {error}")
    record["sdk"] = {
        "selected_path": str(sdk_selected) if sdk_selected is not None else None,
        "selected_link_target": sdk_link_target,
        "real_path": str(sdk_real) if sdk_real is not None else None,
        "within_active_developer_dir": sdk_within_developer,
        "version": sdk_version if version_ok else None,
        "settings_path": str(settings) if settings is not None else None,
        "settings_sha256": settings_sha256,
    }
    if not version_ok:
        errors.append("Darwin SDK version is unavailable")
    record["status"] = "bound" if not errors else "rejected"
    record["errors"] = sorted(set(errors))
    return record, errors


def _is_macho(path: Path) -> bool:
    try:
        with path.open("rb") as stream:
            magic = stream.read(4)
    except OSError:
        return False
    return magic in {
        b"\xfe\xed\xfa\xce",
        b"\xce\xfa\xed\xfe",
        b"\xfe\xed\xfa\xcf",
        b"\xcf\xfa\xed\xfe",
        b"\xca\xfe\xba\xbe",
        b"\xbe\xba\xfe\xca",
        b"\xca\xfe\xba\xbf",
        b"\xbf\xba\xfe\xca",
    }


def _darwin_rpaths(otool: Path, binary: Path) -> tuple[list[str], str | None]:
    try:
        completed = subprocess.run(
            [str(otool), "-l", str(binary)],
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        return [], str(error)
    if completed.returncode != 0:
        return [], (completed.stderr or completed.stdout).strip()
    rpaths: list[str] = []
    expecting_path = False
    for line in completed.stdout.splitlines():
        stripped = line.strip()
        if stripped == "cmd LC_RPATH":
            expecting_path = True
            continue
        if expecting_path and stripped.startswith("path "):
            rpaths.append(stripped[5:].split(" (offset ", 1)[0])
            expecting_path = False
    return rpaths, None


def _darwin_install_id(otool: Path, binary: Path) -> str | None:
    try:
        completed = subprocess.run(
            [str(otool), "-D", str(binary)],
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if completed.returncode != 0:
        return None
    identifiers = [
        line.strip()
        for line in completed.stdout.splitlines()
        if line.strip()
        and not line.strip().endswith(":")
        and " (architecture " not in line
    ]
    return identifiers[0] if len(set(identifiers)) == 1 else None


def _resolve_darwin_dependency(
    raw: str,
    *,
    loader: Path,
    executable: Path,
    otool: Path,
) -> tuple[Path | None, str | None]:
    def expand(value: str) -> Path | None:
        if value == "@loader_path":
            return loader.parent
        if value.startswith("@loader_path/"):
            return loader.parent / value.removeprefix("@loader_path/")
        if value == "@executable_path":
            return executable.parent
        if value.startswith("@executable_path/"):
            return executable.parent / value.removeprefix("@executable_path/")
        if value.startswith("/"):
            return Path(value)
        return None

    direct = expand(raw)
    if direct is not None:
        return direct, None
    if not raw.startswith("@rpath/"):
        return None, f"unsupported Darwin dependency spelling: {raw}"
    suffix = raw.removeprefix("@rpath/")
    loader_rpaths, loader_error = _darwin_rpaths(otool, loader)
    executable_rpaths, executable_error = _darwin_rpaths(otool, executable)
    if loader_error is not None and executable_error is not None:
        return None, f"could not inspect Darwin rpaths for {raw}"
    candidates: list[Path] = []
    for rpath in dict.fromkeys([*loader_rpaths, *executable_rpaths]):
        expanded = expand(rpath)
        if expanded is not None:
            candidate = expanded / suffix
            if candidate.is_file():
                candidates.append(candidate)
    real_candidates = sorted({str(candidate.resolve()) for candidate in candidates})
    if len(real_candidates) != 1:
        return None, f"Darwin @rpath dependency is missing or ambiguous: {raw}"
    return Path(real_candidates[0]), None


def _capture_darwin_dynamic_dependencies(
    roots: list[Path],
    otool: Path,
) -> dict[str, object]:
    """Hash the recursive non-system Mach-O dependency closure of build tools."""
    errors: list[str] = []
    root_paths = sorted({str(path.resolve()) for path in roots if path.is_file()})
    queue: list[tuple[Path, Path]] = [
        (Path(path), Path(path)) for path in root_paths if _is_macho(Path(path))
    ]
    inspected: set[tuple[str, str]] = set()
    dependencies: dict[str, dict[str, object]] = {}
    while queue:
        binary, executable = queue.pop(0)
        state = (str(binary), str(executable))
        if state in inspected:
            continue
        inspected.add(state)
        try:
            completed = subprocess.run(
                [str(otool), "-L", str(binary)],
                capture_output=True,
                text=True,
                check=False,
                timeout=30,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            errors.append(f"could not inspect Mach-O dependencies for {binary}: {error}")
            continue
        if completed.returncode != 0:
            errors.append(f"otool rejected Mach-O dependency query for {binary}")
            continue
        install_id = _darwin_install_id(otool, binary)
        for line in completed.stdout.splitlines()[1:]:
            if not line[:1].isspace() or " (compatibility version " not in line:
                continue
            raw = line.strip().split(" (compatibility version ", 1)[0]
            if not raw:
                continue
            if install_id is not None and raw == install_id:
                continue
            if raw.startswith("/usr/lib/") or raw.startswith("/System/Library/"):
                continue
            selected, resolution_error = _resolve_darwin_dependency(
                raw,
                loader=binary,
                executable=executable,
                otool=otool,
            )
            if resolution_error is not None or selected is None:
                errors.append(
                    resolution_error
                    or f"could not resolve Darwin dependency {raw} for {binary}"
                )
                continue
            if not selected.is_file():
                errors.append(f"non-system Darwin dependency is missing: {selected}")
                continue
            try:
                real = selected.resolve(strict=True)
                sha256 = _sha256_file(real)
                metadata = real.lstat()
            except OSError as error:
                errors.append(f"could not bind Darwin dependency {selected}: {error}")
                continue
            selected_record = {
                "path": str(selected),
                "link_target": os.readlink(selected) if selected.is_symlink() else None,
            }
            record = {
                "resolved_real_path": str(real),
                "mode": stat.S_IMODE(metadata.st_mode),
                "size": metadata.st_size,
                "sha256": sha256,
                "selected_paths": [selected_record],
            }
            existing = dependencies.get(str(real))
            if existing is None:
                dependencies[str(real)] = record
            else:
                for field in ("resolved_real_path", "mode", "size", "sha256"):
                    if existing.get(field) != record.get(field):
                        errors.append(f"Darwin dependency identity changed: {real}")
                selected_paths = existing.get("selected_paths")
                if isinstance(selected_paths, list) and selected_record not in selected_paths:
                    selected_paths.append(selected_record)
                    selected_paths.sort(key=lambda row: str(row["path"]))
            if _is_macho(real):
                queue.append((real, executable))
    closure = {
        "schema": "trust.darwin-dynamic-dependency-closure.v1",
        "roots": root_paths,
        "otool_path": str(otool),
        "dependencies": sorted(
            dependencies.values(), key=lambda row: str(row["resolved_real_path"])
        ),
    }
    closure_sha256 = hashlib.sha256(
        json.dumps(closure, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return {
        **closure,
        "status": "ready" if not errors else "rejected",
        "closure_sha256": closure_sha256,
        "errors": sorted(set(errors)),
    }


def stage_documentation_alias_errors(bin_dir: Path, host: str) -> list[str]:
    """A public compatibility alias must execute the bound Trust documentation tool."""
    trustdoc = bin_dir / _host_executable("trustdoc", host)
    rustdoc = bin_dir / _host_executable("rustdoc", host)
    if not rustdoc.is_file():
        return [f"missing rustdoc compatibility alias: {rustdoc}"]
    if not trustdoc.is_file() or _sha256_file(rustdoc) != _sha256_file(trustdoc):
        return ["rustdoc compatibility alias differs from trustdoc"]
    return []


def bootstrap_cargo_home(root: Path) -> Path:
    """The build owns its Cargo configuration/cache; never the user's global one."""
    return root.resolve() / "build" / "bootstrap-cargo-home"


def bootstrap_cargo_authority(
    root: Path, *, cargo_home: Path | None = None,
) -> tuple[dict[str, object], list[str]]:
    """Read-only authority check matching Cargo's home AND ancestor search."""
    root = root.resolve()
    cargo_home = bootstrap_cargo_home(root) if cargo_home is None else cargo_home.resolve()
    errors: list[str] = []
    for directory in (root / "build", cargo_home):
        if directory == root / "build" and is_sanctioned_build_link(root):
            continue
        if directory.is_symlink() or (directory.exists() and not directory.is_dir()):
            errors.append(f"bootstrap Cargo directory must be a real directory: {directory}")
    config_paths = [cargo_home / name for name in ("config", "config.toml")]
    # CARGO_HOME alone does not stop Cargo walking above the source checkout.
    # In particular ~/.cargo is also an ancestor config for repos under ~.
    config_paths.extend(parent / ".cargo" / name for parent in root.parents
                        for name in ("config", "config.toml"))
    present = [str(path) for path in config_paths if os.path.lexists(path)]
    if present:
        errors.append(
            "unbound Cargo configuration would affect the build: " + ", ".join(present)
            + "; use a clean worktree outside those ancestor directories; "
            "leave the user's configuration unchanged"
        )
    return {
        "schema": "trust.bootstrap-cargo-environment.v1",
        "cargo_home": str(cargo_home),
        "configuration_policy": "empty-owned-home-and-no-external-ancestor-config",
        "unbound_config_paths": present,
    }, errors


def prepare_bootstrap_cargo_environment(root: Path, env: dict[str, str]) -> None:
    authority, errors = bootstrap_cargo_authority(root)
    if errors:
        raise RuntimeError("; ".join(errors))
    cargo_home = bootstrap_cargo_home(root)
    cargo_home.mkdir(mode=0o700, parents=True, exist_ok=True)
    # Check again after creation before any compiler/package-manager child runs.
    _authority, errors = bootstrap_cargo_authority(root)
    if errors:
        raise RuntimeError("; ".join(errors))
    env["CARGO_HOME"] = str(authority["cargo_home"])


def capture_build_authority(
    root: Path,
    host: str,
    llvm_config: str | None,
    *,
    cargo_home: Path | None = None,
    declared_environment: dict[str, str] | None = None,
    mint_configuration: dict[str, object] | None = None,
) -> dict[str, object]:
    """Bind ambient build authority, native tools, and the selected SDK.

    It only reads (the environment, the tools PATH resolves, Cargo
    configuration paths at and above `root`, and on macOS the developer
    directory, the SDK and the tools' dylib closure), and it needs neither the
    stage0 selection nor the bootstrap config nor anything a build writes. That
    is what lets the prerequisite report of a Stage2+ invocation BE this
    function's answer (check_prereqs -> native_authority_prereqs): every error
    returned here, in whatever words, is what `--check` reports for the same
    flags, and what refuses a build before it selects or fetches a stage0.
    """
    errors: list[str] = []
    overrides = _ambient_build_authority_overrides(os.environ)
    try:
        _build_slot_cpu_share(os.environ)
    except RuntimeError as error:
        errors.append(str(error))
    # The mint launches a closed environment itself. Explicit declarations bind
    # its small native-input surface; arbitrary ambient overrides still refuse.
    declared = declared_environment or {}
    permitted = {
        "CARGO_HOME", "RUSTUP_HOME", "SOURCE_DATE_EPOCH", "LIBRARY_PATH", "DYLD_LIBRARY_PATH",
        "CARGO_NET_OFFLINE", "GIT_CONFIG_NOSYSTEM", "GIT_CONFIG_GLOBAL",
    }
    clean_lean = None
    if mint_configuration is not None:
        try:
            config = root / str(mint_configuration.get("config_path"))
            context = _validated_mint_configuration(root, host, config, mint_configuration)
            clean_lean = context.get("clean_lean_inputs")
            if not isinstance(clean_lean, dict) or not isinstance(clean_lean.get("environment"), dict):
                raise ValueError("mint native authority requires bound Clean Lean inputs")
            lean_environment = clean_lean["environment"]
            if (set(lean_environment) != {"CLEAN_OLEAN_PINNED_LEAN_LIB", "CLEAN_OLEAN_REQUIRE_PINNED_LEAN"}
                    or lean_environment.get("CLEAN_OLEAN_REQUIRE_PINNED_LEAN") != "1"
                    or lean_environment.get("CLEAN_OLEAN_PINNED_LEAN_LIB") != clean_lean.get("library_path")
                    or any(declared.get(name) != value for name, value in lean_environment.items())):
                raise ValueError("mint Clean Lean effective environment differs from its bound closure")
            permitted.update(lean_environment)
        except (OSError, ValueError, RuntimeError) as error:
            errors.append(f"mint Clean Lean input authority refused: {error}")
    if set(declared) - permitted:
        errors.append(
            "unsupported declared build-authority environment: " + ", ".join(sorted(set(declared) - permitted))
        )
    for name, value in declared.items():
        if not isinstance(value, str) or os.environ.get(name) != value:
            errors.append(f"declared build-authority environment differs from the process: {name}")
        elif name in permitted:
            overrides.pop(name, None)
    for name, required in (("CARGO_NET_OFFLINE", "true"), ("GIT_CONFIG_NOSYSTEM", "1"),
                           ("GIT_CONFIG_GLOBAL", os.devnull)):
        if name in declared and declared[name] != required:
            errors.append(f"declared {name} must be {required!r}")
    if overrides:
        errors.append(
            "ambient build-authority overrides are set: " + ", ".join(overrides)
        )

    cargo_environment, cargo_errors = bootstrap_cargo_authority(
        root, **({"cargo_home": cargo_home} if cargo_home is not None else {})
    )
    if "CARGO_HOME" in declared and cargo_home is None:
        errors.append("declaring CARGO_HOME requires the same explicit private cargo_home capture")
    if cargo_home is not None and declared.get("CARGO_HOME") != str(cargo_home):
        errors.append("the declared CARGO_HOME does not name the captured private cargo home")
    errors.extend(cargo_errors)
    ambient_cargo_configs = cargo_environment["unbound_config_paths"]

    native_bindings = bind_native_build_tools()
    tools: list[dict[str, object]] = [binding.record for binding in native_bindings]
    selected_llvm = bind_explicit_llvm_config(llvm_config)
    errors.extend(native_tool_refusals(native_bindings, selected_llvm).values())

    platform_toolchain: dict[str, object] | None = None
    sdk: dict[str, object]
    if platform.system().lower() == "darwin":
        platform_toolchain, darwin_errors = _darwin_platform_toolchain()
        errors.extend(darwin_errors)
        sdk = {
            "platform": "darwin",
            "status": platform_toolchain.get("status"),
            **dict(platform_toolchain.get("sdk", {})),
        }
    else:
        sdk = {
            "platform": platform.system().lower(),
            "status": "system-native",
        }

    derived_library_paths: list[dict[str, object]] = []
    homebrew_library: Path | None = None
    if platform.system().lower() == "darwin":
        homebrew_prefix, homebrew_library = _selected_homebrew_library_path()
        if homebrew_prefix is not None and homebrew_library is not None:
            library_tree = _capture_external_tree(
                homebrew_library,
                homebrew_prefix,
                bind_external_symlink_targets=True,
            )
            derived_library_paths.append(library_tree)
            errors.extend(str(error) for error in library_tree.get("errors", []))

    dynamic_dependencies: dict[str, object] | None = None
    if platform.system().lower() == "darwin" and platform_toolchain is not None:
        selected_platform_tools = platform_toolchain.get("tools")
        selected_platform_rows = (
            selected_platform_tools if isinstance(selected_platform_tools, list) else []
        )
        selected_platform_names = {
            str(row.get("name"))
            for row in selected_platform_rows
            if isinstance(row, dict) and row.get("status") == "bound"
        }
        dispatcher_replacements = {
            "cc": "clang",
            "c++": "clang++",
            "ar": "ar",
            "ld": "ld",
            "nm": "nm",
            "ranlib": "ranlib",
            "strip": "strip",
            "git": "git",
            "make": "make",
            "python": "python3",
        }
        otool_path_value = next(
            (
                row.get("resolved_real_path")
                for row in selected_platform_rows
                if isinstance(row, dict) and row.get("name") == "otool"
            ),
            None,
        )
        xcrun_record = platform_toolchain.get("xcrun")
        xcrun_sha256 = (
            xcrun_record.get("sha256") if isinstance(xcrun_record, dict) else None
        )
        dependency_roots: list[Path] = []
        for row in tools:
            resolved_value = row.get("resolved_real_path")
            if not isinstance(resolved_value, str):
                continue
            replacement = dispatcher_replacements.get(str(row.get("name")))
            selected_replacement = replacement in selected_platform_names
            looks_like_dispatcher = (
                str(row.get("resolved_local_path", "")).startswith("/usr/bin/")
                and row.get("sha256") == xcrun_sha256
            )
            if selected_replacement and looks_like_dispatcher:
                continue
            dependency_roots.append(Path(resolved_value))
        dependency_roots.extend(
            Path(str(row["resolved_real_path"]))
            for row in selected_platform_rows
            if isinstance(row, dict)
            and isinstance(row.get("resolved_real_path"), str)
        )
        for dispatcher_key in ("xcrun", "xcode_select"):
            dispatcher = platform_toolchain.get(dispatcher_key)
            if isinstance(dispatcher, dict) and isinstance(
                dispatcher.get("resolved_real_path"), str
            ):
                dependency_roots.append(Path(str(dispatcher["resolved_real_path"])))
        if selected_llvm is not None and isinstance(
            selected_llvm.get("resolved_real_path"), str
        ):
            dependency_roots.append(Path(str(selected_llvm["resolved_real_path"])))
        if homebrew_library is not None:
            try:
                homebrew_library_real = homebrew_library.resolve(strict=True)
            except OSError as error:
                errors.append(f"could not resolve admitted Homebrew library tree: {error}")
            else:
                for current_root, _directory_names, file_names in os.walk(
                    homebrew_library_real,
                    followlinks=False,
                ):
                    current = Path(current_root)
                    for name in file_names:
                        candidate = current / name
                        if candidate.is_file() and _is_macho(candidate):
                            dependency_roots.append(candidate)
        if not isinstance(otool_path_value, str):
            errors.append("xcrun-selected otool is unavailable for dependency binding")
            dynamic_dependencies = {
                "schema": "trust.darwin-dynamic-dependency-closure.v1",
                "status": "rejected",
                "errors": ["xcrun-selected otool is unavailable"],
            }
        else:
            dynamic_dependencies = _capture_darwin_dynamic_dependencies(
                dependency_roots,
                Path(otool_path_value),
            )
            errors.extend(
                str(error) for error in dynamic_dependencies.get("errors", [])
            )

    authority = {
        "schema": "trust.build-authority.v1",
        "host": host,
        "ambient_overrides": overrides,
        "ambient_cargo_configs": ambient_cargo_configs,
        "cargo_environment": cargo_environment,
        "native_tools": tools,
        "selected_llvm": selected_llvm,
        "platform_toolchain": platform_toolchain,
        "sdk": sdk,
        "dynamic_dependencies": dynamic_dependencies,
        "derived_library_paths": derived_library_paths,
    }
    if clean_lean is not None:
        authority["clean_lean_inputs"] = clean_lean
    if declared_environment is not None:
        authority["declared_environment_sha256"] = {
            name: hashlib.sha256(value.encode("utf-8")).hexdigest()
            for name, value in sorted(declared.items()) if isinstance(value, str)
        }
        native_paths = {}
        for name in ("LIBRARY_PATH", "DYLD_LIBRARY_PATH"):
            if name not in declared or not isinstance(declared[name], str):
                continue
            trees = []
            for value in declared[name].split(os.pathsep):
                directory = Path(value)
                if not value or not directory.is_absolute() or not directory.is_dir():
                    errors.append(f"declared {name} contains an unavailable absolute directory: {value!r}")
                    continue
                tree = _capture_external_tree(directory, directory, bind_external_symlink_targets=True)
                errors.extend(str(error) for error in tree.get("errors", []))
                trees.append(tree)
            native_paths[name] = trees
        authority["declared_native_library_paths"] = native_paths
        if isinstance(declared.get("RUSTUP_HOME"), str):
            directory = Path(declared["RUSTUP_HOME"])
            if not directory.is_absolute() or not directory.is_dir():
                errors.append("declared RUSTUP_HOME is not an available absolute directory")
            else:
                tree = _capture_external_tree(directory, directory, bind_external_symlink_targets=True)
                errors.extend(str(error) for error in tree.get("errors", []))
                authority["declared_rustup_home"] = tree
    authority_sha256 = hashlib.sha256(
        json.dumps(authority, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return {
        **authority,
        "status": "ready" if not errors else "rejected",
        "authority_sha256": authority_sha256,
        "errors": sorted(set(errors)),
    }


def _bind_build_authority(
    before: dict[str, object] | None,
    after: dict[str, object],
) -> dict[str, object]:
    authority = dict(after)
    errors = [str(error) for error in after.get("errors", [])]
    before_sha = before.get("authority_sha256") if before is not None else None
    after_sha = after.get("authority_sha256")
    stable = before is not None and before_sha == after_sha
    if before is None:
        errors.append("missing pre-build native authority snapshot")
    else:
        errors.extend(str(error) for error in before.get("errors", []))
        if (json.dumps(before.get("clean_lean_inputs"), sort_keys=True, allow_nan=False)
                != json.dumps(after.get("clean_lean_inputs"), sort_keys=True, allow_nan=False)):
            errors.append("Clean Lean input closure changed during the build")
        if before.get("status") != "ready":
            errors.append("pre-build native authority was rejected")
        if not stable:
            errors.append("native tools, SDK, PATH, or ambient authority changed during the build")
    authority.update(
        {
            "status": "ready" if not errors else "rejected",
            "stable_across_build": stable,
            "pre_build_authority_sha256": before_sha,
            "post_build_authority_sha256": after_sha,
            "errors": sorted(set(errors)),
        }
    )
    return authority


def recreator_invocation_record(argv: list[str]) -> dict[str, object]:
    """The receipt's `recreator_invocation` for a build started with `argv`."""
    return {
        "schema": RECREATOR_INVOCATION_SCHEMA,
        "scope": RECREATOR_INVOCATION_SCOPE,
        "argv": list(argv),
    }


def _unrecordable_character(text: str) -> bool:
    """Whether `text` holds a control character or an unpaired surrogate.

    By code point, never `str.isprintable()`: that asks the Unicode tables of
    the interpreter that runs it, and promotion's reader of this record
    (scripts/lib/stage_receipt_provenance.py `unrecordable_character`, the same
    three ranges) runs under whatever python3 is on PATH. Measured 2026-10-12
    on U+1FAE8: printable to python3.14, unprintable to /usr/bin/python3 3.9.6,
    so a build this script accepted and stamped would have been refused by
    promotion after the whole build. General_Category Cc (U+0000-001F,
    U+007F-009F) and Cs (U+D800-DFFF) are immutable sets.
    """
    return any(
        code < 0x20 or 0x7F <= code <= 0x9F or 0xD800 <= code <= 0xDFFF
        for code in map(ord, text)
    )


def _recreator_invocation_errors(value: object) -> list[str]:
    """Why `value` is not a `recreator_invocation` record; empty when it is one.

    scripts/lib/stage_receipt_provenance.py `invocation_errors` is the same rule
    for promotion, which reads the receipt under whatever Python is on PATH and
    cannot import this file; recreate_bootstrap_test.py runs both on the same
    records.
    """
    if not isinstance(value, dict):
        return ["recreator_invocation is not an object"]
    errors: list[str] = []
    if set(value) != {"schema", "scope", "argv"}:
        errors.append("recreator_invocation does not hold exactly the keys argv, schema, scope")
    if value.get("schema") != RECREATOR_INVOCATION_SCHEMA:
        errors.append(f"recreator_invocation.schema is not {RECREATOR_INVOCATION_SCHEMA}")
    if value.get("scope") != RECREATOR_INVOCATION_SCOPE:
        errors.append(f"recreator_invocation.scope is not {RECREATOR_INVOCATION_SCOPE}")
    argv = value.get("argv")
    if not isinstance(argv, list) or not all(isinstance(item, str) for item in argv):
        errors.append("recreator_invocation.argv is not a list of strings")
    elif any(_unrecordable_character(item) for item in argv):
        errors.append("recreator_invocation.argv holds a control or unprintable character")
    return errors


def _is_hex(value: object, lengths: tuple[int, ...]) -> bool:
    return (
        isinstance(value, str)
        and len(value) in lengths
        and all(character in "0123456789abcdef" for character in value)
    )


def _llvm_source_identity_sha256(rows: object) -> str:
    """The one sha256 that stands for the LLVM source rows `rows`."""
    return hashlib.sha256(
        json.dumps(
            {"schema": LLVM_SOURCE_IDENTITY_SCHEMA, "paths": rows},
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def capture_llvm_source_identity(root: Path) -> dict[str, object]:
    """The LLVM source identity of the tree at `root`, read from git. Read-only.

    `paths` are HEAD's entries for LLVM_SOURCE_IDENTITY_PATHS (path, object
    type, object id) and `identity_sha256` stands for them. `clean` says that
    nothing under those paths is staged, modified or untracked, which is what
    makes HEAD's object ids the identity of what a build compiles. A tree git
    cannot answer for has `errors`, no rows and no identity.
    """
    errors: list[str] = []
    rows: list[dict[str, str]] = []
    listing = _git_bytes(
        root,
        ("ls-tree", "-z", "HEAD", "--", *LLVM_SOURCE_IDENTITY_PATHS),
        errors,
        "the LLVM source identity",
    )
    for entry in (listing or b"").split(b"\0"):
        if not entry:
            continue
        meta, _tab, path = entry.decode("utf-8", errors="replace").partition("\t")
        fields = meta.split(" ")
        if len(fields) != 3 or not _is_hex(fields[2], (40, 64)):
            errors.append("git ls-tree printed an entry that is not one object, for the LLVM source identity")
            continue
        rows.append({"path": path, "type": fields[1], "oid": fields[2]})
    rows.sort(key=lambda row: row["path"])
    if listing is not None and [row["path"] for row in rows] != sorted(LLVM_SOURCE_IDENTITY_PATHS):
        errors.append(
            "HEAD does not hold exactly one entry for each of " + ", ".join(LLVM_SOURCE_IDENTITY_PATHS)
        )
    state = _git_bytes(
        root,
        ("status", "--porcelain=v1", "-z", "--untracked-files=all", "--", *LLVM_SOURCE_IDENTITY_PATHS),
        errors,
        "the state of the LLVM sources",
    )
    if errors:
        return {"paths": [], "identity_sha256": None, "clean": False, "errors": sorted(set(errors))}
    return {
        "paths": rows,
        "identity_sha256": _llvm_source_identity_sha256(rows),
        "clean": state == b"",
        "errors": [],
    }


def _llvm_out_dir(root: Path, host: str, *, build_root: Path | None = None) -> Path:
    """Where x.py builds and installs the host's in-tree LLVM (bootstrap `llvm_out`)."""
    return (build_root if build_root is not None else root / "build") / host / LLVM_OUTPUT_ROOTS[0][0]


def capture_llvm_output(root: Path, host: str, *, build_root: Path | None = None) -> dict[str, object]:
    """What x.py's builds of src/llvm-project left under build/<host>. Read-only.

    Each directory of LLVM_OUTPUT_ROOTS is a cmake install prefix (bin/, lib/,
    include/, share/), with cmake's own work tree in build/ and x.py's stamp
    beside them. `dirs` are those that are there. `fingerprint_sha256` is one
    sha256 over every installed entry of all of them, sorted by path: a regular
    file by its size and sha256, a symbolic link by its target. The work trees
    and each directory's own dot files (x.py's stamp, this script's build
    record) are not in it, so writing the record does not move it.
    `stamp_present`: x.py writes a directory's stamp when its build completes
    (and removes LLVM's before it rebuilds), so a directory without one does
    not hold a completed build. `uncovered` are the LLVM_UNCOVERED_OUTPUTS that
    are there, for any target.
    """
    errors: list[str] = []
    record: dict[str, object] = {
        "dirs": [],
        "present": False,
        "stamp_present": False,
        "uncovered": [],
        "fingerprint_sha256": None,
        "errors": errors,
    }
    build = build_root if build_root is not None else root / "build"
    label_root = _repository_relative_path(root, build)
    try:
        targets = sorted(
            entry.name for entry in os.scandir(build) if entry.is_dir(follow_symlinks=False)
        )
    except FileNotFoundError:
        targets = []
    except OSError as error:
        errors.append(f"build could not be listed: {error}")
        return record
    record["uncovered"] = [
        f"{label_root}/{target}/{name}"
        for target in targets
        for name in LLVM_UNCOVERED_OUTPUTS
        if os.path.lexists(build / target / name)
    ]
    entries: list[tuple[str, Path]] = []
    dirs: list[str] = []
    stamped = True
    for name, stamp in LLVM_OUTPUT_ROOTS:
        out_dir = build / host / name
        label = f"{label_root}/{host}/{name}"
        if not os.path.lexists(out_dir):
            continue
        if out_dir.is_symlink() or not out_dir.is_dir():
            errors.append(f"{label} is not a real directory")
            continue
        dirs.append(label)
        stamped = stamped and (out_dir / stamp).is_file()
        unread: list[OSError] = []
        for current, directories, files in os.walk(out_dir, onerror=unread.append):
            here = Path(current)
            if here == out_dir:
                directories[:] = [
                    entry for entry in directories if entry != "build" and not entry.startswith(".")
                ]
                files = [entry for entry in files if not entry.startswith(".")]
            # os.walk lists a link to a directory among the directories and does not enter it.
            links = [entry for entry in directories if (here / entry).is_symlink()]
            entries.extend(
                (f"{label}/{(here / entry).relative_to(out_dir).as_posix()}", here / entry)
                for entry in (*files, *links)
            )
        errors.extend(f"{label} could not be listed: {error}" for error in unread)
    record["dirs"] = dirs
    record["present"] = bool(dirs)
    record["stamp_present"] = bool(dirs) and stamped
    digest = hashlib.sha256()
    for relative, path in sorted(entries):
        try:
            metadata = path.lstat()
            if stat.S_ISLNK(metadata.st_mode):
                line = f"link\0{relative}\0{os.readlink(path)}\n"
            elif stat.S_ISREG(metadata.st_mode):
                line = f"file\0{relative}\0{metadata.st_size}\0{_sha256_file(path)}\n"
            else:
                errors.append(f"{relative} is neither a regular file nor a link")
                continue
        except OSError as error:
            errors.append(f"{relative} could not be read: {error}")
            continue
        digest.update(line.encode("utf-8", errors="surrogateescape"))
    if dirs and not errors:
        record["fingerprint_sha256"] = digest.hexdigest()
    return record


def _llvm_source_rows_errors(rows: object, where: str) -> list[str]:
    if not isinstance(rows, list) or not rows:
        return [f"{where} is not a non-empty list"]
    paths: list[str] = []
    for row in rows:
        if (
            not isinstance(row, dict)
            or set(row) != {"path", "type", "oid"}
            or not isinstance(row["path"], str)
            or not row["path"]
            or row["type"] not in ("tree", "blob", "commit")
            or not _is_hex(row["oid"], (40, 64))
        ):
            return [f"{where} holds a row that is not a path, an object type and an object id"]
        paths.append(row["path"])
    if paths != sorted(set(paths)):
        return [f"{where} is not sorted by path without a repeat"]
    if LLVM_SOURCE_TREE not in paths:
        return [f"{where} does not name {LLVM_SOURCE_TREE}"]
    return []


def _llvm_build_record_errors(value: object) -> list[str]:
    """Why `value` is not an LLVM build record; empty when it is one.

    scripts/lib/stage_receipt_provenance.py `llvm_build_record_errors` is the
    same rule for promotion (see _recreator_invocation_errors for why there are
    two); recreate_bootstrap_test.py runs both on the same records.
    """
    if not isinstance(value, dict):
        return ["the LLVM build record is not an object"]
    errors: list[str] = []
    if set(value) != LLVM_BUILD_RECORD_KEYS:
        errors.append(
            "the LLVM build record does not hold exactly the keys "
            + ", ".join(sorted(LLVM_BUILD_RECORD_KEYS))
        )
    if value.get("schema") != LLVM_BUILD_RECORD_SCHEMA:
        errors.append(f"the LLVM build record's schema is not {LLVM_BUILD_RECORD_SCHEMA}")
    if not _is_hex(value.get("built_at_commit"), (40, 64)):
        errors.append("the LLVM build record's built_at_commit is not a full commit id")
    if not isinstance(value.get("host"), str) or not value.get("host"):
        errors.append("the LLVM build record's host is not a host triple")
    for key in (
        "source_identity_sha256",
        "bootstrap_config_sha256",
        "native_authority_sha256",
        "output_fingerprint_sha256",
    ):
        if not _is_hex(value.get(key), (64,)):
            errors.append(f"the LLVM build record's {key} is not a sha256")
    row_errors = _llvm_source_rows_errors(
        value.get("source_paths"), "the LLVM build record's source_paths"
    )
    errors.extend(row_errors)
    if not row_errors and value.get("source_identity_sha256") != _llvm_source_identity_sha256(
        value["source_paths"]
    ):
        errors.append(
            "the LLVM build record's source_identity_sha256 is not the identity of its source_paths"
        )
    return errors


def _llvm_identity_errors(value: object, receipt: dict[str, object]) -> list[str]:
    """Why `value` is not the `llvm_identity` record of `receipt`; empty when it is.

    Its form and vocabulary, then its agreement with itself and with the
    receipt it is in: an identity is stated exactly when no reason against it
    is given; a stated in-tree identity quotes a build record for the same
    source identity and output, built for this receipt's host, bootstrap config
    and native authority (and at this receipt's commit when it says LLVM was
    built in this run); the identity of an external LLVM is never stated, and
    its record holds no source identity, output or build record
    (LLVM_EXTERNAL_REASON). Nothing is read from disk: comparing the record
    with the tree is _verify_llvm_identity.

    scripts/lib/stage_receipt_provenance.py `llvm_identity_errors` is the same
    rule for promotion; recreate_bootstrap_test.py runs both on the same records.
    """
    if not isinstance(value, dict):
        return ["llvm_identity is not an object"]
    errors: list[str] = []
    if set(value) != LLVM_IDENTITY_KEYS:
        errors.append(
            "llvm_identity does not hold exactly the keys " + ", ".join(sorted(LLVM_IDENTITY_KEYS))
        )
    if value.get("schema") != LLVM_IDENTITY_SCHEMA:
        errors.append(f"llvm_identity.schema is not {LLVM_IDENTITY_SCHEMA}")
    mode, provenance = value.get("mode"), value.get("provenance")
    if not isinstance(mode, str) or mode not in LLVM_PROVENANCE_OF_MODE:
        errors.append(
            f"llvm_identity.mode is {mode!r}, not one of " + ", ".join(LLVM_PROVENANCE_OF_MODE)
        )
    elif not isinstance(provenance, str) or provenance not in LLVM_PROVENANCE_OF_MODE[mode]:
        errors.append(
            f"llvm_identity.provenance is {provenance!r}; a record of mode {mode} says one of "
            + ", ".join(LLVM_PROVENANCE_OF_MODE[mode])
        )
    stated, reasons = value.get("identity_stated"), value.get("reasons")
    if not isinstance(stated, bool):
        errors.append("llvm_identity.identity_stated is neither true nor false")
    if not isinstance(reasons, list) or not all(isinstance(item, str) and item for item in reasons):
        errors.append("llvm_identity.reasons is not a list of sentences")
    elif isinstance(stated, bool) and stated == bool(reasons):
        errors.append(
            "llvm_identity.identity_stated and llvm_identity.reasons disagree: an identity is "
            "stated exactly when no reason against it is given"
        )
    rows, identity = value.get("source_paths"), value.get("source_identity_sha256")
    if rows == [] and identity is None:
        if stated is True:
            errors.append("llvm_identity states an identity without a source identity")
    else:
        row_errors = _llvm_source_rows_errors(rows, "llvm_identity.source_paths")
        errors.extend(row_errors)
        if not row_errors and identity != _llvm_source_identity_sha256(rows):
            errors.append(
                "llvm_identity.source_identity_sha256 is not the identity of llvm_identity.source_paths"
            )
    output_dirs, fingerprint = value.get("output_dirs"), value.get("output_fingerprint_sha256")
    if not isinstance(output_dirs, list) or not all(
        isinstance(item, str) and item for item in output_dirs
    ):
        errors.append("llvm_identity.output_dirs is not a list of paths")
    if fingerprint is not None and not _is_hex(fingerprint, (64,)):
        errors.append("llvm_identity.output_fingerprint_sha256 is neither null nor a sha256")
    record = value.get("build_record")
    if record is not None:
        errors.extend(_llvm_build_record_errors(record))
    if errors:
        return errors

    def of_receipt(section: str, key: str) -> object:
        table = receipt.get(section)
        return table.get(key) if isinstance(table, dict) else None

    if mode == "external":
        # Never stated, and nothing of this checkout or build directory stands
        # beside it as if it described that LLVM (LLVM_EXTERNAL_REASON).
        if stated:
            errors.append(
                "llvm_identity states the identity of an external LLVM: which sources an LLVM "
                "linked through --llvm-config was built from is never established"
            )
        if record is not None or fingerprint is not None or output_dirs:
            errors.append("llvm_identity of an external LLVM carries an in-tree output or build record")
        if rows != [] or identity is not None:
            errors.append(
                "llvm_identity of an external LLVM carries a source identity: this checkout's LLVM "
                "sources do not describe an LLVM linked through --llvm-config"
            )
    elif not stated:
        if record is not None:
            errors.append("llvm_identity quotes a build record for an identity it does not state")
    elif mode == "in-tree":
        if provenance not in ("built-in-this-run", "reused"):
            errors.append(f"llvm_identity states the identity of an LLVM whose provenance is {provenance}")
        if not output_dirs or fingerprint is None:
            errors.append("llvm_identity states the identity of an in-tree LLVM without its output")
        if record is None:
            errors.append("llvm_identity states the identity of an in-tree LLVM without a build record")
        else:
            for what, mine, recorded in (
                ("source identity", identity, record["source_identity_sha256"]),
                ("output", fingerprint, record["output_fingerprint_sha256"]),
                ("host", receipt.get("host"), record["host"]),
                (
                    "bootstrap config",
                    of_receipt("bootstrap_lineage", "config_sha256"),
                    record["bootstrap_config_sha256"],
                ),
                (
                    "native tool and SDK authority",
                    of_receipt("build_authority", "authority_sha256"),
                    record["native_authority_sha256"],
                ),
            ):
                if mine != recorded:
                    errors.append(f"llvm_identity's build record is for another {what} than this receipt's")
            if provenance == "built-in-this-run" and record["built_at_commit"] != of_receipt(
                "compiler", "source_commit"
            ):
                errors.append(
                    "llvm_identity says LLVM was built in this run, and its build record names "
                    "another commit than this receipt's"
                )
    else:
        errors.append("llvm_identity states the identity of an LLVM of unknown mode")
    return errors


def _exception_text(error: BaseException) -> str:
    """One line for a reason: the class is said for what str() alone does not explain."""
    if isinstance(error, (OSError, UnicodeError, json.JSONDecodeError)):
        return str(error)
    return f"{type(error).__name__}: {error}" if str(error) else type(error).__name__


def read_llvm_build_record(
    root: Path, host: str, *, build_root: Path | None = None,
) -> tuple[dict[str, object] | None, list[str]]:
    """(the build record beside the host's in-tree LLVM, why it is unusable).

    (None, []) when there is none: a directory built before this record
    existed, by a plain `x.py build`, or over a directory that was already
    there.

    NEVER RAISES, whatever is at that name. The documented build command runs
    this in every existing build directory and must go on as it did before the
    record existed, and a verification must not die on it either: a file that
    is too large to be a record is not read, and one that cannot be read or
    parsed (not UTF-8, not JSON, nested deeper than the parser's stack: the
    re-read of 2026-10-13 crashed the build with 200000 `[`) is an unusable
    record with the reason, like any other.
    """
    try:
        path = _llvm_out_dir(root, host, **({"build_root": build_root} if build_root is not None else {})) / LLVM_BUILD_RECORD_NAME
        try:
            metadata = os.lstat(path)
        except FileNotFoundError:
            return None, []
        except OSError as error:
            return None, [f"it cannot be inspected: {error}"]
        if not stat.S_ISREG(metadata.st_mode):
            return None, ["it is not a regular file"]
        if metadata.st_size > LLVM_BUILD_RECORD_MAX_BYTES:
            return None, [
                f"it is {metadata.st_size} bytes, more than the {LLVM_BUILD_RECORD_MAX_BYTES} a "
                "build record is read up to"
            ]
        try:
            # Bounded as well: the file can grow between the lstat and the read.
            with open(path, "rb") as handle:
                raw = handle.read(LLVM_BUILD_RECORD_MAX_BYTES + 1)
            if len(raw) > LLVM_BUILD_RECORD_MAX_BYTES:
                return None, [
                    f"it is more than the {LLVM_BUILD_RECORD_MAX_BYTES} bytes a build record is "
                    "read up to"
                ]
            value = json.loads(raw.decode("utf-8"))
        except (OSError, UnicodeError, ValueError) as error:
            return None, [f"it is not JSON: {error}"]
        errors = _llvm_build_record_errors(value)
        return (None, errors) if errors else (value, [])
    except Exception as error:  # noqa: BLE001 - see NEVER RAISES above
        # RecursionError (JSON nested past the parser's stack) and MemoryError
        # are what was met or can be; whatever else is not a record either.
        return None, [f"it could not be read as a build record: {_exception_text(error)}"]


def write_llvm_build_record(
    root: Path, host: str, record: dict[str, object], *, build_root: Path | None = None,
) -> None:
    """Leave `record` beside the in-tree LLVM it describes (its only writer)."""
    path = _llvm_out_dir(root, host, **({"build_root": build_root} if build_root is not None else {})) / LLVM_BUILD_RECORD_NAME
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def _llvm_mode(config_path: Path, host: str, llvm_config: str | None) -> tuple[str, list[str]]:
    """Which LLVM the bootstrap config makes x.py use, and why that is not known.

    The config is what x.py obeys. `--llvm-config` reaches it only when this
    script writes the file, and an existing config is reused as it is, so the
    argument alone does not say which LLVM gets linked: "external" needs the
    config to name the llvm-config this run was given (the one the build
    authority binds), "in-tree" needs it to name none and to set
    `llvm.download-ci-llvm = false`. Anything else is "unknown": which LLVM
    x.py links is not known, so no source identity and no build directory is
    recorded beside it (any of them may describe an LLVM the stage does not
    link). Only an in-tree LLVM can have its identity stated: "external" says
    which LLVM is linked and nothing of what it was built from
    (LLVM_EXTERNAL_REASON).

    A config that names an llvm-config other than the one this run binds IS
    an external LLVM, and is still "unknown", not "external": what "external"
    says beyond the mode is that the receipt's build authority binds that
    llvm-config executable, and it binds another one or none
    (DECISION_QUEUE, "a seal knows which LLVM it carries", the follow-up).

    So is a config with an `include` key, whatever the rest of it says. x.py
    merges the included files into the one it was given, and they supply every
    key that file leaves unset (src/bootstrap/src/core/config/toml/mod.rs):
    `[target.<host>] llvm-config`, and every `llvm.*` key LLVM is configured
    with. Only this one file is read here and only its sha256 is in the receipt
    (`bootstrap_lineage.config_sha256`), so with an `include` neither says
    which LLVM is linked nor how it was configured. The recreator's own configs
    have none.
    """
    import tomllib

    try:
        parsed = tomllib.loads(config_path.read_bytes().decode("utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        return "unknown", [f"the bootstrap config could not be read for its LLVM settings: {error}"]
    except (RecursionError, MemoryError) as error:
        # A file nested deeper than the parser's stack, or too large to hold.
        return "unknown", [
            "the bootstrap config could not be read for its LLVM settings: "
            + _exception_text(error)
        ]
    if "include" in parsed:
        return "unknown", [
            f"{config_path.name} has an `include` key: x.py merges the included files, which can "
            "name another llvm-config or configure LLVM differently, and neither this record nor "
            "the receipt's config digest covers them"
        ]
    targets, llvm = parsed.get("target"), parsed.get("llvm")
    target = targets.get(host) if isinstance(targets, dict) else None
    configured = target.get("llvm-config") if isinstance(target, dict) else None
    if configured is not None:
        if llvm_config is not None and configured == llvm_config:
            return "external", []
        return "unknown", [
            f"{config_path.name} links the external llvm-config {configured!r}, which is not the "
            f"one this run binds (--llvm-config {llvm_config!r})"
        ]
    if llvm_config is not None:
        return "unknown", [
            f"--llvm-config {llvm_config!r} was given, and {config_path.name}, reused as it is, "
            "does not name it: x.py would not link it"
        ]
    download = llvm.get("download-ci-llvm") if isinstance(llvm, dict) else None
    if download is not False:
        return "unknown", [
            f"{config_path.name} does not set llvm.download-ci-llvm = false (it is {download!r}): "
            "x.py may link a downloaded LLVM, which this record cannot identify"
        ]
    return "in-tree", []


# A preservation record is filesystem custody only, never LLVM build evidence.
EMPTY_LLVM_PRESERVATION = "llvm.preexisting-empty-fresh-seed"
_EMPTY_LLVM_STAT_FIELDS = (
    "st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns",
    "st_mode", "st_nlink", "st_uid", "st_gid", "st_flags",
)


def _empty_llvm_stat(metadata: os.stat_result) -> dict[str, int]:
    return {name: getattr(metadata, name, 0) for name in _EMPTY_LLVM_STAT_FIELDS}


def _open_empty_llvm_directory(name: str | Path, *, directory: int | None = None) -> int:
    descriptor = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=directory)
    try:
        metadata = os.fstat(descriptor)
        if metadata.st_uid != os.geteuid() or stat.S_IMODE(metadata.st_mode) & 0o022:
            raise RuntimeError(f"empty LLVM preservation requires an owned, non-writable-by-others directory: {name}")
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def _assert_empty_llvm_path_bound(name: str | Path, descriptor: int, *, parent: int | None = None) -> None:
    """An open inode alone does not bind the spelling advertised in custody records."""
    try:
        current = os.stat(name, dir_fd=parent, follow_symlinks=False)
        pinned = os.fstat(descriptor)
    except OSError as error:
        raise RuntimeError(f"empty LLVM preservation path or parent changed: {name}") from error
    if (not stat.S_ISDIR(current.st_mode)
            or (current.st_dev, current.st_ino) != (pinned.st_dev, pinned.st_ino)
            or current.st_uid != os.geteuid() or stat.S_IMODE(current.st_mode) & 0o022):
        raise RuntimeError(f"empty LLVM preservation path or parent changed: {name}")


def _empty_llvm_json(directory: int, name: str, value: dict | None = None, *, check_bound=None) -> bytes:
    if check_bound is not None:
        check_bound()
    flags = os.O_NOFOLLOW | (os.O_RDONLY if value is None else os.O_WRONLY | os.O_CREAT | os.O_EXCL)
    descriptor = os.open(name, flags, 0o600, dir_fd=directory)
    try:
        if check_bound is not None:
            check_bound()
        before = os.fstat(descriptor)
        if (not stat.S_ISREG(before.st_mode) or before.st_uid != os.geteuid()
                or before.st_nlink != 1 or stat.S_IMODE(before.st_mode) != 0o600):
            raise RuntimeError(f"unsafe empty LLVM preservation record: {name}")
        if value is not None:
            payload = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
            with os.fdopen(os.dup(descriptor), "wb") as stream:
                if check_bound is not None:
                    check_bound()
                stream.write(payload)
                stream.flush()
                os.fsync(stream.fileno())
            os.fsync(directory)
            if check_bound is not None:
                check_bound()
            return payload
        if before.st_size > 16384:
            raise RuntimeError(f"oversized empty LLVM preservation record: {name}")
        with os.fdopen(os.dup(descriptor), "rb") as stream:
            payload = stream.read(16385)
        if (len(payload) != before.st_size or _empty_llvm_stat(before) != _empty_llvm_stat(os.fstat(descriptor))
                or _empty_llvm_stat(before) != _empty_llvm_stat(os.stat(name, dir_fd=directory, follow_symlinks=False))):
            raise RuntimeError(f"empty LLVM preservation record changed while reading: {name}")
        return payload
    finally:
        os.close(descriptor)


def _validate_empty_llvm_preservation(directory: int, original: Path, preserved: Path, *, check_bound=None) -> None:
    """A retry may retain an exact completed empty inode; it grants no build identity."""
    if check_bound is not None:
        check_bound()
    if sorted(os.listdir(directory)) != ["completed.json", "intent.json", "llvm"]:
        raise RuntimeError(f"incomplete or unexpected empty LLVM preservation state: {preserved.parent}")
    payload = _empty_llvm_json(directory, "intent.json", check_bound=check_bound)
    intent = json.loads(payload)
    completed = json.loads(_empty_llvm_json(directory, "completed.json", check_bound=check_bound))
    if (not isinstance(intent, dict) or not isinstance(completed, dict)
            or set(intent) != {"schema", "scope", "original", "preserved", "before", "pid", "utc"}
            or set(completed) != {"schema", "intent_sha256", "after", "original_absent", "empty", "utc"}
            or intent.get("scope") != "retained filesystem custody only; no LLVM identity or proof"
            or type(intent.get("pid")) is not int or intent["pid"] <= 0
            or intent.get("schema") != "trust.empty-llvm-preservation-intent.v1"
            or intent.get("original") != str(original) or intent.get("preserved") != str(preserved)
            or completed.get("schema") != "trust.empty-llvm-preservation-complete.v1"
            or completed.get("intent_sha256") != hashlib.sha256(payload).hexdigest()
            or completed.get("original_absent") is not True or completed.get("empty") is not True):
        raise RuntimeError(f"foreign or malformed empty LLVM preservation record: {preserved.parent}")
    before, after = intent.get("before"), completed.get("after")
    for row in (before, after):
        if (not isinstance(row, dict) or set(row) != set(_EMPTY_LLVM_STAT_FIELDS)
                or any(type(value) is not int for value in row.values())):
            raise RuntimeError(f"malformed empty LLVM directory identity: {preserved.parent}")
    if any(before[key] != after[key] for key in _EMPTY_LLVM_STAT_FIELDS if key != "st_ctime_ns"):
        raise RuntimeError(f"empty LLVM preservation changed more than rename ctime: {preserved.parent}")
    descriptor = _open_empty_llvm_directory("llvm", directory=directory)
    try:
        if (os.listdir(descriptor) or _empty_llvm_stat(os.fstat(descriptor)) != after
                or _empty_llvm_stat(os.stat("llvm", dir_fd=directory, follow_symlinks=False)) != after):
            raise RuntimeError(f"preserved empty LLVM inode changed: {preserved}")
        _assert_empty_llvm_path_bound(preserved, descriptor)
        if check_bound is not None:
            check_bound()
    finally:
        os.close(descriptor)


def _empty_llvm_exclusive_rename(parent: int):
    """Refuse unsupported recovery before creating any preservation state."""
    if sys.platform != "darwin":
        raise RuntimeError("empty LLVM preservation requires supported atomic exclusive rename")
    import ctypes

    try:
        library = ctypes.CDLL(None, use_errno=True)
        rename = library.renameatx_np
        attributes = library.fgetattrlist
    except (AttributeError, OSError) as error:
        raise RuntimeError("empty LLVM preservation requires atomic exclusive rename APIs") from error
    rename.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    rename.restype = ctypes.c_int
    options_type = ctypes.c_uint if ctypes.sizeof(ctypes.c_void_p) == 8 else ctypes.c_ulong
    attributes.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_size_t, options_type]
    attributes.restype = ctypes.c_int

    # Darwin SDK sys/attr.h: ATTR_VOL_INFO | ATTR_VOL_CAPABILITIES,
    # VOL_CAPABILITIES_INTERFACES, and VOL_CAP_INT_RENAME_EXCL. Query the
    # pinned parent volume, not a guessed filesystem name or same-path rename
    # (Darwin can return success for that no-op even with RENAME_EXCL).
    class AttrList(ctypes.Structure):
        _fields_ = [("bitmapcount", ctypes.c_ushort), ("reserved", ctypes.c_uint16),
                    ("commonattr", ctypes.c_uint32), ("volattr", ctypes.c_uint32),
                    ("dirattr", ctypes.c_uint32), ("fileattr", ctypes.c_uint32),
                    ("forkattr", ctypes.c_uint32)]

    request = AttrList(bitmapcount=5, volattr=0x80020000)
    capabilities = (ctypes.c_uint32 * 9)()  # length, capabilities[4], valid[4]
    if attributes(parent, ctypes.byref(request), ctypes.byref(capabilities), ctypes.sizeof(capabilities), 0) != 0:
        error = ctypes.get_errno()
        raise OSError(error, "could not establish atomic exclusive rename support: " + os.strerror(error))
    if capabilities[0] != ctypes.sizeof(capabilities) or not (capabilities[2] & capabilities[6] & 0x00080000):
        raise RuntimeError("empty LLVM preservation volume lacks valid atomic exclusive rename support")

    def move(source: int, destination: int) -> None:
        # Darwin SDK sys/stdio.h and rename(2): RENAME_EXCL=4 atomically
        # refuses an existing destination. Never fall back to plain rename.
        if rename(source, b"llvm", destination, b"llvm", 0x00000004) != 0:
            error = ctypes.get_errno()
            raise OSError(error, "exclusive empty LLVM preservation rename: " + os.strerror(error), "llvm")

    return move


def _mark_empty_llvm_completion_refused(directory: int, error: BaseException) -> None:
    """Retain failed closure explicitly; never erase or adopt a partial completion."""
    try:
        os.stat("completed.json", dir_fd=directory, follow_symlinks=False)
    except FileNotFoundError:
        return
    except BaseException as marking_error:
        _add_exception_note(error, f"Could not inspect refused empty LLVM completion: {marking_error}")
        return
    try:
        _empty_llvm_json(directory, "refused.json", {
            "schema": "trust.empty-llvm-preservation-refused.v1",
            "reason": "completion was not accepted; preserve all custody state",
        })
    except BaseException as marking_error:
        _add_exception_note(error, f"Could not mark refused empty LLVM completion: {marking_error}")


def _preserve_empty_llvm_locked(parent: int, original: Path, retained: Path, *, check_ancestors, bind_container) -> Path | None:
    """Called only while this owner holds the existing exclusive build-tree lock."""
    def check_container(directory):
        bind_container(directory)
        check_ancestors()
        _assert_empty_llvm_path_bound(EMPTY_LLVM_PRESERVATION, directory, parent=parent)
        _assert_empty_llvm_path_bound(retained, directory)

    check_ancestors()
    if os.path.lexists(retained):
        directory = _open_empty_llvm_directory(EMPTY_LLVM_PRESERVATION, directory=parent)
        try:
            if stat.S_IMODE(os.fstat(directory).st_mode) != 0o700:
                raise RuntimeError(f"empty LLVM preservation container is not private: {retained}")
            check_container(directory)
            _validate_empty_llvm_preservation(directory, original, retained / "llvm",
                                              check_bound=lambda: check_container(directory))
            if not os.path.lexists(original):
                check_container(directory)
                print(f"  retained earlier empty LLVM inode -> {retained / 'llvm'}")
                check_container(directory)
                return retained / "llvm"
        finally:
            os.close(directory)
    if not os.path.lexists(original):
        check_ancestors()
        return None
    descriptor = _open_empty_llvm_directory("llvm", directory=parent)
    try:
        before = _empty_llvm_stat(os.fstat(descriptor))
        if os.listdir(descriptor):
            check_ancestors()
            return None  # Existing output is ALWAYS left to the unchanged strict validator.
        if os.path.lexists(retained):
            raise RuntimeError(f"another empty LLVM directory exists beside retained evidence: {retained}")
        check_ancestors()
        move = _empty_llvm_exclusive_rename(parent)
        check_ancestors()
        # Exclusive mkdir gives this lease a new private destination, never an
        # old backup or evidence directory. Nothing is removed on a failure.
        os.mkdir(EMPTY_LLVM_PRESERVATION, 0o700, dir_fd=parent)
        directory = _open_empty_llvm_directory(EMPTY_LLVM_PRESERVATION, directory=parent)
        try:
            check_container(directory)
            if stat.S_IMODE(os.fstat(directory).st_mode) != 0o700:
                raise RuntimeError(f"empty LLVM preservation container is not private: {retained}")
            if os.listdir(directory):
                raise RuntimeError(f"empty LLVM preservation destination changed: {retained}")
            intent = {
                "schema": "trust.empty-llvm-preservation-intent.v1",
                "scope": "retained filesystem custody only; no LLVM identity or proof",
                "original": str(original), "preserved": str(retained / "llvm"),
                "before": before, "pid": os.getpid(),
                "utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            }
            payload = _empty_llvm_json(directory, "intent.json", intent,
                                       check_bound=lambda: check_container(directory))
            os.fsync(parent)  # Retained container and intent must be durable before the move.
            # The normal lock excludes cooperating build writers. Recheck the
            # exact owned inode, metadata and ALL entries immediately before
            # rename; an empty installed-output fingerprint is insufficient.
            if (os.listdir(descriptor) or _empty_llvm_stat(os.fstat(descriptor)) != before
                    or _empty_llvm_stat(os.stat("llvm", dir_fd=parent, follow_symlinks=False)) != before):
                raise RuntimeError(f"empty LLVM input changed before preservation: {original}")
            if sorted(os.listdir(directory)) != ["intent.json"]:
                raise RuntimeError(f"empty LLVM preservation destination changed: {retained}")
            check_container(directory)
            move(parent, directory)
            check_container(directory)
            os.fsync(parent)
            os.fsync(directory)
            after = _empty_llvm_stat(os.fstat(descriptor))
            if (os.listdir(descriptor) or os.path.lexists(original)
                    or after != _empty_llvm_stat(os.stat("llvm", dir_fd=directory, follow_symlinks=False))
                    or any(before[key] != after[key] for key in before if key != "st_ctime_ns")):
                raise RuntimeError(f"empty LLVM preservation is uncertain; retain {retained}")
            check_container(directory)
            _empty_llvm_json(directory, "completed.json", {
                "schema": "trust.empty-llvm-preservation-complete.v1",
                "intent_sha256": hashlib.sha256(payload).hexdigest(), "after": after,
                "original_absent": True, "empty": True,
                "utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            }, check_bound=lambda: check_container(directory))
            check_container(directory)
            _validate_empty_llvm_preservation(directory, original, retained / "llvm",
                                              check_bound=lambda: check_container(directory))
            check_container(directory)
            print(f"  preserved owned empty LLVM inode -> {retained / 'llvm'}")
            check_container(directory)
            return retained / "llvm"
        except BaseException as error:
            # Keep a failed post-write observation unadoptable on retry.
            _mark_empty_llvm_completion_refused(directory, error)
            _add_exception_note(error, f"Preserve all empty LLVM recovery state, including displaced directories; advertised path {retained} may have changed. No rollback or deletion was attempted.")
            raise
        finally:
            os.close(directory)
    finally:
        os.close(descriptor)


def preserve_empty_llvm_for_fresh_seed(
    root: Path, host: str, llvm_config: str | None, config_path: Path,
) -> Path | None:
    """Only main's strict fresh-seed build calls this, before LLVM observation.

    Preserve an actually empty, owned directory under an exclusive normal build
    lease. This never changes an LLVM validator or infers absence from a receipt:
    the existing observer must subsequently read the actual filesystem anew.
    The lease covers this recovery only; x.py retains its normal build lease.
    """
    mode, reasons = _llvm_mode(config_path, host, llvm_config)
    if mode != "in-tree" or reasons or os.name != "posix":
        return None
    if not root.is_absolute():
        raise RuntimeError("empty LLVM preservation requires an absolute owned checkout")
    if not host or Path(host).parts != (host,) or host in {".", ".."}:
        raise RuntimeError(f"unsafe host component for empty LLVM preservation: {host!r}")
    descriptors = []
    retained_descriptors = []
    try:
        try:
            root_fd = _open_empty_llvm_directory(root)
            descriptors.append(root_fd)
            build_name = "build"
            build_link = None
            if (root / "build").is_symlink():
                if not is_sanctioned_build_link(root):
                    raise RuntimeError("empty LLVM preservation refuses an unsanctioned build link")
                build_name = BUILD_NOINDEX
                build_link = (_empty_llvm_stat(os.stat("build", dir_fd=root_fd, follow_symlinks=False)),
                              os.readlink("build", dir_fd=root_fd))
            build_fd = _open_empty_llvm_directory(build_name, directory=root_fd)
            descriptors.append(build_fd)
            parent = _open_empty_llvm_directory(host, directory=build_fd)
            descriptors.append(parent)
        except FileNotFoundError:
            return None  # No parent/output exists; do not create a recovery namespace.
        original = root / "build" / host / "llvm"
        retained = original.with_name(EMPTY_LLVM_PRESERVATION)
        if not os.path.lexists(original) and not os.path.lexists(retained):
            return None
        if os.path.lexists(original) and not os.path.lexists(retained):
            probe = _open_empty_llvm_directory("llvm", directory=parent)
            try:
                if os.listdir(probe):
                    return None  # No recovery: retain the existing observation/refusal flow.
            finally:
                os.close(probe)
        selected_manager = os.environ.get("TRUST_BUILD_TREE_MANAGER_TARGO")
        if selected_manager is not None and (
            not os.path.isabs(selected_manager)
            or os.path.realpath(selected_manager) != selected_manager
            or not os.path.isfile(selected_manager)
            or not os.access(selected_manager, os.X_OK)
        ):
            raise RuntimeError("explicit build-tree manager must be a physical executable path")
        native_manager = [selected_manager if selected_manager is not None else os.environ.get("TARGO", "targo"),
                          "trust", "repo", "lock"]
        environment = os.environ.copy()
        for name in ("TRUST_BUILD_LOCK_TOKEN", "TRUST_BUILD_LOCK_BREAK", "TRUST_BUILD_LOCK_WAIT", "TRUST_REPO"):
            environment.pop(name, None)
        environment["TRUST_REPO"] = str(root)
        try:
            if selected_manager is not None:
                protocol = subprocess.run(
                    [*native_manager, "--protocol"], cwd=root, env=environment,
                    capture_output=True, text=True, timeout=30,
                )
                if protocol.returncode != 0 or protocol.stdout != "trust-build-tree-manager-v2\n":
                    raise RuntimeError("explicit build-tree manager refused protocol v2; no fallback")
            acquired = subprocess.run(
                [*native_manager, "acquire", "--repo-root", str(root), "--kind", "build", "--purpose", "preserve owned empty LLVM",
                 "--pid", str(os.getpid()), "--wait", "0"],
                cwd=root, env=environment, capture_output=True, text=True, timeout=30,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise RuntimeError(f"empty LLVM preservation requires its own normal build lease: {error}") from error
        token = acquired.stdout.strip()
        if (acquired.returncode != 0 or acquired.stdout != token + "\n"
                or not re.fullmatch(r"[A-Za-z0-9._-]{1,256}", token)):
            raise RuntimeError(f"empty LLVM preservation requires its own normal build lease: {acquired.stderr.strip()}")
        active_error = None
        preserved_result = None
        try:
            def check_ancestors():
                _assert_empty_llvm_path_bound(root, root_fd)
                _assert_empty_llvm_path_bound(build_name, build_fd, parent=root_fd)
                _assert_empty_llvm_path_bound(host, parent, parent=build_fd)
                if build_link is not None:
                    current = os.stat("build", dir_fd=root_fd, follow_symlinks=False)
                    if (_empty_llvm_stat(current) != build_link[0]
                            or os.readlink("build", dir_fd=root_fd) != build_link[1]):
                        raise RuntimeError("empty LLVM preservation path changed: sanctioned build alias")
                _assert_empty_llvm_path_bound(original.parent, parent)

            def bind_container(directory):
                if not retained_descriptors:
                    pinned = os.dup(directory)
                    retained_descriptors.append(pinned)
                    descriptors.append(pinned)
                before, current = os.fstat(retained_descriptors[0]), os.fstat(directory)
                if (before.st_dev, before.st_ino) != (current.st_dev, current.st_ino):
                    raise RuntimeError("empty LLVM preservation path changed: retained container identity")

            def check_retained():
                check_ancestors()
                _assert_empty_llvm_path_bound(EMPTY_LLVM_PRESERVATION, retained_descriptors[0], parent=parent)
                _assert_empty_llvm_path_bound(retained, retained_descriptors[0])

            check_ancestors()
            preserved_result = _preserve_empty_llvm_locked(
                parent, original, retained, check_ancestors=check_ancestors, bind_container=bind_container)
            return preserved_result
        except BaseException as error:
            active_error = error
            raise
        finally:
            try:
                # A fresh native command must resolve the SAME checkout whose
                # descriptor this operation retained. A free replacement tree
                # cannot establish release of our displaced original lease.
                _assert_empty_llvm_path_bound(root, root_fd)
                released = subprocess.run([*native_manager, "release", token, "--repo-root", str(root)], cwd=root,
                                          env=environment, capture_output=True, text=True, timeout=30)
                if released.returncode != 0 or released.stdout or released.stderr:
                    raise RuntimeError(f"empty LLVM preservation normal lease release refused: {released.stderr.strip()}")
                if active_error is None:
                    # Keep the container inode pinned across lease release and
                    # validate the advertised spelling at the public return boundary.
                    check_ancestors()
                    if preserved_result is not None and retained_descriptors:
                        check_retained()
                        _validate_empty_llvm_preservation(retained_descriptors[0], original, retained / "llvm",
                                                          check_bound=check_retained)
                        if os.path.lexists(original):
                            raise RuntimeError("empty LLVM preservation path changed: original output reappeared")
                        check_retained()
            except BaseException as error:
                if active_error is None:
                    if preserved_result is not None and retained_descriptors:
                        _mark_empty_llvm_completion_refused(retained_descriptors[0], error)
                    raise
                _add_exception_note(active_error, f"Empty LLVM recovery lease release also failed: {error}")
    finally:
        for descriptor in reversed(descriptors):
            os.close(descriptor)


def capture_llvm_before_build(
    root: Path, host: str, llvm_config: str | None, config_path: Path,
    *, build_root: Path | None = None,
    mint_configuration: dict[str, object] | None = None,
) -> dict[str, object]:
    """What can be observed, before x.py runs, of the LLVM this build will carry.

    Read-only. The audit compares it with what is there after the build
    (bind_llvm_identity); llvm_identity_obstacle_rows reads it for what main()
    prints, and for the refusal `--require-llvm-identity` asks for.

    NEVER RAISES. It answers for every build that writes a receipt, the
    documented `--require-seed --fresh-seed` in every existing build directory
    among them, and main() runs it between setting the stage0 aside and
    starting x.py: no state of the build directory or of the config may stop
    that build or change what it does. An observation that could not be made,
    for ANY reason, is one of unknown mode with the reason (llvm_unobserved),
    and the build goes on as it would have without the record. Met or
    reachable: OSError (a listing, a read, a link, git that cannot be started),
    UnicodeError and ValueError (a config or a build record that is not UTF-8,
    TOML or JSON), RecursionError (one nested deeper than its parser's stack),
    MemoryError (a file too large to hold), subprocess.TimeoutExpired (git);
    most are turned into a reason where they occur, and `except Exception`
    here is for the rest and for what nobody listed.

    Only an in-tree LLVM has a source identity to capture. This checkout's
    src/llvm-project does not describe an external one (LLVM_EXTERNAL_REASON)
    and is not known to describe one of unknown mode (_llvm_mode), so for
    either git is not asked and `source` holds none.
    """
    try:
        if mint_configuration is None:
            mode, mode_reasons = _llvm_mode(config_path, host, llvm_config)
        else:
            # The mint owner's complete closure excludes external LLVM and
            # binds its fixed --set llvm.download-ci-llvm=false. A generated
            # comment is no authority, and a raw root-file parse is insufficient.
            _validated_mint_configuration(root, host, config_path, mint_configuration)
            if llvm_config is not None:
                raise ValueError("mint configuration cannot bind an external --llvm-config")
            mode, mode_reasons = "in-tree", []
        output: dict[str, object] | None = None
        record: dict[str, object] | None = None
        record_errors: list[str] = []
        if mode == "in-tree":
            layout = {"build_root": build_root} if build_root is not None else {}
            output = capture_llvm_output(root, host, **layout)
            if output["present"]:
                record, record_errors = read_llvm_build_record(root, host, **layout)
        return {
            "mode": mode,
            "mode_reasons": mode_reasons,
            "source": capture_llvm_source_identity(root) if mode == "in-tree" else _llvm_no_source(),
            "output": output,
            "build_record": record,
            "build_record_errors": record_errors,
        }
    except Exception as error:  # noqa: BLE001 - see NEVER RAISES above
        return llvm_unobserved(error)


def _llvm_no_source() -> dict[str, object]:
    """capture_llvm_source_identity's shape for "no source identity was taken"."""
    return {"paths": [], "identity_sha256": None, "clean": False, "errors": []}


def llvm_unobserved(error: BaseException) -> dict[str, object]:
    """capture_llvm_before_build's answer when the observation itself failed with `error`."""
    return {
        "mode": "unknown",
        "mode_reasons": [
            f"the LLVM this build carries could not be observed: {_exception_text(error)}"
        ],
        "unobserved": True,
        "source": _llvm_no_source(),
        "output": None,
        "build_record": None,
        "build_record_errors": [],
    }


def _llvm_reuse_reasons(
    record: object,
    record_errors: object,
    *,
    source: dict[str, object],
    fingerprint: object,
    host: str,
    config_sha256: object,
    native_authority_sha256: object,
) -> list[str]:
    """Why the build record beside an LLVM that is there is not evidence for this run."""
    if record_errors:
        return ["its build record is unusable: " + "; ".join(str(item) for item in record_errors)]
    if not isinstance(record, dict):
        return [
            f"it holds no build record ({LLVM_BUILD_RECORD_NAME}): it was built before the "
            "recreator wrote one, by a plain x.py build, or over a directory that was already there"
        ]
    reasons: list[str] = []
    if record["source_identity_sha256"] != source["identity_sha256"]:
        reasons.append(
            f"its build record is for LLVM source identity {str(record['source_identity_sha256'])[:12]} "
            f"(built at commit {str(record['built_at_commit'])[:12]}), and this tree's is "
            f"{str(source['identity_sha256'])[:12]}"
        )
    for what, recorded, mine in (
        ("host", record["host"], host),
        ("bootstrap config", record["bootstrap_config_sha256"], config_sha256),
        ("native tool and SDK authority", record["native_authority_sha256"], native_authority_sha256),
    ):
        if recorded != mine:
            reasons.append(
                f"its build record is for another {what} ({str(recorded)[:12]}; this run's is "
                f"{str(mine)[:12]})"
            )
    if record["output_fingerprint_sha256"] != fingerprint:
        reasons.append(
            "its installed files are not the ones its build record fingerprints: they changed "
            "after that build"
        )
    return reasons


def _llvm_uncovered_reasons(output: dict[str, object]) -> list[str]:
    return [
        f"{path} is there: x.py builds it from src/llvm-project too, and this record does not cover it"
        for path in output["uncovered"]
    ]


def _llvm_source_reasons(source: dict[str, object]) -> list[str]:
    if source["errors"]:
        return [str(error) for error in source["errors"]]
    if not source["clean"]:
        return [
            "something under " + ", ".join(LLVM_SOURCE_IDENTITY_PATHS) + " is staged, modified or "
            "untracked: HEAD's object ids are not what gets compiled"
        ]
    return []


# The kinds of obstacle, by what would remove one (llvm_identity_refusal).
LLVM_OBSTACLE_UNOBSERVED = "unobserved"
LLVM_OBSTACLE_EXTERNAL = "external"
LLVM_OBSTACLE_CONFIG = "config"
LLVM_OBSTACLE_SOURCE = "source"
LLVM_OBSTACLE_OUTPUT = "output"
LLVM_OBSTACLE_UNCOVERED = "uncovered"
LLVM_OBSTACLE_REUSE = "reuse"


def llvm_identity_obstacle_rows(
    before: dict[str, object],
    *,
    host: str,
    config_sha256: object,
    native_authority_sha256: object,
) -> list[tuple[str, str]]:
    """(kind, reason) for each thing known, before x.py runs, to keep this build from stating its LLVM.

    Empty when nothing stands against it: an in-tree LLVM x.py will build from
    nothing, or one that is there, stamped, with a build record that is
    evidence for this run. Never empty for an external LLVM: its identity is
    never stated (LLVM_EXTERNAL_REASON), and that one row is all there is to
    say of it. Nor for one of unknown mode: the config's reasons are its rows,
    and nothing of this checkout's LLVM sources or build directory is one,
    because neither is known to be what the stage links (_llvm_mode); once
    the config says in-tree, the next run names what else stands in the way.
    What the build then does is judged again afterwards
    (bind_llvm_identity), and one thing can still be found only then: a stamp
    that is there and that x.py does not accept (written while the LLVM sources
    were modified) makes x.py build over the directory, which this script does
    not predict because it does not compute x.py's stamp.
    """
    source = before["source"]
    if before.get("unobserved"):
        # Nothing was observed, so nothing else is known to be in the way.
        return [(LLVM_OBSTACLE_UNOBSERVED, str(reason)) for reason in before["mode_reasons"]]
    if before["mode"] == "external":
        # This checkout's LLVM sources and build directory are not what such a
        # stage carries, so nothing about them is an obstacle or a remedy.
        return [(LLVM_OBSTACLE_EXTERNAL, LLVM_EXTERNAL_REASON)]
    rows = [(LLVM_OBSTACLE_CONFIG, str(reason)) for reason in before["mode_reasons"]]
    if before["mode"] != "in-tree":
        return list(dict.fromkeys(rows))
    rows += [(LLVM_OBSTACLE_SOURCE, reason) for reason in _llvm_source_reasons(source)]
    output = before["output"]
    if isinstance(output, dict):
        rows += [(LLVM_OBSTACLE_OUTPUT, str(error)) for error in output["errors"]]
        rows += [(LLVM_OBSTACLE_UNCOVERED, reason) for reason in _llvm_uncovered_reasons(output)]
        if output["present"]:
            where = " and ".join(output["dirs"])
            if not output["stamp_present"]:
                rows.append(
                    (
                        LLVM_OBSTACLE_REUSE,
                        f"{where} is there without the stamp x.py leaves when a build completes, so "
                        "x.py will run LLVM's build over it: over objects this run did not watch "
                        "being compiled",
                    )
                )
            rows += [
                (LLVM_OBSTACLE_REUSE, f"{where} is there and x.py will use it, and {reason}")
                for reason in _llvm_reuse_reasons(
                    before["build_record"],
                    before["build_record_errors"],
                    source=source,
                    fingerprint=output["fingerprint_sha256"],
                    host=host,
                    config_sha256=config_sha256,
                    native_authority_sha256=native_authority_sha256,
                )
            ]
    return list(dict.fromkeys(rows))


def llvm_identity_obstacles(
    before: dict[str, object],
    *,
    host: str,
    config_sha256: object,
    native_authority_sha256: object,
) -> list[str]:
    """The reasons of llvm_identity_obstacle_rows, without their kinds."""
    return [
        reason
        for _kind, reason in llvm_identity_obstacle_rows(
            before,
            host=host,
            config_sha256=config_sha256,
            native_authority_sha256=native_authority_sha256,
        )
    ]


def llvm_before_report(host: str, before: dict[str, object], obstacles: list[str]) -> list[str]:
    """What main() prints of the pre-build observation."""
    source = before["source"]
    identity = source["identity_sha256"]
    if before.get("unobserved"):
        return [f"not observed: {reason}" for reason in obstacles]
    if before["mode"] != "in-tree":
        # No source identity line: this checkout's src/llvm-project is not what
        # an LLVM linked through --llvm-config was built from, and is not known
        # to be what one of unknown mode was.
        return [
            f"mode: {before['mode']}",
            *(f"its identity cannot be stated: {reason}" for reason in obstacles),
        ]
    lines = [
        f"mode: {before['mode']}",
        (
            f"source identity: {identity} ({LLVM_SOURCE_TREE} tree "
            f"{_llvm_source_tree_oid(source['paths'])})"
            if identity
            else "source identity: not established"
        ),
    ]
    output = before["output"]
    if isinstance(output, dict):
        record = before["build_record"]
        where = " and ".join(output["dirs"])
        if not output["present"] and output["errors"]:
            # Something is at that path and it is not a directory this script
            # reads (a link to an LLVM elsewhere, say): x.py will use whatever
            # it leads to, so "absent" would be false.
            lines.append(
                f"build/{host}/llvm: not observed (the reason is below); x.py uses what is there"
            )
        elif not output["present"]:
            lines.append(f"build/{host}/llvm: absent, so x.py builds LLVM in this run")
        elif not obstacles and isinstance(record, dict):
            lines.append(
                f"{where}: present, with a build record that is evidence for this run "
                f"(built at commit {record['built_at_commit']})"
            )
        else:
            lines.append(f"{where}: present")
    lines.extend(f"its identity cannot be stated: {reason}" for reason in obstacles)
    return lines


def observe_llvm_before_build(
    root: Path,
    host: str,
    llvm_config: str | None,
    config_path: Path,
    *,
    config_sha256: object,
    native_authority_sha256: object,
) -> tuple[dict[str, object], list[tuple[str, str]], list[str]]:
    """main()'s step before x.py: (the observation, its obstacle rows, the lines to print).

    NEVER RAISES. main() calls it with the stage0 that `--fresh-seed` set aside
    not yet put back, in every provenance build, the documented one among them;
    an exception here would end that build where origin/main's goes on, and
    leave the stage0 aside. capture_llvm_before_build already answers for what
    the build directory and the config can do to it; this also holds the two
    functions that only read its answer, so that no fault of this record, of
    any kind, can reach a build that did not ask about its LLVM. What could
    not be worked out is "not observed", which `--require-llvm-identity`
    refuses (and puts the stage0 back) and every other build prints and
    passes.
    """
    try:
        before = capture_llvm_before_build(root, host, llvm_config, config_path)
        rows = llvm_identity_obstacle_rows(
            before,
            host=host,
            config_sha256=config_sha256,
            native_authority_sha256=native_authority_sha256,
        )
        return before, rows, llvm_before_report(host, before, [reason for _kind, reason in rows])
    except Exception as error:  # noqa: BLE001 - see NEVER RAISES above
        before = llvm_unobserved(error)
        reasons = [str(reason) for reason in before["mode_reasons"]]
        return (
            before,
            [(LLVM_OBSTACLE_UNOBSERVED, reason) for reason in reasons],
            [f"not observed: {reason}" for reason in reasons],
        )


def llvm_identity_refusal(
    root: Path,
    host: str,
    before: dict[str, object],
    rows: list[tuple[str, str]],
    invocation: list[str],
    config_path: Path,
) -> str:
    """The refusal of a `--require-llvm-identity` build that could not state its LLVM's identity.

    `rows` are llvm_identity_obstacle_rows' answer, not empty. Every kind of
    obstacle among them gets the command that removes it, or the statement that
    no single command does. An external LLVM is the one refusal that does not
    end in "run the same command again": the same command links the same LLVM.
    """
    lines = [
        "",
        "Refusing to build: --require-llvm-identity asks that this build state the identity of",
        "the LLVM it carries, and it is known now that it could not:",
        *(f"  - {reason}" for _kind, reason in rows),
    ]
    kinds = {kind for kind, _reason in rows}
    output = before["output"]
    if LLVM_OBSTACLE_REUSE in kinds and isinstance(output, dict):
        lines += [
            "x.py rebuilds the in-tree LLVM when HEAD:src/llvm-project moves from the tree recorded",
            "beside it, but it keeps an LLVM that cannot say what it was built from (one built before",
            "that record, whose own build header names no commit this checkout has), and a change",
            "to src/bootstrap, src/version, the bootstrap config or the native tools rebuilds none.",
            "So the recreator states an in-tree LLVM's identity only for one it watched being built",
            "from nothing, or one whose directory carries the record of such a build for the same",
            "LLVM sources, bootstrap config and native tools.",
            "Have this run build LLVM from nothing (it then leaves that record, and later runs in",
            "this build directory reuse the LLVM on it):",
            "    rm -rf " + " ".join(shlex.quote(str(root / path)) for path in output["dirs"]),
            "(A fresh checkout or build directory does the same and leaves this one as it is.)",
        ]
    if LLVM_OBSTACLE_UNCOVERED in kinds and isinstance(output, dict):
        lines += [
            "x.py built other things from src/llvm-project that this record does not fingerprint.",
            "If the bootstrap config no longer builds them (the recreator's own does not):",
            "    rm -rf " + " ".join(shlex.quote(str(root / path)) for path in output["uncovered"]),
            "For a config that does build them no single command applies: such a build cannot",
            "state its LLVM's identity with this record.",
        ]
    if LLVM_OBSTACLE_OUTPUT in kinds:
        lines += [
            f"No single command applies to what is at build/{host}/llvm (or build/{host}/lld): the",
            "recreator states the identity only of an LLVM in a directory of this build tree that",
            "it can read whole. If it is a link, remove the link (not what it points at); if it",
            "cannot be read, fix its permissions.",
        ]
    if LLVM_OBSTACLE_SOURCE in kinds:
        lines += [
            "No single command applies to the LLVM sources: HEAD's object ids are the identity of",
            "what is compiled only when nothing under them differs from HEAD. Commit, or remove,",
            "what this lists:",
            "    git status --short --untracked-files=all -- " + " ".join(LLVM_SOURCE_IDENTITY_PATHS),
        ]
    if LLVM_OBSTACLE_UNOBSERVED in kinds:
        lines += [
            "No single command applies: the recreator could not read what it needs to observe the",
            "LLVM (the reason above is the system's). Make the bootstrap config and",
            f"build/{host}/llvm readable, or build in a fresh checkout.",
        ]
    if LLVM_OBSTACLE_CONFIG in kinds:
        lines += [
            f"No single command applies to the bootstrap config: {config_path} is what x.py obeys,",
            "and it must itself say that the in-tree LLVM is linked: `[llvm] download-ci-llvm =",
            f"false`, no `include`, and no `[target.{host}] llvm-config` (an LLVM linked through",
            "--llvm-config is never stated). Edit it, or drop --llvm-config and let the recreator",
            "write its own again with --force-config, which OVERWRITES that file.",
        ]
    if LLVM_OBSTACLE_EXTERNAL in kinds:
        # No `rm` and no "same command": the same command links the same LLVM.
        lines += [
            "No single command applies: nothing in this checkout or its build directory is in the",
            "way, and nothing removed from them would help. The claim needs a build WITHOUT",
            "--llvm-config, one that builds the in-tree LLVM (src/llvm-project) or reuses one with",
            "the record of such a build. Run this command again without --llvm-config, and with",
            f"--force-config if {config_path} names an llvm-config (it OVERWRITES that file).",
            "Without --require-llvm-identity this build goes ahead on the LLVM --llvm-config names,",
            "and its receipt says that the identity is not stated, and why.",
        ]
        return "\n".join(lines)
    lines += [
        "Then run the same command again:",
        f"    python3 scripts/recreate_bootstrap.py {shlex.join(invocation)}",
        "Without --require-llvm-identity the build goes ahead on the LLVM that is there, and its",
        "receipt says that the identity is not stated, and why.",
    ]
    return "\n".join(lines)


def bind_llvm_identity(
    root: Path,
    host: str,
    before: dict[str, object],
    *,
    commit: str,
    commit_before: str,
    config_sha256: object,
    native_authority_sha256: object,
    selected_llvm: object,
    inputs_stable: bool,
    build_root: Path | None = None,
) -> tuple[dict[str, object], dict[str, object] | None]:
    """(the receipt's `llvm_identity`, the build record to leave beside an LLVM this run built).

    `commit` is HEAD now and `commit_before` what it was before x.py ran. A
    build record names the commit its LLVM was built at, which is the commit
    LLVM's own build reads from git, so a HEAD that moved during the build
    leaves no record, even where the LLVM source identity did not move.

    `before` is capture_llvm_before_build's answer from before x.py ran. The
    second value is None unless this run watched build/<host>/llvm come into
    being and can state what it was built from; it is that LLVM's build record,
    which the record in the receipt quotes. For a reused LLVM the receipt
    quotes the record found beside it, when it is evidence for this run. An
    external LLVM (`--llvm-config`) is never stated, whatever `selected_llvm`,
    the build authority's row for the llvm-config, says of that executable.
    """
    if before.get("unobserved"):
        # Nothing was seen before x.py ran, so nothing seen now can be compared
        # with it: the one thing to say is why.
        return (
            _llvm_identity_of_no_statement("; ".join(str(reason) for reason in before["mode_reasons"])),
            None,
        )
    mode = str(before["mode"])
    if mode == "external":
        # Never stated, and nothing of this checkout stands beside it: neither
        # its LLVM source identity (git is not asked) nor an in-tree LLVM an
        # earlier build left in the build directory. See LLVM_EXTERNAL_REASON.
        reasons = [LLVM_EXTERNAL_REASON]
        if not isinstance(selected_llvm, dict) or selected_llvm.get("status") != "bound":
            reasons.append("the build authority did not bind the external llvm-config")
        if not inputs_stable:
            reasons.append(
                "the bootstrap config or the native tool and SDK authority changed during the build"
            )
        return (
            {
                "schema": LLVM_IDENTITY_SCHEMA,
                "mode": "external",
                "provenance": "external",
                "identity_stated": False,
                "reasons": reasons,
                "source_identity_sha256": None,
                "source_paths": [],
                "output_dirs": [],
                "output_fingerprint_sha256": None,
                "build_record": None,
            },
            None,
        )
    if mode != "in-tree":
        # Unknown: the config x.py obeys does not say which LLVM it links
        # (_llvm_mode). Never stated, and, as for an external LLVM, nothing of
        # this checkout stands beside it: its LLVM sources (git is not asked)
        # and its build directory may describe an LLVM the stage does not link.
        reasons = [str(reason) for reason in before["mode_reasons"]]
        if not inputs_stable:
            reasons.append(
                "the bootstrap config or the native tool and SDK authority changed during the build"
            )
        return (
            {
                "schema": LLVM_IDENTITY_SCHEMA,
                "mode": mode,
                "provenance": "unknown",
                "identity_stated": False,
                "reasons": list(dict.fromkeys(reasons)),
                "source_identity_sha256": None,
                "source_paths": [],
                "output_dirs": [],
                "output_fingerprint_sha256": None,
                "build_record": None,
            },
            None,
        )
    prior_source = before["source"]
    source = capture_llvm_source_identity(root)
    reasons = [str(reason) for reason in before["mode_reasons"]]
    reasons += _llvm_source_reasons(prior_source) + _llvm_source_reasons(source)
    if (source["paths"], source["identity_sha256"]) != (
        prior_source["paths"],
        prior_source["identity_sha256"],
    ):
        reasons.append("the LLVM source identity changed during the build")
    if not inputs_stable:
        reasons.append("the bootstrap config or the native tool and SDK authority changed during the build")
    provenance = "unknown"
    output_dirs: list[str] = []
    fingerprint: object = None
    record: dict[str, object] | None = None
    written: dict[str, object] | None = None
    if mode == "in-tree":
        prior = before["output"]
        output = capture_llvm_output(root, host, **({"build_root": build_root} if build_root is not None else {}))
        output_dirs, fingerprint = list(output["dirs"]), output["fingerprint_sha256"]
        where = " and ".join(output_dirs)
        reasons.extend(str(error) for error in (*prior["errors"], *output["errors"]))
        reasons.extend(_llvm_uncovered_reasons(output))
        if (
            fingerprint is None
            or not output["stamp_present"]
            or _repository_relative_path(root, _llvm_out_dir(root, host, **(
                {"build_root": build_root} if build_root is not None else {}
            ))) not in output_dirs
        ):
            reasons.append(
                f"x.py left no completed in-tree LLVM build in build/{host}/{LLVM_OUTPUT_ROOTS[0][0]}"
            )
        elif not prior["present"]:
            provenance = "built-in-this-run"
            if commit != commit_before:
                reasons.append(
                    "HEAD moved during the build, so no one commit is the one this LLVM was built at"
                )
            if not reasons:
                written = {
                    "schema": LLVM_BUILD_RECORD_SCHEMA,
                    "built_at_commit": commit,
                    "host": host,
                    "source_identity_sha256": source["identity_sha256"],
                    "source_paths": source["paths"],
                    "bootstrap_config_sha256": config_sha256,
                    "native_authority_sha256": native_authority_sha256,
                    "output_fingerprint_sha256": fingerprint,
                }
                problems = _llvm_build_record_errors(written)
                if problems:
                    reasons.append("this run could not record its LLVM build: " + "; ".join(problems))
                    written = None
                record = written
        elif prior["fingerprint_sha256"] == fingerprint:
            provenance = "reused"
            reasons.extend(
                f"{where} was reused, and {reason}"
                for reason in _llvm_reuse_reasons(
                    before["build_record"],
                    before["build_record_errors"],
                    source=source,
                    fingerprint=fingerprint,
                    host=host,
                    config_sha256=config_sha256,
                    native_authority_sha256=native_authority_sha256,
                )
            )
            if not reasons:
                record = before["build_record"]
        else:
            provenance = "changed-in-this-run"
            reasons.append(
                f"{' and '.join(prior['dirs'])} was there before this run and what is installed "
                "changed during it: x.py built over objects this run did not watch being compiled"
            )
    reasons = list(dict.fromkeys(reasons))
    return (
        {
            "schema": LLVM_IDENTITY_SCHEMA,
            "mode": mode,
            "provenance": provenance,
            "identity_stated": not reasons,
            "reasons": reasons,
            "source_identity_sha256": source["identity_sha256"],
            "source_paths": source["paths"],
            "output_dirs": output_dirs,
            "output_fingerprint_sha256": fingerprint,
            "build_record": record,
        },
        written,
    )


def _llvm_identity_of_no_statement(reason: str) -> dict[str, object]:
    """An `llvm_identity` that says only that nothing could be said, and why."""
    return {
        "schema": LLVM_IDENTITY_SCHEMA,
        "mode": "unknown",
        "provenance": "unknown",
        "identity_stated": False,
        "reasons": [reason],
        "source_identity_sha256": None,
        "source_paths": [],
        "output_dirs": [],
        "output_fingerprint_sha256": None,
        "build_record": None,
    }


def _root_commit_of(source_lineage: dict[str, object] | None) -> str:
    """The superproject commit a source-lineage capture saw, or "" when it names none."""
    repositories = source_lineage.get("repositories") if isinstance(source_lineage, dict) else None
    return next(
        (
            str(repository.get("head") or "")
            for repository in (repositories if isinstance(repositories, list) else [])
            if isinstance(repository, dict) and repository.get("path") == "."
        ),
        "",
    )


def settle_llvm_identity(
    root: Path,
    host: str,
    before: dict[str, object],
    *,
    receipt: dict[str, object],
    commit_before: str,
    inputs_stable: bool,
    build_root: Path | None = None,
    preserve_build_record: bool = False,
) -> dict[str, object]:
    """The `llvm_identity` of the receipt being written, its LLVM's build record left beside it.

    `receipt` holds what the record is checked against: the receipt's `host`,
    `compiler`, `bootstrap_lineage` and `build_authority`; `commit_before` is
    the commit the build started at. The build record of an LLVM this run
    built is written here, before the receipt that quotes it.

    NEVER AN ERROR, for the caller or as an exception out of the record's own
    rules: by default the record is all that is new about a build, and it must
    not be able to fail one that did not ask for it. Where bind_llvm_identity's
    answer is not a record the verifier accepts, or the build record could not
    be left in the build directory (the receipt would then quote evidence that
    is not there), the identity is NOT STATED and the record says why. So it is
    for ANY exception out of the observation after the build, the record's own
    rules or the write (capture_llvm_before_build lists what can be met): the
    audit that calls this runs after the whole build, with the stage0 that
    `--fresh-seed` set aside not yet put back or discarded.
    """

    def of_receipt(section: str, key: str) -> object:
        table = receipt.get(section)
        return table.get(key) if isinstance(table, dict) else None

    try:
        identity, build_record = bind_llvm_identity(
            root,
            host,
            before,
            commit=str(of_receipt("compiler", "source_commit") or ""),
            commit_before=commit_before,
            config_sha256=of_receipt("bootstrap_lineage", "config_sha256"),
            native_authority_sha256=of_receipt("build_authority", "authority_sha256"),
            selected_llvm=of_receipt("build_authority", "selected_llvm"),
            inputs_stable=inputs_stable,
            **({"build_root": build_root} if build_root is not None else {}),
        )
    except Exception as error:  # noqa: BLE001 - see NEVER AN ERROR above
        return _llvm_identity_of_no_statement(
            "the LLVM this build carries could not be observed after the build: "
            + _exception_text(error)
        )
    try:
        problems = _llvm_identity_errors(identity, receipt)
    except Exception as error:  # noqa: BLE001 - see NEVER AN ERROR above
        problems = [f"its own rules could not be applied to it ({_exception_text(error)})"]
    if problems:
        return _llvm_identity_of_no_statement(
            "this run could not form a record of its LLVM: " + "; ".join(problems)
        )
    if build_record is not None:
        try:
            layout = {"build_root": build_root} if build_root is not None else {}
            if preserve_build_record:
                retained, problems = read_llvm_build_record(root, host, **layout)
                if problems or retained != build_record:
                    raise ValueError("detached audit requires the unchanged original LLVM build record")
            else:
                write_llvm_build_record(root, host, build_record, **layout)
        except Exception as error:  # noqa: BLE001 - see NEVER AN ERROR above
            return {
                **identity,
                "identity_stated": False,
                "reasons": [
                    "this run could not leave its LLVM build record in the build directory: "
                    + _exception_text(error)
                ],
                "build_record": None,
            }
    return identity


def leave_llvm_build_record_after_failed_build(
    root: Path,
    host: str,
    before: dict[str, object] | None,
    *,
    commit_before: str,
    config_path: Path,
    config_sha256: object,
    build_authority_before: dict[str, object],
    llvm_config: str | None,
) -> None:
    """After a provenance build that FAILED: leave the build record of an LLVM it built from nothing.

    The audit leaves that record, and the audit runs only after a build that
    succeeded. A build that fails later than its LLVM (in a stage-1 crate, in
    the ay install) would leave build/<host>/llvm without one, the retry could
    not state that LLVM's identity, and under `--require-llvm-identity` it
    would be refused until the directory was removed and LLVM built a second
    time. So the record is left here on the audit's own conditions: no such
    directory before x.py and a stamped one now, the LLVM sources at HEAD and
    as they were, HEAD itself where it was, the bootstrap config and the native
    authority as captured before x.py.

    It says what it did. It changes neither the failure being reported nor its
    exit status, whatever goes wrong in it, and it does nothing at all for a
    build that found an LLVM directory (every build in an existing build
    directory).
    """
    try:
        output = before["output"] if before is not None and before["mode"] == "in-tree" else None
        if not isinstance(output, dict) or output["present"] or output["errors"]:
            return
        if not (_llvm_out_dir(root, host) / LLVM_OUTPUT_ROOTS[0][1]).is_file():
            return
        errors: list[str] = []
        head = _git_bytes(root, ("rev-parse", "HEAD"), errors, "HEAD after the failed build")
        commit = (head or b"").decode("ascii", errors="replace").strip()
        no_record = "  the LLVM this run built gets no build record, so a retry cannot state its identity:"
        if not commit or commit != commit_before:
            print(no_record)
            print(f"    HEAD is not the commit the build started at ({commit_before[:12] or 'unknown'})")
            return
        authority = capture_build_authority(root, host, llvm_config)
        identity, record = bind_llvm_identity(
            root,
            host,
            before,
            commit=commit,
            commit_before=commit_before,
            config_sha256=config_sha256,
            native_authority_sha256=build_authority_before.get("authority_sha256"),
            selected_llvm=None,
            inputs_stable=(
                _sha256_file(config_path) == config_sha256
                and authority.get("status") == "ready"
                and authority.get("authority_sha256")
                == build_authority_before.get("authority_sha256")
            ),
        )
        if record is None:
            print(no_record)
            for reason in identity["reasons"]:
                print(f"    {reason}")
            return
        write_llvm_build_record(root, host, record)
        print(
            f"  left the build record of the LLVM this run built (build/{host}/llvm, at commit "
            f"{commit[:12]}): a retry in this build directory can reuse it and state its identity"
        )
    except Exception as error:  # noqa: BLE001 - a failed build is being reported; this must not replace it
        print(f"  (the build record of the LLVM this run built was not left: {error})")


def _llvm_source_tree_oid(rows: object) -> str:
    return next(
        (
            str(row.get("oid"))
            for row in (rows if isinstance(rows, list) else [])
            if isinstance(row, dict) and row.get("path") == LLVM_SOURCE_TREE
        ),
        "unknown",
    )


def llvm_identity_summary(identity: dict[str, object]) -> str:
    """One line for the build log: the LLVM a receipt says its stage carries."""
    stated = "identity stated" if identity["identity_stated"] else "identity NOT stated"
    if identity["mode"] == "external":
        # No source identity beside it: this checkout's is not that LLVM's.
        return f"external, linked through --llvm-config, {stated} (no source identity describes it)"
    if identity["mode"] != "in-tree":
        # Nor beside one of unknown mode: this checkout's is not known to be it.
        return (
            f"{identity['mode']}: which LLVM x.py links is not known, {stated} "
            "(no source identity describes it)"
        )
    record = identity["build_record"]
    built_at = f", built at commit {str(record['built_at_commit'])[:12]}" if isinstance(record, dict) else ""
    return (
        f"{identity['mode']}, {identity['provenance']}, {stated} (source identity "
        f"{str(identity['source_identity_sha256'])[:12]}, {LLVM_SOURCE_TREE} tree "
        f"{_llvm_source_tree_oid(identity['source_paths'])[:12]}{built_at})"
    )


def _verify_llvm_identity(
    root: Path, host: str, receipt: dict[str, object], *, build_root: Path | None = None,
) -> tuple[list[str], list[str]]:
    """(what is wrong with a receipt's `llvm_identity`, what could not be borne out).

    WRONG, whatever was asked: a record that is malformed or contradicts itself
    or its receipt, and a source identity that is not this tree's HEAD's (the
    recursive source closure the verifier has always compared differs then
    too). The receipt is not this tree's.

    NOT BORNE OUT: the record's source identity could not be recomputed (git
    did not answer); or, for an in-tree LLVM, the fingerprint of
    build/<host>/llvm (with build/<host>/lld) as it is now is not the
    receipt's, or the build record there is not the one the receipt quotes.
    Before this record existed the verifier asked nothing of that directory,
    and a later x.py run can rebuild LLVM there without touching the stage a
    receipt binds; so these are findings, printed, and they fail a
    verification only under `--require-llvm-identity`. A record that holds no
    source identity has none to compare: its build could not establish one, or
    its LLVM is external (linked through `--llvm-config`; never stated, and of
    such an LLVM nothing is re-derived here at all: the verifier's own
    build-authority comparison is what answers for the llvm-config executable).
    What cannot be observed in the build directory now is a finding too, never
    an exception.

    NOT re-derived, because no later run can: whether LLVM was built in the
    receipt's run or reused, and that the files a build record fingerprints
    were compiled from the sources it names. Both rest on a run having seen no
    build/<host>/llvm before the x.py that produced it.
    """
    record = receipt["llvm_identity"]
    errors = _llvm_identity_errors(record, receipt)
    if errors:
        return errors, []
    findings: list[str] = []
    if record["source_identity_sha256"] is not None:
        source = capture_llvm_source_identity(root)
        if source["errors"]:
            findings.extend(
                f"the LLVM source identity could not be recomputed: {error}"
                for error in source["errors"]
            )
        else:
            if (record["source_paths"], record["source_identity_sha256"]) != (
                source["paths"],
                source["identity_sha256"],
            ):
                errors.append("current LLVM source identity differs from the receipt")
            if record["identity_stated"] and not source["clean"]:
                errors.append(
                    "the LLVM sources differ from HEAD under a receipt that states their identity"
                )
    if record["mode"] == "in-tree":
        # What the build directory holds NOW. Whatever is there (a file that
        # cannot be read, a build record nested deeper than the parser's stack)
        # is a finding, never an exception: main() runs this verification at
        # the end of the documented build, and before the record existed
        # nothing in that directory could fail it.
        try:
            layout = {"build_root": build_root} if build_root is not None else {}
            output = capture_llvm_output(root, host, **layout)
            findings.extend(str(error) for error in output["errors"])
            if (record["output_dirs"], record["output_fingerprint_sha256"]) != (
                output["dirs"],
                output["fingerprint_sha256"],
            ):
                findings.append("current in-tree LLVM output differs from the receipt")
            if record["build_record"] is not None:
                beside, problems = read_llvm_build_record(root, host, **layout)
                if problems or beside != record["build_record"]:
                    findings.append(
                        "the LLVM build record in the build directory is not the one the receipt quotes"
                    )
        except Exception as error:  # noqa: BLE001 - see the comment above
            findings.append(
                "the in-tree LLVM in the build directory could not be observed: "
                + _exception_text(error)
            )
    return errors, findings


def audit_stage_tool_provenance(
    root: Path,
    host: str,
    stage: int,
    source_lineage_before: dict[str, object] | None = None,
    bootstrap_lineage_before: dict[str, object] | None = None,
    build_authority_before: dict[str, object] | None = None,
    llvm_config: str | None = None,
    *,
    invocation: list[str] | None = None,
    llvm_before: dict[str, object] | None = None,
    build_root: Path | None = None,
    config_path: Path | None = None,
    cargo_home: Path | None = None,
    declared_environment: dict[str, str] | None = None,
    writer: str | None = None,
    mint_configuration: dict[str, object] | None = None,
    receipt_path: Path | None = None,
) -> bool:
    """Bind every release-facing stage tool to its x.py producer.

    The audit is intentionally structural, not a PATH/version-name heuristic:
    every public Rust tool must hash to the exact target-qualified stage-(N+1) tools-bin
    artifact, built by compiler N-1 for the stage-N sysroot. Native LLVM front doors
    bind separately to the exact installed output and stated LLVM identity, with no
    invented Rust producer stage. The receipt additionally binds the stage1
    producer compiler and final compiler to the repository commit and records
    whether bootstrap installed each tool by hard link or content-preserving
    copy.  A missing/unmapped tool, changed producer, stock public alias, or
    compiler/sysroot mismatch fails the one-command bootstrap.

    `invocation` is the argument list this script was started with; the receipt
    keeps it as `recreator_invocation` (see RECREATOR_INVOCATION_SCHEMA). None
    writes no such record.

    `llvm_before` is capture_llvm_before_build's answer from before x.py ran;
    the receipt then says which LLVM the stage carries, as `llvm_identity`
    (see LLVM_IDENTITY_SCHEMA), is release-class only if that identity is
    stated, and an LLVM this run built gets its build record. None writes no
    such record and classifies as before it existed; main() always passes one.

    The seed mint calls this same owner with its actual `build_root`, config,
    private Cargo home and declared closed environment. It supplies observations
    from before its first build and records `writer`, never `recreator_invocation`.
    Its explicit `mint_configuration` binds the effective seed config, includes,
    profile and fixed x.py overrides, and is revalidated on every capture.
    An explicit `receipt_path` writes a new separate receipt exclusively; it never
    overwrites the original stage receipt during a provenance repair.
    """
    build = build_root if build_root is not None else root / "build"
    layout = {"build_root": build_root} if build_root is not None else {}
    bootstrap_layout = {
        **layout, **({"config_path": config_path} if config_path is not None else {}),
        **({"mint_configuration": mint_configuration} if mint_configuration is not None else {}),
    }
    if mint_configuration is not None and writer != "scripts/mint_and_prove_seed.sh":
        raise ValueError("only the mint writer can use its explicit configuration context")
    native_layout = {
        **({"cargo_home": cargo_home} if cargo_home is not None else {}),
        **({"declared_environment": declared_environment} if declared_environment is not None else {}),
        **({"mint_configuration": mint_configuration} if mint_configuration is not None
           and "clean_lean_inputs" in mint_configuration else {}),
    }
    stage_root = build / host / f"stage{stage}"
    bin_dir = stage_root / "bin"
    tools_dir = build / host / f"stage{stage + 1}-tools-bin" / host
    separate_receipt = receipt_path is not None
    original_receipt = stage_root / "tool-provenance.json"
    if separate_receipt:
        if (not receipt_path.is_absolute() or receipt_path == original_receipt
                or os.path.lexists(receipt_path) or not receipt_path.parent.is_dir()):
            raise ValueError("separate stage receipt requires a new absolute output path")
        if (receipt_path.parent.resolve() / receipt_path.name).is_relative_to(build.resolve()):
            raise ValueError("separate stage receipt must be outside the retained build tree")
    else:
        receipt_path = original_receipt
    errors: list[str] = []
    tools: list[dict[str, object]] = []
    source_lineage = _bind_source_lineage(
        source_lineage_before, capture_source_lineage(root)
    )
    bootstrap_lineage = _bind_bootstrap_lineage(
        bootstrap_lineage_before, capture_bootstrap_lineage(root, host, **bootstrap_layout)
    )
    build_authority = _bind_build_authority(
        build_authority_before,
        capture_build_authority(root, host, llvm_config, **native_layout),
    )

    # `rustc`/`trustc` and `rustdoc`/`trustdoc` are COMPAT-ALIAS PAIRS: each Trust-named
    # tool is installed beside the Rust name the ecosystem invokes (§ the version-line
    # argument in rustc_driver_impl — compatibility is owed to the name that was invoked).
    # Only the Trust names are producers; the Rust names are aliases of them, so they are
    # admitted here rather than mapped. `rustdoc` was missing from this set while `rustc`
    # was present, so a stage2 carrying both failed the audit with "unmapped public stage
    # tools: rustdoc" — the pair was half-declared.
    expected_public = expected_public_stage_tools()
    if not bin_dir.is_dir():
        errors.append(f"missing stage tool directory: {bin_dir}")
        actual_public: set[str] = set()
    else:
        actual_public = {
            path.name.removesuffix(".exe")
            for path in bin_dir.iterdir()
            if path.is_file() and os.access(path, os.X_OK)
        }
    missing = sorted(expected_public - actual_public)
    unexpected = sorted(actual_public - expected_public - set(OPTIONAL_STAGE_TOOL_PRODUCERS)
                        - set(NATIVE_STAGE_TOOL_PRODUCERS))
    if missing:
        errors.append(f"missing public stage tools: {', '.join(missing)}")
    if unexpected:
        errors.append(f"unmapped public stage tools: {', '.join(unexpected)}")

    for public_name, producer_name in stage_tool_producers_for(actual_public).items():
        installed = bin_dir / _host_executable(public_name, host)
        producer = tools_dir / _host_executable(producer_name, host)
        record: dict[str, object] = {
            "name": public_name,
            "path": _repository_relative_path(root, installed),
            "producer_path": _repository_relative_path(root, producer),
            # Cache-directory coordinate, distinct from the building compiler.
            "producer_stage": stage + 1,
            "producer_compiler_stage": stage - 1,
        }
        if not installed.is_file():
            errors.append(f"missing public tool {public_name}: {installed}")
            record["status"] = "missing"
            tools.append(record)
            continue
        if not producer.is_file():
            errors.append(f"missing x.py producer for {public_name}: {producer}")
            record["status"] = "producer_missing"
            tools.append(record)
            continue
        installed_sha = _sha256_file(installed)
        producer_sha = _sha256_file(producer)
        record.update(
            {
                "sha256": installed_sha,
                "producer_sha256": producer_sha,
                "same_inode": os.path.samefile(installed, producer),
                "status": "bound" if installed_sha == producer_sha else "mismatch",
            }
        )
        ok, version = _capture_identity(installed, ("--version",))
        record["version"] = version.splitlines()[0] if version else ""
        record["version_probe_ok"] = ok
        if installed_sha != producer_sha:
            errors.append(
                f"public tool {public_name} does not match its x.py producer: "
                f"{installed_sha} != {producer_sha}"
            )
        if not ok:
            errors.append(f"public tool {public_name} rejected --version: {version}")
        tools.append(record)

    trustc = bin_dir / _host_executable("trustc", host)
    rustc = bin_dir / _host_executable("rustc", host)
    builder = build / host / f"stage{stage - 1}" / "bin" / _host_executable(
        "trustc", host
    )
    compiler: dict[str, object] = {
        "path": _repository_relative_path(root, trustc),
        "compatibility_alias": _repository_relative_path(root, rustc),
        "producer_compiler": _repository_relative_path(root, builder),
        "producer_compiler_stage": stage - 1,
    }
    for label, path in (("compiler", trustc), ("producer compiler", builder)):
        if not path.is_file():
            errors.append(f"missing {label}: {path}")
            continue
        compiler[f"{label.replace(' ', '_')}_sha256"] = _sha256_file(path)
        ok, verbose = _capture_identity(path, ("-Vv",))
        compiler[f"{label.replace(' ', '_')}_verbose"] = verbose
        if not ok:
            errors.append(f"{label} rejected -Vv: {verbose}")
    if trustc.is_file() and rustc.is_file():
        trustc_sha = _sha256_file(trustc)
        rustc_sha = _sha256_file(rustc)
        compiler["compatibility_alias_same_inode"] = os.path.samefile(trustc, rustc)
        compiler["compatibility_alias_sha256"] = rustc_sha
        if trustc_sha != rustc_sha:
            errors.append("stage rustc compatibility alias differs from trustc")
    elif not rustc.is_file():
        errors.append(f"missing rustc compatibility alias: {rustc}")

    errors.extend(stage_documentation_alias_errors(bin_dir, host))

    commit = next(
        (
            str(repository.get("head") or "")
            for repository in source_lineage.get("repositories", [])
            if repository.get("path") == "."
        ),
        "",
    )
    compiler["source_commit"] = commit
    verbose = str(compiler.get("compiler_verbose", ""))
    producer_verbose = str(compiler.get("producer_compiler_verbose", ""))
    if not commit:
        errors.append("could not resolve the source commit for compiler binding")
    else:
        for label, value in (("compiler", verbose), ("producer compiler", producer_verbose)):
            if f"commit-hash: {commit}" not in value:
                errors.append(f"{label} is not bound to source commit {commit}")
    if trustc.is_file():
        ok, sysroot = _capture_identity(trustc, ("--print", "sysroot"))
        compiler["reported_sysroot_local_path"] = sysroot
        compiler["reported_sysroot_path_scope"] = "local-diagnostic"
        try:
            sysroot_matches = ok and Path(sysroot).resolve() == stage_root.resolve()
        except OSError:
            sysroot_matches = False
        compiler["sysroot_matches"] = sysroot_matches
        if not sysroot_matches:
            errors.append(f"stage compiler reports foreign sysroot: {sysroot}")

    trustdoc = bin_dir / _host_executable("trustdoc", host)
    rustdoc = bin_dir / _host_executable("rustdoc", host)
    rustdoc_alias: dict[str, object] = {
        "path": _repository_relative_path(root, rustdoc),
        "owner": "trustdoc",
        "owner_path": _repository_relative_path(root, trustdoc),
    }
    if trustdoc.is_file() and rustdoc.is_file():
        trustdoc_sha = _sha256_file(trustdoc)
        rustdoc_sha = _sha256_file(rustdoc)
        rustdoc_alias.update(
            {
                "sha256": rustdoc_sha,
                "owner_sha256": trustdoc_sha,
                "same_inode": os.path.samefile(trustdoc, rustdoc),
                "status": "bound" if rustdoc_sha == trustdoc_sha else "mismatch",
            }
        )
        if rustdoc_sha != trustdoc_sha:
            errors.append("stage rustdoc compatibility alias differs from trustdoc")
    else:
        # Already an error: a missing rustdoc fails the closed-inventory check and a
        # missing trustdoc fails the producer-map loop above. Record the status only.
        rustdoc_alias["status"] = "missing"

    libexec = stage_root / "libexec"
    owned_helper = libexec / _host_executable("trust-analyzer-proc-macro-srv", host)
    retired_helper = libexec / _host_executable("rust-analyzer-proc-macro-srv", host)
    helper_producer = tools_dir / _host_executable("rust-analyzer-proc-macro-srv", host)
    helper: dict[str, object] = {
        "path": _repository_relative_path(root, owned_helper),
        "producer_path": _repository_relative_path(root, helper_producer),
        "producer_stage": stage + 1,
        "producer_compiler_stage": stage - 1,
        "retired_public_path": _repository_relative_path(root, retired_helper),
        "retired_public_path_absent": not retired_helper.exists(),
    }
    if retired_helper.exists():
        errors.append(f"retired public proc-macro helper shipped: {retired_helper}")
    if not owned_helper.is_file() or not helper_producer.is_file():
        errors.append("Trust-owned proc-macro helper or its x.py producer is missing")
    else:
        helper_sha = _sha256_file(owned_helper)
        helper_producer_sha = _sha256_file(helper_producer)
        helper.update(
            {
                "sha256": helper_sha,
                "producer_sha256": helper_producer_sha,
                "same_inode": os.path.samefile(owned_helper, helper_producer),
                "status": "bound" if helper_sha == helper_producer_sha else "mismatch",
            }
        )
        if helper_sha != helper_producer_sha:
            errors.append("Trust-owned proc-macro helper does not match its x.py producer")

    invocation_record = None if invocation is None else recreator_invocation_record(invocation)
    if invocation_record is not None:
        # main() refuses such arguments before the build; a receipt that could
        # not be verified is not written as ready by any other caller either.
        errors.extend(_recreator_invocation_errors(invocation_record))

    llvm_identity: dict[str, object] | None = None
    if llvm_before is not None:
        # Never an error: the record is not allowed to fail a build that did
        # not ask for it (settle_llvm_identity). `--require-llvm-identity` is
        # what turns an identity that is not stated into a failure, in main().
        llvm_identity = settle_llvm_identity(
            root,
            host,
            llvm_before,
            receipt={
                "host": host,
                "compiler": compiler,
                "bootstrap_lineage": bootstrap_lineage,
                "build_authority": build_authority,
            },
            commit_before=_root_commit_of(source_lineage_before),
            inputs_stable=(
                bootstrap_lineage.get("pre_build_config_sha256")
                == bootstrap_lineage.get("post_build_config_sha256")
                and build_authority.get("stable_across_build") is True
            ),
            preserve_build_record=separate_receipt,
            **layout,
        )

    native_tools, native_errors = capture_native_stage_tools(
        root, host, build, bin_dir, actual_public, llvm_identity,
    )
    errors.extend(native_errors)
    tool_binding_status = "ready" if not errors else "rejected"
    lineage_status = source_lineage["status"]
    bootstrap_status = bootstrap_lineage["status"]
    if (
        tool_binding_status == "rejected"
        or lineage_status == "rejected"
        or bootstrap_status == "rejected"
        or build_authority["status"] == "rejected"
    ):
        status = "rejected"
    else:
        status = _classify_receipt_status(lineage_status, bootstrap_lineage)
    receipt = {
        "schema": "trust.stage-tool-provenance.v2",
        "status": status,
        "tool_binding_status": tool_binding_status,
        "source_tree_clean": source_lineage["source_tree_clean"],
        "trust_from_trust": bootstrap_lineage["trust_from_trust"],
        "stage": stage,
        "host": host,
        "path_scope": "repository-root-relative",
        "stage_root": _repository_relative_path(root, stage_root),
        "tools_dir": _repository_relative_path(root, tools_dir),
        "bootstrap_compiler_verification": dict(BOOTSTRAP_COMPILER_VERIFICATION),
        "compiler": compiler,
        "tools": tools,
        "native_stage_tools": native_tools,
        "rustdoc_alias": rustdoc_alias,
        "proc_macro_helper": helper,
        "source_lineage": source_lineage,
        "bootstrap_lineage": bootstrap_lineage,
        "build_authority": build_authority,
        "errors": sorted(
            set(
                errors
                + list(source_lineage["errors"])
                + list(bootstrap_lineage["errors"])
                + list(build_authority["errors"])
            )
        ),
    }
    if invocation_record is not None:
        receipt["recreator_invocation"] = invocation_record
    if writer is not None:
        receipt["writer"] = writer
    if llvm_identity is not None:
        receipt["llvm_identity"] = llvm_identity
    stage_root.mkdir(parents=True, exist_ok=True)
    temporary = receipt_path.with_suffix(".json.tmp")
    if separate_receipt:
        temporary = receipt_path.with_name(receipt_path.name + f".tmp.{os.getpid()}")
        with temporary.open("x", encoding="utf-8") as stream:
            stream.write(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
        try:
            os.link(temporary, receipt_path)  # no overwrite, including a racing symlink
        finally:
            temporary.unlink()
    else:
        temporary.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        temporary.replace(receipt_path)
    if llvm_identity is not None:
        print(f"  llvm: {llvm_identity_summary(llvm_identity)}")
        for reason in llvm_identity["reasons"]:
            print(f"    not stated: {reason}")
    if status == "rejected":
        for error in receipt["errors"]:
            print(f"  ERROR: {error}")
        print(f"  rejected stage tool provenance -> {receipt_path}")
        return False
    print(f"  audited stage tool provenance ({status}) -> {receipt_path}")
    return True


def _same_local_path(recorded: object, reported: str) -> bool:
    """True iff a recorded local path and a reported one name the same location."""
    if not isinstance(recorded, str) or not recorded:
        return False
    if recorded == reported:
        return True
    try:
        return Path(recorded).resolve() == Path(reported).resolve()
    except (OSError, RuntimeError, ValueError):
        return False


def _require_receipt_path(
    root: Path,
    value: object,
    expected: Path,
    errors: list[str],
    label: str,
) -> None:
    expected_value = _repository_relative_path(root, expected)
    if value != expected_value:
        errors.append(f"{label} is not the expected repository-relative path {expected_value}")


def verify_stage_tool_provenance(
    root: Path,
    host: str,
    stage: int,
    *,
    require_immutable_lineage: bool = False,
    require_public_release: bool = False,
    require_llvm_identity: bool = False,
    build_root: Path | None = None,
    config_path: Path | None = None,
    cargo_home: Path | None = None,
    declared_environment: dict[str, str] | None = None,
    mint_configuration: dict[str, object] | None = None,
    receipt_path: Path | None = None,
) -> bool:
    """Read-only verification of a previously written stage provenance receipt.

    `require_llvm_identity`: the receipt must state the identity of the LLVM
    its stage carries, and the build directory must still bear it out
    (_verify_llvm_identity). Without it a receipt is asked nothing about its
    LLVM that it was not asked before the record existed, beyond being this
    tree's: one without the record, and one that does not state the identity,
    verify as they did.
    """
    build = build_root if build_root is not None else root / "build"
    layout = {"build_root": build_root} if build_root is not None else {}
    bootstrap_layout = {
        **layout, **({"config_path": config_path} if config_path is not None else {}),
        **({"mint_configuration": mint_configuration} if mint_configuration is not None else {}),
    }
    native_layout = {
        **({"cargo_home": cargo_home} if cargo_home is not None else {}),
        **({"declared_environment": declared_environment} if declared_environment is not None else {}),
        **({"mint_configuration": mint_configuration} if mint_configuration is not None
           and "clean_lean_inputs" in mint_configuration else {}),
    }
    stage_root = build / host / f"stage{stage}"
    bin_dir = stage_root / "bin"
    tools_dir = build / host / f"stage{stage + 1}-tools-bin" / host
    if receipt_path is None:
        receipt_path = stage_root / "tool-provenance.json"
    elif not receipt_path.is_absolute() or not receipt_path.is_file() or receipt_path.is_symlink():
        print("  ERROR: separate stage receipt must be an absolute regular file")
        return False
    errors: list[str] = []
    try:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        print(f"  ERROR: could not read stage provenance receipt {receipt_path}: {error}")
        return False
    if not isinstance(receipt, dict):
        print(f"  ERROR: stage provenance receipt is not a JSON object: {receipt_path}")
        return False

    if receipt.get("schema") != "trust.stage-tool-provenance.v2":
        errors.append("stage provenance receipt does not use schema v2")
    if receipt.get("stage") != stage or receipt.get("host") != host:
        errors.append("stage provenance receipt stage/host does not match the requested sysroot")
    if receipt.get("path_scope") != "repository-root-relative":
        errors.append("stage provenance receipt path scope is not repository-root-relative")
    if mint_configuration is not None and receipt.get("writer") != "scripts/mint_and_prove_seed.sh":
        errors.append("only a mint receipt can use its explicit configuration context")
    if receipt.get("bootstrap_compiler_verification") != BOOTSTRAP_COMPILER_VERIFICATION:
        errors.append(
            "stage provenance receipt does not declare the exact non-self-proving "
            "bootstrap compiler verification mode"
        )
    _require_receipt_path(root, receipt.get("stage_root"), stage_root, errors, "stage_root")
    _require_receipt_path(root, receipt.get("tools_dir"), tools_dir, errors, "tools_dir")
    # The build's own statement of how it was started. Nothing here can
    # recompute it, so only its form is checked; a receipt written before the
    # record existed has none and is not asked for one.
    if "recreator_invocation" in receipt:
        errors.extend(_recreator_invocation_errors(receipt["recreator_invocation"]))

    current_lineage = capture_source_lineage(root)
    recorded_lineage = receipt.get("source_lineage")
    if not isinstance(recorded_lineage, dict):
        errors.append("stage provenance receipt is missing source_lineage")
        recorded_lineage = {}
    if recorded_lineage.get("schema") != "trust.source-lineage.v1":
        errors.append("recorded source lineage does not use the canonical schema")
    if recorded_lineage.get("errors") != []:
        errors.append("recorded source lineage contains errors")
    if current_lineage["status"] == "rejected":
        errors.extend(str(error) for error in current_lineage["errors"])
    if current_lineage.get("schema") != "trust.source-lineage.v1" or current_lineage.get(
        "errors"
    ) != []:
        errors.append("current source lineage is not canonical and error-free")
    current_sha = current_lineage.get("closure_sha256")
    pre_sha = recorded_lineage.get("pre_build_closure_sha256")
    post_sha = recorded_lineage.get("post_build_closure_sha256")
    if recorded_lineage.get("stable_across_build") is not True or pre_sha != post_sha:
        errors.append("receipt does not bind a source closure stable across the build")
    if post_sha != current_sha or recorded_lineage.get("closure_sha256") != current_sha:
        errors.append("current recursive source closure differs from the receipt")
    if recorded_lineage.get("repositories") != current_lineage.get("repositories"):
        errors.append("current recursive repository rows differ from the receipt")
    current_lineage_status = current_lineage.get("status")
    if recorded_lineage.get("status") != current_lineage_status:
        errors.append("current source-lineage classification differs from the receipt")
    expected_source_clean = current_lineage_status == "immutable_release"
    if recorded_lineage.get("source_tree_clean") != expected_source_clean:
        errors.append("recorded source_tree_clean disagrees with current source lineage")
    if receipt.get("source_tree_clean") != expected_source_clean:
        errors.append("top-level source_tree_clean disagrees with current source lineage")

    current_bootstrap = capture_bootstrap_lineage(root, host, **bootstrap_layout)
    recorded_bootstrap = receipt.get("bootstrap_lineage")
    if not isinstance(recorded_bootstrap, dict):
        errors.append("stage provenance receipt is missing bootstrap_lineage")
        recorded_bootstrap = {}
    if recorded_bootstrap.get("schema") != "trust.bootstrap-lineage.v1":
        errors.append("recorded bootstrap lineage does not use the canonical schema")
    if recorded_bootstrap.get("errors") != []:
        errors.append("recorded bootstrap lineage contains errors")
    if current_bootstrap["status"] == "rejected":
        errors.extend(str(error) for error in current_bootstrap["errors"])
    if current_bootstrap.get("schema") != "trust.bootstrap-lineage.v1" or current_bootstrap.get(
        "errors"
    ) != []:
        errors.append("current bootstrap lineage is not canonical and error-free")
    if recorded_bootstrap.get("stable_across_build") is not True:
        errors.append("receipt does not bind a stable bootstrap configuration")
    current_config_sha256 = current_bootstrap.get("config_sha256")
    if (
        recorded_bootstrap.get("pre_build_config_sha256") != current_config_sha256
        or recorded_bootstrap.get("post_build_config_sha256") != current_config_sha256
    ):
        errors.append("bootstrap config pre/post digests do not match current config")
    for field in (
        "status",
        "mode",
        "trust_from_trust",
        "config_path",
        "config_sha256",
        "declared_stage0_overrides",
        "config_file_sha256",
        "mint_configuration",
    ):
        if recorded_bootstrap.get(field) != current_bootstrap.get(field):
            errors.append(f"current bootstrap {field} differs from the receipt")
    if (json.dumps(recorded_bootstrap.get("mint_configuration"), sort_keys=True, allow_nan=False)
            != json.dumps(current_bootstrap.get("mint_configuration"), sort_keys=True, allow_nan=False)):
        errors.append("current bootstrap mint configuration differs from the receipt")
    current_trust_from_trust = current_bootstrap.get("status") in {
        "trust_from_trust", "local_atpkg"
    }
    if receipt.get("trust_from_trust") != current_trust_from_trust:
        errors.append("top-level trust_from_trust disagrees with current bootstrap lineage")
    recorded_seed = recorded_bootstrap.get("validated_seed")
    current_seed = current_bootstrap.get("validated_seed")
    recorded_genesis = recorded_bootstrap.get("genesis_adapter")
    current_genesis = current_bootstrap.get("genesis_adapter")
    if current_bootstrap.get("mode") == "seed":
        if recorded_genesis is not None or current_genesis is not None:
            errors.append("seed-mode bootstrap unexpectedly carries genesis authority")
        if not isinstance(recorded_seed, dict) or not isinstance(current_seed, dict):
            errors.append("seed-mode receipt is missing validated seed authority")
        else:
            if recorded_seed.get("schema") != "trust.validated-seed-lineage.v1":
                errors.append("recorded validated seed does not use the canonical schema")
            if recorded_seed.get("status") != "validated" or current_seed.get(
                "status"
            ) != "validated":
                errors.append("validated seed status is not validated")
            if recorded_seed.get("errors") != [] or current_seed.get("errors") != []:
                errors.append("validated seed lineage contains errors")
            if recorded_seed.get("stable_across_build") is not True:
                errors.append("receipt does not bind seed authority stable across the build")
            seed_sha = current_seed.get("authority_sha256")
            if (
                recorded_seed.get("pre_build_authority_sha256") != seed_sha
                or recorded_seed.get("post_build_authority_sha256") != seed_sha
                or recorded_seed.get("authority_sha256") != seed_sha
                or recorded_seed.get("authority") != current_seed.get("authority")
            ):
                errors.append("current seed pins, payloads, or admission differ from the receipt")
            if recorded_seed.get("admission_status") != current_seed.get(
                "admission_status"
            ):
                errors.append("current seed admission class differs from the receipt")
            if recorded_seed.get("compiler") != current_seed.get("compiler"):
                errors.append("current hydrated seed compiler differs from the receipt")
            compiler = current_seed.get("compiler")
            if not isinstance(compiler, dict) or compiler.get(
                "schema"
            ) != "trust.seed-compiler-identity.v1" or compiler.get("status") != "validated" or compiler.get(
                "errors"
            ) != []:
                errors.append("current hydrated seed compiler identity is not canonical")
            current_compiler_sha256 = (
                hashlib.sha256(
                    json.dumps(
                        compiler,
                        sort_keys=True,
                        separators=(",", ":"),
                    ).encode("utf-8")
                ).hexdigest()
                if isinstance(compiler, dict)
                else None
            )
            materialized = recorded_seed.get("compiler_materialized_during_build")
            compiler_stable = recorded_seed.get("compiler_stable_across_build")
            materialization_status = recorded_seed.get("materialization_status")
            pre_compiler_sha256 = recorded_seed.get(
                "pre_build_compiler_identity_sha256"
            )
            post_compiler_sha256 = recorded_seed.get(
                "post_build_compiler_identity_sha256"
            )
            if materialized is True:
                valid_history = (
                    compiler_stable is None
                    and materialization_status == "fresh-from-validated-archives"
                    and pre_compiler_sha256 is None
                    and post_compiler_sha256 == current_compiler_sha256
                )
            elif materialized is False:
                valid_history = (
                    compiler_stable is True
                    and materialization_status == "preexisting-unproven"
                    and pre_compiler_sha256 == current_compiler_sha256
                    and post_compiler_sha256 == current_compiler_sha256
                )
            else:
                valid_history = False
            if not valid_history:
                errors.append("seed compiler materialization history is contradictory")
    elif recorded_seed is not None or current_seed is not None:
        errors.append("non-seed bootstrap unexpectedly carries validated seed authority")

    if current_bootstrap.get("mode") == "genesis":
        if not isinstance(recorded_genesis, dict) or not isinstance(current_genesis, dict):
            errors.append("genesis-mode receipt is missing adapter authority")
        else:
            if (
                recorded_genesis.get("schema")
                != "trust.genesis-adapter-authority.v1"
                or current_genesis.get("schema")
                != "trust.genesis-adapter-authority.v1"
                or recorded_genesis.get("status") != "ready"
                or current_genesis.get("status") != "ready"
                or recorded_genesis.get("errors") != []
                or current_genesis.get("errors") != []
            ):
                errors.append("genesis adapter authority is not canonical and ready")
            current_genesis_sha = current_genesis.get("authority_sha256")
            if (
                recorded_genesis.get("stable_across_build") is not True
                or recorded_genesis.get("pre_build_authority_sha256")
                != current_genesis_sha
                or recorded_genesis.get("post_build_authority_sha256")
                != current_genesis_sha
                or recorded_genesis.get("authority_sha256") != current_genesis_sha
                or recorded_genesis.get("authority")
                != current_genesis.get("authority")
            ):
                errors.append("current genesis adapter authority differs from the receipt")
    elif recorded_genesis is not None or current_genesis is not None:
        errors.append("non-genesis bootstrap unexpectedly carries genesis authority")

    recorded_atpkg = recorded_bootstrap.get("atpkg_authority")
    current_atpkg = current_bootstrap.get("atpkg_authority")
    if current_bootstrap.get("mode") == "atpkg":
        if not _atpkg_authority_ready(recorded_atpkg) or not _atpkg_authority_ready(current_atpkg):
            errors.append("atpkg-mode receipt is missing canonical local candidate authority")
        else:
            current_atpkg_sha = current_atpkg["authority_sha256"]
            if (
                recorded_atpkg.get("stable_across_build") is not True
                or recorded_atpkg.get("pre_build_authority_sha256") != current_atpkg_sha
                or recorded_atpkg.get("post_build_authority_sha256") != current_atpkg_sha
                or recorded_atpkg["authority_sha256"] != current_atpkg_sha
                or recorded_atpkg["authority"] != current_atpkg["authority"]
            ):
                errors.append("current atpkg pack/verifier authority differs from the receipt")
    elif recorded_atpkg is not None or current_atpkg is not None:
        errors.append("non-atpkg bootstrap unexpectedly carries atpkg authority")

    recorded_build_authority = receipt.get("build_authority")
    if not isinstance(recorded_build_authority, dict):
        errors.append("stage provenance receipt is missing build_authority")
        recorded_build_authority = {}
    recorded_llvm = recorded_build_authority.get("selected_llvm")
    verifier_llvm_config = (
        str(recorded_llvm.get("resolved_local_path"))
        if isinstance(recorded_llvm, dict)
        and isinstance(recorded_llvm.get("resolved_local_path"), str)
        else None
    )
    current_build_authority = capture_build_authority(root, host, verifier_llvm_config, **native_layout)
    if recorded_build_authority.get("schema") != "trust.build-authority.v1":
        errors.append("recorded build authority does not use the canonical schema")
    if recorded_build_authority.get("status") != "ready" or recorded_build_authority.get(
        "errors"
    ) != []:
        errors.append("recorded build authority is not ready and error-free")
    if current_build_authority.get("status") != "ready" or current_build_authority.get(
        "errors"
    ) != []:
        errors.append("current build authority is not ready and error-free")
    authority_sha = current_build_authority.get("authority_sha256")
    if (
        recorded_build_authority.get("stable_across_build") is not True
        or recorded_build_authority.get("pre_build_authority_sha256") != authority_sha
        or recorded_build_authority.get("post_build_authority_sha256") != authority_sha
        or recorded_build_authority.get("authority_sha256") != authority_sha
    ):
        errors.append("current native tool/SDK authority differs from the receipt")
    for field in (
        "host",
        "ambient_overrides",
        "ambient_cargo_configs",
        "cargo_environment",
        "native_tools",
        "selected_llvm",
        "platform_toolchain",
        "sdk",
        "dynamic_dependencies",
        "derived_library_paths",
    ):
        if recorded_build_authority.get(field) != current_build_authority.get(field):
            errors.append(f"current build authority {field} differs from the receipt")
    if (json.dumps(recorded_build_authority.get("clean_lean_inputs"), sort_keys=True, allow_nan=False)
            != json.dumps(current_build_authority.get("clean_lean_inputs"), sort_keys=True, allow_nan=False)):
        errors.append("current build authority Clean Lean inputs differ from the receipt")

    expected_public = expected_public_stage_tools()
    if not bin_dir.is_dir():
        errors.append(f"missing stage tool directory: {bin_dir}")
        actual_public: set[str] = set()
    else:
        actual_public = {
            path.name.removesuffix(".exe")
            for path in bin_dir.iterdir()
            if path.is_file() and os.access(path, os.X_OK)
        }
    if not expected_public <= actual_public or (
        actual_public - expected_public - set(OPTIONAL_STAGE_TOOL_PRODUCERS)
        - set(NATIVE_STAGE_TOOL_PRODUCERS)
    ):
        errors.append("current public stage tool inventory differs from the closed producer map")
    producers = stage_tool_producers_for(actual_public)

    receipt_tools = receipt.get("tools")
    if not isinstance(receipt_tools, list):
        errors.append("receipt tools field is not a list")
        receipt_tools = []
    tool_rows: dict[str, dict[str, object]] = {}
    for row in receipt_tools:
        if not isinstance(row, dict) or not isinstance(row.get("name"), str):
            errors.append("receipt contains a malformed tool row")
            continue
        name = str(row["name"])
        if name in tool_rows:
            errors.append(f"receipt contains duplicate tool row {name}")
            continue
        tool_rows[name] = row
    if set(tool_rows) != set(producers):
        errors.append("receipt tool rows do not exactly cover the closed producer map")

    for public_name, producer_name in producers.items():
        row = tool_rows.get(public_name, {})
        installed = bin_dir / _host_executable(public_name, host)
        producer = tools_dir / _host_executable(producer_name, host)
        _require_receipt_path(root, row.get("path"), installed, errors, f"{public_name} path")
        _require_receipt_path(
            root, row.get("producer_path"), producer, errors, f"{public_name} producer_path"
        )
        if row.get("producer_stage") != stage + 1:
            errors.append(f"{public_name} producer_stage is not stage {stage + 1}")
        if (
            type(row.get("producer_compiler_stage")) is not int
            or row["producer_compiler_stage"] != stage - 1
        ):
            errors.append(f"{public_name} producer_compiler_stage is not stage {stage - 1}")
        if not installed.is_file() or not producer.is_file():
            errors.append(f"{public_name} or its exact producer is missing")
            continue
        installed_sha = _sha256_file(installed)
        producer_sha = _sha256_file(producer)
        if installed_sha != producer_sha:
            errors.append(f"{public_name} no longer matches its x.py producer")
        if row.get("sha256") != installed_sha or row.get("producer_sha256") != producer_sha:
            errors.append(f"{public_name} hashes differ from the receipt")
        same_inode = os.path.samefile(installed, producer)
        if row.get("same_inode") != same_inode or row.get("status") != "bound":
            errors.append(f"{public_name} binding metadata differs from the receipt")
        version_ok, version = _capture_identity(installed, ("--version",))
        current_version = version.splitlines()[0] if version else ""
        if not version_ok or row.get("version_probe_ok") is not True:
            errors.append(f"{public_name} version identity probe failed")
        if row.get("version") != current_version:
            errors.append(f"{public_name} version identity differs from the receipt")

    trustc = bin_dir / _host_executable("trustc", host)
    rustc = bin_dir / _host_executable("rustc", host)
    builder = build / host / f"stage{stage - 1}" / "bin" / _host_executable(
        "trustc", host
    )
    compiler = receipt.get("compiler")
    if not isinstance(compiler, dict):
        errors.append("receipt compiler field is not an object")
        compiler = {}
    _require_receipt_path(root, compiler.get("path"), trustc, errors, "compiler path")
    _require_receipt_path(
        root, compiler.get("compatibility_alias"), rustc, errors, "compiler alias"
    )
    _require_receipt_path(
        root, compiler.get("producer_compiler"), builder, errors, "producer compiler"
    )
    if compiler.get("producer_compiler_stage") != stage - 1:
        errors.append("compiler producer stage differs from the receipt")
    root_head = next(
        (
            str(repository.get("head") or "")
            for repository in current_lineage.get("repositories", [])
            if repository.get("path") == "."
        ),
        "",
    )
    if compiler.get("source_commit") != root_head:
        errors.append("compiler source commit differs from current root HEAD")
    for label, path, digest_field, verbose_field in (
        ("compiler", trustc, "compiler_sha256", "compiler_verbose"),
        (
            "producer compiler",
            builder,
            "producer_compiler_sha256",
            "producer_compiler_verbose",
        ),
    ):
        if not path.is_file():
            errors.append(f"missing {label}: {path}")
            continue
        digest = _sha256_file(path)
        if compiler.get(digest_field) != digest:
            errors.append(f"{label} hash differs from the receipt")
        version_ok, verbose = _capture_identity(path, ("-Vv",))
        if not version_ok or f"commit-hash: {root_head}" not in verbose:
            errors.append(f"{label} is not bound to current root HEAD")
        if compiler.get(verbose_field) != verbose:
            errors.append(f"{label} verbose identity differs from the receipt")
    if trustc.is_file() and rustc.is_file():
        alias_sha = _sha256_file(rustc)
        if alias_sha != _sha256_file(trustc):
            errors.append("rustc compatibility alias differs from trustc")
        if compiler.get("compatibility_alias_sha256") != alias_sha:
            errors.append("rustc compatibility alias hash differs from the receipt")
        if compiler.get("compatibility_alias_same_inode") != os.path.samefile(trustc, rustc):
            errors.append("rustc compatibility alias inode identity differs from the receipt")
        sysroot_ok, reported_sysroot = _capture_identity(trustc, ("--print", "sysroot"))
        try:
            sysroot_matches = sysroot_ok and Path(reported_sysroot).resolve() == stage_root.resolve()
        except OSError:
            sysroot_matches = False
        if not sysroot_matches or compiler.get("sysroot_matches") is not True:
            errors.append("compiler no longer reports the expected stage sysroot")
        # Compared by resolved identity, not spelling: trustc prints its
        # CANONICAL sysroot (measured 2026-09-25), so after the sanctioned
        # `build -> build.noindex` move the same directory prints as
        # `.../build.noindex/...` while a pre-move receipt recorded `.../build/...`.
        if not _same_local_path(compiler.get("reported_sysroot_local_path"), reported_sysroot):
            errors.append("compiler-reported local sysroot differs from the receipt")
        if compiler.get("reported_sysroot_path_scope") != "local-diagnostic":
            errors.append("compiler-reported sysroot path scope is not local-diagnostic")

    errors.extend(stage_documentation_alias_errors(bin_dir, host))

    trustdoc = bin_dir / _host_executable("trustdoc", host)
    rustdoc = bin_dir / _host_executable("rustdoc", host)
    rustdoc_alias = receipt.get("rustdoc_alias")
    if not isinstance(rustdoc_alias, dict):
        errors.append("receipt rustdoc_alias field is not an object")
        rustdoc_alias = {}
    _require_receipt_path(root, rustdoc_alias.get("path"), rustdoc, errors, "rustdoc alias")
    _require_receipt_path(
        root, rustdoc_alias.get("owner_path"), trustdoc, errors, "rustdoc alias owner"
    )
    if rustdoc_alias.get("owner") != "trustdoc":
        errors.append("rustdoc alias owner is not trustdoc")
    if not trustdoc.is_file() or not rustdoc.is_file():
        errors.append("rustdoc compatibility alias or trustdoc is missing")
    else:
        alias_sha = _sha256_file(rustdoc)
        owner_sha = _sha256_file(trustdoc)
        if alias_sha != owner_sha:
            errors.append("rustdoc compatibility alias differs from trustdoc")
        if (
            rustdoc_alias.get("sha256") != alias_sha
            or rustdoc_alias.get("owner_sha256") != owner_sha
        ):
            errors.append("rustdoc compatibility alias hashes differ from the receipt")
        if rustdoc_alias.get("same_inode") != os.path.samefile(trustdoc, rustdoc):
            errors.append("rustdoc compatibility alias inode identity differs from the receipt")
        if rustdoc_alias.get("status") != "bound":
            errors.append("rustdoc compatibility alias binding status differs from the receipt")

    helper = receipt.get("proc_macro_helper")
    if not isinstance(helper, dict):
        errors.append("receipt proc_macro_helper field is not an object")
        helper = {}
    owned_helper = stage_root / "libexec" / _host_executable(
        "trust-analyzer-proc-macro-srv", host
    )
    retired_helper = stage_root / "libexec" / _host_executable(
        "rust-analyzer-proc-macro-srv", host
    )
    helper_producer = tools_dir / _host_executable("rust-analyzer-proc-macro-srv", host)
    _require_receipt_path(root, helper.get("path"), owned_helper, errors, "proc-macro helper")
    _require_receipt_path(
        root, helper.get("producer_path"), helper_producer, errors, "proc-macro producer"
    )
    _require_receipt_path(
        root,
        helper.get("retired_public_path"),
        retired_helper,
        errors,
        "retired proc-macro helper",
    )
    if (
        helper.get("producer_stage") != stage + 1
        or type(helper.get("producer_compiler_stage")) is not int
        or helper["producer_compiler_stage"] != stage - 1
    ):
        errors.append("proc-macro helper producer stage metadata is incorrect")
    if retired_helper.exists() or helper.get("retired_public_path_absent") is not True:
        errors.append("retired public proc-macro helper is present or misreported")
    if not owned_helper.is_file() or not helper_producer.is_file():
        errors.append("Trust-owned proc-macro helper or producer is missing")
    else:
        helper_sha = _sha256_file(owned_helper)
        producer_sha = _sha256_file(helper_producer)
        if helper_sha != producer_sha:
            errors.append("Trust-owned proc-macro helper differs from its producer")
        if helper.get("sha256") != helper_sha or helper.get("producer_sha256") != producer_sha:
            errors.append("proc-macro helper hashes differ from the receipt")
        if helper.get("same_inode") != os.path.samefile(owned_helper, helper_producer):
            errors.append("proc-macro helper inode identity differs from the receipt")
        if helper.get("status") != "bound":
            errors.append("proc-macro helper binding status differs from the receipt")

    # The LLVM the stage carries. The status word does not depend on it, and a
    # receipt written before the record existed has none and is not asked for
    # one, unless the caller requires the identity.
    llvm_lines: list[str] = []
    if "llvm_identity" in receipt:
        llvm_errors, llvm_findings = _verify_llvm_identity(root, host, receipt, **layout)
        errors.extend(llvm_errors)
        recorded_llvm = receipt["llvm_identity"]
        if not llvm_errors:
            llvm_lines.append(f"llvm: {llvm_identity_summary(recorded_llvm)}")
            if require_llvm_identity or actual_public & set(NATIVE_STAGE_TOOL_PRODUCERS):
                errors.extend(llvm_findings)
                if not recorded_llvm["identity_stated"]:
                    errors.append(
                        "the identity of the LLVM this stage carries is required "
                        "(--require-llvm-identity) and this receipt does not state it: "
                        + "; ".join(str(reason) for reason in recorded_llvm["reasons"])
                    )
            else:
                llvm_lines.extend(
                    f"llvm, not verified (--require-llvm-identity makes it an error): {finding}"
                    for finding in llvm_findings
                )
    elif require_llvm_identity:
        errors.append(
            "the identity of the LLVM this stage carries is required (--require-llvm-identity) "
            "and this receipt holds no llvm_identity record: it was written before the recreator "
            "recorded one"
        )
    native_tools, native_errors = capture_native_stage_tools(
        root, host, build, bin_dir, actual_public, receipt.get("llvm_identity"),
    )
    errors.extend(native_errors)
    recorded_native = receipt.get("native_stage_tools", [])
    if (not isinstance(recorded_native, list) or recorded_native != native_tools
            or any(type(row.get(field)) is not bool for row in recorded_native
                   for field in ("same_inode", "version_probe_ok")
                   if isinstance(row, dict))):
        errors.append("native stage tool rows differ from their exact LLVM producers")
    expected_status = _classify_receipt_status(current_lineage_status, recorded_bootstrap)
    if receipt.get("tool_binding_status") != "ready" or receipt.get("status") != expected_status:
        errors.append("receipt readiness classification disagrees with current binding/lineage")
    if receipt.get("errors") != []:
        errors.append("ready receipt contains errors")
    if require_immutable_lineage and (
        expected_status not in {"release-ready", "internal-release-ready"}
        or not expected_source_clean
        or not current_trust_from_trust
    ):
        errors.append(
            "immutable Trust-from-Trust lineage is required but this receipt is not an "
            "immutable internal/public release"
        )
    if require_public_release and expected_status != "release-ready":
        errors.append(
            "cryptographically admitted public release provenance is required but unavailable"
        )

    for line in llvm_lines:
        print(f"  {line}")
    if errors:
        for error in sorted(set(errors)):
            print(f"  ERROR: {error}")
        print(f"  rejected existing stage provenance -> {receipt_path}")
        return False
    print(f"  verified existing stage provenance ({expected_status}) -> {receipt_path}")
    return True


def find_rustup() -> str | None:
    """Find rustup, including Homebrew's keg-only installation paths."""
    direct = which("rustup")
    if direct:
        return direct

    candidates: list[Path] = []
    brew = which("brew")
    if brew:
        try:
            prefix = subprocess.run(
                [brew, "--prefix", "rustup"],
                capture_output=True,
                text=True,
                check=False,
                timeout=10,
            )
            if prefix.returncode == 0 and prefix.stdout.strip():
                candidates.append(Path(prefix.stdout.strip()) / "bin" / "rustup")
        except (FileNotFoundError, subprocess.TimeoutExpired):
            pass
    candidates.extend(
        [
            Path("/opt/homebrew/opt/rustup/bin/rustup"),
            Path("/usr/local/opt/rustup/bin/rustup"),
        ]
    )
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return str(candidate)
    return None


def register_rustup_toolchain(root: Path, host: str, stage: int) -> bool:
    """Register the built sysroot as rustup's `trust` toolchain (batteries-on).

    `rustup toolchain link` re-points an existing name safely, so every
    successful build refreshes the link. The machine default is only claimed
    when rustup has none yet — an explicitly chosen default is never silently
    displaced (switch with `rustup default trust`).
    """
    sysroot = root / "build" / host / f"stage{stage}"
    rustup = find_rustup()
    if not rustup:
        print("\n  ERROR: rustup not found — register the toolchain later with:")
        print(f"    rustup toolchain link trust {sysroot}")
        return False
    print("\n  registering rustup toolchain:")
    link = subprocess.run(
        [rustup, "toolchain", "link", "trust", str(sysroot)],
        capture_output=True,
        text=True,
    )
    if link.returncode != 0:
        print(f"  ERROR: rustup toolchain link failed: {(link.stderr or link.stdout).strip()}")
        return False
    print(f"  rustup toolchain `trust` -> {sysroot}")
    current = subprocess.run([rustup, "default"], capture_output=True, text=True)
    default_name = (current.stdout or "").strip()
    if current.returncode != 0 or not default_name:
        set_default = subprocess.run(
            [rustup, "default", "trust"], capture_output=True, text=True
        )
        if set_default.returncode == 0:
            print("  rustup default -> trust")
        else:
            print(
                "  ERROR: rustup could not select the newly linked trust toolchain: "
                f"{(set_default.stderr or set_default.stdout).strip()}"
            )
            return False
    elif not default_name.startswith("trust"):
        print(f"  rustup default stays `{default_name}` — run `rustup default trust` to switch")
    return True


def maybe_register_rustup_toolchain(
    root: Path,
    host: str,
    stage: int,
    *,
    allow_non_stage2: bool = False,
) -> bool:
    """Register stage2 only, unless the caller explicitly opts into another stage."""
    if stage != 2 and not allow_non_stage2:
        print(
            f"\n  stage{stage} build: not re-pointing the global rustup `trust` toolchain "
            "(use --register-non-stage2 to opt in)."
        )
        return True
    return register_rustup_toolchain(root, host, stage)


def _selected_homebrew_library_path() -> tuple[Path | None, Path | None]:
    """Return the exact libgit2 keg/lib pair used by the build child."""
    brew = which("brew")
    prefix: Path | None = None
    if brew:
        try:
            prefix_value = subprocess.run(
                [brew, "--prefix", "libgit2"],
                text=True,
                capture_output=True,
                check=True,
                timeout=10,
            ).stdout.strip()
        except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired):
            prefix_value = ""
        if prefix_value:
            prefix = Path(prefix_value)
    for candidate in filter(
        None,
        [
            prefix,
            Path("/opt/homebrew/opt/libgit2"),
            Path("/usr/local/opt/libgit2"),
        ],
    ):
        library = candidate / "lib"
        if library.is_dir():
            return candidate, library
    return None, None


def add_homebrew_library_path(env: dict[str, str]) -> None:
    """macOS: put the exact Homebrew libgit2 keg on LIBRARY_PATH.

    Targo's libgit2 binding needs this keg-only search path. Avoid exposing the
    broad mutable Homebrew lib directory to every native link.
    """
    if platform.system().lower() != "darwin":
        return
    _prefix, library = _selected_homebrew_library_path()
    if library is not None:
        existing = env.get("LIBRARY_PATH", "")
        if str(library) not in existing.split(":"):
            env["LIBRARY_PATH"] = (
                f"{library}:{existing}" if existing else str(library)
            )


def _advertises_z_option(help_text: str, name: str) -> bool:
    """Whether `-Z help` lists exactly this unstable option.

    Mirrors the matching bootstrap.py performs (`^\\s*-Z\\s+<name>(?:=|\\s|$)`)
    without taking a regex dependency: the name must be followed by `=`,
    whitespace, or end of line, so `trust-verify` does not match
    `trust-verify-survey` and `no-trust-verify` does not match `trust-verify`.
    """
    for line in help_text.splitlines():
        stripped = line.strip()
        if not stripped.startswith("-Z"):
            continue
        rest = stripped[2:].lstrip()
        if rest == name:
            return True
        if rest.startswith(name) and rest[len(name) : len(name) + 1] in ("=", " ", "\t"):
            return True
    return False


def seed_verification_off_switch(
    root: Path, host: str, env: dict, *, compiler: Path | None = None,
) -> str | None:
    """Which verification off-switch the selected Trust stage0 actually speaks.

    The caller passes the configured atpkg compiler when that mode is selected;
    only the archive lane defaults to the hydrated seed under build/<host>.

    The checksum-pinned seed can predate the wave-2 flag-surface consolidation
    (576db732cd) that renamed the off-switch to `-Ztrust-verify=off`. Such a
    seed advertises only the retired `-Zno-trust-verify` and aborts the very
    first bootstrap Cargo invocation with `unknown unstable option:
    trust-verify` when handed the current spelling — which is exactly what a
    hardcoded flag did here, defeating the pre-rename bridge bootstrap.py
    already carries (2149dc74774). Probe the concrete driver instead of
    assuming a vintage.

    Returns "flag" for a post-rename seed, "env" for a pre-rename one, and
    None when the driver advertises neither spelling (a stock/genesis
    compiler has no Trust machinery to disable and must never receive the
    Trust-specific unstable flag).
    """
    trustc = compiler if compiler is not None else root / "build" / host / "stage0" / "bin" / "trustc"
    if not trustc.is_file():
        return None
    try:
        result = subprocess.run(
            [str(trustc), "-Z", "help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            env=env,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if result.returncode != 0:
        return None
    help_text = result.stdout.decode("utf-8", "replace")
    if _advertises_z_option(help_text, "trust-verify"):
        return "flag"
    if _advertises_z_option(help_text, "no-trust-verify"):
        return "env"
    return None


CLEAN_LEAN_ENV_NAMES = frozenset({
    "CLEAN_OLEAN_PINNED_LEAN_LIB", "CLEAN_OLEAN_REQUIRE_PINNED_LEAN",
})

# These are existing native resource locators, not compiler/SDK selections.
# Keep their original values together with their live descriptors. The native
# owner still authenticates their custody; strict provenance's ambient-input
# refusal below is deliberately unchanged.
XPY_RESOURCE_ENV_NAMES = frozenset({
    "ATERM_SDK_LEASE_V3", "ATERM_WORKLOAD_HOST_STORE_FD_V1",
    "ATERM_WORKLOAD_CPU_FDS_V1", "BUILD_SLOT_FENCE_FDS",
    "TRUST_CPU_IMPLICIT_FD", "TRUST_CPU_HANDOFF",
    "TRUST_FIXED_ADMISSION_FD_V1", "TRUST_FIXED_CLAIM_HANDOFF_V1",
    "CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS", "CARGO_JOBSERVER_HANDOFF",
})


@dataclass(frozen=True)
class CleanLeanSelection:
    """An explicit input selector, never a release/source or cached-build token."""

    manifest: Path
    library: Path
    sha256: str

    def environment(self, root: Path) -> dict[str, str]:
        # Reuse the owner that checks the source Oracle, pinned world, complete
        # installation, links and current bytes. A path/header alone is not it.
        path = Path(__file__).resolve().with_name("mint_seed_support.py")
        spec = importlib.util.spec_from_file_location("trust_xpy_clean_lean_inputs", path)
        if spec is None or spec.loader is None:
            raise RuntimeError(f"cannot load Clean Lean input owner: {path}")
        module = importlib.util.module_from_spec(spec)
        previous = sys.dont_write_bytecode
        sys.dont_write_bytecode = True
        try:
            spec.loader.exec_module(module)
        finally:
            sys.dont_write_bytecode = previous
        current = module.verify_clean_lean_inputs(root, self.manifest, self.library, self.sha256)
        environment = current.get("environment")
        if (not isinstance(environment, dict) or set(environment) != CLEAN_LEAN_ENV_NAMES
                or environment.get("CLEAN_OLEAN_REQUIRE_PINNED_LEAN") != "1"
                or environment.get("CLEAN_OLEAN_PINNED_LEAN_LIB") != current.get("library_path")
                or not all(isinstance(value, str) for value in environment.values())):
            raise RuntimeError("validated Clean Lean input has a malformed producer environment")
        return dict(environment)


def add_clean_lean_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--clean-lean-manifest", action=_GivenOnceNotEmpty,
                        help="Explicit current Clean/Oracle/whole-installation input manifest; "
                        "stage0/1 normal builds only, not Stage2+ provenance admission.")
    parser.add_argument("--clean-lean-lib", action=_GivenOnceNotEmpty,
                        help="The independently selected pinned lib/lean named by that manifest.")
    parser.add_argument("--clean-lean-manifest-sha256", action=_GivenOnceNotEmpty,
                        help="Independently retained SHA256 of the Clean Lean manifest.")


def clean_lean_selection(args: argparse.Namespace) -> CleanLeanSelection | None:
    values = (args.clean_lean_manifest, args.clean_lean_lib, args.clean_lean_manifest_sha256)
    if not any(value is not None for value in values):
        return None
    if any(value is None for value in values):
        raise ValueError("Clean Lean selection requires manifest, library and manifest SHA256 together")
    return CleanLeanSelection(Path(values[0]), Path(values[1]), values[2])


def xpy_environment(
    root: Path, host: str, *, seed_mode: bool, seed_compiler: Path | None = None,
    clean_lean: CleanLeanSelection | None = None,
) -> dict[str, str]:
    """One actual producer environment for normal build and support commands."""
    env = os.environ.copy()
    # Validate the original advertisements before scrubbing build authority.
    # In particular, a malformed/closed locator must not disappear and make
    # the child attempt fresh admission. GNU priority remains with the shared
    # parser; do not inspect or resurrect a lower-priority advertisement.
    _seed_transport().landing_targo.resource_fds(env)
    resource_environment = {name: env[name] for name in XPY_RESOURCE_ENV_NAMES if name in env}
    lean_environment = clean_lean.environment(root) if clean_lean is not None else {}
    for name in CLEAN_LEAN_ENV_NAMES:
        if name in env and env[name] != lean_environment.get(name):
            raise RuntimeError(
                f"{name} is ambient or differs from the explicit Clean Lean input; "
                "select --clean-lean-manifest, --clean-lean-lib and "
                "--clean-lean-manifest-sha256 for both build and test-support"
            )
    env.pop(REEXEC_GUARD_ENV, None)
    # A machine-wide admission is a CPU ceiling, not compiler selection. Keep
    # its exact positive share for both Python bootstrap and the Rust driver:
    # they refuse BUILD_SLOT_HELD=1 without it and independently cap CLI/TOML
    # jobs by this share. All other CARGO_* authority remains scrubbed below.
    admitted_share = _build_slot_cpu_share(env)
    # Pre-build authority capture rejects these; scrub again at the process
    # boundary so a concurrent caller cannot smuggle compiler/linker overrides.
    manager_selector = "TRUST_BUILD_TREE_MANAGER_TARGO"
    selected_manager = env.get(manager_selector)
    for name in _ambient_build_authority_overrides(env):
        env.pop(name, None)
    # x.py owns the explicit physical-path and protocol-v2 refusal for this
    # coordination input. Forward only its selector, never a compiler or Cargo
    # override. Strict native authority capture keeps its separate rules.
    if selected_manager is not None:
        env[manager_selector] = selected_manager
    env.update(resource_environment)
    if admitted_share is not None:
        env["CARGO_BUILD_JOBS"] = admitted_share
    # Only independently selected, fully revalidated Lean inputs survive scrub.
    env.update(lean_environment)
    prepare_bootstrap_cargo_environment(root, env)
    # The Trust seed is batteries-on: without the exact bootstrap-only compiler
    # off-switch, its first Cargo invocation tries to strictly verify bootstrap's
    # third-party dependencies before the Rust bootstrap shims exist.  Besides
    # being unsupported, that contradicted the mode recorded in every stage
    # provenance receipt.  Install the recorded flag only after ambient authority
    # has been scrubbed and only for the checksum/admission-bound Trust seed.  A
    # stock/genesis compiler must never receive this Trust-specific unstable flag.
    if seed_mode:
        off_switch = seed_verification_off_switch(root, host, env, compiler=seed_compiler)
        if off_switch == "flag":
            env["RUSTFLAGS_BOOTSTRAP"] = BOOTSTRAP_COMPILER_VERIFICATION["flag"]
        elif off_switch == "env":
            # A PRE-RENAME seed gets the version-invariant nested-process
            # transport instead of a flag it cannot parse. Every Trust vintage
            # translates TRUST_NO_VERIFY before option parsing, so the recorded
            # policy is identical — only the spelling differs. Setting the flag
            # here would abort the build before a single bootstrap crate
            # compiles; see bootstrap.py's apply_trust_bootstrap_compiler_policy,
            # which reaches the same conclusion from the same probe.
            env["TRUST_NO_VERIFY"] = "1"
    add_homebrew_library_path(env)
    return env


def normal_xpy_arguments(extra: list[str]) -> list[str]:
    """Preserve tool data while keeping a selected normal config's selectors owned."""
    owned = {"--stage", "--config", "--src", "--build", "--build-dir", "--host",
             "--set", "--skip-stage0-validation"}
    test_values = {"--test-args", "--compiletest-rustc-args"}
    out = []
    index = 0
    while index < len(extra):
        argument = extra[index]
        if argument == "--":
            out.extend(extra[index:])
            break
        if argument.split("=", 1)[0] in owned:
            raise ValueError(f"{argument.split('=', 1)[0]} is owned by the selected "
                             "stage/Trust bootstrap configuration, not x.py passthrough")
        # Keep hyphen-leading test values opaque to Python's earlier parser.
        if argument in test_values and index + 1 < len(extra):
            out.append(argument + "=" + extra[index + 1])
            index += 2
        else:
            out.append(argument)
            index += 1
    return out


def run_xpy(
    root: Path, host: str, command: str, stage: int, jobs: int | None, extra: list[str],
    *, seed_mode: bool, seed_compiler: Path | None = None,
    clean_lean: CleanLeanSelection | None = None,
    config_path: Path | None = None,
    normal_config: WrittenBootstrapConfig | None = None,
) -> int:
    if command not in {"build", "test"}:
        raise ValueError("normal bootstrap command must be build or test")
    cmd = [sys.executable, str(root / "x.py"), command, "--stage", str(stage)]
    if normal_config is not None:
        if stage not in (0, 1):
            raise ValueError("selected normal bootstrap config requires stage0/1")
        if config_path is not None and config_path != normal_config.path:
            raise ValueError("conflicting normal bootstrap config paths")
        extra = normal_xpy_arguments(extra)
        normal_config.require_normal_source_identity()
        config_path = normal_config.path
    else:
        # Preserve Stage2/provenance and unbound/custom-config requests. Only a
        # byte-bound normal config can make this historical override redundant.
        cmd += ["--set", "rust.trust-source-identity=false"]
    if config_path is not None:
        cmd += ["--config", str(config_path)]
    if jobs is not None:
        cmd += ["-j", str(jobs)]
    # A literal -- starts the test tool's arguments, so owned x.py options must
    # precede the passthrough rather than becoming arguments to the test tool.
    cmd += extra
    env = xpy_environment(root, host, seed_mode=seed_mode,
                          seed_compiler=seed_compiler, clean_lean=clean_lean)
    if clean_lean is not None:
        print(f"Clean Lean input: {clean_lean.manifest} sha256={clean_lean.sha256}")
        print(f"Clean Lean library: {env['CLEAN_OLEAN_PINNED_LEAN_LIB']}")
    if normal_config is not None:
        # Environment preparation may probe inputs; recheck just before dispatch.
        normal_config.require_normal_source_identity()
    print(f"\n$ {' '.join(cmd)}\n")
    descriptors = _seed_transport().landing_targo.resource_fds(env)
    if sys.platform == "win32" and descriptors:
        raise RuntimeError("Windows x.py cannot inherit native POSIX custody")
    descriptor_arguments = {"pass_fds": descriptors} if descriptors else {}
    result = subprocess.run(cmd, env=env, cwd=str(root), **descriptor_arguments)
    if normal_config is not None:
        normal_config.require_normal_source_identity()
    if clean_lean is not None:
        # A child cannot turn a changed input into a successful retained run.
        # A later deliberately selected NEW manifest remains a normal input
        # change: x.py/Cargo owns the ensuing rebuild; no stamp is touched.
        clean_lean.environment(root)
    return result.returncode


def run_xpy_build(
    root: Path, host: str, stage: int, jobs: int | None, extra: list[str],
    *, seed_mode: bool, seed_compiler: Path | None = None,
    clean_lean: CleanLeanSelection | None = None,
    normal_config: WrittenBootstrapConfig | None = None,
) -> int:
    # Stage2/unbound requests retain the historical source identity override.
    return run_xpy(root, host, "build", stage, jobs, extra, seed_mode=seed_mode,
                   seed_compiler=seed_compiler, clean_lean=clean_lean,
                   normal_config=normal_config)


def normalized_xpy_extra(extra: list[str]) -> list[str]:
    """Normalize argparse.REMAINDER's optional separator."""
    out = list(extra)
    if out and out[0] == "--":
        out = out[1:]
    return out


# What --verify-stage-provenance reads of its command line: the stage and host
# it verifies, the requirements it asks, and --check, whose report it replaces
# (the --check help says so). The remainder is refused on its own.
VERIFICATION_READS = frozenset({
    "verify_stage_provenance",
    "check",
    "stage",
    "host",
    "require_immutable_lineage",
    "require_public_release",
    "require_llvm_identity",
    "extra",
})


def options_verification_does_not_use(args: argparse.Namespace) -> list[str]:
    """The options typed that --verify-stage-provenance would not read, in parser order.

    Until 2026-10-14 the verifier ran with whatever else was typed and read none of
    it: `--verify-stage-provenance --require-seed` (or `--llvm-config X`, `--no-build`)
    answered "verified" with the same arguments to the verifier as without them
    (measured by the review of the follow-up of 2026-10-13). Every option that is not
    at its default and is not one the verifier reads is named, so an option added to
    the parser later is refused here until it is made one the verifier reads.
    """
    defaults = vars(parse_args([]))
    return [
        "--" + dest.replace("_", "-")
        for dest, value in vars(args).items()
        if dest not in VERIFICATION_READS and value != defaults[dest]
    ]


def rustup_registration_required(
    stage: int,
    *,
    no_build: bool,
    no_register: bool,
    register_non_stage2: bool,
) -> bool:
    return (
        not no_build
        and not no_register
        and (stage == 2 or register_non_stage2)
    )


class _GivenOnce(argparse.Action):
    """Store an option's value, and refuse the option a second time.

    argparse keeps the last value of a repeated option, so until 2026-10-14
    `--verify-stage-provenance --stage 2 --stage 3` verified stage 3 without a
    word about the 2 (measured by the review of the follow-up of 2026-10-13).
    One value is used, so a second is refused, never ignored.
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.given = False

    def __call__(self, parser, namespace, values, option_string=None):
        if self.given:
            parser.error(
                f"{option_string} given twice ({getattr(namespace, self.dest)}, then {values}): "
                "one value is used, so a second is refused, never ignored"
            )
        self.given = True
        setattr(namespace, self.dest, values)


class _GivenOnceNotEmpty(_GivenOnce):
    """A host or a path: given once, and never as an empty word.

    Until 2026-10-14 the recreator read an empty value as its default: `--host ""`
    (or `--host=`) meant the detected host in every mode, the verifier included,
    and `--llvm-config ""` meant the in-tree LLVM to the config writer and the
    prerequisite check while the Stage2 capture and the LLVM-mode code tested for
    no value at all (DECISION_QUEUE, "a seal knows which LLVM it carries", the
    second reading of the follow-up's close, item (i)). An empty word names no
    host and no file, so it is refused, never read as the default, as the
    receipt reader and promote-toolchain.sh refuse an empty path.
    """

    def __call__(self, parser, namespace, values, option_string=None):
        if values == "":
            parser.error(
                f"{option_string} is empty: an empty value names nothing, so it is refused, "
                "never read as the default (leave the option out for the default)"
            )
        super().__call__(parser, namespace, values, option_string)


def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        prog="recreate-bootstrap",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument(
        "--check",
        action="store_true",
        help="Only report prerequisites and detected state; do not build, and leave the "
        "checkout as it is: a check creates, changes and removes nothing in it, not even a "
        "Python bytecode cache (the Python helpers it starts are told not to write one). "
        "Its only scratch space is the temporary directory (TMPDIR), in directories it "
        "removes before it returns: the throwaway Cargo home of the atpkg manifest-schema "
        "probe, the selected seed Targo snapshot used for runtime inspection, and the "
        "one-file crate the seed validation compiles when the hydrated stage0 carries "
        "the pinned date. Not covered: whatever the interpreter, or a tool "
        "the check runs (among them git, cargo, rustup, brew, atpkg, xcrun, the hydrated "
        "stage0 compiler and each native build tool it identifies), "
        "keeps for itself outside the checkout. With --verify-stage-provenance that "
        "verification runs instead of a check. "
        "For a Stage2+ build (not --no-build) the native rows are the answer of the native "
        "tool and SDK authority capture that build runs before x.py, run here read-only: "
        "they fail exactly when, and for the reasons, that capture would refuse the build "
        "on this machine (tools, ambient overrides, Cargo configuration, and on macOS the "
        "developer directory, SDK and dylib closure). The build's source-lineage and "
        "bootstrap-lineage captures need its submodule and config steps and are not "
        "previewed. With --fresh-seed it is the check of that build: it selects the stage0 as "
        "that build does (the pinned archives, never an atpkg pack, and without fetching) and "
        "sets nothing aside. A passing check ends `--check: prerequisites OK (stage0 mode: <mode>).` "
        "A failing check ends `--check: prerequisites NOT met (stage0 mode: <mode>).` only "
        "for those Stage2+ build flags, and only once a stage0 was selected: a failing "
        "--stage 0/1 or --no-build check prints no `stage0 mode` line, and neither does a "
        "check whose stage0 selection is refused.",
    )
    p.add_argument(
        "--verify-stage-provenance",
        action="store_true",
        help="Read-only: recompute source/tool state and verify the existing stage receipt. "
        "The receipt's `recreator_invocation` (the arguments its build was started with) "
        "cannot be recomputed: it is checked for form only, and a receipt written before "
        "that record existed is not asked for one. Of the receipt's `llvm_identity` (the "
        "LLVM the stage carries) it always checks the form, the record's agreement with its "
        "receipt, and the source identity, recomputed from this tree's HEAD. It also "
        "recomputes the fingerprint of build/<host>/llvm (with build/<host>/lld) as it is "
        "now and compares the build record there with the one the receipt quotes; what "
        "differs is printed, and is an error only with --require-llvm-identity. It cannot "
        "recompute whether LLVM was built in the receipt's run or reused, nor that the files "
        "a build record fingerprints were compiled from the sources it names: both rest on a "
        "run having found no build/<host>/llvm before the x.py that produced it. A receipt "
        "written before that record existed is not asked for one either. Of an LLVM linked "
        "through --llvm-config (mode external) it recomputes nothing: such a record is never "
        "stated and holds no source identity, and what answers for the llvm-config executable "
        "is the build-authority comparison this verification always made. It takes --stage, "
        "--host, --require-immutable-lineage, --require-public-release, --require-llvm-identity "
        "and --check (whose report it replaces); any other option, which it would not read, is "
        "refused.",
    )
    p.add_argument(
        "--require-immutable-lineage",
        action="store_true",
        help="With --verify-stage-provenance, require immutable internal or public seed lineage.",
    )
    p.add_argument(
        "--require-public-release",
        action="store_true",
        help="With --verify-stage-provenance, require cryptographically admitted public release status.",
    )
    p.add_argument(
        "--require-llvm-identity",
        action="store_true",
        help="Require that the stage states the identity of the LLVM it carries: the flag "
        "for a build that will be sealed. x.py rebuilds the in-tree LLVM when "
        "HEAD:src/llvm-project moves from the tree recorded beside it, but it keeps an LLVM "
        "that cannot say what it was built from (one built before that record, whose own "
        "build header names no commit this checkout has), and a change to src/bootstrap, "
        "src/version or the bootstrap config rebuilds none, so a reused build directory "
        "can carry an LLVM built from other sources or with another recipe; the receipt "
        "records what could be established (`llvm_identity`) "
        "and, without this flag, nothing else about the build changes. With it, on a "
        "Stage2+ build: the build is refused BEFORE x.py starts when it is already known "
        "that the identity could not be stated (build/<host>/llvm is there without the "
        "record of a build from nothing for this tree's LLVM sources, bootstrap config and "
        "native tools, or without x.py's stamp; the LLVM sources differ from HEAD; the "
        "bootstrap config does not itself say that the in-tree LLVM is linked; or the stage "
        "links an LLVM through --llvm-config, whose identity is never stated), with the "
        "command that fixes it or the statement that no single command does; and a finished "
        "build whose receipt does not state the identity fails. `--check` does not preview "
        "that refusal. With --verify-stage-provenance: the receipt must hold the record and "
        "state the identity, and build/<host>/llvm must still be what it fingerprints. "
        "Cost: an LLVM build from nothing once per build directory, and again after any "
        "change to src/llvm-project, src/bootstrap, src/version, the bootstrap config or "
        "the native tool and SDK authority the receipt binds, which is compared whole "
        "(a Homebrew self-update moves it).",
    )
    p.add_argument(
        "--stage",
        action=_GivenOnce,
        type=int,
        default=2,
        help="x.py build stage (default: 2). Given twice, it is refused, as are --host, "
        "--jobs and --llvm-config: one value is used.",
    )
    p.add_argument(
        "--register-non-stage2",
        action="store_true",
        help="Explicitly allow a non-stage2 build to re-point rustup's global `trust` toolchain.",
    )
    p.add_argument(
        "--no-register",
        action="store_true",
        help="Build and audit the sysroot without requiring rustup or registering a global "
        "toolchain name. The resulting stage directory remains directly runnable/installable.",
    )
    p.add_argument(
        "--no-atpkg",
        action="store_true",
        help="Do not seed from an atpkg-installed `trust` pack even when one is present; "
        "resolve the checksum-pinned src/stage0 seed (or genesis) instead. Once the seed "
        "ledger records a minted pin, the atpkg mode and the genesis fallback are retired "
        "(D12 (d)) and this is the default.",
    )
    p.add_argument(
        "--host",
        action=_GivenOnceNotEmpty,
        default=None,
        help="Host triple override (default: auto-detected, e.g. aarch64-apple-darwin). "
        "An empty value is refused, as is one for --llvm-config: leave the option out for "
        "the default.",
    )
    p.add_argument(
        "--force",
        action="store_true",
        help="Recreate the build/<host>/stage0 genesis adapter even if present.",
    )
    p.add_argument(
        "--genesis",
        action="store_true",
        help="Force the stock-rust genesis adapter path even if the pinned Trust "
        "seed is available (dev convenience; not release evidence).",
    )
    p.add_argument(
        "--require-seed",
        action="store_true",
        help="Require verified local-atpkg Trust (candidate only) or validated pinned "
        "Trust archives; never fall back to stock-rust genesis. Once the seed ledger "
        "records a minted pin, only the pinned archives, with or without this flag.",
    )
    p.add_argument(
        "--fresh-seed",
        action="store_true",
        help="Force pinned archives, never local atpkg (with --check too, which reports on "
        "that build and sets nothing aside). For Stage2+ immutable provenance, safely quarantine an existing extracted "
        "build/<host>/stage0 before bootstrap-lineage capture so x.py must rehydrate it "
        "from the checksum-validated archives. The backup is removed only after the "
        "provenance receipt passes direct immutable-lineage verification. It does not "
        "rebuild the in-tree LLVM: the receipt records which LLVM the stage carries, and "
        "--require-llvm-identity is what refuses one it cannot state.",
    )
    p.add_argument(
        "--no-fetch",
        action="store_true",
        help="Do not fetch missing seed payloads via agh; use only what is on disk.",
    )
    p.add_argument(
        "--force-config",
        action="store_true",
        help="Overwrite an existing bootstrap.toml/config.toml.",
    )
    p.add_argument("--prepare-tool", choices=("targo-build-tool",), default=None,
                   help="With --no-build only, inspect explicit tool graphs and defer unrelated first-party sources; never full compiler-source readiness.")
    p.add_argument("--tool-source-inspector", type=Path, default=None,
                   help="Explicit existing native Targo used only for selected tool Cargo graph inspection.")
    p.add_argument("--source-object-cache", action="append", default=[], metavar="GITLINK=REPOSITORY",
                   help="Give Agh a read-only exact-object cache for one indexed first-party checkout; "
                        "matching regular working bytes are optional native CoW DATA hints too.")
    p.add_argument("--source-working-cache", action="append", default=[], metavar="GITLINK=DIRECTORY",
                   help="Use a separate read-only regular-file DATA donor for native CoW source "
                        "materialization; never Git or publication authority. Every reused byte is "
                        "checked against the independently acquired target, with normal Git fallback.")
    p.add_argument(
        "--no-build",
        action="store_true",
        help="Set up the selected stage0 mode + config but do not invoke `./x.py build`.",
    )
    p.add_argument(
        "-j",
        "--jobs",
        action=_GivenOnce,
        type=int,
        default=None,
        help="Parallel build jobs to forward to `./x.py build`.",
    )
    p.add_argument(
        "--llvm-config",
        action=_GivenOnceNotEmpty,
        default=None,
        help="Path to an external `llvm-config` (e.g. /opt/homebrew/opt/llvm/bin/"
        "llvm-config). Links that LLVM instead of building LLVM in-tree; the "
        "compiler profile still requires cmake/ninja for LLD. The major version must "
        "match what rustc_llvm expects. The stage receipt records such an LLVM as "
        "external and never states its identity (the build binds the llvm-config "
        "executable, not what it points at), so --require-llvm-identity refuses it.",
    )
    p.add_argument(
        "extra",
        nargs=argparse.REMAINDER,
        help="Extra args after `--` are forwarded to `./x.py build` for non-provenance "
        "stage0/stage1 builds only. Stage2+ rejects them because x.py overrides can "
        "replace the compiler/config authority outside the provenance receipt; "
        "--verify-stage-provenance and --no-build, which run no x.py, reject them too. "
        "Every word from the first one that is not an option is such an argument, so "
        "type the recreator's own options before it.",
    )
    add_clean_lean_arguments(p)
    return p.parse_args(argv)


def inspect_tool_source_graph(root: Path, tool: str, inspector: Path) -> None:
    """Inspect only the bootstrap metatool and declared Targo Cargo graph.

    This is a tool-only/deferred-sources observation, never full compiler-source
    readiness. The later native x.py selected graph retains all original gates.
    """
    if tool != "targo-build-tool":
        raise RuntimeError("unsupported source-preparation tool")
    inspector = inspector.resolve(strict=True)
    if not inspector.is_file():
        raise RuntimeError("tool source inspector is unavailable")
    inspected = []
    for manifest_name in ("src/bootstrap/Cargo.toml", "src/tools/targo/Cargo.toml"):
        manifest = root / manifest_name
        lock = manifest.with_name("Cargo.lock")
        before = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in (manifest, lock)}
        argv = [str(inspector), "metadata", "--locked", "--offline",
                "--format-version", "1", "--manifest-path", str(manifest)]
        environment = os.environ.copy()
        environment["RUSTC"] = str(inspector.with_name("trustc"))
        result = subprocess.run(argv, cwd=root, env=environment, capture_output=True)
        if result.returncode != 0:
            raise RuntimeError("tool source graph inspection refused: " +
                               result.stderr.decode(errors="replace"))
        document = json.loads(result.stdout)
        if document.get("version") != 1:
            raise RuntimeError("unsupported tool source metadata schema")
        packages = document.get("packages")
        if not isinstance(packages, list) or not packages:
            raise RuntimeError("tool source graph has no package census")
        for package in packages:
            path = Path(package["manifest_path"]).resolve(strict=True)
            if path.is_relative_to(root / "first-party"):
                raise RuntimeError("selected tool requires first-party source: " + str(path))
        if before != {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in (manifest, lock)}:
            raise RuntimeError("tool source manifest/lock changed while inspected")
        inspected.append({"manifest": manifest_name, "inputs_sha256": before,
                          "argv": argv, "metadata_sha256": hashlib.sha256(result.stdout).hexdigest(),
                          "package_manifests": sorted(p["manifest_path"] for p in packages)})
    target = root / "build/tool-source-preparation"
    target.mkdir(parents=True, exist_ok=True)
    state = {"schema": "trust.tool-source-preparation.v1", "scope": "tool-only",
             "tool": tool, "compiler_sources_ready": False, "first_party": "deferred",
             "inspector_path": str(inspector),
             "inspector_sha256": hashlib.sha256(inspector.read_bytes()).hexdigest(),
             "metadata_format": 1, "graphs": inspected}
    (target / (tool + ".json")).write_text(json.dumps(state, sort_keys=True) + "\n")


def _first_party_checkout_caches(root: Path, declarations: list[str], *, working: bool = False) -> dict[str, Path]:
    if not declarations:
        return {}
    paths = {entry.path.as_posix() for entry in _indexed_submodules(root)
             if entry.path.as_posix().startswith("first-party/")}
    caches = {}
    for declaration in declarations:
        path, separator, location = declaration.partition("=")
        cache = Path(location)
        if (not separator or path not in paths or path in caches or not cache.is_absolute()
                or not cache.is_dir() or cache.resolve(strict=True).is_relative_to(root.resolve())):
            role = "working cache" if working else "object cache"
            kind = "directory" if working else "repository"
            raise RuntimeError(f"source {role} must name one indexed first-party path and an external absolute {kind}")
        if working and (root.resolve().is_relative_to(cache.resolve(strict=True))
                        or any(parent.is_symlink() for parent in (cache, *cache.parents))):
            raise RuntimeError("source working cache must be a disjoint real directory without symlink ancestors")
        caches[path] = cache
    return caches


def prepare_first_party_sources(root: Path, *, no_build: bool,
                                tool: str | None = None, inspector: Path | None = None,
                                checkout_caches: dict[str, Path] | None = None,
                                working_caches: dict[str, Path] | None = None) -> None:
    if tool is not None:
        if checkout_caches or working_caches:
            role = "working" if working_caches else "object"
            raise RuntimeError(f"source {role} caches apply only to full indexed source preparation")
        if not no_build or inspector is None:
            raise RuntimeError("explicit tool preparation requires --no-build and its source inspector")
        inspect_tool_source_graph(root, tool, inspector)
        print("\nTool-only source graphs inspected; unrelated first-party source deferred. "
              "This is not full compiler-source readiness.")
        return
    print("\nEnsuring first-party submodules are materialized:")
    if checkout_caches or working_caches:
        options = {"checkout_caches": checkout_caches} if checkout_caches else {}
        if working_caches:
            options["working_caches"] = working_caches
        ensure_submodules(root, **options)
    else:
        ensure_submodules(root)
    # Trust: retire only our own previous deferred-scope control after the
    # ordinary full source preparation actually succeeds.
    (root / "build/tool-source-preparation/targo-build-tool.json").unlink(missing_ok=True)


def main(argv: list[str] | None = None) -> int:
    ensure_python_311()
    line_buffer_output()
    # Kept as given: a Stage2+ build writes it into its receipt.
    invocation = list(sys.argv[1:] if argv is None else argv)
    if invocation[:1] == ["fetch-source-pin"]:
        return fetch_source_pin_main(invocation[1:])
    if invocation[:1] == ["materialize-source-witnesses"]:
        parser = argparse.ArgumentParser(description="Restore exact local bridge source DATA under submodule ownership")
        parser.add_argument("--root", type=Path, required=True)
        options = parser.parse_args(invocation[1:])
        materialize_bridge_source_witnesses(options.root)
        return 0
    args = parse_args(invocation)
    root = repo_root()
    host = args.host or host_triple()
    try:
        clean_lean = clean_lean_selection(args)
        if clean_lean is not None and (args.stage >= 2 or args.no_build
                                       or args.verify_stage_provenance):
            raise ValueError("explicit normal-x.py Clean Lean selection requires a stage0/1 "
                             "build or its --check; Stage2+ mint/provenance keeps its closed owner")
        if clean_lean is not None and args.check:
            clean_lean.environment(root)
    except (RuntimeError, OSError, ValueError) as error:
        print(f"Clean Lean input selection refused: {error}")
        return 2

    print(f"Trust bootstrap recreator")
    print(f"  repo:  {root}")
    print(f"  host:  {host}")

    if (
        args.require_immutable_lineage or args.require_public_release
    ) and not args.verify_stage_provenance:
        print("\nlineage/release requirements require --verify-stage-provenance.")
        return 2
    if args.fresh_seed and args.verify_stage_provenance:
        print(
            "\n--fresh-seed changes build inputs and conflicts with read-only "
            "provenance verification."
        )
        return 2
    if args.require_llvm_identity and not args.verify_stage_provenance and (
        args.check or args.no_build or args.stage < 2
    ):
        print("\n--require-llvm-identity requires a Stage2+ build or --verify-stage-provenance; "
              "it cannot be combined with --check, --no-build, or --stage 0/1.")
        return 2
    # --fresh-seed with --check is the check of that build: it selects the stage0
    # as the build does (the pinned archives, never an atpkg pack) and moves
    # nothing. Until 2026-10-14 it was refused, so the nearest check, a bare
    # `--check --stage 2` (scripts/dev-bootstrap.sh --check among its callers),
    # answered for an installed atpkg pack the --fresh-seed build never uses
    # (KNOWN_HAZARDS TRUST-KI-1014-6).
    if args.fresh_seed and (args.no_build or args.stage < 2):
        print("\n--fresh-seed requires a Stage2+ build (or the --check of one); it cannot be "
              "combined with --no-build or --stage 0/1.")
        return 2
    if args.fresh_seed and args.genesis:
        print("\n--fresh-seed requires seed mode and conflicts with --genesis.")
        return 2
    if args.fresh_seed and not args.require_seed:
        print("\n--fresh-seed requires --require-seed so it can never fall back to genesis.")
        return 2
    if args.genesis and args.require_seed:
        print("\n--genesis conflicts with --require-seed; stock rust is not a Trust seed.")
        return 2
    # The words left over (argparse's REMAINDER: everything from the first word
    # that is not an option, and what follows `--`) reach something only in a
    # build that runs x.py: forwarded there for stage 0/1, refused below for
    # Stage2+. The verifier and `--no-build` run no x.py, and nothing read them:
    # until 2026-10-13 `--verify-stage-provenance --stage 2 stage2
    # --require-llvm-identity` (or `... -- --require-llvm-identity`) answered
    # "verified" without the check it names (measured by the third reading of
    # the LLVM-identity change). Refused there too, never ignored.
    if args.prepare_tool is not None and (not args.no_build or args.check
            or args.verify_stage_provenance or args.stage > 1 or args.tool_source_inspector is None):
        print("\n--prepare-tool requires stage0/1 --no-build with an explicit source inspector; no check/provenance/build grade.")
        return 2
    if args.source_object_cache and (args.prepare_tool is not None
            or args.check or args.verify_stage_provenance):
        print("\n--source-object-cache requires full indexed source materialization.")
        return 2
    if args.source_working_cache and (args.prepare_tool is not None
            or args.check or args.verify_stage_provenance):
        print("\n--source-working-cache requires full indexed source materialization.")
        return 2
    if args.tool_source_inspector is not None and args.prepare_tool is None:
        print("\n--tool-source-inspector requires an explicit --prepare-tool.")
        return 2
    extra = normalized_xpy_extra(args.extra)
    if extra and (args.verify_stage_provenance or args.no_build):
        mode = "--verify-stage-provenance" if args.verify_stage_provenance else "--no-build"
        print(
            f"\n{mode} runs no x.py build, and these words after its options would reach "
            "nothing: " + shlex.join(extra)
        )
        print(
            "They are refused, never ignored: an option typed after a stray word or `--` is not "
            "read as an option. Type every option before any other word."
        )
        return 2
    if args.verify_stage_provenance:
        unused = options_verification_does_not_use(args)
        if unused:
            print(
                "\n--verify-stage-provenance reads a stage receipt and builds nothing, and does not "
                "use: " + " ".join(unused)
            )
            print(
                "An option it does not use is refused, never ignored. It takes --stage, --host, "
                "--require-immutable-lineage, --require-public-release, --require-llvm-identity and "
                "--check (whose report it replaces)."
            )
            return 2
        if args.stage < 2:
            print("\n--verify-stage-provenance requires --stage 2 or newer.")
            return 2
        return 0 if verify_stage_tool_provenance(
            root,
            host,
            args.stage,
            require_immutable_lineage=args.require_immutable_lineage,
            require_public_release=args.require_public_release,
            require_llvm_identity=args.require_llvm_identity,
        ) else 1

    if args.no_register and args.register_non_stage2:
        print("\n--no-register conflicts with --register-non-stage2.")
        return 2

    # One definition of "these flags run the provenance captures": it gates the
    # captures below AND where the prerequisite report gets its native rows, so
    # `--check` answers for the build the same flags would start.
    provenance_build = provenance_build_requested(args.stage, no_build=args.no_build)
    if provenance_build and extra:
        print(
            "\nStage2+ provenance builds refuse forwarded x.py arguments: "
            + " ".join(extra)
        )
        print(
            "Forwarded --set/config/compiler overrides are not bound by the stage receipt. "
            "Use the recreator's explicit options or run x.py directly without making a "
            "provenance claim."
        )
        return 2
    if provenance_build:
        # Before anything is fetched or built, for a build and for the check of
        # one: the receipt records these arguments, and one it could not verify
        # afterwards would cost the whole build.
        unrecordable = _recreator_invocation_errors(recreator_invocation_record(invocation))
        if unrecordable:
            print(
                "\nStage2+ provenance builds record their arguments in the stage receipt, "
                "and these cannot be recorded: " + "; ".join(unrecordable)
            )
            return 2

    registration_required = rustup_registration_required(
        args.stage,
        no_build=args.no_build,
        no_register=args.no_register,
        register_non_stage2=args.register_non_stage2,
    )
    # Rows printed so far; a build stops at the first table that holds an unmet
    # one, a check reports them all together at the end.
    reported: list[Prereq] = []
    if provenance_build:
        # Decided BEFORE the stage0 selection, which is where a build fetches
        # the seed archives: the native rows are the verdict of the capture this
        # build would run just before x.py (it needs nothing the selection or a
        # later step produces), and python and rustup do not depend on the mode
        # either. A build that cannot start is refused here, before any fetch.
        # A check goes on, so that it can still name the stage0 it would use.
        print()
        print("Prerequisites:")
        reported = check_prereqs(
            args.llvm_config,
            require_rustup=registration_required,
            native_authority=True,
            root=root,
            host=host,
            phase=PREREQS_BEFORE_SELECTION,
        )
        print_prereqs(reported)
        if not args.check and report_unmet_prereqs(reported):
            return 1

    print("\nSelecting stage0 authority:")
    try:
        selection = resolve_stage0_selection(root, args)
    except (RuntimeError, OSError) as error:
        print(f"\nStage0 selection refused: {error}")
        report_unmet_prereqs(reported)
        return 1
    seed_mode = selection.mode != "genesis"

    if provenance_build:
        # What only the selected mode decides: stock rustc/cargo for genesis,
        # the selected Trust seed's actual runtime on macOS.
        prereqs = check_prereqs(
            args.llvm_config,
            seed_mode=seed_mode,
            phase=PREREQS_OF_SELECTED_MODE,
            root=root,
            host=host,
            seed_selection=selection,
        )
        if prereqs:
            print()
            print(f"Prerequisites of the selected stage0 mode ({selection.mode}):")
            print_prereqs(prereqs)
    else:
        print()
        print("Prerequisites:")
        prereqs = check_prereqs(
            args.llvm_config,
            seed_mode=seed_mode,
            require_rustup=registration_required,
            root=root,
            host=host,
            seed_selection=selection,
        )
        print_prereqs(prereqs)
    reported = [*reported, *prereqs]
    if report_unmet_prereqs(reported):
        if args.check and provenance_build:
            # Still the answer to "which stage0 would this use": the docs use a
            # bare `--check` for exactly that, and a bare `--check` is a Stage 2
            # check, which a machine can now fail.
            print(f"\n--check: prerequisites NOT met (stage0 mode: {selection.mode}).")
        return 1

    if args.check:
        if args.fresh_seed:
            print(
                f"\n--fresh-seed: the build sets build/{host}/stage0 aside and x.py hydrates it "
                "again from the pinned archives validated above; a check sets nothing aside."
            )
        elif selection.mode == "atpkg" and provenance_build:
            print(
                "\nThis check answers for a build with these flags, which uses the installed atpkg "
                "pack. A --fresh-seed build never does: `--check --require-seed --fresh-seed` "
                "answers for that one."
            )
        print(f"\n--check: prerequisites OK (stage0 mode: {selection.mode}).")
        return 0

    checkout_caches = _first_party_checkout_caches(root, args.source_object_cache)
    working_caches = _first_party_checkout_caches(root, args.source_working_cache, working=True)
    if checkout_caches or working_caches:
        prepare_first_party_sources(root, no_build=args.no_build, tool=args.prepare_tool,
                                    inspector=args.tool_source_inspector, checkout_caches=checkout_caches,
                                    **({"working_caches": working_caches} if working_caches else {}))
    else:
        prepare_first_party_sources(root, no_build=args.no_build, tool=args.prepare_tool,
                                    inspector=args.tool_source_inspector)

    if not seed_mode:
        print("\nMaterializing local genesis stage0 adapter:")
        ensure_local_genesis_stage0(root, host, args.force)

    print("\nWriting bootstrap config:")
    try:
        written_config = write_config(root, host, args.force_config, args.llvm_config,
                                      seed_mode=seed_mode, selection=selection)
    except (RuntimeError, OSError, ValueError) as error:
        print(f"\nBootstrap config refused: {error}")
        return 1

    if args.no_build:
        print("\n--no-build: " + ("tool-only setup complete; full compiler sources remain deferred."
              if args.prepare_tool else "setup complete. Run `./x.py build --stage 2` when ready."))
        return 0

    source_lineage_before: dict[str, object] | None = None
    bootstrap_lineage_before: dict[str, object] | None = None
    build_authority_before: dict[str, object] | None = None
    llvm_before: dict[str, object] | None = None
    seed_stage0_quarantine: Path | None = None
    if provenance_build:
        print("\nCapturing recursive pre-build source lineage:")
        source_lineage_before = capture_source_lineage(root)
        print(f"  status: {source_lineage_before['status']}")
        print(f"  closure: {source_lineage_before['closure_sha256']}")
        if source_lineage_before["status"] == "rejected":
            for error in source_lineage_before["errors"]:
                print(f"  ERROR: {error}")
            print("\nRefusing to build from ambiguous recursive source state.")
            return 1
        if args.fresh_seed:
            print("\nPreparing fresh seed materialization for immutable provenance:")
            try:
                seed_stage0_quarantine = quarantine_seed_stage0(root, host)
            except RuntimeError as error:
                print(f"  ERROR: {error}")
                return 1
        print("\nCapturing pre-build bootstrap lineage:")
        bootstrap_lineage_before = capture_bootstrap_lineage(root, host)
        print(f"  status: {bootstrap_lineage_before['status']}")
        print(f"  config: {bootstrap_lineage_before['config_sha256']}")
        if (
            bootstrap_lineage_before["status"] == "rejected"
            or bootstrap_lineage_before["mode"] != selection.mode
            or bootstrap_lineage_before["config_sha256"] != written_config.sha256
            or bootstrap_lineage_before.get("config_path") != str(written_config.path.relative_to(root))
        ):
            for error in bootstrap_lineage_before["errors"]:
                print(f"  ERROR: {error}")
            if bootstrap_lineage_before["mode"] != selection.mode:
                print(f"  ERROR: stage0 mode mismatch: the recreator selected {selection.mode!r} "
                      f"but the bootstrap config declares {bootstrap_lineage_before['mode']!r}")
            print("\nRefusing to build with ambiguous or mismatched bootstrap lineage/config identity.")
            recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
            return 1
        if selection.mode == "atpkg" and (
            not _atpkg_authority_ready(bootstrap_lineage_before.get("atpkg_authority"))
            or bootstrap_lineage_before["atpkg_authority"] != selection.atpkg_authority
        ):
            print("\nRefusing to build: selected atpkg pack/verifier authority changed before build.")
            return 1
        print("\nCapturing pre-build native tool and SDK authority:")
        build_authority_before = capture_build_authority(root, host, args.llvm_config)
        print(f"  status: {build_authority_before['status']}")
        print(f"  authority: {build_authority_before['authority_sha256']}")
        if build_authority_before["status"] == "rejected":
            for error in build_authority_before["errors"]:
                print(f"  ERROR: {error}")
            print("\nRefusing to build with ambiguous ambient native authority.")
            recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
            return 1
        if args.fresh_seed and args.require_llvm_identity:
            try:
                preserve_empty_llvm_for_fresh_seed(root, host, args.llvm_config, written_config.path)
            except (RuntimeError, OSError, ValueError) as error:
                print(f"\nEmpty LLVM preservation refused: {error}")
                for note in getattr(error, "__notes__", ()):
                    print(f"  {note}")
                recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
                return 1
        # The record of the LLVM this build carries. By default it is ONLY a
        # record: nothing observed here stops, changes or slows the build past
        # the observation itself, and the receipt's status word is what it was.
        print("\nObserving the LLVM this build will carry:")
        llvm_before, llvm_obstacle_rows, llvm_report = observe_llvm_before_build(
            root,
            host,
            args.llvm_config,
            written_config.path,
            config_sha256=written_config.sha256,
            native_authority_sha256=build_authority_before["authority_sha256"],
        )
        for line in llvm_report:
            print(f"  {line}")
        if llvm_obstacle_rows and args.require_llvm_identity:
            # Asked for, and already known to be out of reach: refused now
            # instead of after the whole build.
            try:
                print(
                    llvm_identity_refusal(
                        root, host, llvm_before, llvm_obstacle_rows, invocation, written_config.path
                    )
                )
            finally:
                # Whatever the refusal's text meets, the stage0 goes back.
                recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
            return 1
    print("\nBuilding stage", args.stage, "(this is the long part)...")
    seed_compiler = selection.atpkg_root / "bin/trustc" if selection.mode == "atpkg" else None
    try:
        normal_config = None
        if args.stage in (0, 1):
            try:
                normal_xpy_arguments(extra)
            except ValueError:
                # Custom selector passthrough keeps its previous unbound/full
                # route; it cannot claim the writer's config as its sole owner.
                pass
            else:
                normal_config = written_config
        rc = run_xpy_build(root, host, args.stage, args.jobs, extra,
                           seed_mode=seed_mode, seed_compiler=seed_compiler,
                           **({"normal_config": normal_config} if normal_config is not None else {}),
                           **({"clean_lean": clean_lean} if clean_lean is not None else {}))
    except (RuntimeError, OSError, ValueError) as error:
        print(f"\nNormal x.py producer environment refused: {error}")
        recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
        return 1
    if rc != 0:
        print(f"\n`./x.py build` failed (exit {rc}).")
        if provenance_build:
            leave_llvm_build_record_after_failed_build(
                root,
                host,
                llvm_before,
                commit_before=_root_commit_of(source_lineage_before),
                config_path=written_config.path,
                config_sha256=written_config.sha256,
                build_authority_before=build_authority_before,
                llvm_config=args.llvm_config,
            )
        recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
        return rc

    print()
    print("Build succeeded.")
    print(f"  stage{args.stage} sysroot: build/{host}/stage{args.stage}/bin/")

    # Batteries-on: installation is incomplete if the solver is absent. Do not
    # register a compiler that would silently downgrade every solver row to
    # Unknown while the one-command path reports success.
    if not install_ay_solver(root, host, args.stage):
        print("\nBuild succeeded, but required ay installation failed.")
        if provenance_build:
            leave_llvm_build_record_after_failed_build(
                root,
                host,
                llvm_before,
                commit_before=_root_commit_of(source_lineage_before),
                config_path=written_config.path,
                config_sha256=written_config.sha256,
                build_authority_before=build_authority_before,
                llvm_config=args.llvm_config,
            )
        recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
        return 1

    # A successful compilation is not a usable stage2 result until every
    # release-facing executable is byte-bound to the x.py artifact built by
    # the immediately preceding Trust compiler generation.  This catches
    # ambient post-build replacements and hardlink-cache contamination.
    if provenance_build and not audit_stage_tool_provenance(
        root,
        host,
        args.stage,
        source_lineage_before,
        bootstrap_lineage_before,
        build_authority_before,
        args.llvm_config,
        invocation=invocation,
        llvm_before=llvm_before,
    ):
        print("\nBuild succeeded, but stage tool provenance audit failed.")
        recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
        return 1

    if args.fresh_seed and not verify_stage_tool_provenance(
        root,
        host,
        args.stage,
        require_immutable_lineage=True,
    ):
        print("\nFresh seed build completed, but immutable provenance verification failed.")
        recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
        return 1

    # Asked for by its own flag only: the receipt just written must state the
    # identity of the LLVM its stage carries, and the build directory bear it
    # out. The verification above is what it was without the flag.
    if args.require_llvm_identity and not verify_stage_tool_provenance(
        root,
        host,
        args.stage,
        require_llvm_identity=True,
    ):
        print(
            "\nBuild completed, but its receipt does not state the identity of the LLVM the "
            "stage carries (--require-llvm-identity). The reason is above and in the receipt's "
            "llvm_identity.reasons.\n"
            "No single command applies here: something changed while x.py ran, or x.py built over "
            "an LLVM that was there. Run the same command again; it then refuses before x.py "
            "starts and names what stands in the way, with the command that removes it:\n"
            f"    python3 scripts/recreate_bootstrap.py {shlex.join(invocation)}"
        )
        recover_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
        return 1

    try:
        discard_seed_stage0_quarantine(root, host, seed_stage0_quarantine)
    except RuntimeError as error:
        print(f"\nFresh seed receipt passed, but backup cleanup failed: {error}")
        return 1

    # Batteries-on for the release-facing stage2 sysroot. A stage1 convenience
    # build must not silently replace the machine-global `trust` toolchain.
    if args.no_register:
        print("\n  --no-register: leaving rustup/global toolchain state unchanged.")
    elif not maybe_register_rustup_toolchain(
        root,
        host,
        args.stage,
        allow_non_stage2=args.register_non_stage2,
    ):
        print("\nBuild succeeded, but required rustup registration failed.")
        return 1

    print("  next: re-seed bootstrap/trust-stage0 from this build by running")
    print("        python3 src/tools/trust-stage0-dist/prepare.py --help")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
