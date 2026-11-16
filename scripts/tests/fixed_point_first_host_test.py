#!/usr/bin/env python3
"""Regressions for the fixed-point kind of seed host record (docs/PLAN.md PKG-S6).

scripts/seed_fixed_point.py judges the evidence of a first Linux seed admitted as a
fixed point of an unpinned host chain, and scripts/seed_host_ledger.py admits such a
record only through FIXED_POINT_FIRST_HOSTS, the door, which lands empty. These tests
import the real seed_host_ledger.py, seed_fixed_point.py and mint_seed_support.py and
build one small self-consistent evidence set (three stage2 manifests and any
controls, every run record, three admissions, the two configs, eight real host
archives and the shared source archive, the member, native, input and chain tables).
Each test changes one thing and names the rule that must refuse it. A record whose
words say pass while its evidence says otherwise is refused; nothing the receipt
states is believed.

No compiler, no x.py, no network.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor. This test imports tomllib (3.11+) at its top.
# `python3 fixed_point_first_host_test.py` on a machine whose python3 is older re-execs
# here under the newest >=3.11 on PATH (scripts/tests/python_floor_test.py holds every
# such script to this).
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_os.execv(_floor_path, [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]])
    _floor_sys.exit("fixed_point_first_host_test.py requires Python 3.11+ (tomllib); none found on PATH")

import ast
import copy
import hashlib
import importlib.util
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import tomllib
import unittest
from pathlib import Path
from unittest import mock

# The ledger refuses a proof root reached through a link (macOS /var -> /private/var).
tempfile.tempdir = os.path.realpath(tempfile.gettempdir())

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts import seed_host_ledger as host_ledger  # noqa: E402

fp = host_ledger.fixed_point_module()
support = fp.mint_support()
_BOOTSTRAP_PY = None


def bootstrap_py():
    """src/bootstrap/bootstrap.py, whose line reader (get_toml_static) reads a config
    before x.py's Rust bootstrap reads it as TOML; loaded once, run never."""
    global _BOOTSTRAP_PY
    if _BOOTSTRAP_PY is None:
        spec = importlib.util.spec_from_file_location("trust_fixed_point_bootstrap_py",
                                                      ROOT / "src" / "bootstrap" / "bootstrap.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        _BOOTSTRAP_PY = module
    return _BOOTSTRAP_PY

HOST, DARWIN = "aarch64-unknown-linux-gnu", "aarch64-apple-darwin"
COMMIT = "82bb867eddb94599f68194f701c766f2b6f5a02f"
DATE, VERSION = "2026-11-07", "0.13.0"
P0 = "6dad0d786fa63187a5e611b440953c94a04cbfca"   # the producer's stage0 commit
S0 = "29ebb403de7a102850d6cb10a62d5cc3baf723ed"   # the cross-check's
R1 = "20565c3255adf151f9eb920e89cdf83c38f84abe"
BUILD_ROOT = f"{fp.BUILD_ROOT_PARENT}/{COMMIT[:10]}"
LEAN_LIB = f"{BUILD_ROOT}/inputs/lean/leanprover--lean4---v4.30.0-rc2/lib/lean"
ACCOUNT = ("/home/fixture-person", "fixture-person")
ALLOWED = host_ledger.FIXED_POINT_UNREPRODUCED_ALLOWED
LEAN_SHA, CARGO_SHA, ORCHESTRATION, NINJA_SHA = "4" * 64, "5" * 64, "6" * 64, "a" * 64
# The rung config every build read: also this run's builder-config in trust-src.
RUNG_CONFIG = (f'# rung config\ninclude = ["{BUILD_ROOT}/src/bootstrap.toml"]\n\n[build]\n'
               f'rustc = "{BUILD_ROOT}/stage0/bin/trustc"\ncargo = "{BUILD_ROOT}/stage0/bin/cargo"\n'
               f'rustdoc = "{BUILD_ROOT}/stage0/bin/trustdoc"\nrustfmt = "{BUILD_ROOT}/stage0/bin/trustfmt"\n'
               "jobs = 20\n").encode()
DARWIN_BUILDER_CONFIG = b"build-dir = '<home>/build'\n"
# The base config's target table, by its dotted key.
TARGET = f"target.{HOST}"
# Every key of src/bootstrap/src/core/config/toml/*.rs that is no tool key of the C12
# tool rule (seed_fixed_point.py RUST_TOOL_KEYS, HOST_TOOL_KEYS, UNBOUND_KEYS,
# TRIPLE_KEYS, the download keys, profile and include): read where bootstrap consumes
# it, each names no program for the build, or a tool it drives, to run, and no
# prebuilt machine code for it to link. A switch here may make the build run more of
# what it runs anyway (ninja selects the bound ninja over make; jemalloc and
# sanitizers build in-tree C with the bound compilers; lld builds rust-lld in-tree),
# a path here names a directory or data, and a word here may select a host library
# the linker finds on its own search path (llvm-libunwind = "system", libzstd,
# static-libstdcpp, use-libcxx, std-features: the open native-compiler-resources
# family). default-linker-linux-override = "self-contained-lld-cc" makes a built
# compiler link through cc with the rust-lld built in-tree beside it (it requires
# rust.lld), never a stage0's. trust-stage1-seed (on by default, macOS only) lets a
# fresh tree clone another worktree's stage 1: it names nothing, and refusing it set
# would not turn it off.
CONFIG_KEYS_THAT_RUN_NOTHING = frozenset({
    # [build] (toml/build.rs; tool.<name>.features is its Tool table)
    "description", "build-dir", "docs", "compiler-docs", "library-docs-private-items",
    "docs-minification", "submodules", "locked-deps", "vendor", "full-bootstrap", "bootstrap-cache-path",
    "extended", "tools", "tool", "features", "verbose", "sanitizers", "cargo-native-static",
    "low-priority", "configure-args", "local-rebuild", "print-step-timings", "print-step-rusage", "check-stage",
    "doc-stage", "build-stage", "test-stage", "install-stage", "dist-stage", "bench-stage", "metrics",
    "jobs", "compiletest-allow-stage0", "exclude", "record_failed_tests_path",
    "allocator",
    # vf5-base names a prepared DATA package Bootstrap stages into lib/trust/vf5-base-v1, its
    # bytes bound by vf5-base-sha256 in the config itself; neither runs or links anything.
    "vf5-base", "vf5-base-sha256",
    # [dist] and [install] (toml/dist.rs, toml/install.rs)
    "sign-folder", "upload-addr", "src-tarball", "compression-formats", "compression-profile",
    "include-mingw-linker", "prefix", "sysconfdir", "docdir", "bindir", "libdir", "mandir", "datadir",
    # [llvm] (toml/llvm.rs)
    "optimize", "release-debuginfo", "assertions", "tests", "enzyme", "plugins", "static-libstdcpp",
    "libzstd", "ninja", "targets", "experimental-targets", "link-jobs", "link-shared", "version-suffix",
    "use-libcxx", "allow-old-toolchain", "offload", "polly", "clang", "enable-warnings", "tpde",
    # [pgo] (toml/pgo.rs; its rustc, rustdoc, cargo and clippy tables share a Rust tool key's name)
    "llvm", "cranelift", "use", "generate",
    # [rust] (toml/rust.rs)
    "debug", "codegen-units", "codegen-units-std", "debug-assertions", "randomize-layout", "debug-assertions-std",
    "debug-assertions-tools", "overflow-checks", "overflow-checks-std", "debug-logging", "debuginfo-level",
    "debuginfo-level-rustc", "debuginfo-level-std", "debuginfo-level-tools", "debuginfo-level-tests",
    "compress-debuginfo", "backtrace", "incremental", "channel", "rpath", "strip", "frame-pointers",
    "stack-protector", "verbose-tests", "optimize-tests", "codegen-tests", "omit-git-hash", "dist-src",
    "codegen-backends", "llvm-bitcode-linker", "lld", "llvm-tools", "deny-warnings", "backtrace-on-ice",
    "verify-llvm-ir", "thin-lto-import-instr-limit", "remap-debuginfo", "jemalloc", "test-compare-mode",
    "llvm-libunwind", "control-flow-guard", "ehcont-guard", "new-symbol-mangling", "annotate-moves-size-limit",
    "profile-generate", "profile-use", "lto", "validate-mir-opts", "std-features", "break-on-ice",
    "parallel-frontend-threads", "trust-source-identity", "trust-stage1-seed", "trust-prune-superseded",
    "trust-ir-metadata", "stdlib-semver-baseline", "wasm-panic-unwind-default",
    # [target.<triple>] (toml/target.rs)
    "default-linker-linux-override", "split-debuginfo", "llvm-has-rust-patches", "crt-static", "no-std",
    # the top level (toml/change_id.rs)
    "change-id",
})
# The top-level keys TomlConfig reads itself (toml/mod.rs), each held by its own rule:
# profile (seed_fixed_point.py PROFILES) and include (the base config includes nothing,
# the rung config only the base config).
CONFIG_KEYS_WITH_THEIR_OWN_RULE = frozenset({"profile", "include"})
# The FIFO jobserver every run was handed (seed_staircase.py run --fifo-jobserver), and
# the make adapter first on its PATH, which ran HOST_TOOL_ROWS' make.
JOBSERVER = f"{BUILD_ROOT}/ledger/tmp/jobserver.fifo"
MAKE_ADAPTER = {"path": f"{BUILD_ROOT}/ledger/pathbin/make", "sha256": "6" * 64, "make": "/usr/bin/make",
                "make_sha256": "9" * 64}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest_of(text: str) -> str:
    return sha(text.encode())


# The producer's stage2, file by file; the links it holds besides.
STAGE2 = {
    "bin/trustc": b"\x7fELF trustc", "bin/rustc": b"\x7fELF trustc", "bin/trustdoc": b"\x7fELF trustdoc",
    "bin/targo": b"\x7fELF targo", "bin/cargo": b"\x7fELF targo", "bin/trustfmt": b"\x7fELF trustfmt",
    "bin/targo-trust": b"\x7fELF targo-trust", "bin/ty": b"\x7fELF ty", "bin/tippy": b"\x7fELF tippy",
    "bin/trust-analyzer": b"\x7fELF trust-analyzer", "bin/llvm-objcopy": b"\x7fELF llvm-objcopy, copied",
    "lib/librustc_driver-fixture.so": b"\x7fELF driver", "lib/libstd-fixture.so": b"\x7fELF std dylib",
    f"lib/rustlib/{HOST}/lib/libstd-fixture.rlib": b"!<arch>\nstd",
    f"lib/rustlib/{HOST}/lib/librustc_middle-fixture.rlib": b"!<arch>\nmiddle",
}
LINKS = {"bin/cargo-alias": "cargo", "lib/rustlib/src/rust": f"{BUILD_ROOT}/src"}
# archive stem -> (component directory, installed files)
ARCHIVES = {
    "trustc": ("trustc", {path: STAGE2[path] for path in ("bin/trustc", "bin/rustc", "bin/trustdoc",
                                                          "lib/librustc_driver-fixture.so",
                                                          "lib/libstd-fixture.so")}),
    "trust-std": (f"trust-std-{HOST}", {f"lib/rustlib/{HOST}/lib/libstd-fixture.rlib":
                                        STAGE2[f"lib/rustlib/{HOST}/lib/libstd-fixture.rlib"]}),
    "trustc-dev": ("trustc-dev", {f"lib/rustlib/{HOST}/lib/librustc_middle-fixture.rlib":
                                  STAGE2[f"lib/rustlib/{HOST}/lib/librustc_middle-fixture.rlib"]}),
    "targo": ("targo", {"bin/targo": STAGE2["bin/targo"], "bin/cargo": STAGE2["bin/cargo"],
                        "bin/cargo-alias": ("link", "cargo")}),
    "trustfmt": ("trustfmt-preview", {"bin/trustfmt": STAGE2["bin/trustfmt"]}),
    "targo-trust": ("targo-trust", {"bin/targo-trust": STAGE2["bin/targo-trust"]}),
    "tippy": ("tippy-preview", {"bin/tippy": STAGE2["bin/tippy"]}),
    "trust-analyzer": ("trust-analyzer-preview", {"bin/trust-analyzer": STAGE2["bin/trust-analyzer"],
                                                  "lib/rustlib/etc/analyzer-notes.txt": b"notes, not code\n"}),
}
SOURCE_FILE = "lib/rustlib/src/rust/library/core/src/lib.rs"
PRODUCER_STAGE0 = {path: digest_of(f"producer {path}") for path in
                   ("bin/trustc", "bin/cargo", "bin/targo", "bin/trustdoc", "bin/trustfmt",
                    "lib/librustc_driver-p.so", "lib/libstd-p.so")}
CROSS_STAGE0 = {path: digest_of(f"cross-check {path}") for path in PRODUCER_STAGE0}
ROOT_TRUSTC = digest_of("root trustc")
TREES = {"registry/index": {"entries": 2, "sha256": "2" * 64}, "registry/cache": {"entries": 1, "sha256": "1" * 64}}
R1_TRUSTC = digest_of("r1 trustc")
# The host tools setup bound: by role, and by the path the base config names (the same files).
GCC, GXX, PYTHON = "/usr/bin/aarch64-linux-gnu-gcc-13", "/usr/bin/aarch64-linux-gnu-g++-13", "/usr/bin/python3.12"
CXX_SHA, PYTHON_SHA = digest_of("g++"), digest_of("python")
HOST_TOOL_ROWS = {
    "cc": {"path": "/usr/bin/cc", "real": GCC, "sha256": "c" * 64, "version": "cc (fixture) 13.3.0"},
    "c++": {"path": "/usr/bin/c++", "real": GXX, "sha256": CXX_SHA, "version": "c++ (fixture) 13.3.0"},
    "python": {"path": "/usr/bin/python3", "real": PYTHON, "sha256": PYTHON_SHA, "version": "3.12.3"},
    "make": {"path": "/usr/bin/make", "real": "/usr/bin/make", "sha256": "9" * 64, "version": "GNU Make 4.3"},
    "/usr/bin/gcc": {"path": "/usr/bin/gcc", "real": GCC, "sha256": "c" * 64, "version": "gcc (fixture) 13.3.0",
                     "measured": "setup"},
    "/usr/bin/g++": {"path": "/usr/bin/g++", "real": GXX, "sha256": CXX_SHA, "version": "g++ (fixture) 13.3.0",
                     "measured": "setup"},
    "/usr/bin/python3": {"path": "/usr/bin/python3", "real": PYTHON, "sha256": PYTHON_SHA,
                         "version": "Python 3.12.3", "measured": "setup"},
}
CONFIG_HOST_TOOLS = "/usr/bin/g++:setup,/usr/bin/gcc:setup,/usr/bin/python3:setup"


def identity(stage2: dict[str, bytes]) -> dict[str, str]:
    """seed_staircase.py sysroot_files of a stage2."""
    return {path: sha(data) for path, data in stage2.items()
            if path in fp.STAGE0_FILES or path.startswith(("lib/librustc_driver-", "lib/libstd-"))}


FIXED_STAGE0 = identity(STAGE2)


def manifest(stage2: dict[str, bytes], links: dict[str, str] = LINKS) -> dict:
    """A trust-stage2-tree-v1 manifest of a tree with these files and links."""
    paths = set(stage2) | set(links)
    directories = {str(Path(path).parent) for path in paths}
    for directory in list(directories):
        while directory not in (".", ""):
            directories.add(directory)
            directory = str(Path(directory).parent)
    directories.discard(".")
    records = []
    for path in sorted(paths | directories):
        if path in stage2:
            records.append({"path": path, "kind": "file", "mode": 0o755, "bytes": len(stage2[path]),
                            "sha256": sha(stage2[path])})
        elif path in links:
            records.append({"path": path, "kind": "symlink", "target": links[path]})
        else:
            records.append({"path": path, "kind": "directory", "mode": 0o755})
    return {"schema": "trust-stage2-tree-v1", "sha256": support.records_sha256(records), "records": records}


def archive_name(stem: str) -> str:
    return f"{stem}-{VERSION}-trust" + ("" if stem == "trust-src" else f"-{HOST}") + ".tar.xz"


def write_archive(directory: Path, stem: str, folder: str, files: dict[str, bytes | tuple[str, str]],
                  builder_config: bytes | None = None, *, modes: dict[str, int] | None = None) -> Path:
    """A rust-installer archive: `files` by installed path, each bytes or ("link", target)."""
    name = archive_name(stem)
    prefix = name.removesuffix(".tar.xz")
    members = {"components": f"{folder}\n".encode(), "install.sh": b"#!/bin/sh\n",
               f"{folder}/manifest.in": "".join(f"file:{path}\n" for path in sorted(files)).encode(),
               **{f"{folder}/{path}": data for path, data in files.items()}}
    if builder_config is not None:
        members["builder-config"] = builder_config
    with tarfile.open(directory / name, "w:xz") as bundle:
        for member, data in members.items():
            info = tarfile.TarInfo(f"{prefix}/{member}")
            info.mtime = 0
            if isinstance(data, tuple):
                info.type, info.linkname, info.mode = tarfile.SYMTYPE, data[1], 0o777
                bundle.addfile(info)
                continue
            info.size = len(data)
            info.mode = (modes or {}).get(member.split("/", 1)[-1], 0o755 if member.endswith((".sh",))
                                          or "/bin/" in member else 0o644)
            bundle.addfile(info, io.BytesIO(data))
    return directory / name


CACHE: Path
MEMBERS: bytes


THIS_RUN: Path


def setUpModule() -> None:
    global CACHE, MEMBERS, THIS_RUN, _TMP
    _TMP = tempfile.TemporaryDirectory()
    CACHE = Path(_TMP.name).resolve() / "archives"
    CACHE.mkdir()
    for stem, (folder, files) in ARCHIVES.items():
        write_archive(CACHE, stem, folder, files)
    write_archive(CACHE, "trust-src", "rust-src", {SOURCE_FILE: b"pub fn core() {}\n"}, DARWIN_BUILDER_CONFIG)
    # This run's dist of trust-src: the same members, its own builder-config (the rung config).
    (CACHE.parent / "this-run").mkdir()
    THIS_RUN = write_archive(CACHE.parent / "this-run", "trust-src", "rust-src", {SOURCE_FILE: b"pub fn core() {}\n"},
                             RUNG_CONFIG)
    MEMBERS = members()


def tearDownModule() -> None:
    _TMP.cleanup()


def pins() -> dict[str, str]:
    result = {"dist_server": "file://{trust-root}/bootstrap/trust-stage0"}
    for name in ("compiler", "rustfmt"):
        result.update({f"{name}_git_commit_hash": COMMIT, f"{name}_date": DATE,
                       f"{name}_version": f"{VERSION}-trust", f"{name}_channel_manifest_hash": digest_of("manifest")})
    for component in host_ledger.COMPONENTS:
        if component != "trust-src":
            result[f"dist/{DATE}/{component}-{VERSION}-trust-{DARWIN}.tar.xz"] = digest_of(f"darwin {component}")
    for path in sorted(CACHE.glob("*.tar.xz")):
        result[f"dist/{DATE}/{path.name}"] = sha(path.read_bytes())
    return result


def run_record(label: str, words: list[str], stage0_commit: str, stage0: dict[str, str],
               produced: dict[str, str] | None) -> dict:
    tools = {key: {"kind": "elf", "named": f"{BUILD_ROOT}/stage0/bin/{name}", "real": f"{BUILD_ROOT}/stage0/bin/{name}",
                   "sha256": stage0[f"bin/{name}"]} for key, name in fp.STAGE0_KEYS.items()}
    record = {
        "schema": "trust-seed-staircase-v1", "kind": "rung", "label": label, "worktree": f"{BUILD_ROOT}/src",
        "commit": COMMIT, "argv": ["x.py", "--config", f"{BUILD_ROOT}/ledger/rung.bootstrap.toml", *words],
        "rc": 0, "no_stock_evidence": True, "trap_hits": [], "elapsed_s": 10,
        "process_census": {"kind": "process-census", "flagged": [], "ended": "watched-exited", "max_gap_s": 1.1,
                           "abandoned_children": 0},
        "build_census": {"kind": "build-census", "clean": True, "rustc_info_files": 7},
        "stage0_matches_admission": True, "stage0_runtime_unchanged": True, "tool_dirs_unchanged": True,
        "config_tools": {"matches_admission": True, "config_sha256": "rung", "problems": [], "tools": tools},
        "stage0_observed": {"root": f"{BUILD_ROOT}/stage0", "sha256": dict(stage0)},
        "tool_dirs": [{"dir": f"{BUILD_ROOT}/tools", "entries": [
            {"name": "ninja", "path": f"{BUILD_ROOT}/tools/ninja", "real": f"{BUILD_ROOT}/tools/ninja",
             "sha256": NINJA_SHA}]}],
        "environment": {"HOME": f"{BUILD_ROOT}/home", "USER": "trust-seed", "LOGNAME": "trust-seed",
                        "CARGO_HOME": f"{BUILD_ROOT}/ledger/cargo-home", "TMPDIR": f"{BUILD_ROOT}/ledger/tmp",
                        "CARGO_NET_OFFLINE": "true", "CLEAN_OLEAN_PINNED_LEAN_LIB": LEAN_LIB,
                        "CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1", "TRUST_STAIRCASE_RUNG": label,
                        "PATH": f"{BUILD_ROOT}/ledger/trap:/usr/bin:/bin",
                        "MAKEFLAGS": f"-j20 --jobserver-auth=fifo:{JOBSERVER}"},
        # seed_staircase.py run --fifo-jobserver, for the rung config's jobs = 20.
        "jobserver": {"kind": "fifo", "path": JOBSERVER, "jobs": 20, "jobs_from": "[build] jobs of the rung config",
                      "tokens": 19, "tokens_at_end": 19, "path_unchanged": True, "make_adapter": dict(MAKE_ADAPTER)},
        "clean_lean": {"library": LEAN_LIB, "before": {"manifest_sha256": LEAN_SHA},
                       "after": {"manifest_sha256": LEAN_SHA}, "unchanged": True},
        "tool": {"path": f"{ACCOUNT[0]}/trust-seed-driver/scripts/seed_staircase.py", "sha256": ORCHESTRATION,
                 "checkout_head": "7" * 40, "modified_in_checkout": False},
        "stage0_commit": stage0_commit, "stage0_sha256": dict(stage0),
    }
    if produced is not None:
        record["produced"] = {"stage2": f"{BUILD_ROOT}/src/build/{HOST}/stage2", "sha256": produced}
    return record


def ran(stage0: dict[str, str], **more):
    """A run-record change: it ran another stage0, as every field that says so says."""
    def change(run):
        run.update(stage0_sha256=dict(stage0), **more)
        run["stage0_observed"]["sha256"] = dict(stage0)
        for key, name in fp.STAGE0_KEYS.items():
            run["config_tools"]["tools"][key]["sha256"] = stage0[f"bin/{name}"]
    return change


def dump(value: object) -> bytes:
    return (json.dumps(value, indent=1, sort_keys=True) + "\n").encode()


def members() -> bytes:
    """archive-members.json of the eight host archives and the shared one (prepare.py
    kept the pinned trust-src with builder-config excluded; its repack is "d" * 64)."""
    archives = [fp.archive_table(CACHE / archive_name(stem)) for stem in sorted(ARCHIVES)]
    source = CACHE / archive_name("trust-src")
    kept = {"this_run_sha256": "d" * 64, "excluded": [
        {"path": "builder-config", "pinned_sha256": sha(DARWIN_BUILDER_CONFIG), "this_run_sha256": sha(RUNG_CONFIG),
         "reason": "the bootstrap config of the host that ran x.py dist"}]}
    shared = fp.shared_entry(source, sha(source.read_bytes()), THIS_RUN, kept)
    return dump({"schema": fp.MEMBERS_SCHEMA, "host": HOST, "archives": sorted(archives, key=lambda a: a["name"]),
                 "shared": shared})


class Evidence:
    """A self-consistent record. `raw` holds every evidence file as the producing
    host would (naming the account); `fields()` recomputes the receipt from it;
    `write()` normalises, renders and lays out the seed root."""

    def __init__(self, base: Path, fixed: dict[str, bytes] | None = None,
                 controls: tuple[dict[str, bytes], ...] = (), cross: dict[str, bytes] | None = None):
        self.base = base
        self.trees = {"producer": dict(STAGE2), "fixed-point": {**STAGE2, **(fixed or {})},
                      "cross-check": {**STAGE2, **(cross or {})}}
        for number, change in enumerate(controls, 1):
            self.trees[f"control-{number}"] = {**STAGE2, **change}
        self.controls = len(controls)
        self.pins = pins()
        self.raw: dict[str, bytes] = {}
        self.surface = {"schema": "trust-self-host-seed-surface-v1", "host": HOST, "source_version": VERSION,
                        "tool_versions": {"trustc": "rustc 1.101.0-dev (82bb867ed 2026-11-07)",
                                          "targo": "targo 1.101.0-dev (82bb867ed 2026-11-07)",
                                          "trustfmt": "trustfmt 1.12.0-trust (82bb867edd 2026-11-07)"},
                        "entrypoint_sha256": {name: sha(STAGE2[f"bin/{name}"]) for name in
                                              ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt")},
                        "tree": {"sha256": digest_of("installed tree")}}
        self.fields_override: dict[str, str] = {}
        self.build_raw()

    # the evidence ------------------------------------------------------------
    def build_raw(self) -> None:
        self.raw["base-config.toml"] = (b'profile = "compiler"\n\n[build]\npython = "/usr/bin/python3"\n\n'
                                        b'[llvm]\ndownload-ci-llvm = false\n\n[rust]\ndownload-rustc = false\n\n'
                                        b'[install]\nprefix = "' + BUILD_ROOT.encode() + b'/src/install"\n\n'
                                        b'[target.aarch64-unknown-linux-gnu]\ncc = "/usr/bin/gcc"\n'
                                        b'cxx = "/usr/bin/g++"\nlinker = "/usr/bin/gcc"\n')
        self.raw["rung-config.toml"] = RUNG_CONFIG
        for role, tree in self.trees.items():
            self.raw[f"stage2-{role}.json"] = dump(manifest(tree))
        stage0 = {"producer": (P0, PRODUCER_STAGE0), "cross-check": (S0, CROSS_STAGE0),
                  "fixed-point": (COMMIT, FIXED_STAGE0)}
        for role, (commit, digests) in stage0.items():
            self.raw[f"admission-{role}.json"] = dump({"kind": "stage0-admission", "schema": "trust-seed-staircase-v1",
                                                       "commit": commit, "sha256": digests,
                                                       "stage0": f"{BUILD_ROOT}/stage0"})
        build = list(fp.BUILD_WORDS)
        labels = {"producer": "p-build", "fixed-point": "f-build", "cross-check": "s-build"}
        for role, tree in self.trees.items():
            commit, digests = stage0.get(role, (COMMIT, FIXED_STAGE0))
            label = labels.get(role) or f"c{role.rsplit('-', 1)[1]}-build"
            self.raw[f"run-{role}.json"] = dump(run_record(label, build, commit, digests, identity(tree)))
        for name, label, words in (("producer-dist", "p-dist", ["dist", "--stage", "2", *host_ledger.COMPONENTS]),
                                   ("producer-full", "p-full", ["build", "--stage", "2"]),
                                   ("producer-manifest-tool", "p-manifest-tool",
                                    ["build", "--stage", "2", "src/tools/build-manifest"])):
            self.raw[f"run-{name}.json"] = dump(run_record(label, words, P0, PRODUCER_STAGE0, identity(STAGE2)))
        rows = [{"path": "llvm/bin/llvm-objcopy", "kind": "elf", "bytes": 26,
                 "sha256": sha(STAGE2["bin/llvm-objcopy"])},
                {"path": "llvm/lib/libLLVM.a", "kind": "ar", "bytes": 9, "sha256": digest_of("libLLVM")}]
        self.raw["native-outputs.json"] = dump({"schema": fp.NATIVE_SCHEMA, "files": len(rows),
                                                "sha256": support.records_sha256(rows), "rows": rows})
        self.raw["inputs.json"] = dump({
            "schema": fp.INPUTS_SCHEMA, "commit": COMMIT, "host": HOST, "root": BUILD_ROOT,
            "cargo_home_inputs": {"sha256": CARGO_SHA, "fingerprint": "3" * 64, "trees": TREES,
                                  "manifest": {"schema": "trust-cargo-home-inputs-v1", "fingerprint": "3" * 64,
                                               "trees": TREES, "source": f"{ACCOUNT[0]}/cargo-home"}},
            "clean_lean_inputs": {"sha256": LEAN_SHA, "library": LEAN_LIB},
            "ninja": {"path": f"{BUILD_ROOT}/tools/ninja", "bytes": 396960, "sha256": NINJA_SHA},
            "host_tools": copy.deepcopy(HOST_TOOL_ROWS)})
        self.raw["chain.json"] = dump({
            "schema": fp.CHAIN_SCHEMA, "NOT_A_LINEAGE_RECORD": "root is not a src/stage0-pinned extraction",
            "source": {"file": f"{ACCOUNT[0]}/linux-selfhost/CHAIN-UNPINNED-ROOT.json", "sha256": "8" * 64},
            "root": {"commit": fp.ROOT_COMMIT, "compiler_sha256": ROOT_TRUSTC},
            "rungs": [
                {"label": "r1", "commit": R1, "stage0_commit": fp.ROOT_COMMIT, "stage0_compiler_sha256": ROOT_TRUSTC,
                 "produced_compiler_sha256": R1_TRUSTC, "rc": 0, "no_stock_evidence": True, "record_sha256": "1" * 64},
                {"label": "r2", "commit": S0, "stage0_commit": R1, "stage0_compiler_sha256": R1_TRUSTC,
                 "produced_compiler_sha256": CROSS_STAGE0["bin/trustc"], "rc": 0, "no_stock_evidence": True,
                 "record_sha256": "2" * 64},
                {"label": "r3", "commit": P0, "stage0_commit": S0, "stage0_compiler_sha256": CROSS_STAGE0["bin/trustc"],
                 "produced_compiler_sha256": PRODUCER_STAGE0["bin/trustc"], "rc": 0, "no_stock_evidence": True,
                 "record_sha256": "3" * 64}],
            "origin": {"provenance": [{"file": f"{ACCOUNT[0]}/seal/PROVENANCE", "reported_commit": fp.ROOT_COMMIT},
                                      {"file": f"{ACCOUNT[0]}/toolchains/trust-ec2b5c59/PROVENANCE",
                                       "reported_commit": fp.STOCK_ANCESTOR_COMMIT}],
                       "config_lines": [f'rustc = "{ACCOUNT[0]}/toolchains/trust-ec2b5c59/bin/trustc"']}})
        self.raw["archive-members.json"] = MEMBERS

    def doc(self, name: str) -> dict:
        return json.loads(self.raw[name])

    def edit(self, name: str, change) -> None:
        """Change one evidence JSON file in place."""
        value = self.doc(name)
        change(value)
        self.raw[name] = dump(value)

    # the receipt, computed here (not by the module under test) --------------
    def tracked(self) -> tuple[dict[str, bytes], dict[str, int]]:
        tracked, counts = {}, {}
        for name, payload in self.raw.items():
            tracked[name], counts[name] = fp.normalise(payload, ACCOUNT)
        return tracked, counts

    def fields(self) -> dict[str, str]:
        self.bind_rung()
        tracked, counts = self.tracked()
        docs = {name: json.loads(payload) for name, payload in tracked.items() if name.endswith(".json")}
        producer = docs["stage2-producer.json"]
        rows = {row["path"]: row for row in producer["records"]}
        files = {path: row["sha256"] for path, row in rows.items() if row["kind"] == "file"}
        seeds = [docs["stage2-fixed-point.json"], *(docs[f"stage2-control-{n}.json"]
                                                    for n in range(1, self.controls + 1))]
        not_reproduced, nondeterministic = [], []
        for path in ALLOWED:
            seen = {json.dumps({r["path"]: r for r in tree["records"]}.get(path), sort_keys=True) for tree in seeds}
            if len(seen) > 1:
                nondeterministic.append(path)
            if json.dumps(rows.get(path), sort_keys=True) not in seen:
                not_reproduced.append(path)
        members = docs["archive-members.json"]
        native = {row["sha256"] for row in docs["native-outputs.json"]["rows"]}
        copied = sum(1 for digest in files.values() if digest in native)
        archive_only = sorted({member["path"] for archive in members["archives"] for member in archive["members"]
                               if member["path"] not in rows})
        executables = sorted({member["path"] for archive in members["archives"] for member in archive["members"]
                              if member["path"] not in rows and member["kind"] in ("script", "executable")})

        def listed(items):
            return ",".join(sorted(items)) or "none"

        def verdict(role):
            return "identical" if docs[f"stage2-{role}.json"]["records"] == producer["records"] else \
                "compiler-and-std-identical"

        # SEED-TOKEN-LEAK-STAGE0-1: every run whose jobserver came back short, <label>:<given>-><returned>.
        deficits = []
        for name, doc in docs.items():
            held = doc.get("jobserver") if name.startswith("run-") else None
            given, returned = (held or {}).get("tokens"), (held or {}).get("tokens_at_end")
            if type(given) is int and type(returned) is int and returned < given:
                deficits.append(f"{doc['label']}:{given}->{returned}")

        fields = {
            "schema": "trust-seed-fixed-point-v1", "kind": "fixed-point-unpinned-root", "host": HOST,
            "source_commit": COMMIT, "source_commit_date": DATE, "source_version": VERSION,
            "root": "unpinned-host-chain", "predecessor_pin": "none", "lineage_disjoint_anchor": "none",
            "double_compile_diverse": "false", "independent_chain_reproduction": "none",
            "producer_custody": "recorded-not-authenticated", "replayed_on": "producing-host",
            "stock_built_ancestor": "inferred-no-receipt",
            "stock_built_ancestor_commit": "ec2b5c59f7ae81dc57dac2a3346cb4c0ef9fad0d",
            "stock_built_ancestor_toolchain": fp.STOCK_ANCESTOR_TOOLCHAIN,
            "root_commit": "6986546eaafc7620e49331269685dbd1b2900ba3",
            "chain_commits": ",".join(("6986546eaafc7620e49331269685dbd1b2900ba3", R1, S0, P0)),
            "cohort_mint_host": DARWIN,
            "open_input_families": ",".join(sorted(open_families())),
            "build_root": BUILD_ROOT,
            "build_scope": "<build>/<host>/stage2 after x.py build --stage 2 compiler/rustc library/std",
            "build_driver": "each build's own stage0 cargo",
            "producer_stage0_commit": P0, "producer_stage0_compiler_sha256": PRODUCER_STAGE0["bin/trustc"],
            "producer_stage0_driver_sha256": PRODUCER_STAGE0["lib/librustc_driver-p.so"],
            "producer_stage0_cargo_sha256": PRODUCER_STAGE0["bin/cargo"],
            "cross_check_stage0_commit": S0, "cross_check_stage0_compiler_sha256": CROSS_STAGE0["bin/trustc"],
            "cross_check_stage0_driver_sha256": CROSS_STAGE0["lib/librustc_driver-p.so"],
            "cross_check_stage0_cargo_sha256": CROSS_STAGE0["bin/cargo"],
            "fixed_point_stage0": "pinned-archives",
            "fixed_point_stage0_compiler_sha256": FIXED_STAGE0["bin/trustc"],
            "fixed_point_stage0_driver_sha256": FIXED_STAGE0["lib/librustc_driver-fixture.so"],
            "fixed_point_stage0_cargo_sha256": FIXED_STAGE0["bin/cargo"],
            "controls": str(self.controls),
            "base_config_sha256": sha(tracked["base-config.toml"]),
            "rung_config_sha256": sha(tracked["rung-config.toml"]),
            "config_generator_commit": COMMIT, "config_departures": "build.jobs",
            "dist_components": " ".join(host_ledger.COMPONENTS), "orchestration_commit": "7" * 40,
            "orchestration_sha256": ORCHESTRATION, "private_home": f"{BUILD_ROOT}/home",
            "clean_lean_inputs_sha256": LEAN_SHA, "cargo_home_inputs_sha256": CARGO_SHA,
            "native_outputs_sha256": docs["native-outputs.json"]["sha256"],
            "host_c_compiler": f"{'c' * 64} cc (fixture) 13.3.0", "config_host_tools": CONFIG_HOST_TOOLS,
            "account_home_sha256": fp.account_digest("home", ACCOUNT[0]),
            "account_login_sha256": fp.account_digest("login", ACCOUNT[1]),
            "stage2_tree_sha256_producer": producer["sha256"],
            "stage2_tree_sha256_fixed_point": docs["stage2-fixed-point.json"]["sha256"],
            "stage2_tree_sha256_cross_check": docs["stage2-cross-check.json"]["sha256"],
            "stage2_core_sha256": support.records_sha256([row for row in producer["records"]
                                                          if row["path"] not in ALLOWED]),
            "fixed_point_verdict": verdict("fixed-point"), "cross_check_verdict": verdict("cross-check"),
            "not_reproduced": listed(not_reproduced), "nondeterministic": listed(nondeterministic),
            "not_reproduced_cause_hypothesis": fp.NOT_REPRODUCED_HYPOTHESIS if not_reproduced else "none",
            "compared_files": str(len(files)), "rust_built_rows": str(len(files) - copied),
            "native_copied_rows": str(copied),
            "archive_members": str(sum(len(archive["members"]) for archive in members["archives"])),
            "archive_only": listed(archive_only), "archive_only_executables": listed(executables),
            "archive_bytes_total": str(sum(archive["bytes"] for archive in members["archives"])),
            "no_stock_evidence": "pass", "trap_hits": "0", "process_census_flagged": "0",
            "jobserver_token_deficits": listed(deficits),
            "shared_source_archive": "bytes pinned by cohort_mint_host", "shared_source_members": "identical",
            "shared_source_members_excluded": "builder-config", "shared_source_bytes": "recompressed-differs",
        }
        # run records name the tracked rung config's digest
        for name, payload in tracked.items():
            field = fp.evidence_field(name)
            fields[f"{field}_sha256"] = sha(payload)
            fields[f"{field}_raw_sha256"] = sha(self.raw[name])
            fields[f"{field}_normalised_count"] = str(counts[name])
        fields.update(self.fields_override)
        return fields

    def bind_rung(self) -> None:
        """Every run record names the tracked rung config's digest (as the real runs do)."""
        rung = sha(fp.normalise(self.raw["rung-config.toml"], ACCOUNT)[0])
        for name in list(self.raw):
            if name.startswith("run-"):
                self.edit(name, lambda run: run["config_tools"].update(config_sha256=rung))

    # the seed root ------------------------------------------------------------
    def receipt(self, fields: dict[str, str] | None = None, rows: str = "") -> bytes:
        self.bind_rung()
        tracked, _ = self.tracked()
        producer = json.loads(tracked["stage2-producer.json"])
        files = {row["path"]: row["sha256"] for row in producer["records"] if row["kind"] == "file"}
        links = {row["path"]: row["target"] for row in producer["records"]
                 if row["kind"] == "symlink" and not row["target"].startswith("/")}
        return fp.render_receipt(self.fields() if fields is None else fields, files, links) + rows.encode()

    def rendered(self, fields: dict[str, str], *, extra: dict[str, str]) -> bytes:
        """A receipt in its canonical form with `extra` compiler_file rows besides the producer's."""
        self.bind_rung()
        producer = json.loads(self.tracked()[0]["stage2-producer.json"])
        files = {row["path"]: row["sha256"] for row in producer["records"] if row["kind"] == "file"}
        links = {row["path"]: row["target"] for row in producer["records"]
                 if row["kind"] == "symlink" and not row["target"].startswith("/")}
        return fp.render_receipt(fields, {**files, **extra}, links)

    def write(self, *, receipt: bytes | None = None, extra: dict[str, bytes] | None = None,
              missing: tuple[str, ...] = ()) -> tuple[Path, dict, dict]:
        """(seed root, host record, candidate door) of the evidence as it stands."""
        self.bind_rung()
        seed = self.base / f"seed-{len(list(self.base.glob('seed-*')))}" / "bootstrap" / "trust-stage0"
        proofs = seed / "host-proofs" / HOST
        (proofs / "fixed-point").mkdir(parents=True)
        tracked, _ = self.tracked()
        for name, payload in {**tracked, **(extra or {})}.items():
            if name not in missing:
                (proofs / "fixed-point" / name).write_bytes(payload)
        receipt = self.receipt() if receipt is None else receipt
        (proofs / "SEED-FIXED-POINT").write_bytes(receipt)
        surface = dump(self.surface)
        (proofs / "seed-surface.json").write_bytes(surface)
        door = {HOST: {"commit": COMMIT, "receipt_sha256": sha(receipt)}}
        try:
            record = host_ledger.make_fixed_point_host_record(self.pins, HOST, receipt, surface, door=door)
        except ValueError:
            record = {"schema": host_ledger.FIXED_POINT_SCHEMA, "unrenderable": True}
        (proofs / "host-record.json").write_bytes(host_ledger.record_bytes(record))
        dated = seed / "dist" / DATE
        dated.mkdir(parents=True)
        for path in CACHE.glob("*.tar.xz"):
            shutil.copyfile(path, dated / path.name)
        return seed, record, door


def open_families() -> list[str]:
    """seed_input_closure.py OPEN_FAMILIES' names, read from its source (it is
    loaded only through the source loader, so it is parsed, not imported)."""
    tree = ast.parse((ROOT / "scripts" / "seed_input_closure.py").read_text())
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(getattr(t, "id", None) == "OPEN_FAMILIES" for t in node.targets):
            return [element.elts[0].value for element in node.value.elts]
    raise AssertionError("seed_input_closure.py has no OPEN_FAMILIES")


class Case(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name).resolve()

    def evidence(self, **options) -> Evidence:
        return Evidence(self.base, **options)

    def capture(self, evidence: Evidence, **write) -> dict:
        seed, record, door = evidence.write(**write)
        actual, _ = host_ledger.capture_fixed_point_record(seed, evidence.pins, HOST, record, door=door)
        return actual

    def refuses(self, pattern: str, evidence: Evidence, **write) -> str:
        with self.assertRaisesRegex(ValueError, pattern) as caught:
            self.capture(evidence, **write)
        return str(caught.exception)

    def refused_field(self, pattern: str, **override) -> None:
        evidence = self.evidence()
        evidence.fields_override = override
        self.refuses(pattern, evidence)


class DoorTests(Case):
    def test_the_door_lands_empty(self):
        self.assertEqual(host_ledger.FIXED_POINT_FIRST_HOSTS, {})
        self.assertIn(host_ledger.FIXED_POINT_SCHEMA, host_ledger.HOST_SCHEMAS)
        self.assertEqual(host_ledger.FIXED_POINT_UNREPRODUCED_ALLOWED, ("bin/targo-trust", "bin/ty"))

    def test_empty_door_refuses_every_record(self):
        evidence = self.evidence()
        seed, record, door = evidence.write()
        # Accepted with the candidate door, by every rule ...
        host_ledger.capture_fixed_point_record(seed, evidence.pins, HOST, record, door=door)
        # ... and refused by the real, empty table, through either entry point.
        with self.assertRaisesRegex(ValueError, "fixed-point A1: the door .*has no entry for "
                                                "aarch64-unknown-linux-gnu"):
            host_ledger.capture_host_record(seed, evidence.pins, HOST, record)
        with self.assertRaisesRegex(ValueError, "fixed-point A1"):
            host_ledger.capture_fixed_point_record(seed, evidence.pins, HOST, record)
        with mock.patch.dict(host_ledger.FIXED_POINT_FIRST_HOSTS, door):
            actual, _ = host_ledger.capture_host_record(seed, evidence.pins, HOST, record)
        self.assertEqual(actual, record)

    def test_door_binds_host_commit_and_receipt_digest(self):
        evidence = self.evidence()
        seed, record, door = evidence.write()
        receipt = (seed / "host-proofs" / HOST / "SEED-FIXED-POINT").read_bytes()
        surface = (seed / "host-proofs" / HOST / "seed-surface.json").read_bytes()
        for what, entry in (("another commit", {"commit": "f" * 40, "receipt_sha256": sha(receipt)}),
                            ("another receipt", {"commit": COMMIT, "receipt_sha256": "0" * 64}),
                            ("no receipt digest", {"commit": COMMIT})):
            with self.subTest(what), self.assertRaisesRegex(ValueError, "fixed-point A1"):
                host_ledger.make_fixed_point_host_record(evidence.pins, HOST, receipt, surface, door={HOST: entry})
        # A2: Darwin can never use the kind, whatever the door says.
        with self.assertRaisesRegex(ValueError, "fixed-point A2: aarch64-apple-darwin is not a native Linux host"):
            host_ledger.make_fixed_point_host_record(evidence.pins, DARWIN, receipt, surface,
                                                     door={DARWIN: door[HOST]})
        # A3, A4: the cohort.
        split = {**evidence.pins, "rustfmt_date": "2026-11-08"}
        with self.assertRaisesRegex(ValueError, "fixed-point A3"):
            host_ledger.make_fixed_point_host_record(split, HOST, receipt, surface, door=door)
        short = {key: value for key, value in evidence.pins.items() if f"/tippy-{VERSION}-trust-{HOST}" not in key}
        with self.assertRaisesRegex(ValueError, "missing exact aarch64-unknown-linux-gnu seed archive"):
            host_ledger.make_fixed_point_host_record(short, HOST, receipt, surface, door=door)
        self.assertEqual(record["admission_kind"], "fixed-point-unpinned-root")


class ReceiptFormTests(Case):
    def test_duplicate_compiler_file_path_refused(self):
        evidence = self.evidence()
        receipt = evidence.receipt()
        first = next(line for line in receipt.decode().splitlines() if line.startswith("compiler_file="))
        for what, rows, pattern in (
                ("a repeated path", first + "\n", "B1: receipt line .* repeats the compared path 'bin/cargo'"),
                ("a repeated path as a link", "compiler_link=x " + first.split(" ", 1)[1] + "\n",
                 "B1: receipt line .* repeats the compared path"),
                ("a repeated field", "controls=0\n", "B1: the receipt repeats the field controls"),
                ("a path out of stage2", f"compiler_file={'a' * 64} ../etc/passwd\n", "B1: .*escapes stage2"),
                ("an absolute path", f"compiler_file={'a' * 64} /bin/sh\n", "B1: .*escapes stage2"),
                ("a malformed line", "not a field\n", "B1: receipt line .* is not a key=value line"),
                ("a short digest", "compiler_file=abc bin/x\n", "B1: .*no exact sha256")):
            with self.subTest(what), self.assertRaisesRegex(ValueError, "fixed-point " + pattern):
                fp.parse_receipt(receipt + rows.encode())
        for payload, pattern in ((b"", "empty or over"), (b"x" * (fp.MAX_PROOF_BYTES + 1), "empty or over"),
                                 (b"schema=x\n", "no compiler_file rows"), (b"\xff\n", "not UTF-8")):
            with self.subTest(pattern), self.assertRaisesRegex(ValueError, "fixed-point B1: .*" + pattern):
                fp.parse_receipt(payload)
        # The capture path parses the same way: a duplicated row never reaches the evidence.
        self.refuses("B1: receipt line .* repeats the compared path", evidence,
                     receipt=receipt + (first + "\n").encode())

    def test_identity_and_build_literals_are_the_pins(self):
        for key, value, pattern in (
                ("source_commit", "f" * 40, "B2: source_commit"), ("source_version", "0.14.0", "B2: source_version"),
                ("source_commit_date", "2026-11-08", "B2: source_commit_date"),
                ("build_root", "/var/tmp/elsewhere", "B2: build_root"),
                ("build_scope", "everything", "B2: build_scope"),
                ("build_driver", "the producer's cargo", "B2: build_driver"),
                ("fixed_point_stage0", "a copy", "B2: fixed_point_stage0"),
                ("private_home", "/home/someone", "B2: private_home"),
                ("kind", "genesis-root", "B2: kind"), ("schema", "trust-seed-mint-v1", "B2: schema")):
            with self.subTest(key):
                self.refused_field(pattern, **{key: value})

    def test_disclosure_literals_cannot_change(self):
        for key, value in (("root", "pinned"), ("predecessor_pin", "29ebb403de"),
                           ("lineage_disjoint_anchor", COMMIT), ("double_compile_diverse", "true"),
                           ("independent_chain_reproduction", "darwin-chain"),
                           ("producer_custody", "authenticated"), ("replayed_on", "second-host")):
            with self.subTest(key):
                self.refused_field(f"B3: {key} = ", **{key: value})
        self.refused_field("B3: cohort_mint_host", cohort_mint_host=HOST)
        self.refused_field("B3: root_commit", root_commit=P0)

    def test_stock_ancestor_only_inferred(self):
        for value in ("none", "false", "recorded", "absent"):
            with self.subTest(value):
                self.refused_field("B4: stock_built_ancestor = ", stock_built_ancestor=value)
        evidence = self.evidence()
        fields = evidence.fields()
        del fields["stock_built_ancestor"]
        with self.assertRaisesRegex(ValueError, "B1: the fields to render"):
            evidence.receipt(fields)
        text = evidence.receipt().decode().replace("stock_built_ancestor=inferred-no-receipt\n", "")
        self.refuses("B1: the receipt lacks stock_built_ancestor", evidence, receipt=text.encode())
        self.refused_field("B4: stock_built_ancestor_commit", stock_built_ancestor_commit="e" * 39 + "x")
        self.refused_field("B4: stock_built_ancestor_commit", stock_built_ancestor_commit="e" * 40)

    def test_mint_vocabulary_refused(self):
        evidence = self.evidence()
        for row in ("pinned_seed_commit=" + P0, "ddc_verdict=identical", "self_host_proof=pass",
                    "ddc_seed_relation=lineage-disjoint"):
            with self.subTest(row):
                self.refuses("B5: the receipt uses the mint vocabulary", evidence,
                             receipt=evidence.receipt() + (row + "\n").encode())

    def test_open_input_families_cannot_shrink(self):
        self.assertEqual(list(fp.OPEN_INPUT_FAMILIES), sorted(open_families()))
        self.assertEqual(len(fp.OPEN_INPUT_FAMILIES), 8)
        families = sorted(open_families())
        for value in (",".join(families[1:]), ",".join(families + ["new-family"]), ",".join(reversed(families))):
            with self.subTest(value):
                self.refused_field("B6: open_input_families", open_input_families=value)

    def test_digests_and_commits_are_formed_and_distinct(self):
        self.refused_field("B7: producer_stage0_compiler_sha256 is not a sha256",
                           producer_stage0_compiler_sha256="xyz")
        self.refused_field("B7: orchestration_commit is not a commit", orchestration_commit="HEAD")
        self.refused_field("B7: the producer's stage0, the cross-check's stage0 and the source are not three",
                           cross_check_stage0_commit=P0)
        chain = ",".join((fp.ROOT_COMMIT, R1, S0, P0))
        for value in (",".join((R1, S0, P0)), ",".join((fp.ROOT_COMMIT, R1, S0)), ",".join((fp.ROOT_COMMIT, R1, P0)),
                      chain + "," + P0):
            with self.subTest(value):
                self.refused_field("B7: chain_commits", chain_commits=value)
        self.refused_field("B7: the base config was not written by the source commit", config_generator_commit=P0)

    def test_more_than_three_controls_refused(self):
        evidence = self.evidence()
        text = evidence.receipt().decode().replace("controls=0\n", "controls=4\n")
        self.refuses("C5: controls = '4': at most 3", evidence, receipt=text.encode())

    def test_normalisation_fields_must_be_there(self):
        evidence = self.evidence()
        receipt = evidence.receipt().decode()
        for key in ("evidence_run_producer_raw_sha256", "evidence_chain_normalised_count", "account_login_sha256"):
            with self.subTest(key):
                text = "".join(line + "\n" for line in receipt.splitlines() if not line.startswith(key + "="))
                self.refuses("T7: the receipt lacks its normalisation fields", evidence, receipt=text.encode())
        # A count that does not fit the two digests.
        self.refused_field("T7: run-producer.json had replacements and is its raw record's bytes",
                           evidence_run_producer_raw_sha256=evidence.fields()["evidence_run_producer_sha256"])
        self.refused_field("T7: base-config.toml had nothing replaced and is not its raw record's bytes",
                           evidence_base_config_raw_sha256="0" * 64)


class AccountTests(Case):
    def test_normalise_replaces_home_then_login_as_a_word(self):
        payload = (b'{"tool": "x", "/home/fixture-person": 1, "user": "fixture-person", '
                   b'"other": "fixture-personal", "dash": "x-fixture-person.y"}')
        text, count = fp.normalise(payload, ACCOUNT)
        self.assertEqual(text, b'{"tool": "<home>/trust/x", "<home>": 1, "user": "<account>", '
                               b'"other": "fixture-personal", "dash": "x-<account>.y"}')
        self.assertEqual(count, 4)
        self.assertEqual(fp.normalise(b"nothing here", ACCOUNT), (b"nothing here", 0))
        with self.assertRaisesRegex(ValueError, "T7: an evidence file is not UTF-8"):
            fp.normalise(b"\xff", ACCOUNT)

    def test_the_account_is_found_from_the_receipts_digests(self):
        home, login = fp.account_digest("home", ACCOUNT[0]), fp.account_digest("login", ACCOUNT[1])
        for payload, found in ((b'"/var/x/home/fixture-person/y"', "home"), (b'"path": "/home/fixture-person"', "home"),
                               (b"user=fixture-person\n", "login"), (b'"a.fixture-person-b"', "login"),
                               (b'"\\/home\\/fixture-person"', "home"), (b'"fixture-personal"', None),
                               (b'"\\u0066ixture-person"', "login")):
            with self.subTest(payload):
                self.assertEqual(fp.account_found(payload, home, login, name="x.json"), found)
        self.assertIsNone(fp.account_found(b"<home>/x <account>", home, login, name="x.txt"))

    def test_an_account_name_left_in_is_refused(self):
        evidence = self.evidence()
        # A tracked file that names the account; the receipt binds it as written.
        evidence.raw["inputs.json"] = evidence.raw["inputs.json"].replace(
            b'"root"', b'"note": "/home/fixture\\u002dperson/x", "root"')
        self.refuses(r"T7: inputs.json still names the invoking account's home", evidence)
        evidence = self.evidence()
        evidence.surface["tool_versions"]["targo"] = "targo built by fixture-person"
        self.refuses(r"T7: seed-surface.json still names the invoking account's login", evidence)

    def test_the_tracked_evidence_names_no_account(self):
        evidence = self.evidence()
        tracked, counts = evidence.tracked()
        self.assertGreater(counts["run-producer.json"], 0)
        self.assertGreater(counts["chain.json"], 0)
        self.assertEqual(counts["base-config.toml"], 0)
        for name, payload in tracked.items():
            self.assertNotIn(b"fixture-person", payload, name)
        self.capture(evidence)


class EvidenceTests(Case):
    def test_valid_record_round_trips(self):
        evidence = self.evidence()
        seed, record, door = evidence.write()
        rendered = "\n".join(["[release]", *host_ledger.render_host_tables({HOST: record})])
        parsed = tomllib.loads(rendered)["release"]
        self.assertEqual(parsed["hosts"][HOST], record)
        self.assertIs(host_ledger.select_host_record(parsed, HOST), parsed["hosts"][HOST])
        with mock.patch.dict(host_ledger.FIXED_POINT_FIRST_HOSTS, door):
            actual, digest = host_ledger.capture_host_record(seed, evidence.pins, HOST, parsed["hosts"][HOST])
        self.assertEqual(actual, record)
        self.assertEqual(digest, sha((seed / "host-proofs" / HOST / "host-record.json").read_bytes()))
        self.assertEqual(record["root_disclosure"]["stock_built_ancestor"], "inferred-no-receipt")
        self.assertEqual(record["root_disclosure"]["not_reproduced"], "none")
        self.assertEqual(set(record["root_disclosure"]), set(fp.DISCLOSED))
        for absent in ("mint", "pinned_seed_date", "root_initialization", "legacy_admission"):
            self.assertNotIn(absent, record)
        self.assertEqual(len(record["payloads"]), 9)
        self.assertTrue(all(isinstance(value, str) for value in record["root_disclosure"].values()))
        # The full join over the real archives holds too.
        self.assertGreater(fp.check_archive_joins(seed, record["payloads"], HOST, host_ledger.read_proof,
                                                  archive_root=seed), 10)

    def test_record_cannot_be_rebound(self):
        evidence = self.evidence()
        seed, record, door = evidence.write()
        proofs = seed / "host-proofs" / HOST

        def flipped(path: Path, old: bytes, new: bytes):
            payload = path.read_bytes()
            self.assertIn(old, payload)
            path.write_bytes(payload.replace(old, new, 1))
            return lambda: path.write_bytes(payload)

        changed_pin = next(key for key in evidence.pins if f"/trustc-{VERSION}-trust-{HOST}" in key)
        cases = (
            ("a pin", lambda: None, {changed_pin: "0" * 64}, "A1|rebound|differs from its original|C13"),
            ("a receipt byte", lambda: flipped(proofs / "SEED-FIXED-POINT", b"controls=0", b"controls=1"), {},
             "A1"),
            ("a surface byte", lambda: flipped(proofs / "seed-surface.json", b"rustc 1.101.0", b"rustc 1.101.1"), {},
             "differs from its original native record"),
            ("an evidence byte", lambda: flipped(proofs / "fixed-point" / "chain.json", b'"r1"', b'"r0"'), {},
             "C1: chain.json has sha256"),
            ("a host-record field", lambda: flipped(proofs / "host-record.json", b'"producing-host"',
                                                    b'"another-host"'), {}, "differs from its original"),
        )
        for what, change, pins_change, pattern in cases:
            with self.subTest(what):
                undo = change()
                try:
                    with self.assertRaisesRegex(ValueError, pattern):
                        host_ledger.capture_fixed_point_record(seed, {**evidence.pins, **pins_change}, HOST,
                                                               record, door=door)
                finally:
                    if undo:
                        undo()
        # The ledger table edited (a field of the record the recreator was handed).
        edited = copy.deepcopy(record)
        edited["root_disclosure"]["producer_custody"] = "authenticated"
        with self.assertRaisesRegex(ValueError, "differs from its original"):
            host_ledger.capture_fixed_point_record(seed, evidence.pins, HOST, edited, door=door)
        host_ledger.capture_fixed_point_record(seed, evidence.pins, HOST, record, door=door)

    def test_metadata_without_evidence_is_refused(self):
        evidence = self.evidence()
        self.refuses(r"C1: host-proofs/.*/fixed-point holds no extra file beyond, and lacks \['run-producer.json'\]",
                     evidence, missing=("run-producer.json",))
        evidence = self.evidence()
        self.refuses(r"C1: .*holds \['notes.txt'\] beyond", evidence, extra={"notes.txt": b"x"})
        evidence = self.evidence()
        self.refuses(r"C1: run-cross-check.json has sha256 [0-9a-f]{64}, and the receipt's "
                     "evidence_run_cross_check_sha256 is 0{64}",
                     evidence, receipt=evidence.receipt({**evidence.fields(),
                                                         "evidence_run_cross_check_sha256": "0" * 64}))
        # Every file gone: a receipt, a surface and a host record alone admit nothing.
        evidence = self.evidence()
        self.refuses("C1: ", evidence, missing=tuple(evidence.raw))

    def test_core_digest_is_recomputed_from_manifests(self):
        self.refused_field("C4: stage2_core_sha256 is not the core digest", stage2_core_sha256="0" * 64)
        self.refused_field("C2: stage2_tree_sha256_producer is not the digest", stage2_tree_sha256_producer="0" * 64)
        evidence = self.evidence()
        evidence.edit("stage2-producer.json", lambda doc: doc["records"].append(
            {"path": "bin/extra", "kind": "file", "mode": 493, "bytes": 1, "sha256": "1" * 64}))
        self.refuses("C2: .*stage2 tree digest does not match its records", evidence)
        evidence = self.evidence()
        evidence.edit("stage2-cross-check.json", lambda doc: doc["records"].append(doc["records"][1]))
        self.refuses("C2: .*repeats stage2 record path", evidence)
        evidence = self.evidence()
        evidence.edit("stage2-producer.json", lambda doc: doc.update(schema="trust-stage2-tree-v2"))
        self.refuses("C2: .*invalid stage2 manifest schema", evidence)

    def test_three_cores_must_agree(self):
        for role, change in (("cross-check", {"bin/trustc": b"\x7fELF trustc, another"}),
                             ("fixed-point", {"lib/librustc_driver-fixture.so": b"\x7fELF driver, another"}),
                             ("fixed-point", {f"lib/rustlib/{HOST}/lib/libstd-fixture.rlib": b"!<arch>\nother std"})):
            with self.subTest(role=role, change=sorted(change)):
                options = {"cross" if role == "cross-check" else "fixed": change}
                evidence = self.evidence(**options)
                self.refuses(f"C4: the {role} tree differs from the producer's outside bin/targo-trust, bin/ty "
                             rf"\({sorted(change)[0]}\)", evidence)

    def test_difference_outside_the_two_files_refuses(self):
        # A control may differ only where the fixed point may.
        evidence = self.evidence(fixed={"bin/ty": b"\x7fELF ty, order 2"},
                                 controls=({"bin/ty": b"\x7fELF ty", "bin/trustdoc": b"\x7fELF trustdoc 2"},))
        self.refuses(r"C4: the control-1 tree differs from the producer's outside .* \(bin/trustdoc\)", evidence)
        # And a row the receipt lists that the producer's manifest does not hold.
        evidence = self.evidence()
        self.refuses("C3: the compiler_file rows are not exactly the producer manifest's files", evidence,
                     receipt=evidence.rendered({**evidence.fields(), "compared_files": "16"},
                                               extra={"bin/hidden": "a" * 64}))
        evidence = self.evidence()
        text = evidence.receipt().decode()
        drop = next(line for line in text.splitlines() if line.endswith(" bin/ty"))
        self.refuses("C3: compared_files = 15, and the receipt has 14", evidence,
                     receipt=text.replace(drop + "\n", "").encode())
        self.refuses("C3: the compiler_link rows are not", evidence,
                     receipt=text.replace("compiler_link=cargo bin/cargo-alias\n", "").encode())

    def test_reproduced_means_a_seed_build_gave_the_producer_bytes(self):
        other, third = b"\x7fELF ty, order 2", b"\x7fELF ty, order 3"
        cases = (
            ("P equals F", {}, (), ("none", "none"), "identical"),
            ("F differs, a control gives P's bytes", {"bin/ty": other}, ({},), ("none", "bin/ty"),
             "compiler-and-std-identical"),
            ("F and the controls vary and none is P's", {"bin/ty": other}, ({"bin/ty": third},),
             ("bin/ty", "bin/ty"), "compiler-and-std-identical"),
            ("both files, one reproduced", {"bin/ty": other, "bin/targo-trust": b"\x7fELF tt 2"},
             ({"bin/targo-trust": b"\x7fELF tt 3"}, {"bin/targo-trust": b"\x7fELF tt 2"}),
             ("bin/targo-trust", "bin/targo-trust,bin/ty"), "compiler-and-std-identical"),
        )
        for what, fixed, controls, (not_reproduced, nondeterministic), verdict in cases:
            with self.subTest(what):
                evidence = self.evidence(fixed=fixed, controls=controls)
                fields = evidence.fields()
                self.assertEqual((fields["not_reproduced"], fields["nondeterministic"], fields["fixed_point_verdict"]),
                                 (not_reproduced, nondeterministic, verdict))
                actual = self.capture(evidence)
                self.assertEqual(actual["root_disclosure"]["not_reproduced"], not_reproduced)
                self.assertEqual(actual["root_disclosure"]["controls"], str(len(controls)))
        # Every build by the pinned seed agrees, and not with the producer: refused.
        for controls in ((), ({"bin/ty": other},), ({"bin/ty": other}, {"bin/ty": other}, {"bin/ty": other})):
            with self.subTest(controls=len(controls)):
                evidence = self.evidence(fixed={"bin/ty": other}, controls=controls)
                self.refuses(r"C5: bin/ty has one digest in every build by the pinned seed \("
                             rf"{len(controls) + 1}\) and another in the producer's", evidence)
        # The receipt's lists must be the recomputed ones.
        evidence = self.evidence(fixed={"bin/ty": other}, controls=({"bin/ty": third},))
        fields = evidence.fields()
        for key, value, pattern in (("not_reproduced", "none", "C5: not_reproduced = 'none'"),
                                    ("nondeterministic", "none", "C5: nondeterministic = 'none'"),
                                    ("not_reproduced", "bin/targo-trust,bin/ty", "C5: not_reproduced = "),
                                    ("fixed_point_verdict", "identical", "C6: fixed_point_verdict = 'identical'")):
            with self.subTest(key=key, value=value):
                change = {key: value}
                if key == "not_reproduced" and value == "none":
                    change["not_reproduced_cause_hypothesis"] = "none"
                evidence.fields_override = change
                self.refuses(pattern, evidence)
        evidence = self.evidence()
        evidence.fields_override = {"cross_check_verdict": "compiler-and-std-identical"}
        self.refuses("C6: cross_check_verdict = 'compiler-and-std-identical', and the manifests give 'identical'",
                     evidence)
        self.refused_field("C5: not_reproduced = 'bin/trustc' is not a sorted list", not_reproduced="bin/trustc",
                           not_reproduced_cause_hypothesis="x")
        self.refused_field("C5: a hypothesis is given for files that were all reproduced",
                           not_reproduced_cause_hypothesis="a guess")

    def test_run_records_are_read(self):
        def environment(key, value):
            def change(run):
                if value is None:
                    run["environment"].pop(key, None)
                else:
                    run["environment"][key] = value
            return change

        cases = (
            ("rc 1", lambda run: run.update(rc=1), "x.py exited 1"),
            ("a trap hit", lambda run: run.update(trap_hits=["cargo"]), "trap hits"),
            ("a flagged process", lambda run: run["process_census"].update(flagged=[{"exe": "rustc"}]),
             "census flagged"),
            ("an incomplete census", lambda run: run["process_census"].update(ended="sampler-died"), "census flagged"),
            ("a census gap", lambda run: run["process_census"].update(max_gap_s=600.0), "census flagged"),
            ("a dirty build census", lambda run: run["build_census"].update(clean=False), "build census"),
            ("no .rustc_info.json", lambda run: run["build_census"].update(rustc_info_files=0), "build census"),
            ("another worktree", lambda run: run.update(worktree="/var/tmp/elsewhere/src"), "it ran in"),
            ("another argv", lambda run: run.update(argv=run["argv"] + ["--keep-stage", "1"]), "its argv"),
            ("another commit", lambda run: run.update(commit=P0), "it built"),
            ("HOME outside the root", environment("HOME", "/home/fixture-person"), "HOME"),
            ("another USER", environment("USER", "fixture-person"), "USER"),
            ("SSH_AUTH_SOCK present", environment("SSH_AUTH_SOCK", "/run/user/1000/ssh"), "SSH_AUTH_SOCK"),
            ("CARGO_NET_OFFLINE absent", environment("CARGO_NET_OFFLINE", None), "CARGO_NET_OFFLINE"),
            ("a Lean variable missing", environment("CLEAN_OLEAN_REQUIRE_PINNED_LEAN", None),
             "CLEAN_OLEAN_REQUIRE_PINNED_LEAN"),
            ("TMPDIR outside the ledger", environment("TMPDIR", "/tmp"), "TMPDIR"),
            ("the Lean library changed", lambda run: run["clean_lean"].update(unchanged=False), "Lean library"),
            ("another config", lambda run: run["config_tools"].update(config_sha256="0" * 64), "config x.py read"),
            ("a config the admission does not name", lambda run: run["config_tools"].update(matches_admission=False),
             "config x.py read"),
            ("stage0 not the admission", lambda run: run.update(stage0_matches_admission=False),
             "stage0_matches_admission"),
            ("no-stock false", lambda run: run.update(no_stock_evidence=False), "no-stock evidence"),
            ("another run tool", lambda run: run["tool"].update(sha256="0" * 64), "seed_staircase.py"),
            ("a modified run tool", lambda run: run["tool"].update(modified_in_checkout=True), "seed_staircase.py"),
            ("another label", lambda run: run.update(label="x-build"), "label"),
        )
        for what, change, pattern in cases:
            for name in ("run-producer.json", "run-fixed-point.json", "run-producer-dist.json"):
                with self.subTest(what, name=name):
                    evidence = self.evidence()
                    if what == "another config":
                        original = evidence.bind_rung
                        evidence.bind_rung = lambda: (original(), evidence.edit(name, change))
                    else:
                        evidence.edit(name, change)
                    self.refuses(rf"C7: {name} is not a clean run: .*{pattern}", evidence)
        evidence = self.evidence()
        evidence.edit("run-cross-check.json", lambda run: run.update(label="p-build"))
        self.refuses("C7: run-cross-check.json is not a clean run: its label 'p-build' is not s-build", evidence)
        evidence = self.evidence(fixed={"bin/ty": b"\x7fELF ty 2"}, controls=({},))
        evidence.edit("run-control-1.json", lambda run: (run.update(label="f-build-2"),
                                                         run["environment"].update(TRUST_STAIRCASE_RUNG="f-build-2")))
        self.refuses("C7: run-control-1.json is not a clean run: its label 'f-build-2' is not c1-build", evidence)
        # A later attempt's label is that role's.
        evidence = self.evidence()
        evidence.edit("run-fixed-point.json", lambda run: (run.update(label="f-build-2"),
                                                           run["environment"].update(TRUST_STAIRCASE_RUNG="f-build-2")))
        self.capture(evidence)

    def test_manifest_must_be_its_runs_tree(self):
        evidence = self.evidence()
        evidence.edit("run-cross-check.json", lambda run: run["produced"]["sha256"].update(
            {"bin/trustc": "9" * 64}))
        self.refuses("C8: stage2-cross-check.json is not the tree run-cross-check.json says it produced", evidence)
        evidence = self.evidence()
        evidence.edit("run-fixed-point.json", lambda run: run.pop("produced"))
        self.refuses("C8: stage2-fixed-point.json is not the tree", evidence)
        evidence = self.evidence()
        evidence.edit("run-producer-full.json", lambda run: run["produced"]["sha256"].update(
            {"lib/libstd-fixture.so": "9" * 64}))
        self.refuses("C8: run-producer-full.json left a stage2 whose identity files are not the producer's compared "
                     "rows", evidence)

    def test_admission_must_be_the_runs_stage0(self):
        evidence = self.evidence()
        evidence.edit("admission-producer.json", lambda doc: doc.update(refusals=["a stock binary"]))
        self.refuses("C9: admission-producer.json is not a clean stage0 admission", evidence)
        evidence = self.evidence()
        evidence.edit("admission-cross-check.json", lambda doc: doc["sha256"].update({"bin/cargo": "9" * 64}))
        self.refuses("C9: admission-cross-check.json is not the stage0 run-cross-check.json ran", evidence)
        evidence = self.evidence()
        evidence.edit("admission-producer.json", lambda doc: doc.update(commit=R1))
        evidence.edit("run-producer.json", lambda run: run.update(stage0_commit=R1))
        self.refuses("C9: admission-producer.json is not the stage0 .* or not the receipt's commit", evidence)
        self.refused_field("C9: the receipt's producer stage0 digests", producer_stage0_cargo_sha256="9" * 64)
        evidence = self.evidence()
        evidence.edit("run-producer-dist.json", ran(CROSS_STAGE0))
        self.refuses("C9: run-producer-dist.json did not run the producer's stage0", evidence)

    def test_fixed_point_stage0_is_the_archive_compiler(self):
        # The fixed point's stage0 is a compiler whose bytes are not the producer's rows.
        stage0 = {**FIXED_STAGE0, "bin/trustfmt": "9" * 64}
        evidence = self.evidence()
        evidence.edit("admission-fixed-point.json", lambda doc: doc.update(sha256=stage0))
        for name in ("run-fixed-point.json",):
            evidence.edit(name, ran(stage0))
        self.refuses("C10: the fixed-point stage0's bin/trustfmt is not the producer's row", evidence)
        evidence = self.evidence()
        stage0 = {key: value for key, value in FIXED_STAGE0.items() if not key.startswith("lib/libstd-")}
        evidence.edit("admission-fixed-point.json", lambda doc: doc.update(sha256=stage0))
        evidence.edit("run-fixed-point.json", ran(stage0))
        self.refuses("C10: admission-fixed-point.json does not name .* the std dylib", evidence)
        evidence = self.evidence(fixed={"bin/ty": b"\x7fELF ty 2"}, controls=({},))
        evidence.edit("run-control-1.json", ran(PRODUCER_STAGE0, stage0_commit=P0))
        self.refuses("C10: run-control-1.json did not run the fixed point's stage0", evidence)

    def test_same_compiler_repeat_cannot_stand_in(self):
        evidence = self.evidence()
        evidence.edit("admission-cross-check.json", lambda doc: doc.update(sha256=PRODUCER_STAGE0))
        evidence.edit("run-cross-check.json", ran(PRODUCER_STAGE0))
        evidence.fields_override = {"cross_check_stage0_compiler_sha256": PRODUCER_STAGE0["bin/trustc"],
                                    "cross_check_stage0_driver_sha256": PRODUCER_STAGE0["lib/librustc_driver-p.so"],
                                    "cross_check_stage0_cargo_sha256": PRODUCER_STAGE0["bin/cargo"]}
        self.refuses("C11: the producer, fixed-point and cross-check stage0 compilers are not three different",
                     evidence)

    def test_configs_are_read(self):
        evidence = self.evidence()
        evidence.raw["rung-config.toml"] += b'[rust]\nlto = "off"\n'
        self.refuses(r"C12: the rung config departs from the recreator's in 'build.jobs,rust.lto', and "
                     "config_departures says 'build.jobs'", evidence)
        evidence = self.evidence()
        evidence.raw["rung-config.toml"] = evidence.raw["rung-config.toml"].replace(
            f"{BUILD_ROOT}/stage0/bin/cargo".encode(), b"/usr/bin/cargo")
        self.refuses("C12: rung-config.toml names build.cargo = '/usr/bin/cargo'", evidence)
        evidence = self.evidence()
        evidence.raw["rung-config.toml"] = evidence.raw["rung-config.toml"].replace(
            b"jobs = 20", b'jobs = 20\ncargo-clippy = "/opt/stock/cargo-clippy"')
        evidence.fields_override = {"config_departures": "build.cargo-clippy,build.jobs"}
        self.refuses("C12: rung-config.toml names build.cargo-clippy = '/opt/stock/cargo-clippy', outside", evidence)
        evidence = self.evidence()
        evidence.raw["rung-config.toml"] = evidence.raw["rung-config.toml"].replace(b"src/bootstrap.toml",
                                                                                    b"src/other.toml")
        self.refuses("C12: rung-config.toml does not include exactly", evidence)
        self.refused_field("C12: base_config_sha256 or rung_config_sha256 is not", base_config_sha256="0" * 64)

    def test_archive_members_join_the_manifest(self):
        def member(path):
            def change(doc):
                for archive in doc["archives"]:
                    for row in archive["members"]:
                        if row["path"] == path:
                            yield archive, row
            return change

        def edit_member(path, update):
            def change(doc):
                for archive, row in list(member(path)(doc)):
                    update(row)
                    archive["members_sha256"] = support.records_sha256(archive["members"])
            return change

        evidence = self.evidence()
        evidence.edit("archive-members.json", edit_member("bin/tippy", lambda row: row.update(sha256="9" * 64)))
        self.refuses("C13: tippy-0.13.0-trust-aarch64-unknown-linux-gnu.tar.xz ships bin/tippy with other bytes",
                     evidence)
        # An elf member with no row refuses, even when the receipt lists it archive_only.
        evidence = self.evidence()
        evidence.edit("archive-members.json", edit_member("lib/rustlib/etc/analyzer-notes.txt",
                                                          lambda row: row.update(kind="elf")))
        evidence.fields_override = {"archive_only": "lib/rustlib/etc/analyzer-notes.txt"}
        self.refuses("C13: .*ships the elf file lib/rustlib/etc/analyzer-notes.txt, and the producer's stage2 has no "
                     "row for it", evidence)
        self.refused_field("C13: archive_only = 'none', and the members give 'lib/rustlib/etc/analyzer-notes.txt'",
                           archive_only="none")
        self.refused_field("C13: archive_members / archive_bytes_total", archive_members="3")
        # A surface entrypoint with no row refuses.
        evidence = self.evidence()
        evidence.surface["entrypoint_sha256"]["trustdoc"] = "9" * 64
        self.refuses("C13: the surface entrypoint trustdoc is not one archive member", evidence)
        evidence = self.evidence()
        rows = dict(STAGE2)
        del rows["bin/rustc"]
        for role in ("producer", "fixed-point", "cross-check"):
            evidence.trees[role] = rows
        evidence.build_raw()
        self.refuses("C13: .*ships the elf file bin/rustc, and the producer's stage2 has no row for it", evidence)
        # A not-reproduced file whose member is not the producer's row.
        evidence = self.evidence(fixed={"bin/targo-trust": b"\x7fELF tt 2"}, controls=({"bin/targo-trust":
                                                                                       b"\x7fELF tt 3"},))
        evidence.edit("archive-members.json", edit_member("bin/targo-trust",
                                                          lambda row: row.update(sha256=sha(b"\x7fELF tt 2"))))
        self.refuses("C13: targo-trust-.* ships bin/targo-trust with other bytes than the producer's row", evidence)
        # An archive digest that is not its pin.
        evidence = self.evidence()
        evidence.edit("archive-members.json", lambda doc: doc["archives"][0].update(sha256="9" * 64))
        self.refuses("C13: targo-0.13.0-trust-aarch64-unknown-linux-gnu.tar.xz in archive-members.json has another "
                     "sha256 than its pin", evidence)
        evidence = self.evidence()
        evidence.edit("archive-members.json", lambda doc: doc["archives"].pop())
        self.refuses("C13: archive-members.json does not cover the eight host archives", evidence)

    def test_shared_source_is_bound_and_its_exclusion_said(self):
        self.refused_field("C13: the shared archive's member tables were compared excluding \\['builder-config'\\], "
                           "and the receipt says 'none'", shared_source_members_excluded="none")
        self.refused_field("C13: shared_source_bytes = 'identical', and the digests give 'recompressed-differs'",
                           shared_source_bytes="identical")
        self.refused_field("B2: shared_source_members = 'differs'", shared_source_members="differs")
        evidence = self.evidence()
        evidence.edit("archive-members.json", lambda doc: doc["shared"]["excluded"].append(
            {"path": "trust-src/manifest.in"}))
        self.refuses("C13: the shared archive's member tables were compared excluding", evidence)
        evidence = self.evidence()
        evidence.edit("archive-members.json", lambda doc: doc["shared"].update(pinned_sha256="9" * 64))
        self.refuses("C13: archive-members.json does not bind the pinned shared source archive", evidence)

    def test_native_rows_are_counted_apart(self):
        evidence = self.evidence()
        fields = evidence.fields()
        self.assertEqual((fields["native_copied_rows"], fields["rust_built_rows"]), ("1", "14"))
        self.refused_field("C14: native_copied_rows / rust_built_rows are 0 / 15", native_copied_rows="0",
                           rust_built_rows="15")
        self.refused_field("C14: native-outputs.json does not hash to native_outputs_sha256",
                           native_outputs_sha256="0" * 64)
        evidence = self.evidence()
        evidence.edit("native-outputs.json", lambda doc: doc["rows"][0].update(kind="text"))
        self.refuses("C14: native-outputs.json is not a table of ELF and ar files", evidence)

    def test_inputs_carry_the_receipts_digests(self):
        self.refused_field("C15: inputs.json does not carry the receipt's cargo-home and Lean input digests",
                           cargo_home_inputs_sha256="0" * 64)
        self.refused_field("C15: host_c_compiler is not the C compiler", host_c_compiler="c" * 64 + " gcc 99")
        evidence = self.evidence()
        evidence.edit("inputs.json", lambda doc: doc["clean_lean_inputs"].update(sha256="0" * 64))
        evidence.fields_override = {"clean_lean_inputs_sha256": "0" * 64}
        self.refuses("C7: run-producer.json is not a clean run: .*Lean library", evidence)

    def test_the_host_tools_the_base_config_names_are_the_roles_files(self):
        target = "target.aarch64-unknown-linux-gnu"

        def tool(name, **change):
            return lambda doc: doc["host_tools"][name].update(change)

        for what, change, pattern in (
                # The live defect: the receipt names cc's bytes, and the config builds with a gcc elsewhere.
                ("a gcc that resolves elsewhere", tool("/usr/bin/gcc", real="/usr/lib/ccache/gcc", sha256="9" * 64),
                 rf"C15: base-config.toml names {target}.cc = '/usr/bin/gcc', which is /usr/lib/ccache/gcc \(sha256 "
                 rf"9{{16}}\), and the cc inputs.json binds is {GCC} \(sha256 c{{16}}\)"),
                ("a gcc of other bytes at the same place", tool("/usr/bin/gcc", sha256="9" * 64),
                 rf"C15: base-config.toml names {target}.cc = '/usr/bin/gcc', which is {GCC} \(sha256 9{{16}}\)"),
                ("a g++ that is not the c++", tool("/usr/bin/g++", real=GCC, sha256="c" * 64),
                 rf"C15: base-config.toml names {target}.cxx = '/usr/bin/g\+\+', which is {GCC} .* and the c\+\+ "
                 "inputs.json binds is"),
                ("a python that is not the one that ran", tool("/usr/bin/python3", sha256="9" * 64),
                 "C15: base-config.toml names build.python = '/usr/bin/python3', .* and the python inputs.json binds"),
                # Every role a config key maps to is bound in full, not skipped.
                ("a cc role with no real path", lambda doc: doc["host_tools"]["cc"].pop("real"),
                 "C15: inputs.json does not bind the cc by its absolute path, real path, sha256 and version line"),
                ("a cc role with no path", lambda doc: doc["host_tools"]["cc"].pop("path"),
                 "C15: inputs.json does not bind the cc by its absolute path"),
                ("no c++ role", lambda doc: doc["host_tools"].pop("c++"),
                 r"C15: inputs.json does not bind the c\+\+ by its absolute path, .* version line \(None\)"),
                ("a c++ role with no version line", lambda doc: doc["host_tools"]["c++"].pop("version"),
                 r"C15: inputs.json does not bind the c\+\+ by"),
                ("a python role by a relative path", tool("python", path="python3"),
                 "C15: inputs.json does not bind the python by its absolute path"),
                ("a python role of no sha256", tool("python", sha256="not a digest"),
                 "C15: inputs.json does not bind the python by"),
                ("a relative real path in the gcc row and the cc role",
                 lambda doc: (tool("/usr/bin/gcc", real="gcc-13")(doc), tool("cc", real="gcc-13")(doc)),
                 "C15: inputs.json does not bind the cc by"),
                ("a gcc row without its version line", lambda doc: doc["host_tools"]["/usr/bin/gcc"].pop("version"),
                 "C15: inputs.json does not bind /usr/bin/gcc, which base-config.toml names .* and version line"),
                ("a config-named tool missing", lambda doc: doc["host_tools"].pop("/usr/bin/gcc"),
                 r"C15: inputs.json binds the host tools '/usr/bin/g\+\+,/usr/bin/python3' by path, and "
                 r"base-config.toml names '/usr/bin/g\+\+,/usr/bin/gcc,/usr/bin/python3': every host tool the base "
                 "config names is bound"),
                ("a tool the config does not name",
                 lambda doc: doc["host_tools"].update({"/usr/bin/ar": {"path": "/usr/bin/ar", "real": "/usr/bin/ar",
                                                                       "sha256": "9" * 64, "version": "ar",
                                                                       "measured": "setup"}}),
                 "C15: inputs.json binds the host tools .*/usr/bin/ar.* and no other is"),
                ("a row without its sha256", lambda doc: doc["host_tools"]["/usr/bin/gcc"].pop("sha256"),
                 r"C15: inputs.json does not bind /usr/bin/gcc, which base-config.toml names \("
                 rf"{target}.cc, {target}.linker\), by its path, real path, sha256 and version line"),
                ("a row of another path", tool("/usr/bin/gcc", path="/usr/bin/cc"),
                 "C15: inputs.json does not bind /usr/bin/gcc"),
                ("measured later", tool("/usr/bin/gcc", measured="later"),
                 "C15: inputs.json says /usr/bin/gcc was measured 'later'; a host tool the base config names is "
                 "measured at setup or at record"),
                ("measured when, unsaid", lambda doc: doc["host_tools"]["/usr/bin/gcc"].pop("measured"),
                 "C15: inputs.json says /usr/bin/gcc was measured None"),
                ("no host_tools table", lambda doc: doc.pop("host_tools"), "C15: host_c_compiler is not the C compiler")):
            with self.subTest(what):
                evidence = self.evidence()
                evidence.edit("inputs.json", change)
                self.refuses(pattern, evidence)
        # The keys that name a host tool: each one's tool is its role's file, or it is
        # bound by path alone (ar, ranlib), or it is refused.
        clang = "/usr/lib/llvm-18/bin/clang"

        def config(*edits):
            def apply(text):
                for old, new in edits:
                    self.assertIn(old, text)
                    text = text.replace(old, new)
                return text
            return apply

        rust = b"download-rustc = false\n"
        build = b'python = "/usr/bin/python3"\n'
        cxx = b'cxx = "/usr/bin/g++"\n'
        linker = b'linker = "/usr/bin/gcc"\n'
        under_root = BUILD_ROOT.encode() + b"/ledger/pathbin"

        def ar_row(**change):
            return {"path": "/usr/bin/ar", "real": "/usr/bin/aarch64-linux-gnu-ar", "sha256": "a" * 64,
                    "version": "GNU ar 2.42", "measured": "setup", **change}

        def add(path, row):
            return lambda doc: doc["host_tools"].update({path: row})

        g_plus_plus_is_clang = tool("/usr/bin/g++", real=clang, sha256="9" * 64)
        for what, edit, change, field, pattern in (
                # The default linker a built compiler runs when no target linker is set.
                ("[rust] default-linker naming the c++", config((rust, rust + b'default-linker = "/usr/bin/g++"\n')),
                 None, None,
                 r"C15: base-config.toml names rust.default-linker = '/usr/bin/g\+\+', which is " + re.escape(GXX)
                 + rf" \(sha256 {CXX_SHA[:16]}\), and the cc inputs.json binds is {GCC}"),
                ("a target linker naming the c++", config((linker, b'linker = "/usr/bin/g++"\n')), None, None,
                 rf"C15: base-config.toml names {target}.linker = '/usr/bin/g\+\+', .* and the cc inputs.json binds"),
                ("a target default-linker naming a g++ that is clang",
                 config((cxx, b""), (linker, linker + b'default-linker = "/usr/bin/g++"\n')), g_plus_plus_is_clang,
                 None, rf"C15: base-config.toml names {target}.default-linker = '/usr/bin/g\+\+', which is {clang}"),
                # A launcher around every compile, and a wrapper around every test program.
                ("[build] ccache naming a g++ that is clang",
                 config((cxx, b""), (build, build + b'ccache = "/usr/bin/g++"\n')), g_plus_plus_is_clang, None,
                 r"C15: base-config.toml names build.ccache = '/usr/bin/g\+\+', and ccache is not a key whose tool a "
                 r"role binds \(cc, linker, default-linker, cxx, python\) nor one bound by its path alone \(ar, "
                 r"ranlib\)"),
                ("a target runner naming the gcc", config((linker, linker + b'runner = "/usr/bin/gcc"\n')), None, None,
                 rf"C15: base-config.toml names {target}.runner = '/usr/bin/gcc', and runner is not a key"),
                ("a list naming a host tool", config((build, build + b'extra = ["/usr/bin/ar"]\n')), None, None,
                 r"C15: inputs.json binds the host tools '/usr/bin/g\+\+,/usr/bin/gcc,/usr/bin/python3' by path, and "
                 r"base-config.toml names '/usr/bin/ar,"),
                ("a list naming a bound host tool", config((build, build + b'extra = ["/usr/bin/ar"]\n')),
                 add("/usr/bin/ar", ar_row()), f"/usr/bin/ar:setup,{CONFIG_HOST_TOOLS}",
                 "C15: base-config.toml names build.extra = '/usr/bin/ar', and extra is not a key"),
                # C12: these keys name a host tool or nothing; not a program under the root, not a name.
                ("[rust] default-linker under the root",
                 config((rust, rust + b'default-linker = "' + under_root + b'/cc"\n')), None, None,
                 r"C12: base-config.toml names rust.default-linker = '.*/ledger/pathbin/cc', which is not one of the "
                 "named host tools"),
                ("ccache under the root", config((build, build + b'ccache = "' + under_root + b'/ccache"\n')), None,
                 None, r"C12: base-config.toml names build.ccache = '.*/ledger/pathbin/ccache', which is not one of "
                 r"the named host tools \(.*\) or false"),
                ("ccache by its name", config((build, build + b"ccache = true\n")), None, None,
                 r"C12: base-config.toml names build.ccache = True, which is not one of the named host tools"),
                ("a runner under the root", config((linker, linker + b'runner = "' + under_root + b'/qemu"\n')),
                 None, None, rf"C12: base-config.toml names {target}.runner = '.*/qemu', which is not one of"),
                # ar is bound by its path alone, so its row's form is all that holds it.
                ("an ar row with a relative real path", config((linker, linker + b'ar = "/usr/bin/ar"\n')),
                 add("/usr/bin/ar", ar_row(real="aarch64-linux-gnu-ar")), f"/usr/bin/ar:setup,{CONFIG_HOST_TOOLS}",
                 r"C15: inputs.json does not bind /usr/bin/ar, which base-config.toml names \(" + target + r".ar\)"),
                # A role measured at a path the config names is the file bound there: by
                # its real path and by its bytes, each on its own.
                ("the cc's path bound to clang", config((linker, linker + b'ar = "/usr/bin/cc"\n')),
                 add("/usr/bin/cc", {**HOST_TOOL_ROWS["cc"], "real": clang, "sha256": "9" * 64, "measured": "setup"}),
                 f"/usr/bin/cc:setup,{CONFIG_HOST_TOOLS}",
                 f"C15: inputs.json binds /usr/bin/cc as the cc \\({GCC}, sha256 c{{16}}\\) and, where "
                 f"base-config.toml names it, as {clang} \\(sha256 9{{16}}\\): one path is one file"),
                ("the cc's path, the cc's real path, other bytes", config((linker, linker + b'ar = "/usr/bin/cc"\n')),
                 add("/usr/bin/cc", {**HOST_TOOL_ROWS["cc"], "sha256": "9" * 64, "measured": "setup"}),
                 f"/usr/bin/cc:setup,{CONFIG_HOST_TOOLS}",
                 rf"C15: inputs.json binds /usr/bin/cc as the cc \({GCC}, sha256 c{{16}}\) and, where base-config.toml "
                 rf"names it, as {GCC} \(sha256 9{{16}}\)"),
                ("the cc's path, the cc's bytes, another real path",
                 config((linker, linker + b'ar = "/usr/bin/cc"\n')),
                 add("/usr/bin/cc", {**HOST_TOOL_ROWS["cc"], "real": clang, "measured": "setup"}),
                 f"/usr/bin/cc:setup,{CONFIG_HOST_TOOLS}",
                 rf"C15: inputs.json binds /usr/bin/cc as the cc .* as {clang} \(sha256 c{{16}}\)"),
                ("the cc's path bound to clang, the cc role without its path",
                 config((linker, linker + b'ar = "/usr/bin/cc"\n')),
                 lambda doc: (add("/usr/bin/cc", {**HOST_TOOL_ROWS["cc"], "real": clang, "sha256": "9" * 64,
                                                  "measured": "setup"})(doc), doc["host_tools"]["cc"].pop("path")),
                 f"/usr/bin/cc:setup,{CONFIG_HOST_TOOLS}", "C15: inputs.json does not bind the cc by")):
            with self.subTest(what):
                evidence = self.evidence()
                evidence.raw["base-config.toml"] = edit(evidence.raw["base-config.toml"])
                if change is not None:
                    evidence.edit("inputs.json", change)
                if field is not None:
                    evidence.fields_override = {"config_host_tools": field}
                self.refuses(pattern, evidence)
        for what, edit, change, field in (
                # The default linker naming the cc's file; ccache off; ar bound by its path.
                ("[rust] default-linker naming the gcc", config((rust, rust + b'default-linker = "/usr/bin/gcc"\n')),
                 None, None),
                ("ccache off", config((build, build + b"ccache = false\n")), None, None),
                ("ar by its path", config((linker, linker + b'ar = "/usr/bin/ar"\n')), add("/usr/bin/ar", ar_row()),
                 f"/usr/bin/ar:setup,{CONFIG_HOST_TOOLS}"),
                # The cc's own path, bound as the cc's file: ar has no measured role to compare.
                ("ar naming the cc's path, the cc's file", config((linker, linker + b'ar = "/usr/bin/cc"\n')),
                 add("/usr/bin/cc", {**HOST_TOOL_ROWS["cc"], "measured": "setup"}),
                 f"/usr/bin/cc:setup,{CONFIG_HOST_TOOLS}")):
            with self.subTest(what):
                evidence = self.evidence()
                evidence.raw["base-config.toml"] = edit(evidence.raw["base-config.toml"])
                if change is not None:
                    evidence.edit("inputs.json", change)
                if field is not None:
                    evidence.fields_override = {"config_host_tools": field}
                self.assertEqual(self.capture(evidence)["schema"], host_ledger.FIXED_POINT_SCHEMA)

    def test_a_record_time_measurement_is_disclosed_and_accepted(self):
        evidence = self.evidence()
        evidence.edit("inputs.json", lambda doc: doc["host_tools"]["/usr/bin/gcc"].update(measured="record"))
        # The receipt must say so ...
        said = "/usr/bin/g++:setup,/usr/bin/gcc:record,/usr/bin/python3:setup"
        self.refuses(re.escape(f"C15: config_host_tools = '{CONFIG_HOST_TOOLS}', and base-config.toml and "
                               f"inputs.json give '{said}'"), evidence)
        # ... and, when it does, the record is accepted.
        evidence.fields_override = {"config_host_tools": said}
        self.assertEqual(self.capture(evidence)["schema"], host_ledger.FIXED_POINT_SCHEMA)
        # A receipt cannot claim setup for what record measured, or drop a tool.
        for value in ("/usr/bin/g++:setup,/usr/bin/python3:setup", "none"):
            with self.subTest(value):
                evidence.fields_override = {"config_host_tools": value}
                self.refuses("C15: config_host_tools = ", evidence)

    def test_config_host_tools_is_formed(self):
        for value in ("/usr/bin/gcc:later", "/usr/bin/python3:setup,/usr/bin/gcc:setup", "/opt/bin/gcc:setup",
                      "/usr/bin/gcc:record,/usr/bin/gcc:setup", "/usr/bin/gcc", "/usr/bin/gcc:setup,"):
            with self.subTest(value):
                self.refused_field("B7: config_host_tools is not a sorted list of '<host tool>:<setup|record>', one "
                                   "row a tool", config_host_tools=value)

    def test_chain_summary_names_the_stage0s(self):
        evidence = self.evidence()
        evidence.edit("chain.json", lambda doc: doc.pop("NOT_A_LINEAGE_RECORD"))
        self.refuses("C16: chain.json lacks its schema or the NOT_A_LINEAGE_RECORD marker", evidence)
        evidence = self.evidence()
        evidence.edit("chain.json", lambda doc: doc["rungs"][2].update(produced_compiler_sha256="9" * 64))
        self.refuses("C16: chain.json does not name the producer stage0", evidence)
        evidence = self.evidence()
        evidence.edit("chain.json", lambda doc: (doc["rungs"][1].update(produced_compiler_sha256="9" * 64),
                                                 doc["rungs"][2].update(stage0_compiler_sha256="9" * 64)))
        self.refuses("C16: chain.json does not name the cross_check stage0", evidence)
        evidence = self.evidence()
        evidence.edit("chain.json", lambda doc: doc["rungs"].pop(0))
        self.refuses("C16: chain rung r2 was built by 20565c3255, which no earlier rung or the root produced",
                     evidence)
        evidence = self.evidence()
        evidence.edit("chain.json", lambda doc: doc["origin"]["provenance"].pop())
        self.refuses("C16: chain.json's origin does not carry", evidence)
        evidence = self.evidence()
        evidence.edit("chain.json", lambda doc: doc["rungs"].append(
            {**doc["rungs"][2], "label": "r4", "commit": "a" * 40, "stage0_commit": P0,
             "stage0_compiler_sha256": PRODUCER_STAGE0["bin/trustc"]}))
        self.refuses("C16: chain.json's commits .* are not chain_commits", evidence)

    def test_check_archive_joins_reads_the_real_archives(self):
        evidence = self.evidence()
        seed, record, _ = evidence.write()
        joined = fp.check_archive_joins(seed, record["payloads"], HOST, host_ledger.read_proof, archive_root=seed)
        self.assertEqual(joined, sum(len(files) for _, files in ARCHIVES.values()))
        # An archive with other bytes than its pin, and a member table that is not the archive's.
        archive = seed / "dist" / DATE / archive_name("tippy")
        write_archive(archive.parent, "tippy", "tippy-preview", {"bin/tippy": b"\x7fELF tippy, rebuilt"})
        with self.assertRaisesRegex(ValueError, "C13: .*tippy.* has sha256 [0-9a-f]{64}, and the pin is"):
            fp.check_archive_joins(seed, record["payloads"], HOST, host_ledger.read_proof, archive_root=seed)
        payloads = {**record["payloads"], f"dist/{DATE}/{archive.name}": sha(archive.read_bytes())}
        with self.assertRaisesRegex(ValueError, "C13: tippy-.* read again is not the member table"):
            fp.check_archive_joins(seed, payloads, HOST, host_ledger.read_proof, archive_root=seed)
        shutil.copyfile(CACHE / archive.name, archive)
        source = seed / "dist" / DATE / archive_name("trust-src")
        write_archive(source.parent, "trust-src", "rust-src", {SOURCE_FILE: b"pub fn other() {}\n"})
        payloads = {**record["payloads"], f"dist/{DATE}/{source.name}": sha(source.read_bytes())}
        with self.assertRaisesRegex(ValueError, "C13: the pinned trust-src-.*member table is not the one"):
            fp.check_archive_joins(seed, payloads, HOST, host_ledger.read_proof, archive_root=seed)

    def test_archive_table_lists_what_the_installer_installs(self):
        table = fp.archive_table(CACHE / archive_name("trust-analyzer"))
        self.assertEqual([(row["path"], row["kind"], row["type"]) for row in table["members"]],
                         [("bin/trust-analyzer", "elf", "file"), ("lib/rustlib/etc/analyzer-notes.txt", "other",
                                                                  "file")])
        self.assertEqual(table["members_sha256"], support.records_sha256(table["members"]))
        with tempfile.TemporaryDirectory() as tmp:
            broken = write_archive(Path(tmp), "tippy", "tippy-preview", {"bin/tippy": b"x"})
            with tarfile.open(broken, "w:xz") as bundle:
                info = tarfile.TarInfo(f"{broken.name.removesuffix('.tar.xz')}/components")
                info.size = 6
                bundle.addfile(info, io.BytesIO(b"tippy\n"))
            with self.assertRaisesRegex(ValueError, "C13: .* names tippy and has no manifest.in"):
                fp.archive_table(broken)


class MemberBindingTests(Case):
    def test_every_hashed_member_must_be_its_receipt_row(self):
        evidence = self.evidence()
        seed, record, _ = evidence.write()
        members = {f"bin/{name}": {"member_sha256": sha(STAGE2[f"bin/{name}"])}
                   for name in ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt", "targo-trust", "tippy",
                                "trust-analyzer")}
        host_ledger.check_fixed_point_member_bindings(seed, HOST, record, members)
        self.assertEqual(fp.member_rows((seed / "host-proofs" / HOST / "SEED-FIXED-POINT").read_bytes())["bin/ty"],
                         sha(STAGE2["bin/ty"]))
        with self.assertRaisesRegex(ValueError, "pinned archive member bin/tippy differs from its fixed-point receipt"):
            host_ledger.check_fixed_point_member_bindings(seed, HOST, record, {**members, "bin/tippy":
                                                                               {"member_sha256": "9" * 64}})
        with self.assertRaisesRegex(ValueError, "bin/tippy-driver has no compiler_file row"):
            host_ledger.check_fixed_point_member_bindings(seed, HOST, record, {**members, "bin/tippy-driver":
                                                                               {"member_sha256": "9" * 64}})
        with self.assertRaisesRegex(ValueError, "no hashed archive member"):
            host_ledger.check_fixed_point_member_bindings(seed, HOST, record, {})
        with self.assertRaisesRegex(ValueError, "only a fixed-point record"):
            host_ledger.check_fixed_point_member_bindings(seed, HOST, {**record, "schema": host_ledger.SCHEMA},
                                                          members)
        # The surface binding of every native kind applies to this one too.
        bindings = {f"bin/{name}": {"member_sha256": digest} for name, digest in record["entrypoint_sha256"].items()}
        host_ledger.check_entrypoint_bindings(record, bindings)
        with self.assertRaisesRegex(ValueError, "native host surface trustc differs"):
            host_ledger.check_entrypoint_bindings(record, {**bindings, "bin/trustc": {"member_sha256": "9" * 64}})


def edit_member(path: str, update):
    """An archive-members.json change: update the member at `path` and rehash its list."""
    def change(doc):
        for archive in doc["archives"]:
            for row in archive["members"]:
                if row["path"] == path:
                    update(row)
            archive["members_sha256"] = support.records_sha256(archive["members"])
    return change


def door_wiring_problems() -> list[str]:
    """What the recreator must do before the door may hold an entry: bind every
    archive member it hashes to the receipt's compiler_file row on each capture
    (design E, seed_host_ledger.check_fixed_point_member_bindings), and record
    seed_fixed_point.py's sha256 beside seed_host_ledger.py's, since that file
    judges the record too. Both are wired in capture_validated_seed_lineage (the
    design's code_changes[5]; ConsumerTests runs them); this keeps an entry out
    of the door if either is removed."""
    source = (ROOT / "scripts" / "recreate_bootstrap.py").read_text()
    return [f"scripts/recreate_bootstrap.py does not name {need}"
            for need in ("check_fixed_point_member_bindings", "seed_fixed_point.py") if need not in source]


class ReviewedReceiptTests(Case):
    """The receipt says nothing its fields do not, and its free words are fixed."""

    def test_the_receipt_is_its_canonical_rendering(self):
        evidence = self.evidence()
        receipt = evidence.receipt()
        fp.require_canonical(receipt, fp.parse_receipt(receipt))
        for what, payload in (
                ("a comment claiming more", receipt + b"# independent_chain_reproduction=verified-on-darwin\n"),
                ("a comment in the fields",
                 receipt.replace(b"controls=0\n", b"controls=0\n# stock_built_ancestor=none\n")),
                ("two fields swapped", receipt.replace(b"root=unpinned-host-chain\npredecessor_pin=none\n",
                                                       b"predecessor_pin=none\nroot=unpinned-host-chain\n")),
                ("a blank line", receipt.replace(b"controls=0\n", b"controls=0\n\n"))):
            with self.subTest(what):
                self.assertNotEqual(payload, receipt)
                self.refuses("B1: the receipt is not the canonical rendering of its own fields and rows", evidence,
                             receipt=payload)
        self.refuses("B1: the receipt has fields this kind does not define: notes", evidence,
                     receipt=receipt + b"notes=anything\n")
        with self.assertRaisesRegex(ValueError, "B1: the receipt carries a CR or NUL"):
            fp.parse_receipt(receipt.replace(b"controls=0\n", b"controls=0\r\n"))
        for path in ("./bin/x", "bin/./x", "bin//x", "bin/../x"):
            with self.subTest(path), self.assertRaisesRegex(ValueError, "B1: .*escapes stage2"):
                fp.parse_receipt(receipt + f"compiler_file={'a' * 64} {path}\n".encode())

    def test_the_free_words_are_fixed(self):
        for value in ("none", "verified stock-free toolchain", fp.STOCK_ANCESTOR_TOOLCHAIN + " and more"):
            with self.subTest(value):
                self.refused_field("B4: stock_built_ancestor_toolchain = ", stock_built_ancestor_toolchain=value)
        for key, value in (("no_stock_evidence", "fail"), ("trap_hits", "1"), ("process_census_flagged", "2")):
            with self.subTest(key):
                self.refused_field(f"B2: {key} = ", **{key: value})
        evidence = self.evidence(fixed={"bin/ty": b"\x7fELF ty, order 2"}, controls=({"bin/ty": b"\x7fELF ty, 3"},))
        for value, pattern in (("none", "C5: not_reproduced lists files and no cause hypothesis"),
                               ("verified: a ThinLTO ordering",
                                "C5: not_reproduced_cause_hypothesis is not the fixed")):
            with self.subTest(value):
                evidence.fields_override = {"not_reproduced_cause_hypothesis": value}
                self.refuses(pattern, evidence)
        evidence.fields_override = {}
        self.assertEqual(self.capture(evidence)["root_disclosure"]["not_reproduced"], "bin/ty")

    def test_the_chain_is_the_designs(self):
        evidence = self.evidence()
        other = "a" * 40
        evidence.edit("chain.json", lambda doc: (doc["rungs"][0].update(commit=other),
                                                 doc["rungs"][1].update(stage0_commit=other)))
        evidence.fields_override = {"chain_commits": ",".join((fp.ROOT_COMMIT, other, S0, P0))}
        self.refuses("B3: chain_commits is not the host chain this kind admits", evidence)
        self.assertEqual(fp.CHAIN_COMMITS, (fp.ROOT_COMMIT, R1, S0, P0))

    def test_the_dist_line_names_every_component(self):
        evidence = self.evidence()
        evidence.edit("run-producer-dist.json",
                      lambda run: run.update(argv=[*run["argv"][:3], "dist", "--stage", "2", "trustc"]))
        evidence.fields_override = {"dist_components": "trustc"}
        self.refuses("C7: dist_components = 'trustc' is not exactly the seed cohort's components", evidence)
        self.refused_field("C7: dist_components = .* is not exactly",
                           dist_components=" ".join([*host_ledger.COMPONENTS, "rust-docs"]))
        # Their order is the dist run's; every one is there.
        order = " ".join(reversed(host_ledger.COMPONENTS))
        evidence = self.evidence()
        evidence.edit("run-producer-dist.json",
                      lambda run: run.update(argv=[*run["argv"][:3], "dist", "--stage", "2", *order.split(" ")]))
        evidence.fields_override = {"dist_components": order}
        self.capture(evidence)


class ReviewedAccountTests(Case):
    """T7: the search covers what normalisation replaces, escapes and decoys."""

    def digests(self, account=ACCOUNT) -> tuple[str, str]:
        return fp.account_digest("home", account[0]), fp.account_digest("login", account[1])

    def test_the_login_is_found_wherever_it_starts_a_word(self):
        home, login = self.digests()
        for text, found in (("fixture-person_scratch", "login"), ("fixture-person2", "login"),
                            ("x_fixture-person", "login"), ("x.fixture-person-y", "login"),
                            ("/tmp/fixture-person/", "login"), ("xfixture-person", None), ("2fixture-person", None),
                            ("fixture-personal", None), ("fixture-person" + "a", None)):
            with self.subTest(text):
                self.assertEqual(fp.account_found(text.encode(), home, login, name="x.txt"), found)
                tracked, count = fp.normalise(text.encode(), ACCOUNT)
                self.assertEqual(count, 1 if found else 0)
                self.assertIsNone(fp.account_found(tracked, home, login, name="x.txt"))
        # Through a whole capture: both are replaced, and the record holds.
        evidence = self.evidence()
        evidence.raw["base-config.toml"] += b"# fixture-person_scratch fixture-person2\n"
        self.assertEqual(evidence.tracked()[1]["base-config.toml"], 2)
        self.capture(evidence)

    def test_an_escaped_home_in_a_config_is_found(self):
        home, login = self.digests()
        escaped = b'[dist]\nsrc-tarball-dir = "\\u002Fhome\\u002Ffixture-person\\u002Fsrc"\n'
        self.assertIsNone(fp.account_found(escaped, home, login, name="x.txt"))
        self.assertEqual(fp.account_found(escaped, home, login, name="base-config.toml"), "home")
        evidence = self.evidence()
        evidence.raw["base-config.toml"] += escaped
        self.refuses("T7: base-config.toml still names the invoking account's home", evidence)

    def test_a_receipt_with_another_accounts_digests_is_refused(self):
        evidence = self.evidence()
        with mock.patch.object(sys.modules[__name__], "ACCOUNT", ("/home/decoy", "decoy")):
            fields = evidence.fields()
            self.assertTrue(all(fields[f"{fp.evidence_field(name)}_normalised_count"] == "0" for name in evidence.raw))
            self.refuses(r"T7: .* names a home directory \(/home/<name> or /Users/<name>\) that is not <home>",
                         evidence)
        for payload, found in ((b'"/home/x"', True), (b'"<home>/y"', True), (b'["a", "/home/<account>/y"]', False),
                               (b'"<home>/y"', False), (b'"/var/tmp/r/home/x"', False), (b'"\\/home\\/x"', True),
                               (b'"PATH": "/usr/bin:/home/x/bin"', True), (b'"/home/<account>x"', True)):
            with self.subTest(payload):
                self.assertEqual(fp.personal_home_found(payload, "x.json"), found)

    def test_the_counts_fit_the_tokens(self):
        evidence = self.evidence()
        fields = evidence.fields()
        field = fp.evidence_field("chain.json")
        self.refuses(r"T7: chain.json holds [1-9][0-9]* <home> or <account> token\(s\), and the receipt says 0",
                     evidence, receipt=evidence.receipt({**fields, f"{field}_raw_sha256": fields[f"{field}_sha256"],
                                               f"{field}_normalised_count": "0"}))
        self.refuses(r"T7: chain.json holds [0-9]+ <home> or <account> token\(s\), and the receipt says 999", evidence,
                     receipt=evidence.receipt({**fields, f"{field}_normalised_count": "999"}))

    def test_the_receipt_and_surface_are_searched(self):
        self.refused_field("T7: SEED-FIXED-POINT still names the invoking account's login",
                           host_c_compiler=f"{'c' * 64} cc built by fixture-person")
        self.refused_field("T7: SEED-FIXED-POINT still names the invoking account's home",
                           host_c_compiler=f"{'c' * 64} cc of /home/fixture-person/gcc")

    def test_an_account_the_search_cannot_find_is_refused(self):
        deep = "".join(f"/s{number}" for number in range(fp.MAX_HOME_SEGMENTS + 1))
        for account in (("/home/x", "a" * (fp.MAX_LOGIN + 1)), ("/home/x", "with space"), ("/home/x", ""),
                        ("relative/home", "x"), (deep, "x"), ("/home/x y", "x")):
            with self.subTest(account), self.assertRaisesRegex(ValueError, "T7: the invoking account cannot be "
                                                                            "recorded"):
                fp.normalise(b"x", account)
        self.assertIsNone(fp.account_problem(("/home/hôme-of-nobody", "nobody")))

    def test_the_search_is_bounded(self):
        home, login = self.digests()
        run = "".join(f"/s{number}" for number in range(2000)) + ACCOUNT[0] + "/x"
        candidates = fp._home_candidates(run)
        self.assertLessEqual(len(candidates), fp.MAX_HOME_SEGMENTS * (run.count("/") + 1))
        self.assertEqual(fp.account_found(run.encode(), home, login, name="x.txt"), "home")
        token = "a1" * 5000
        self.assertLessEqual(len(fp._login_candidates(token)), fp.MAX_LOGIN)


class ReviewedEvidenceTests(Case):
    """C5, C7-C16: each rule a reviewer could delete with every earlier test green."""

    def test_more_run_record_fields_are_read(self):
        def environment(key, value):
            return lambda run: run["environment"].update({key: value})

        def relabel(run):
            run.update(label=run["label"] + "-x")
            run["environment"]["TRUST_STAIRCASE_RUNG"] = run["label"]

        cases = (
            ("another kind", lambda run: run.update(kind="attempt"), "it is not a seed_staircase.py run record"),
            ("a dead sampler", lambda run: run.update(sampler_died="at 300s"), "its process census died"),
            ("the stage0 runtime changed", lambda run: run.update(stage0_runtime_unchanged=False),
             "stage0_runtime_unchanged is not true"),
            ("the tool dirs changed", lambda run: run.update(tool_dirs_unchanged=False),
             "tool_dirs_unchanged is not true"),
            ("CARGO_HOME elsewhere", environment("CARGO_HOME", "/var/tmp/cargo"), "its environment's CARGO_HOME"),
            ("another LOGNAME", environment("LOGNAME", "someone"), "its environment's LOGNAME"),
            ("another rung variable", environment("TRUST_STAIRCASE_RUNG", "r9"),
             "its environment's TRUST_STAIRCASE_RUNG"),
            ("the Lean library elsewhere", lambda run: run["clean_lean"].update(library="/opt/lean/lib/lean"),
             "the Lean library it was given"),
            ("a checkout head that is not a commit", lambda run: run["tool"].update(checkout_head="HEAD"),
             "not run by the recorded seed_staircase.py"),
            ("a label suffix that is not an attempt", relabel, "its label '.*-x' is not"),
            ("a config tool elsewhere", lambda run: run["config_tools"]["tools"]["rustc"].update(real="/usr/bin/rustc"),
             "its config tool rustc is not"),
            ("a config tool with other bytes",
             lambda run: run["config_tools"]["tools"]["cargo"].update(sha256="0" * 64), "its config tool cargo is not"),
            ("no config tools", lambda run: run["config_tools"].pop("tools"), "its config_tools name None"),
            ("a fifth config tool", lambda run: run["config_tools"]["tools"].update(
                clippy={"named": "/usr/bin/clippy-driver", "real": "/usr/bin/clippy-driver", "sha256": "0" * 64}),
             r"its config_tools name \['cargo', 'clippy', 'rustc', 'rustdoc', 'rustfmt'\], not the four"),
            ("another observed stage0", lambda run: run["stage0_observed"].update(root="/usr"),
             "the stage0 it observed"),
            ("an observed stage0 with other bytes",
             lambda run: run["stage0_observed"]["sha256"].update({"bin/trustc": "0" * 64}), "the stage0 it observed"),
            ("another ninja", lambda run: run["tool_dirs"][0]["entries"][0].update(sha256="0" * 64), "ninja"),
            ("a tool beside ninja", lambda run: run["tool_dirs"][0]["entries"].append(
                {"name": "rustc", "path": "/usr/bin/rustc", "real": "/usr/bin/rustc", "sha256": "0" * 64}), "ninja"),
            ("no tool dirs", lambda run: run.update(tool_dirs=[]), "ninja"),
        )
        for what, change, pattern in cases:
            for name in ("run-producer.json", "run-fixed-point.json", "run-producer-dist.json"):
                with self.subTest(what, name=name):
                    evidence = self.evidence()
                    evidence.edit(name, change)
                    self.refuses(rf"C7: {name} is not a clean run: .*{pattern}", evidence)
        self.refused_field("C7: orchestration_commit is not the checkout run-producer.json's seed_staircase.py",
                           orchestration_commit="a" * 40)

    def test_every_run_was_handed_one_fifo_jobserver_that_balanced(self):
        # BOOTSTRAP-JOBSERVER-PROBE-1: a run without the FIFO jobserver (a pipe one, or
        # none) is the run whose build-script probes the shim refused.
        def flags(value):
            return lambda run: run["environment"].pop("MAKEFLAGS") if value is None else \
                run["environment"].update(MAKEFLAGS=value)

        def jobserver(**changes):
            return lambda run: run["jobserver"].update(changes)

        def adapter(**changes):
            return lambda run: run["jobserver"]["make_adapter"].update(changes)

        tmp = f"{BUILD_ROOT}/ledger/tmp"
        cases = (
            ("no MAKEFLAGS", flags(None), "its environment's MAKEFLAGS is None, not -j20 --jobserver-auth=fifo:"),
            ("a pipe jobserver", flags("-j20 --jobserver-auth=3,4"), "MAKEFLAGS is '-j20 --jobserver-auth=3,4'"),
            ("another job count", flags(f"-j8 --jobserver-auth=fifo:{JOBSERVER}"), "MAKEFLAGS is '-j8 "),
            ("a FIFO outside the ledger", flags("-j20 --jobserver-auth=fifo:/tmp/jobserver.fifo"), "MAKEFLAGS is"),
            ("a FIFO below the ledger's tmp", flags(f"-j20 --jobserver-auth=fifo:{tmp}/x/jobserver.fifo"),
             "MAKEFLAGS is"),
            ("the ledger's tmp itself", flags(f"-j20 --jobserver-auth=fifo:{tmp}/.."), "MAKEFLAGS is"),
            ("the ledger's tmp as .", flags(f"-j20 --jobserver-auth=fifo:{tmp}/."), "MAKEFLAGS is"),
            ("more after the path", flags(f"-j20 --jobserver-auth=fifo:{JOBSERVER} --other"), "MAKEFLAGS is"),
            ("no jobserver record", lambda run: run.pop("jobserver"),
             r"its jobserver record is not the FIFO its MAKEFLAGS names with 19 token\(s\) preloaded, all there again "
             r"when x.py had exited, its path unchanged \(it differs in jobs, kind, path, path_unchanged, tokens, "
             r"tokens_at_end\)"),
            ("another kind", jobserver(kind="pipe"), r"\(it differs in kind\)"),
            ("another path", jobserver(path=f"{tmp}/other.fifo"), r"\(it differs in path\)"),
            ("another job count", jobserver(jobs=8), r"\(it differs in jobs\)"),
            # A lost token under the cross-check's stage0 is SEED-TOKEN-LEAK-STAGE0-1's (TokenLeakTests); the
            # census below does not show nothing outlived x.py, so here no run's is excused.
            ("a lost token", lambda run: (run["jobserver"].update(tokens_at_end=18),
                                          run["process_census"].pop("abandoned_children")),
             r"\(it differs in tokens_at_end\); SEED-TOKEN-LEAK-STAGE0-1 \(docs/OPEN_ISSUES.md "
             r"RUSTC-FRONTEND-TOKEN-LEAK-1\) does not excuse its jobserver's 18 of the 19 token\(s\) back: its process "
             r"census ended 'watched-exited' with abandoned_children None"),
            ("an extra token", jobserver(tokens_at_end=20), r"\(it differs in tokens_at_end\)"),
            ("a count that is text", jobserver(tokens="19"), r"\(it differs in tokens\)"),
            # 19.0 == 19 in Python: only the type tells a count from something else.
            ("a count that is not a whole number", jobserver(tokens_at_end=19.0), r"\(it differs in tokens_at_end\)"),
            ("a path flag that is not a boolean", jobserver(path_unchanged=1), r"\(it differs in path_unchanged\)"),
            ("a token short at the start", jobserver(tokens=18, tokens_at_end=18),
             r"\(it differs in tokens, tokens_at_end\)"),
            ("a path that changed under the build", jobserver(path_unchanged=False), r"\(it differs in path_unchanged\)"),
            # GNU make before 4.4 reached the FIFO through the adapter, which ran the make inputs.json binds.
            ("no make adapter", lambda run: run["jobserver"].pop("make_adapter"),
             rf"its jobserver record does not name the make adapter at {BUILD_ROOT}/ledger/pathbin/make by its "
             r"sha256, running the make inputs.json binds \(/usr/bin/make, sha256 9999999999999999\) \(it differs in "
             r"make, make_sha256, path\)"),
            ("an adapter elsewhere", adapter(path="/usr/local/bin/make"), r"\(it differs in path\)"),
            ("another make", adapter(make="/usr/local/bin/make"), r"\(it differs in make\)"),
            ("another make's bytes", adapter(make_sha256="8" * 64), r"\(it differs in make_sha256\)"),
            ("an adapter without its sha256", adapter(sha256=None), r"\(it differs in sha256\)"),
            ("an adapter sha256 that is not one", adapter(sha256="x" * 64), r"\(it differs in sha256\)"),
        )
        for what, change, pattern in cases:
            for name in ("run-producer.json", "run-cross-check.json", "run-producer-dist.json"):
                with self.subTest(what, name=name):
                    evidence = self.evidence()
                    evidence.edit(name, change)
                    self.refuses(rf"C7: {name} is not a clean run: .*{pattern}", evidence)
        # One jobserver for every run: each of two well-formed FIFOs is not enough.
        evidence = self.evidence()
        other = f"{tmp}/other.fifo"
        evidence.edit("run-producer-dist.json", lambda run: (
            run["environment"].update(MAKEFLAGS=f"-j20 --jobserver-auth=fifo:{other}"),
            run["jobserver"].update(path=other)))
        self.refuses(rf"C7: the runs were handed 2 jobservers \(-j20 --jobserver-auth=fifo:{JOBSERVER}; -j20 "
                     rf"--jobserver-auth=fifo:{other}\); the roles differ only in their stage0", evidence)
        # ... and one make adapter.
        evidence = self.evidence()
        evidence.edit("run-cross-check.json", adapter(sha256="5" * 64))
        self.refuses(r"C7: the runs reached make through 2 make adapters \(sha256 5555555555555555, 6666666666666666\); "
                     "every run is handed one", evidence)
        # A make the adapter ran is the make inputs.json binds; with none bound, no run is clean.
        for what, change in (("no make row", lambda doc: doc["host_tools"].pop("make")),
                             ("a make row without its sha256", lambda doc: doc["host_tools"]["make"].pop("sha256"))):
            with self.subTest(what):
                evidence = self.evidence()
                evidence.edit("inputs.json", change)
                self.refuses(r"C7: run-producer.json is not a clean run: .*inputs.json's host_tools binds no make by "
                             r"its path, real path, sha256 and version line .*, and the run's make adapter runs one",
                             evidence)
        # The job count is the rung config's, and it must be one.
        for config, said in ((RUNG_CONFIG.replace(b"jobs = 20\n", b""), "None"),
                             (RUNG_CONFIG.replace(b"jobs = 20", b"jobs = true"), "True"),
                             (RUNG_CONFIG.replace(b"jobs = 20", b"jobs = 0"), "0")):
            with self.subTest(said):
                evidence = self.evidence()
                evidence.raw["rung-config.toml"] = config
                self.refuses(rf"C7: run-producer.json is not a clean run: .*the rung config's build.jobs is {said}, "
                             "not the job count a FIFO jobserver advertises", evidence)
        # The fixture itself, every run handed the one FIFO, is a valid record.
        self.capture(self.evidence())

    def test_a_build_that_did_not_make_an_allowed_file_gives_no_digest(self):
        other = b"\x7fELF ty, built by the pinned seed"
        for what, fixed, controls, lacking in (("F lacks it, C1 differs", {}, ({"bin/ty": other},), "fixed-point"),
                                               ("F differs, C1 lacks it", {"bin/ty": other}, ({},), "control-1"),
                                               ("the producer lacks it", {}, (), "producer")):
            with self.subTest(what):
                evidence = self.evidence(fixed=fixed, controls=controls)
                del evidence.trees[lacking]["bin/ty"]
                evidence.build_raw()
                self.refuses(r"C5: bin/ty is in some of the producer's and the pinned seed's trees .* and not in "
                             "others", evidence)
        # Absent from every tree: nothing to judge.
        evidence = self.evidence()
        for tree in evidence.trees.values():
            del tree["bin/ty"]
        evidence.build_raw()
        self.assertEqual(self.capture(evidence)["root_disclosure"]["not_reproduced"], "none")

    def test_every_dist_run_records_the_identity_files_it_left(self):
        for name in ("run-producer-dist.json", "run-producer-full.json", "run-producer-manifest-tool.json"):
            for what, change in (("no produced", lambda run: run.pop("produced")),
                                 ("an empty produced", lambda run: run["produced"].update(sha256={})),
                                 ("no std dylib", lambda run: run["produced"]["sha256"].pop("lib/libstd-fixture.so"))):
                with self.subTest(name=name, what=what):
                    evidence = self.evidence()
                    evidence.edit(name, change)
                    self.refuses(f"C8: {name} left a stage2 whose identity files are not the producer's", evidence)
        evidence = self.evidence()
        evidence.edit("run-cross-check.json", lambda run: run["produced"]["sha256"].pop("bin/trustc"))
        self.refuses("C8: stage2-cross-check.json is not the tree run-cross-check.json says it produced", evidence)

    def test_admissions_are_read_whole(self):
        evidence = self.evidence()
        evidence.edit("admission-producer.json", lambda doc: doc.update(kind="stage0-attempt"))
        self.refuses("C9: admission-producer.json is not a clean stage0 admission", evidence)
        extra = {**PRODUCER_STAGE0, "lib/librustc_driver-zz.so": "9" * 64}
        evidence = self.evidence()
        evidence.edit("admission-producer.json", lambda doc: doc.update(sha256=extra))
        for name in ("run-producer.json", "run-producer-dist.json", "run-producer-full.json",
                     "run-producer-manifest-tool.json"):
            evidence.edit(name, ran(extra))
        self.refuses("C9: the receipt's producer stage0 digests are not admission-producer.json's", evidence)
        evidence = self.evidence()
        evidence.edit("run-producer-dist.json", lambda run: run.update(stage0_commit=S0))
        self.refuses("C9: run-producer-dist.json did not run the producer's stage0", evidence)

    def test_a_manifest_without_std_is_refused(self):
        evidence = self.evidence()
        rlib = f"lib/rustlib/{HOST}/lib/libstd-fixture.rlib"
        for role in list(evidence.trees):
            del evidence.trees[role][rlib]
        evidence.build_raw()
        self.refuses("C2: stage2-producer.json has no compiler, driver or std", evidence)

    def test_the_fixed_point_stage0_is_an_archive_member(self):
        evidence = self.evidence()

        def drop(doc):
            for archive in doc["archives"]:
                archive["members"] = [row for row in archive["members"] if row["path"] != "lib/libstd-fixture.so"]
                archive["members_sha256"] = support.records_sha256(archive["members"])
        evidence.edit("archive-members.json", drop)
        self.refuses("C10: the fixed-point stage0's lib/libstd-fixture.so is not the pinned archive member", evidence)

    def test_every_config_key_keeps_the_tool_rule(self):
        base_cases = (
            (b'[rust]\ndownload-rustc = true\n', "base-config.toml sets rust.download-rustc = True"),
            (b'[rust]\ndownload-rustc = "if-unchanged"\n', "base-config.toml sets rust.download-rustc"),
            (b'[llvm]\ndownload-ci-llvm = true\n', "base-config.toml sets llvm.download-ci-llvm"),
            (b'[target.aarch64-unknown-linux-gnu]\nllvm-config = "/usr/bin/llvm-config"\n',
             "base-config.toml names target.aarch64-unknown-linux-gnu.llvm-config = '/usr/bin/llvm-config', outside"),
            (b'[build]\ncargo-clippy = "/usr/bin/cargo-clippy"\n', "base-config.toml names build.cargo-clippy"),
            (b'[build]\ninitial-rustc = "/usr/bin/rustc"\n', "base-config.toml names build.initial-rustc"),
            (b'[target.aarch64-unknown-linux-gnu]\nlinker = "/opt/stock/bin/cc"\n',
             "base-config.toml names target.aarch64-unknown-linux-gnu.linker = '/opt/stock/bin/cc', which is not one"),
            (b'[build]\npython = "python3"\n', "base-config.toml names build.python = 'python3', which is not one"),
            (b'[install]\nprefix = "/usr/local"\n', "base-config.toml names install.prefix = '/usr/local', a path "
                                                    "outside"),
            (b'include = ["/etc/trust.toml"]\n', "base-config.toml includes another file"),
            (b'= broken\n', "base-config.toml is not TOML"),
        )
        for payload, pattern in base_cases:
            with self.subTest(payload):
                evidence = self.evidence()
                evidence.raw["base-config.toml"] = payload
                self.refuses(f"C12: {pattern}", evidence)
        rung_cases = (
            (b'cargo-clippy = "cargo-clippy"\n', "build.cargo-clippy,build.jobs",
             "rung-config.toml names build.cargo-clippy = 'cargo-clippy', outside"),
            (b'\n[target.aarch64-unknown-linux-gnu]\nllvm-config = "/usr/lib/llvm-18/bin/llvm-config"\n',
             "build.jobs,target.aarch64-unknown-linux-gnu.llvm-config",
             "rung-config.toml names target.aarch64-unknown-linux-gnu.llvm-config"),
            (b'\n[rust]\nlto = "off"\n', "build.jobs,rust.lto",
             "the rung config departs from the recreator's in rust.lto; a rung config departs only in build.jobs"),
        )
        for payload, departures, pattern in rung_cases:
            with self.subTest(payload):
                evidence = self.evidence()
                evidence.raw["rung-config.toml"] = RUNG_CONFIG + payload
                evidence.fields_override = {"config_departures": departures}
                self.refuses(f"C12: {pattern}", evidence)

    def unbound(self, table: str, line: str) -> Evidence:
        """The fixture's evidence, which is admitted, with `line` added to its base
        config's [table] (a table the base config does not have, at its end)."""
        evidence = self.evidence()
        text = evidence.raw["base-config.toml"]
        anchor = {"build": b'python = "/usr/bin/python3"\n', "llvm": b"download-ci-llvm = false\n",
                  "rust": b"download-rustc = false\n", TARGET: b'linker = "/usr/bin/gcc"\n'}.get(table)
        if anchor is None:
            text += f"\n[{table}]\n{line}".encode()
        else:
            self.assertEqual(text.count(anchor), 1)
            text = text.replace(anchor, anchor + line.encode())
        evidence.raw["base-config.toml"] = text
        return evidence

    def unbound_refusal(self, what: str, said: str) -> str:
        """The C12 words, as a pattern, that refuse `what` for setting the unbound key
        `said` names (`<dotted key> = <repr of the value>`)."""
        last = said.split(" = ", 1)[0].rsplit(".", 1)[-1]
        settings = fp.UNBOUND_KEY_SETTINGS.get(last, ())
        ending = (f"sets it only to {' or '.join(str(setting).lower() for setting in settings)}" if settings
                  else "does not set it")
        return (f"C12: {what} sets {re.escape(said)}, which makes the build {re.escape(fp.UNBOUND_KEYS[last])}, "
                f"and no record binds that: a config {ending}$")

    def test_a_key_that_runs_a_program_no_record_binds_is_refused(self):
        # Each key of src/bootstrap/src/core/config/toml/*.rs that makes the build run a
        # program, or link prebuilt machine code, and is neither a Rust nor a host tool
        # key, set to a program or a file under the build root, to a name the build
        # finds on PATH, or to arguments that name either: a walk that held only the Rust
        # and host tool keys admitted every one.
        under = f"{BUILD_ROOT}/ledger/pathbin"
        musl, wasi = "target.aarch64-unknown-linux-musl", "target.wasm32-wasip1"
        cases = []
        for table, key in (("build", "yarn"), ("build", "windows-rc"), ("build", "sde"),
                           ("build", "compiletest-diff-tool"), ("build", "tidy-extra-checks"),
                           ("build", "android-ndk"), ("build", "compiler-test-fixture"), ("llvm", "clang-cl"),
                           ("llvm", "use-linker"), ("llvm", "offload-clang-dir"), ("rust", "musl-root"),
                           (TARGET, "musl-root"), (TARGET, "qemu-rootfs"),
                           # Prebuilt machine code the build links: an archive, or a directory of them.
                           ("build", "optimized-compiler-builtins"), (TARGET, "optimized-compiler-builtins"),
                           (TARGET, "profiler"), (musl, "musl-libdir"), (wasi, "wasi-root"),
                           (TARGET, "llvm-zstd-pkg-config-dir")):
            for value in (f"{under}/{key}", key):
                cases.append((table, f"{key} = {json.dumps(value)}\n", f"{table}.{key} = {value!r}"))
        # An archive outside the root by a relative path; a directory key set to a switch;
        # a runtime key set to a number, not a switch.
        cases += [("build", 'optimized-compiler-builtins = "../../../../tmp/libclang_rt.builtins.a"\n',
                   "build.optimized-compiler-builtins = '../../../../tmp/libclang_rt.builtins.a'"),
                  (musl, "musl-libdir = false\n", f"{musl}.musl-libdir = False"),
                  (TARGET, "profiler = 1\n", f"{TARGET}.profiler = 1")]
        for key in ("cflags", "cxxflags", "ldflags"):
            for value in (f"-fuse-ld={under}/ld", "-fuse-ld=gold", f"-B{under}"):
                cases.append(("llvm", f"{key} = {json.dumps(value)}\n", f"llvm.{key} = {value!r}"))
        for table in ("rust", TARGET):
            for value in ([f"-Clinker={under}/cc"], ["-Clinker=cc"]):
                cases.append((table, f"rustflags = {json.dumps(value)}\n", f"{table}.rustflags = {value!r}"))
        # A table: the CMake definitions LLVM's build is given, which no leaf's name shows.
        for value in (f"{under}/cc", "clang"):
            cases.append(("llvm.build-config", f"CMAKE_C_COMPILER = {json.dumps(value)}\n",
                          f"llvm.build-config = {{'CMAKE_C_COMPILER': {value!r}}}"))
        # The switches, on in any form: thin-lto has gcc run an ld.lld it finds by name, and
        # wasm-proc-macros has cc-rs find wasm32-wasip2's compiler by name.
        cases += [("build", "patch-binaries-for-nix = true\n", "build.patch-binaries-for-nix = True"),
                  ("llvm", "thin-lto = true\n", "llvm.thin-lto = True"),
                  ("rust", "wasm-proc-macros = true\n", "rust.wasm-proc-macros = True")]
        for value, said in (("true", "True"), ('"external"', "'external'"), ('"self-contained"', "'self-contained'")):
            cases.append(("rust", f"bootstrap-override-lld = {value}\n", f"rust.bootstrap-override-lld = {said}"))
        for table, line, said in cases:
            with self.subTest(said):
                self.refuses(self.unbound_refusal("base-config.toml", said), self.unbound(table, line))
        # Every unbound key is one of these cases.
        self.assertEqual({case[2].split(" = ", 1)[0].rsplit(".", 1)[-1] for case in cases}, set(fp.UNBOUND_KEYS))
        # The rung config is held to it too.
        evidence = self.evidence()
        evidence.raw["rung-config.toml"] = RUNG_CONFIG + b'\n[llvm]\nuse-linker = "lld"\n'
        evidence.fields_override = {"config_departures": "build.jobs,llvm.use-linker"}
        self.refuses("C12: rung-config.toml sets llvm.use-linker = 'lld', which makes the build run", evidence)

    def test_a_switch_off_and_a_table_named_like_a_tool_key_keep_the_record(self):
        # false runs nothing, and true builds compiler-rt's builtins or profiler runtime
        # in-tree with the bound compilers; the pgo and tool tables are named for what
        # they configure, not a program, and only a value is held to the Rust tool rule.
        for table, line in (("build", "patch-binaries-for-nix = false\n"),
                            ("rust", "bootstrap-override-lld = false\n"),
                            ("llvm", "thin-lto = false\n"), ("rust", "wasm-proc-macros = false\n"),
                            ("build", "optimized-compiler-builtins = true\n"),
                            ("build", "optimized-compiler-builtins = false\n"),
                            (TARGET, "optimized-compiler-builtins = true\n"),
                            ("build", "profiler = true\n"), (TARGET, "profiler = true\n"),
                            (TARGET, "profiler = false\n"),
                            ("pgo.rustc", f'use = "{BUILD_ROOT}/profiles/rustc.profdata"\n'),
                            ("build.tool.cargo", 'features = ["all-static"]\n')):
            with self.subTest(line):
                self.assertEqual(self.capture(self.unbound(table, line))["schema"], host_ledger.FIXED_POINT_SCHEMA)

    def test_a_config_names_no_triple_but_the_host_bootstrap_detects(self):
        # A triple build.target or build.host adds is one cc-rs finds a C compiler,
        # archiver and linker for by name on PATH when its table names none, and runs
        # (cc_detect.rs fill_compilers); a path there is read as a target specification,
        # whose own linker rustc runs (target_selection.rs from_user). A walk that held
        # only the tool keys admitted every one.
        under = f"{BUILD_ROOT}/ledger/pathbin"
        for key, value in (("target", [HOST, "x86_64-unknown-linux-gnu"]), ("target", [f"{under}/evil.json"]),
                           ("target", [HOST]), ("host", [HOST, "x86_64-unknown-linux-gnu"]),
                           ("build", "x86_64-unknown-linux-gnu")):
            with self.subTest(key=key, value=value):
                self.refuses(f"C12: base-config.toml sets {re.escape(f'build.{key} = {value!r}')}: a seed builds "
                             "for the host bootstrap detects and no other triple",
                             self.unbound("build", f"{key} = {json.dumps(value)}\n"))

    def test_no_string_climbs_out_of_the_directory_it_is_read_from(self):
        # A relative path resolves under the directory it is read from (x.py runs in
        # <root>/src), which a `..` part leaves: a walk that held only absolute strings
        # under the root admitted the relative ones.
        for table, key, value in (("build", "build-dir", "../../../../tmp/elsewhere"),
                                  ("build", "bootstrap-cache-path", "../../../../tmp/cache"),
                                  ("build", "exclude", ["library", "../../../tmp"]),
                                  ("rust", "profile-use", "../profiles/rustc.profdata"),
                                  ("pgo.rustc", "use", "../../../tmp/rustc.profdata"),
                                  ("build", "build-dir", f"{BUILD_ROOT}/src/../../elsewhere")):
            item = value[-1] if isinstance(value, list) else value
            with self.subTest(key=key, value=value):
                self.refuses(f"C12: base-config.toml names {re.escape(f'{table}.{key} = {item!r}')}, a path that "
                             "climbs out of the directory it is read from$",
                             self.unbound(table, f"{key} = {json.dumps(value)}\n"))
        # A relative path that climbs nowhere keeps the record.
        self.assertEqual(self.capture(self.unbound("build", 'build-dir = "build"\n'))["schema"],
                         host_ledger.FIXED_POINT_SCHEMA)

    def test_the_base_config_names_the_recreators_profile(self):
        # bootstrap merges the defaults file of the profile under the config, a file the
        # evidence does not hold: tools's sets tidy-extra-checks, so a walk of the config
        # alone admitted a refused key no line of it showed.
        text = self.evidence().raw["base-config.toml"]
        anchor = b'profile = "compiler"\n'
        self.assertEqual(text.count(anchor), 1)
        for profile in ("tools", "dist", "library", "user"):
            with self.subTest(profile):
                evidence = self.evidence()
                evidence.raw["base-config.toml"] = text.replace(anchor, f'profile = "{profile}"\n'.encode())
                self.refuses(f"C12: base-config.toml sets profile = '{profile}': bootstrap merges the defaults file "
                             "of the top-level profile", evidence)
        evidence = self.evidence()
        evidence.raw["base-config.toml"] = text.replace(anchor, b"")
        self.refuses(r"C12: base-config.toml sets no profile \(compiler, the recreator's\)", evidence)
        # A key named profile anywhere but the top level is refused too.
        self.refuses("C12: base-config.toml sets rust.profile = 'compiler': bootstrap merges",
                     self.unbound("rust", 'profile = "compiler"\n'))

    def test_the_defaults_of_the_profile_the_base_config_names_keep_the_tool_rule(self):
        # What the validator cannot read: each in-tree defaults file bootstrap merges for
        # a profile PROFILES admits keeps C12, line by line as bootstrap.py reads it and
        # key by key. The tools profile's sets tidy-extra-checks: why PROFILES is not all.
        kept, refused = set(), {}
        for path in sorted((ROOT / "src" / "bootstrap" / "defaults").glob("bootstrap.*.toml")):
            profile = path.name.split(".")[1]
            try:
                fp.check_config_lines(path.read_bytes(), path.name)
                fp.check_config_tools(tomllib.loads(path.read_text()), BUILD_ROOT, path.name)
            except ValueError as error:
                refused[profile] = str(error)
                continue
            kept.add(profile)
        self.assertLessEqual(set(fp.PROFILES), kept, refused)
        self.assertRegex(refused.get("tools", ""), "sets build.tidy-extra-checks")

    def test_a_config_bootstrap_py_reads_otherwise_than_toml_is_refused(self):
        # src/bootstrap/bootstrap.py reads a config line by line (get_toml_static) and
        # builds and runs bootstrap with what it read, the build triple's cc and linker,
        # build.rustc, build-dir, bootstrap-cache-path and patch-binaries-for-nix among
        # them, before the Rust bootstrap reads it as TOML. Each text here is TOML the
        # tool rule's walk admitted, and the real get_toml_static reads the key named
        # beside it otherwise than TOML does (in an included file, after the `[]` line
        # config_with_includes puts before it, for the top-level dotted key).
        reader = bootstrap_py().RustBuild.get_toml_static
        under = f"{BUILD_ROOT}/ledger/pathbin"
        base = self.evidence().raw["base-config.toml"].decode()
        python, linker, header = 'python = "/usr/bin/python3"\n', 'linker = "/usr/bin/gcc"\n', f"[{TARGET}]\n"
        for char in base:
            self.assertNotIn(char, fp.CONFIG_LINE_BREAKS)
        line = r"line \d+ is {}, which bootstrap.py's line reader".format
        cases = (
            ("a multi-line string whose lines read as keys",
             base.replace(python, python + f'description = """\n{header}linker = "{under}/evil"\n'
                          f'cc = "{under}/evil"\n[build]\npatch-binaries-for-nix = true\n"""\n'),
             ("linker", TARGET), line(re.escape(repr('description = """')))),
            *((f"{char!r} in a comment", base.replace(header, header + f'# the host{char}linker = "{under}/evil"\n'),
               ("linker", TARGET), "holds " + re.escape(repr(char))) for char in "\x85\u2028\u2029"),
            ("a literal string holding a double quote",
             base.replace(python, python + f"build-dir = '{BUILD_ROOT}/a\"/tmp/elsewhere\"'\n"),
             ("build-dir", "build"), line(r".build-dir = .*")),
            ("an escape", base.replace(linker, 'linker = "\\u002Fusr/bin/gcc"\n'), ("linker", TARGET),
             line(re.escape(repr('linker = "\\u002Fusr/bin/gcc"')))),
            ("a trailing comment holding a string",
             base.replace(python, python + f"build-dir = '{BUILD_ROOT}/build' # \"/tmp/elsewhere\"\n"),
             ("build-dir", "build"), line(r".build-dir = .*")),
            ("a quoted key", base.replace(python, python + f'"rustc" = "{BUILD_ROOT}/stage0/bin/trustc"\n'),
             ("rustc", "build"), line(re.escape(repr(f'"rustc" = "{BUILD_ROOT}/stage0/bin/trustc"')))),
            ("a header with a trailing comment", base.replace(header, f"[{TARGET}] # the host\n"),
             ("linker", TARGET), line(re.escape(repr(f"[{TARGET}] # the host")))),
            ("an empty string", base.replace(python, python + 'bootstrap-cache-path = ""\n'),
             ("bootstrap-cache-path", "build"), line(re.escape(repr('bootstrap-cache-path = ""')))),
            ("a top-level dotted key",
             base.replace(f"[build]\n{python}", f'build.python = "/usr/bin/python3"\n'
                          f'build.bootstrap-cache-path = "{BUILD_ROOT}/cache"\n'),
             ("bootstrap-cache-path", "build"), line(re.escape(repr('build.python = "/usr/bin/python3"')))),
        )
        for name, text, (key, section), pattern in cases:
            with self.subTest(name):
                self.assertNotEqual(text, base)
                document = tomllib.loads(text)
                for part in section.split("."):
                    document = document[part]
                said = document.get(key)
                said = ("true" if said else "false") if isinstance(said, bool) else said
                read = reader(("\n[]\n" if "dotted" in name else "") + text, key, section)
                self.assertNotEqual(read, said, "bootstrap.py reads this key as TOML does")
                evidence = self.evidence()
                evidence.raw["base-config.toml"] = text.encode()
                self.refuses(f"C12: base-config.toml {pattern}", evidence)
        # The same rule refuses what bootstrap.py would read alike here but not where a
        # line reader reads otherwise: other line breaks, a multi-line array, an inline table.
        for name, text, pattern in (
                ("CRLF", base.replace("\n", "\r\n"), "holds '\\\\r'"),
                ("a multi-line array", base.replace(python, python + 'exclude = [\n    "src/tools",\n]\n'),
                 line(re.escape(repr("exclude = [")))),
                ("an inline table",
                 base.replace(python, python + 'tool = { cargo = { features = ["all-static"] } }\n'),
                 line(r"'tool = .*"))):
            with self.subTest(name):
                tomllib.loads(text)
                evidence = self.evidence()
                evidence.raw["base-config.toml"] = text.encode()
                self.refuses(f"C12: base-config.toml {pattern}", evidence)
        # The rung config, which bootstrap.py reads first, is held to it too: its job
        # count with a comment is a count bootstrap.py hands Cargo with the comment.
        rung = RUNG_CONFIG.replace(b"jobs = 20\n", b"jobs = 20 # the host's CPUs\n")
        self.assertEqual(reader(rung.decode(), "jobs", "build"), "20 # the host's CPUs")
        evidence = self.evidence()
        evidence.raw["rung-config.toml"] = rung
        self.refuses("C12: rung-config.toml " + line(re.escape(repr("jobs = 20 # the host's CPUs"))), evidence)
        evidence = self.evidence()
        evidence.raw["rung-config.toml"] = RUNG_CONFIG + f'# x\u2028cc = "{under}/evil"\n'.encode()
        self.refuses("C12: rung-config.toml holds '\\\\u2028'", evidence)

    def test_config_line_breaks_are_every_break_str_splitlines_reads(self):
        # bootstrap.py splits a config with str.splitlines: every character it breaks a
        # line at but \n is one a config does not hold.
        breaks = {chr(code) for code in range(0x110000) if len(f"a{chr(code)}b".splitlines()) == 2}
        self.assertEqual(breaks, set(fp.CONFIG_LINE_BREAKS) | {"\n"})

    def recreator_config(self) -> str:
        """What recreate_bootstrap.write_config writes in seed mode on a Linux host that
        has /usr/bin/gcc and /usr/bin/g++ (82bb867edd's config came from the same
        template and Linux branch, without the lld block LINUX-SEED-LLD-1 added), with
        its checkout at <root>/src."""
        from scripts import recreate_bootstrap as recreate
        src = self.base / "recreator" / "src"
        src.mkdir(parents=True)
        is_file = Path.is_file
        with mock.patch.object(recreate.platform, "system", return_value="Linux"), \
                mock.patch.object(recreate, "find_python_ge_311", return_value="/usr/bin/python3"), \
                mock.patch.object(Path, "is_file", lambda path, *args, **options: str(path) in (
                                  "/usr/bin/gcc", "/usr/bin/g++") or is_file(path, *args, **options)), \
                mock.patch.object(sys, "stdout", io.StringIO()):
            written = recreate.write_config(src, HOST, force=False, seed_mode=True)
        return written.path.read_text().replace(str(src), f"{BUILD_ROOT}/src")

    def test_the_base_config_the_recreator_writes_on_linux_keeps_the_tool_rule_but_its_own_lld(self):
        text = self.recreator_config()
        document = tomllib.loads(text)
        self.assertEqual(document["rust"]["codegen-backends"], ["llvm", "trust-cg"])
        self.assertEqual(document["target"][HOST], {"cc": "/usr/bin/gcc", "cxx": "/usr/bin/g++",
                                                    "linker": "/usr/bin/gcc"})
        # Since LINUX-SEED-LLD-1 a Linux config links with the stage0's own rust-lld, which no
        # admission binds: a fixed point of such a commit is refused by that key alone.
        self.assertEqual(document["rust"]["bootstrap-override-lld"], "self-contained")
        evidence = self.evidence()
        evidence.raw["base-config.toml"] = text.encode()
        with self.assertRaisesRegex(ValueError, r"fixed-point C12: base-config\.toml sets "
                                                r"rust\.bootstrap-override-lld = 'self-contained'"):
            self.capture(evidence)
        from scripts import recreate_bootstrap as recreate
        block = recreate.LINUX_LLD_BLOCK
        self.assertEqual(text.count(block), 1)
        evidence.raw["base-config.toml"] = text.replace(block, "").encode()
        self.assertEqual(self.capture(evidence)["schema"], host_ledger.FIXED_POINT_SCHEMA)

    def test_bootstrap_py_reads_every_key_of_the_admitted_configs_as_toml_does(self):
        # The rung config with the base config it includes, as x.py's bootstrap.py reads
        # them (config_with_includes, get_toml_static, _toml_top_level_include): for the
        # fixture's base config and the recreator's, each scalar key reads as TOML reads it.
        bootstrap = bootstrap_py()
        for name, base in (("fixture", self.evidence().raw["base-config.toml"].decode()),
                           ("recreator", self.recreator_config())):
            directory = self.base / f"read-{name}"
            directory.mkdir()
            (directory / "bootstrap.toml").write_text(base)
            rung = RUNG_CONFIG.decode().replace(f"{BUILD_ROOT}/src/bootstrap.toml", str(directory / "bootstrap.toml"))
            (directory / "rung.toml").write_text(rung)
            text = bootstrap.config_with_includes(rung, str(directory / "rung.toml"))
            self.assertEqual(bootstrap._toml_top_level_include(rung), [str(directory / "bootstrap.toml")])
            read = 0
            for document in (tomllib.loads(rung), tomllib.loads(base)):
                for key, value in fp._flat(document):
                    if isinstance(value, list):
                        continue
                    section, _, last = key.rpartition(".")
                    said = ("true" if value else "false") if isinstance(value, bool) else str(value)
                    with self.subTest(name=name, key=key):
                        self.assertEqual(bootstrap.RustBuild.get_toml_static(text, last, section or None), said)
                    read += 1
            self.assertGreater(read, 10)

    def test_every_bootstrap_config_key_is_classed_for_the_tool_rule(self):
        # The keys bootstrap reads (every define_config! name, serde's renames and
        # aliases, and TomlConfig's own top-level keys, in
        # src/bootstrap/src/core/config/toml/*.rs), each in one class: a Rust tool key, a
        # host tool key, an unbound key, a triple key, a download key, a key with its own
        # rule (profile, include), or one that names no program for the build to run and
        # no prebuilt code for it to link (CONFIG_KEYS_THAT_RUN_NOTHING). A key bootstrap
        # gains is classed here before a seed config is trusted with it. The census
        # cannot tell a key put in the wrong class: each class's comment says why.
        names, tables = set(), set()
        directory = ROOT / "src" / "bootstrap" / "src" / "core" / "config" / "toml"
        for path in sorted(directory.glob("*.rs")):
            text = path.read_text()
            for block in re.findall(r"^define_config! \{\n(.*?)^\}$", text, re.M | re.S):
                names.update(re.findall(r'^\s*\w+: [^=\n]+ = "([^"]+)",', block, re.M))
                tables.update(re.findall(r"^\s*struct (\w+) \{", block, re.M))
            names.update(re.findall(r'#\[serde\([^]]*\b(?:rename|alias) = "([^"]+)"', text))
        # TomlConfig's own fields (serde kebab-case) but the tables it reads into.
        body = re.search(r"^pub\(crate\) struct TomlConfig \{\n(.*?)^\}$", (directory / "mod.rs").read_text(),
                         re.M | re.S).group(1)
        fields = re.findall(r"^\s*pub\(\w+\) (\w+): (.+),$", body, re.M)
        self.assertIn(("profile", "Option<String>"), fields)
        names.update(field.replace("_", "-") for field, kind in fields
                     if not any(re.search(rf"\b{table}\b", kind) for table in tables) and field != "change_id")
        self.assertIn("compiletest-diff-tool", names)
        self.assertLessEqual({"profile", "include", "change-id"}, names)
        classes = {"rust tool": set(fp.RUST_TOOL_KEYS), "host tool": set(fp.HOST_TOOL_KEYS),
                   "unbound": set(fp.UNBOUND_KEYS), "triple": set(fp.TRIPLE_KEYS),
                   "download": {name for name in names if name.startswith("download-")},
                   "its own rule": CONFIG_KEYS_WITH_THEIR_OWN_RULE, "runs nothing": CONFIG_KEYS_THAT_RUN_NOTHING}
        for name in sorted(names):
            with self.subTest(name):
                self.assertEqual(len([label for label, members in classes.items() if name in members]), 1,
                                 f"{name} is in {[label for label, members in classes.items() if name in members]}")
        self.assertLessEqual(set(fp.UNBOUND_KEYS) | set(fp.TRIPLE_KEYS) | CONFIG_KEYS_WITH_THEIR_OWN_RULE
                             | CONFIG_KEYS_THAT_RUN_NOTHING, names)
        self.assertLessEqual(set(fp.UNBOUND_KEY_SETTINGS), set(fp.UNBOUND_KEYS))
        # No name is in two of the validator's four lists.
        lists = (fp.RUST_TOOL_KEYS, fp.HOST_TOOL_KEYS, tuple(fp.UNBOUND_KEYS), fp.TRIPLE_KEYS)
        self.assertEqual(len(set().union(*lists)), sum(len(set(keys)) for keys in lists))

    def test_archive_members_are_read_whole(self):
        evidence = self.evidence()
        evidence.edit("archive-members.json", edit_member("bin/cargo-alias", lambda row: row.update(link="trustc")))
        self.refuses("C13: targo-.* ships the link bin/cargo-alias with another target than the producer's", evidence)
        evidence = self.evidence()

        def twice(doc):
            notes = next(dict(row) for archive in doc["archives"] for row in archive["members"]
                         if row["path"] == "lib/rustlib/etc/analyzer-notes.txt")
            last = doc["archives"][-1]
            last["members"] = sorted([*last["members"], {**notes, "sha256": "9" * 64}], key=lambda row: row["path"])
            last["members_sha256"] = support.records_sha256(last["members"])
        evidence.edit("archive-members.json", twice)
        self.refuses("C13: two archives install lib/rustlib/etc/analyzer-notes.txt with different bytes", evidence)
        evidence = self.evidence()
        evidence.edit("archive-members.json", lambda doc: doc["archives"][0]["members"][0].update(mode=0o777))
        self.refuses("C13: .*'s member list is not its members_sha256", evidence)
        self.refused_field("C13: archive_members / archive_bytes_total", archive_bytes_total="1")
        evidence = self.evidence()
        evidence.edit("archive-members.json", edit_member("lib/rustlib/etc/analyzer-notes.txt",
                                                          lambda row: row.update(kind="weird")))
        self.refuses("C13: .* lists lib/rustlib/etc/analyzer-notes.txt with the kind 'weird'", evidence)

    def test_an_archive_only_script_is_named(self):
        # What the installer's manifest.in ships beside the compiler: scripts no build compared.
        with tempfile.TemporaryDirectory() as tmp:
            archive = write_archive(Path(tmp), "trustc", "trustc", {
                "bin/trust-gdb": b"#!/bin/sh\nexec gdb \"$@\"\n", "lib/rustlib/etc/gdb_load.py": b"import gdb\n",
                "lib/rustlib/etc/helper": b"data", "bin/trustc": STAGE2["bin/trustc"]},
                modes={"lib/rustlib/etc/helper": 0o755})
            kinds = {row["path"]: row["kind"] for row in fp.archive_table(archive)["members"]}
        self.assertEqual(kinds, {"bin/trust-gdb": "script", "bin/trustc": "elf", "lib/rustlib/etc/gdb_load.py": "other",
                                 "lib/rustlib/etc/helper": "executable"})
        evidence = self.evidence()
        evidence.edit("archive-members.json", edit_member("lib/rustlib/etc/analyzer-notes.txt",
                                                          lambda row: row.update(kind="script")))
        fields = evidence.fields()
        self.assertEqual((fields["archive_only"], fields["archive_only_executables"]),
                         ("lib/rustlib/etc/analyzer-notes.txt", "lib/rustlib/etc/analyzer-notes.txt"))
        self.capture(evidence)
        evidence.fields_override = {"archive_only_executables": "none"}
        self.refuses("C13: archive_only_executables = 'none', and the members give "
                     "'lib/rustlib/etc/analyzer-notes.txt'", evidence)
        self.refused_field("C13: archive_only_executables names a member archive_only does not",
                           archive_only_executables="bin/trust-gdb")

    def test_shared_source_identity_is_recomputed(self):
        def shared(change):
            evidence = self.evidence()
            evidence.edit("archive-members.json", lambda doc: change(doc["shared"]))
            return evidence

        cases = (
            ("the excluded pinned member is another file",
             lambda doc: doc["excluded"][0].update(pinned_sha256="0" * 64), "the excluded builder-config is not the "
                                                                              "two archives' own member"),
            ("a vacuous exclusion", lambda doc: (doc.update(pinned_host_local_sha256=sha(RUNG_CONFIG)),
                                                 doc["excluded"][0].update(pinned_sha256=sha(RUNG_CONFIG))),
             ".*an exclusion must be of a real difference"),
            ("tables that differ outside builder-config",
             lambda doc: doc["this_run_dist"].update(member_table_without_host_local_sha256="0" * 64),
             "this run's trust-src-.* and the pinned one have different member tables outside the package-root "
             "builder-config"),
            ("an exclusion of tables that are equal whole",
             lambda doc: doc["this_run_dist"].update(member_table_sha256=doc["pinned_member_table_sha256"]),
             "the member tables are equal whole, and the comparison excluded"),
            ("this run's builder-config is not the rung config",
             lambda doc: (doc["this_run_dist"].update(host_local_sha256="0" * 64),
                          doc["excluded"][0].update(this_run_sha256="0" * 64)),
             "this run's builder-config is not the rung config"),
            ("no this-run table", lambda doc: doc.pop("this_run_dist"),
             "archive-members.json does not bind the pinned shared source"),
        )
        for what, change, pattern in cases:
            with self.subTest(what):
                self.refuses(f"C13: {pattern}", shared(change))
        evidence = shared(lambda doc: doc.update(excluded=[]))
        evidence.fields_override = {"shared_source_members_excluded": "none"}
        self.refuses("C13: the member tables are different whole, and the comparison excluded", evidence)

    def test_the_shared_archives_are_read_again(self):
        evidence = self.evidence()
        seed, record, _ = evidence.write()
        joins = lambda **more: fp.check_archive_joins(seed, record["payloads"], HOST, host_ledger.read_proof,  # noqa
                                                      archive_root=seed, **more)
        self.assertGreater(joins(this_run_shared=THIS_RUN), 0)
        with tempfile.TemporaryDirectory() as tmp:
            other = write_archive(Path(tmp), "trust-src", "rust-src", {SOURCE_FILE: b"pub fn core() {}\n"},
                                  b"another config\n")
            with self.assertRaisesRegex(ValueError, "C13: this run's .* read again is not the this_run_dist"):
                joins(this_run_shared=other)
        # The excluded member's pinned digest is the real pinned archive's builder-config.
        evidence = self.evidence()
        evidence.edit("archive-members.json", lambda doc: doc["shared"]["excluded"][0].update(pinned_sha256="0" * 64))
        seed, record, _ = evidence.write()
        with self.assertRaisesRegex(ValueError, "C13: the excluded builder-config is not the pinned trust-src-"):
            fp.check_archive_joins(seed, record["payloads"], HOST, host_ledger.read_proof, archive_root=seed)
        # Both builder-config digests stated wrong together pass capture; the real pinned archive refuses them.
        evidence = self.evidence()
        evidence.edit("archive-members.json", lambda doc: (doc["shared"].update(pinned_host_local_sha256="0" * 64),
                                                           doc["shared"]["excluded"][0].update(pinned_sha256="0" * 64)))
        seed, record, door = evidence.write()
        host_ledger.capture_fixed_point_record(seed, evidence.pins, HOST, record, door=door)
        with self.assertRaisesRegex(ValueError, "C13: the pinned trust-src-.*'s member table is not the one"):
            fp.check_archive_joins(seed, record["payloads"], HOST, host_ledger.read_proof, archive_root=seed)
        # The pinned shared archive recompressed: the same members, other bytes.
        evidence = self.evidence()
        seed, record, _ = evidence.write()
        source = seed / "dist" / DATE / archive_name("trust-src")
        with tarfile.open(source, "r:xz") as old:
            members = [(info, old.extractfile(info).read() if info.isfile() else None) for info in old]
        with tarfile.open(source, "w:xz", preset=1) as new:
            for info, data in members:
                new.addfile(info, None if data is None else io.BytesIO(data))
        self.assertNotEqual(sha(source.read_bytes()), record["payloads"][f"dist/{DATE}/{source.name}"])
        with self.assertRaisesRegex(ValueError, "C13: .* is not the pinned shared archive"):
            fp.check_archive_joins(seed, record["payloads"], HOST, host_ledger.read_proof, archive_root=seed)

    def test_native_rows_are_their_digest_and_place(self):
        evidence = self.evidence()
        evidence.edit("native-outputs.json", lambda doc: doc["rows"][1].update(bytes=10))
        self.refuses("C14: native-outputs.json does not hash to native_outputs_sha256", evidence)
        evidence = self.evidence()

        def planted(doc):
            doc["rows"] = sorted([*doc["rows"], {"path": "stage2/bin/trustc", "kind": "elf", "bytes": 12,
                                                 "sha256": sha(STAGE2["bin/trustc"])}], key=lambda row: row["path"])
            doc["files"], doc["sha256"] = len(doc["rows"]), support.records_sha256(doc["rows"])
        evidence.edit("native-outputs.json", planted)
        self.refuses(r"C14: native-outputs.json lists \['stage2/bin/trustc'\], which is not under llvm/ or lld/",
                     evidence)

    def test_inputs_are_read_whole(self):
        evidence = self.evidence()
        evidence.edit("inputs.json", lambda doc: doc.update(commit=P0))
        self.refuses("C15: inputs.json is not the inputs of this commit, host and root", evidence)
        evidence = self.evidence()
        elsewhere = "/opt/lean/lib/lean"
        evidence.edit("inputs.json", lambda doc: doc["clean_lean_inputs"].update(library=elsewhere))
        for name in list(evidence.raw):
            if name.startswith("run-"):
                evidence.edit(name, lambda run: (run["environment"].update(CLEAN_OLEAN_PINNED_LEAN_LIB=elsewhere),
                                                 run["clean_lean"].update(library=elsewhere)))
        self.refuses("C15: the Lean library '/opt/lean/lib/lean' is not a copy under", evidence)
        for what, change, pattern in (
                ("a manifest of nothing", lambda doc: doc["cargo_home_inputs"].update(manifest={"anything": True}),
                 "C15: inputs.json's cargo-home manifest is not"),
                ("a manifest of other trees", lambda doc: doc["cargo_home_inputs"]["manifest"].update(trees={}),
                 "C15: inputs.json's cargo-home manifest is not"),
                ("a system ninja", lambda doc: doc.update(ninja={"path": "/usr/bin/ninja", "sha256": NINJA_SHA}),
                 "C15: inputs.json's ninja is not the copy at"),
                ("another ninja", lambda doc: doc["ninja"].update(sha256="0" * 64),
                 "C7: run-producer.json is not a clean run: .*ninja")):
            with self.subTest(what):
                evidence = self.evidence()
                evidence.edit("inputs.json", change)
                self.refuses(pattern, evidence)

    def test_every_chain_rung_is_a_clean_trust_build(self):
        for what, change, pattern in (
                ("an intermediate rung that failed", lambda doc: doc["rungs"][0].update(rc=1),
                 "chain rung r1 is not a clean build"),
                ("an intermediate rung without no-stock evidence",
                 lambda doc: doc["rungs"][0].update(no_stock_evidence=False), "chain rung r1 is not a clean build"),
                ("a rung built by a compiler no rung made",
                 lambda doc: doc["rungs"][2].update(stage0_compiler_sha256="9" * 64),
                 "chain rung r3 ran the compiler 9{16}, which is not the root's or an earlier rung's build of "
                 "29ebb403de"),
                ("the root's compiler run as another commit's",
                 lambda doc: doc["rungs"][1].update(stage0_compiler_sha256=ROOT_TRUSTC),
                 "chain rung r2 ran the compiler"),
                ("a config line that does not name the ancestor",
                 lambda doc: doc["origin"].update(config_lines=['rustc = "/opt/x/bin/trustc"']),
                 "chain.json's origin does not carry")):
            with self.subTest(what):
                evidence = self.evidence()
                evidence.edit("chain.json", change)
                self.refuses(f"C16: {pattern}", evidence)

    def test_the_evidence_digest_is_read_from_the_files(self):
        evidence = self.evidence()
        seed, record, door = evidence.write()
        receipt_bytes = (seed / "host-proofs" / HOST / "SEED-FIXED-POINT").read_bytes()
        surface_bytes = (seed / "host-proofs" / HOST / "seed-surface.json").read_bytes()
        found = fp.capture_evidence(seed, evidence.pins, HOST, fp.parse_receipt(receipt_bytes), receipt_bytes,
                                    host_ledger.validate_surface(surface_bytes, HOST, VERSION), surface_bytes,
                                    host_ledger.read_proof, payloads=record["payloads"], allowed=ALLOWED)
        self.assertEqual(found["sha256"], record["evidence_sha256"])


class TokenLeakTests(Case):
    """SEED-TOKEN-LEAK-STAGE0-1 (docs/DECISION_QUEUE.md): a run whose FIFO jobserver came
    back short is accepted only when x.py exited 0, its census shows nothing outlived x.py,
    the FIFO's path was unchanged, the count is not below none and its stage0 is a chain
    commit that does not contain d57cafb60f7 (docs/OPEN_ISSUES.md RUSTC-FRONTEND-TOKEN-LEAK-1); the
    receipt names every such run, and the validator recomputes the list."""

    RULE = (r"SEED-TOKEN-LEAK-STAGE0-1 \(docs/OPEN_ISSUES.md RUSTC-FRONTEND-TOKEN-LEAK-1\) does not excuse its "
            r"jobserver's 18 of the 19 token\(s\) back: ")

    @staticmethod
    def short(*, rc: object = 0, path_unchanged: object = True, **census):
        """A run whose jobserver got 18 of its 19 tokens back; `census` changes its process census."""
        def change(run):
            run["jobserver"].update(tokens_at_end=18, path_unchanged=path_unchanged)
            run["process_census"].update(census)
            run["rc"] = rc
        return change

    def test_a_token_kept_by_a_chain_stage0_without_the_fix_is_accepted_and_disclosed(self):
        evidence = self.evidence()
        evidence.edit("run-cross-check.json", self.short())
        self.assertEqual(evidence.fields()["jobserver_token_deficits"], "s-build:19->18")
        seed, record, door = evidence.write()
        self.assertIn(b"\njobserver_token_deficits=s-build:19->18\n",
                      (seed / "host-proofs" / HOST / "SEED-FIXED-POINT").read_bytes())
        actual, _ = host_ledger.capture_fixed_point_record(seed, evidence.pins, HOST, record, door=door)
        self.assertEqual(actual, record)
        # Disclosed and recomputed: a receipt that leaves the run out, or says another count or run, is refused.
        for said in ("none", "s-build:19->17", "p-build:19->18,s-build:19->18"):
            with self.subTest(said):
                evidence.fields_override = {"jobserver_token_deficits": said}
                self.refuses(rf"C7: jobserver_token_deficits = '{re.escape(said)}', and the run records give "
                             r"'s-build:19->18': every run whose jobserver came back short is disclosed "
                             r"\(SEED-TOKEN-LEAK-STAGE0-1\)", evidence)
        # A record whose every run balanced says none, and a receipt that names a run is refused.
        balanced = self.evidence()
        self.assertEqual(balanced.fields()["jobserver_token_deficits"], "none")
        balanced.fields_override = {"jobserver_token_deficits": "s-build:19->18"}
        self.refuses(r"C7: jobserver_token_deficits = 's-build:19->18', and the run records give 'none'", balanced)

    def test_the_receipt_field_is_none_or_a_sorted_list_of_deficits(self):
        for said in ("s-build:19->19", "s-build:18->19", "s-build:19->18,p-build:19->18",
                     "s-build:19->18,s-build:19->18", "S-build:19->18", "s-build:19-18", "s-build:019->18",
                     "s-build:19->-1", "s-build"):
            with self.subTest(said):
                self.refused_field(r"B7: jobserver_token_deficits = .* is not 'none' or a sorted list of "
                                   r"<label>:<given>-><returned>, each with fewer returned \(SEED-TOKEN-LEAK-STAGE0-1\)",
                                   jobserver_token_deficits=said)

    def test_a_short_jobserver_is_refused_unless_every_condition_holds(self):
        # Each condition broken alone, on the cross-check, whose stage0 (29ebb403de) does not contain the fix.
        cases = (
            ("x.py did not exit 0", self.short(rc=1), r"x.py exited 1, not 0"),
            ("a census that did not see x.py exit", self.short(ended="cap"),
             r"its process census ended 'cap' with abandoned_children 0, not watched-exited with 0, so a process may "
             r"have outlived x.py holding the token"),
            ("an abandoned child", self.short(abandoned_children=1),
             r"its process census ended 'watched-exited' with abandoned_children 1, not watched-exited with 0"),
            ("an abandoned child count that is not a number", self.short(abandoned_children=False),
             r"its process census ended 'watched-exited' with abandoned_children False, not watched-exited with 0"),
            ("a FIFO path that changed", self.short(path_unchanged=False),
             r"its jobserver's path did not name the FIFO when x.py had exited"),
        )
        for what, change, pattern in cases:
            with self.subTest(what):
                evidence = self.evidence()
                evidence.edit("run-cross-check.json", change)
                self.refuses(rf"C7: run-cross-check.json is not a clean run: .*{self.RULE}{pattern}", evidence)
        with self.subTest("a count below none"):
            evidence = self.evidence()
            evidence.edit("run-cross-check.json", lambda run: run["jobserver"].update(tokens_at_end=-1))
            # The receipt cannot list it (its form is a count of none or more), so C7 is reached with none.
            evidence.fields_override = {"jobserver_token_deficits": "none"}
            self.refuses(r"C7: run-cross-check.json is not a clean run: .*SEED-TOKEN-LEAK-STAGE0-1 \(docs/OPEN_ISSUES.md "
                         r"RUSTC-FRONTEND-TOKEN-LEAK-1\) does not excuse its jobserver's -1 of the 19 token\(s\) back: it "
                         r"counted -1 token\(s\) at the end, not none or more", evidence)
        # The stage0 condition broken alone: every other run's stage0 contains the fix (the
        # producer's 6dad0d786f; the seed's, which the fixed point and every control ran).
        stage0 = (r"its stage0 commit '{}' is not one of the chain commits that do not contain d57cafb60f "
                  r"\(6986546eaa, 20565c3255, 29ebb403de\)")
        for name, commit in (("run-producer.json", P0), ("run-producer-dist.json", P0), ("run-producer-full.json", P0),
                             ("run-producer-manifest-tool.json", P0), ("run-fixed-point.json", COMMIT)):
            with self.subTest(name):
                evidence = self.evidence()
                evidence.edit(name, self.short())
                self.refuses(rf"C7: {name} is not a clean run: .*{self.RULE}{stage0.format(commit[:10])}", evidence)
        evidence = self.evidence(fixed={"bin/ty": b"\x7fELF ty 2"}, controls=({},))
        evidence.edit("run-control-1.json", self.short())
        self.refuses(rf"C7: run-control-1.json is not a clean run: .*{self.RULE}{stage0.format(COMMIT[:10])}", evidence)
        # A surplus is never excused, whatever the stage0.
        evidence = self.evidence()
        evidence.edit("run-cross-check.json", lambda run: run["jobserver"].update(tokens_at_end=20))
        text = self.refuses(r"C7: run-cross-check.json is not a clean run: .*\(it differs in tokens_at_end\)", evidence)
        self.assertNotIn("SEED-TOKEN-LEAK-STAGE0-1", text)

    def test_the_chain_commits_without_the_fix_are_the_ones_git_names(self):
        # TOKEN_LEAK_STAGE0_COMMITS is fixed because the validator runs no git; git decides it.
        contains = {}
        for commit in (*fp.CHAIN_COMMITS, COMMIT):
            done = subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor", fp.TOKEN_LEAK_FIX_COMMIT,
                                   commit], capture_output=True, text=True)
            self.assertIn(done.returncode, (0, 1), f"git cannot say whether {commit} contains "
                                                   f"{fp.TOKEN_LEAK_FIX_COMMIT}: {done.stderr.strip()}")
            contains[commit] = done.returncode == 0
        self.assertEqual(len(set(fp.TOKEN_LEAK_STAGE0_COMMITS)), len(fp.TOKEN_LEAK_STAGE0_COMMITS))
        self.assertEqual(set(fp.TOKEN_LEAK_STAGE0_COMMITS),
                         {commit for commit in fp.CHAIN_COMMITS if not contains[commit]})
        # The producer's stage0 and the seed (the fixed point's and every control's stage0) contain it.
        self.assertTrue(contains[P0])
        self.assertTrue(contains[COMMIT])


class ReviewedLedgerTests(Case):
    def test_the_record_maker_validates_the_surface_itself(self):
        evidence = self.evidence()
        seed, record, door = evidence.write()
        receipt = (seed / "host-proofs" / HOST / "SEED-FIXED-POINT").read_bytes()
        for key, value in (("host", "x86_64-unknown-linux-gnu"), ("source_version", "0.14.0")):
            with self.subTest(key), self.assertRaisesRegex(ValueError, f"host seed surface {key} disagrees"):
                host_ledger.make_fixed_point_host_record(evidence.pins, HOST, receipt,
                                                         dump({**evidence.surface, key: value}), door=door)

    def test_member_binding_reads_the_bound_receipt(self):
        evidence = self.evidence()
        seed, record, _ = evidence.write()
        members = {"bin/trustc": {"member_sha256": sha(STAGE2["bin/trustc"])}}
        host_ledger.check_fixed_point_member_bindings(seed, HOST, record, members)
        with self.assertRaisesRegex(ValueError, "fixed-point receipt is not the one its host record binds"):
            host_ledger.check_fixed_point_member_bindings(seed, HOST, {**record, "receipt_sha256": "0" * 64}, members)

    def test_the_door_opens_only_with_the_recreators_member_binding(self):
        problems = door_wiring_problems()
        # Today the door is empty, so nothing is admitted without the binding ...
        self.assertTrue(not host_ledger.FIXED_POINT_FIRST_HOSTS or not problems, problems)
        # ... and an entry added before the recreator binds every hashed member fails here.
        if problems:
            with mock.patch.dict(host_ledger.FIXED_POINT_FIRST_HOSTS, {HOST: {"commit": COMMIT,
                                                                              "receipt_sha256": "0" * 64}}):
                self.assertFalse(not host_ledger.FIXED_POINT_FIRST_HOSTS or not door_wiring_problems())


def load_staircase():
    sys.path.insert(0, str(ROOT / "scripts"))
    try:
        spec = importlib.util.spec_from_file_location("fixed_point_first_host_staircase_consumer",
                                                      ROOT / "scripts" / "seed_staircase.py")
        staircase = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(staircase)
    finally:
        sys.path.remove(str(ROOT / "scripts"))
    return staircase


def opened(load, door):
    """`load` (a loader of seed_host_ledger.py) whose module's door holds `door`:
    each consumer loads its own copy of the helper, so the door is set on it."""
    def load_with_door(*args, **kwargs):
        module = load(*args, **kwargs)
        module.FIXED_POINT_FIRST_HOSTS.update(door)
        return module
    return load_with_door


class ConsumerTests(Case):
    """The consumers of a fixed-point record (design code_changes 5, 7 and 9): the
    recreator's seed capture binds every archive member it hashes to the receipt's
    rows and grades a build from it below every release; the mint carries no
    anchor from it; a staircase lineage over a pinned root names it. Each test
    lays out a repository whose only host record is this fixture's."""

    def repository(self, evidence: Evidence) -> tuple[Path, dict, dict]:
        seed, record, door = evidence.write()
        root = seed.parent.parent
        pins = {key: value for key, value in evidence.pins.items() if DARWIN not in key}
        (root / "src").mkdir()
        (root / "src" / "stage0").write_text("".join(f"{key}={value}\n" for key, value in pins.items()))
        (root / "src" / "version").write_text(VERSION + "\n")
        (root / "scripts").mkdir()
        (root / "scripts" / "check_seed_freshness.py").write_text("# inert: the checker is not run here\n")
        (seed / "dist" / DATE / "channel-rust-trust.toml").write_bytes(b"manifest")
        self.assertEqual(sha(b"manifest"), pins["compiler_channel_manifest_hash"])
        checksums = sorted(f"sha256:{value}" for key, value in pins.items() if key.startswith("dist/"))
        (seed / "seed-ledger.toml").write_text(
            'scope = "internal"\npromotion_decision = "admit-internal"\n'
            'signatures = ["placeholder:internal-admission-only:not-publicly-signed"]\n'
            f"checksums = [{', '.join(json.dumps(item) for item in checksums)}]\n\n"
            f'[release]\nrepo = "fixture/trust"\ndate = "{DATE}"\ncompiler_version = "{VERSION}-trust"\n'
            f'compiler_git_commit_hash = "{COMMIT}"\nchannel_manifest_hash = "{sha(b"manifest")}"\n'
            'visibility = "private"\n'
            + "\n".join(host_ledger.render_host_tables({HOST: record})) + '\n\n[artifact_root]\npath = "fixture"\n')
        return root, record, door

    @staticmethod
    def hashed(changes: dict[str, str] | None = None) -> dict[str, dict[str, str]]:
        """What the recreator's archive capture hashes, by installed path: here the
        entrypoints the fixture's archives carry, with `changes` (path -> member
        digest) applied."""
        bindings = {f"bin/{name}": {"member_sha256": sha(STAGE2[f"bin/{name}"])}
                    for name in ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt", "targo-trust",
                                 "tippy", "trust-analyzer")}
        for path, digest in (changes or {}).items():
            bindings[path] = {"member_sha256": digest}
        return bindings

    def recreator_capture(self, root: Path, door: dict, bindings: dict, recreate=None) -> dict:
        from scripts import recreate_bootstrap
        recreate = recreate or recreate_bootstrap
        with mock.patch.object(recreate, "seed_host_ledger_module",
                               side_effect=opened(recreate.seed_host_ledger_module, door)), \
                mock.patch.object(recreate, "_run_seed_checker",
                                  return_value=mock.Mock(returncode=0, stdout=b"", stderr=b"")), \
                mock.patch.object(recreate, "_capture_seed_archive_members", return_value=([], bindings)), \
                mock.patch.object(recreate, "_capture_seed_compiler_identity",
                                  return_value={"status": "validated", "errors": []}):
            return recreate.capture_validated_seed_lineage(root, HOST)

    def test_the_recreator_binds_every_hashed_member_and_grades_below_a_release(self):
        from scripts import recreate_bootstrap as recreate
        root, record, door = self.repository(self.evidence())
        lineage = self.recreator_capture(root, door, self.hashed())
        self.assertEqual((lineage["status"], lineage["errors"]), ("validated", []))
        self.assertEqual(lineage["admission_status"], "internal-admitted")
        authority = lineage["authority"]["seed_ledger"]["host_records"]
        self.assertEqual(authority["records"], {HOST: record})
        # The validator that judged the evidence is named by its bytes, beside the helper.
        self.assertEqual(authority["fixed_point_validator_sha256"],
                         sha((ROOT / "scripts" / "seed_fixed_point.py").read_bytes()))
        self.assertEqual(authority["helper_sha256"], sha((ROOT / "scripts" / "seed_host_ledger.py").read_bytes()))
        built = {"status": "trust_from_trust",
                 "validated_seed": {**lineage, "materialization_status": "fresh-from-validated-archives"}}
        self.assertEqual(recreate._classify_receipt_status("immutable_release", built), "unpinned-root-seed-ready")
        # A member the archive capture hashed that the receipt does not have, or has other bytes for.
        for bindings, message in (
            (self.hashed({"bin/tippy": "9" * 64}),
             "pinned archive member bin/tippy differs from its fixed-point receipt row"),
            (self.hashed({"bin/tippy-driver": "9" * 64}),
             "pinned archive member bin/tippy-driver has no compiler_file row in the fixed-point receipt"),
        ):
            with self.subTest(message=message):
                refused = self.recreator_capture(root, door, bindings)
                self.assertEqual(refused["status"], "rejected")
                self.assertIn("seed admission fixed-point receipt does not bind the pinned archive members: "
                              + message, refused["errors"])
        # The shipped door is empty: the same tree is refused before any evidence is read.
        closed = self.recreator_capture(root, {}, self.hashed())
        self.assertEqual(closed["status"], "rejected")
        self.assertTrue(any("fixed-point A1" in error for error in closed["errors"]), closed["errors"])
        # And a ledger whose only record is this one pins the seed (D12 (d)).
        self.assertIn("root_disclosure", recreate.minted_seed_pin(root))

    def test_a_single_host_ledger_never_admits_the_fixed_points_archives(self):
        # The same archives, ledgered in the single-host format (no [release.hosts],
        # so no host record and no fixed-point grade), with the shipped empty door
        # and with this record's door: the recreator refuses the format for a Linux
        # host, so no release status is reached through it.
        from scripts import recreate_bootstrap as recreate
        root, record, door = self.repository(self.evidence())
        ledger = root / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
        head = ledger.read_text().partition("\n[release.hosts.")[0]
        ledger.write_text(
            head + f'\nhost_triple = "{HOST}"\n\n[release.reported_product_identities]\n'
            + "".join(f"{key} = {json.dumps(value)}\n"
                      for key, value in sorted(record["reported_product_identities"].items()))
            + '\n[artifact_root]\npath = "fixture"\n')
        for label, opened_door in (("the shipped empty door", {}), ("this record's door", door)):
            with self.subTest(label):
                lineage = self.recreator_capture(root, opened_door, self.hashed())
                self.assertEqual(lineage["status"], "rejected")
                self.assertEqual(lineage["errors"], [
                    "seed admission ledger is in the single-host format (no [release.hosts]), which admits no "
                    f"Linux host: {HOST}'s seed is admitted only through its own "
                    f'[release.hosts."{HOST}"] host record (docs/PLAN.md PKG-S6)'])
                self.assertNotIn("host_records", lineage["authority"]["seed_ledger"])
                built = {"status": "trust_from_trust",
                         "validated_seed": {**lineage, "materialization_status": "fresh-from-validated-archives"}}
                self.assertEqual(recreate._classify_receipt_status("immutable_release", built), "rejected")

    def test_the_recreators_capture_writes_no_bytecode_beside_the_validators(self):
        # The read-only `--check` and `--verify-stage-provenance` reach this capture:
        # the helper loads seed_fixed_point.py and its siblings only now, and leaves
        # no cache beside them. A scratch copy, since scripts/ may hold one already.
        from scripts import recreate_bootstrap as recreate
        root, _record, door = self.repository(self.evidence())
        scratch = self.base / "loader"
        (scratch / "scripts").mkdir(parents=True)
        (scratch / "src" / "bootstrap").mkdir(parents=True)
        for name in ("seed_host_ledger.py", "seed_fixed_point.py", "seed_root_initialization.py",
                     "mint_seed_support.py"):
            shutil.copyfile(ROOT / "scripts" / name, scratch / "scripts" / name)
        shutil.copyfile(ROOT / "src" / "bootstrap" / "stage0_identity.py",
                        scratch / "src" / "bootstrap" / "stage0_identity.py")
        with mock.patch.object(recreate, "__file__", str(scratch / "scripts" / "recreate_bootstrap.py")), \
                mock.patch.object(sys, "pycache_prefix", None), mock.patch.object(sys, "dont_write_bytecode", False):
            lineage = self.recreator_capture(root, door, self.hashed(), recreate)
            self.assertEqual((lineage["status"], lineage["errors"]), ("validated", []))
            self.assertFalse(sys.dont_write_bytecode, "the caller's setting is put back")
            self.assertEqual(sorted(path.name for path in (scratch / "scripts").iterdir()),
                             ["mint_seed_support.py", "seed_fixed_point.py", "seed_host_ledger.py",
                              "seed_root_initialization.py"])
            # Not vacuous: loaded the ordinary way, a validator is cached there.
            spec = importlib.util.spec_from_file_location("fixed_point_cache_control",
                                                          scratch / "scripts" / "seed_root_initialization.py")
            spec.loader.exec_module(importlib.util.module_from_spec(spec))
        self.assertTrue(any((scratch / "scripts" / "__pycache__").glob("seed_root_initialization.*.pyc")))

    def test_the_mint_inherits_no_anchor_from_a_fixed_point(self):
        root, _record, door = self.repository(self.evidence())
        with mock.patch.object(support, "detected_host", return_value=HOST), \
                mock.patch.object(support, "seed_host_ledger_module",
                                  side_effect=opened(support.seed_host_ledger_module, door)):
            self.assertEqual(support.committed_seed_mint(root), {"lineage_disjoint_anchor": "none"})
        with mock.patch.object(support, "detected_host", return_value=HOST), \
                self.assertRaisesRegex(support.WorkflowError, "fixed-point A1"):
            support.committed_seed_mint(root)

    def test_a_staircase_lineage_names_the_fixed_point_that_admitted_its_root(self):
        staircase = load_staircase()
        root, record, door = self.repository(self.evidence())
        with mock.patch.object(staircase, "seed_host_ledger_module",
                               side_effect=opened(staircase.seed_host_ledger_module, door)):
            admitted = staircase.pinned_root_admission(root, HOST)
        self.assertEqual(admitted, {"kind": fp.KIND, "root_disclosure": record["root_disclosure"]})
        self.assertEqual(admitted["root_disclosure"]["root"], "unpinned-host-chain")
        with self.assertRaisesRegex(staircase.Refusal, f"the pinned root's {HOST} seed host record is not "
                                    "admitted: fixed-point A1"):
            staircase.pinned_root_admission(root, HOST)


class UnchangedKindsTests(unittest.TestCase):
    def test_darwin_record_is_untouched_by_the_added_host(self):
        seed = ROOT / "bootstrap" / "trust-stage0"
        record = json.loads((seed / host_ledger.record_path(DARWIN)).read_text())
        stage0 = {}
        for line in (ROOT / "src" / "stage0").read_text().splitlines():
            key, separator, value = line.partition("=")
            if separator and not line.startswith("#"):
                stage0[key.strip()] = value.strip()
        actual, _ = host_ledger.capture_host_record(seed, stage0, DARWIN, record)
        self.assertEqual(actual, record)
        rendered = host_ledger.render_host_tables({DARWIN: record})
        ledger_text = (seed / "seed-ledger.toml").read_text()
        self.assertIn("\n".join(rendered[1:]), ledger_text)
        self.assertNotIn("evidence_sha256", "\n".join(rendered))
        self.assertNotIn("root_disclosure", "\n".join(rendered))

    def test_genesis_and_legacy_refusals_unchanged(self):
        module = host_ledger.initialization_module()
        with self.assertRaisesRegex(ValueError, "GENESIS-ROOT admission is pending"):
            module.validate_completed_producer(Path("/nonexistent"), HOST, {})
        with tempfile.TemporaryDirectory() as tmp:
            seed = Path(os.path.realpath(tmp))
            (seed / "host-proofs" / HOST).mkdir(parents=True)
            (seed / host_ledger.record_path(HOST)).write_text("{}\n")
            with self.assertRaisesRegex(ValueError, "unsupported seed host evidence kind"):
                host_ledger.capture_host_record(seed, pins(), HOST, {"schema": "trust-seed-other-v1"})
        with self.assertRaisesRegex(ValueError, "legacy admission cannot acquire native surface evidence"):
            host_ledger.check_entrypoint_bindings({"schema": host_ledger.LEGACY_SCHEMA,
                                                   "admission_kind": "legacy-bound", "entrypoint_sha256": {}}, {})
        with self.assertRaisesRegex(ValueError, "unsupported seed entrypoint evidence kind"):
            host_ledger.check_entrypoint_bindings({"schema": "trust-seed-other-v1"}, {})

    def test_the_constants_the_validator_mirrors_are_their_sources(self):
        sys.path.insert(0, str(ROOT / "scripts"))
        try:
            spec = importlib.util.spec_from_file_location("fixed_point_first_host_staircase",
                                                          ROOT / "scripts" / "seed_staircase.py")
            staircase = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(staircase)
        finally:
            sys.path.remove(str(ROOT / "scripts"))
        self.assertEqual(fp.MAX_CENSUS_GAP_S, staircase.MAX_CENSUS_GAP_S)
        self.assertEqual(fp.STAGE0_FILES, staircase.IDENTITY_FILES)
        self.assertEqual(fp.BUILD_SCOPE, host_ledger.initialization_module().DDC_SCOPE)
        self.assertEqual(tuple(fp.BUILD_WORDS), ("build", "--stage", "2", "compiler/rustc", "library/std"))
        names = fp.evidence_names(2)
        self.assertEqual(len(names), len(set(names)))
        self.assertIn("run-control-2.json", names)
        self.assertEqual(len(fp.receipt_keys(2)), len(set(fp.receipt_keys(2))))


if __name__ == "__main__":
    unittest.main()
