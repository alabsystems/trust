"""The evidence validator of a first Linux seed admitted as a fixed point.

docs/PLAN.md PKG-S6 adds aarch64-unknown-linux-gnu to a stage0 pin that Darwin
minted, admitted from Trust compilers only: the pinned compiler commit built on
the Linux host by the host chain's newest compiler (the producer), by the pinned
archives made from the producer's own build (the fixed point), and by an older
chain compiler (the cross-check), the three stage2 trees compared. The host
record kind is `fixed-point-unpinned-root` (seed_host_ledger.py
FIXED_POINT_SCHEMA); its receipt is host-proofs/<host>/SEED-FIXED-POINT and its
evidence the files under host-proofs/<host>/fixed-point/.

This module judges that evidence. It is pure Python over tracked bytes, with no
platform call, so a Darwin host runs it on the Linux record. Nothing a receipt
STATES is believed: the core digest of each tree, the files that differ, both
verdicts, which files a build by the pinned seed reproduced, the stage0 of every
build and the archive joins are computed again from the evidence files and
compared with the receipt. Each rule is a refusal (ValueError) whose message
starts with the rule's name in the design of record (A, B, C, T7).

What this validator does NOT establish, and the receipt says so in fixed
literals (B3, B4): who ran the builds (producer_custody), that the chain's root
was built without stock Rust (stock_built_ancestor), a diverse double compile or
an independent chain (double_compile_diverse, independent_chain_reproduction),
and a replay anywhere but the producing host (replayed_on).

THE ACCOUNT. Raw run records on the producing host name the invoking account
(the chain compilers' std carries /home/<account>/... paths, and the census
records them). The tracked evidence names it nowhere: `record` replaces the
account's home with `<home>` and its login with `<account>` (`normalise`) and
binds each raw file's sha256 and replacement count in the receipt. The receipt
carries the account only as two domain-separated digests (account_home_sha256,
account_login_sha256), so this validator can refuse evidence in which the
account still occurs without the running host's account and without spelling
it. A digest of a login can confirm a guess at it; it does not spell it. Because
a receipt could carry another account's digests, the validator also refuses any
personal home directory (/home/<name>, /Users/<name>) that is not `<home>`,
whatever the digests say, and holds each normalised count to the tokens its file
holds.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat
import tarfile
import tomllib
from pathlib import Path, PurePosixPath

RECEIPT_SCHEMA = "trust-seed-fixed-point-v1"
KIND = "fixed-point-unpinned-root"
RECEIPT_NAME = "SEED-FIXED-POINT"
EVIDENCE_DIR = "fixed-point"
MEMBERS_SCHEMA = "trust-seed-fixed-point-archive-members-v1"
INPUTS_SCHEMA = "trust-seed-fixed-point-inputs-v1"
CHAIN_SCHEMA = "trust-seed-fixed-point-chain-v1"
NATIVE_SCHEMA = "trust-fixed-point-linux-seed-native-outputs-v1"
STAIRCASE_SCHEMA = "trust-seed-staircase-v1"
MAX_PROOF_BYTES = 4 * 1024 * 1024
MAX_TOTAL_EVIDENCE_BYTES = 64 * 1024 * 1024
MAX_ARCHIVE_BYTES = 32 * 1024 * 1024 * 1024
SHA = re.compile(r"[0-9a-f]{64}")
COMMIT = re.compile(r"[0-9a-f]{40,64}")
DATE = re.compile(r"[0-9]{4}-[0-9]{2}-[0-9]{2}")
KEY = re.compile(r"[a-z][a-z0-9_]*")
COUNT = re.compile(r"0|[1-9][0-9]*")
WORD = re.compile(r"[a-z][a-z0-9-]*")
DOTTED = re.compile(r"[A-Za-z0-9_-]+(\.[A-Za-z0-9_-]+)+")

# Fixed literals (B2, B3, B4). Each is what the record discloses, not a result.
DISCLOSURE = (
    ("root", "unpinned-host-chain"),
    ("predecessor_pin", "none"),
    ("lineage_disjoint_anchor", "none"),
    ("double_compile_diverse", "false"),
    ("independent_chain_reproduction", "none"),
    ("producer_custody", "recorded-not-authenticated"),
    ("replayed_on", "producing-host"),
)
STOCK_ANCESTOR = "inferred-no-receipt"
# ec2b5c59f7 built the chain's root 6986546eaa; its own build config was genesis
# mode (a stock nightly under Trust names). Read from a config file and a host
# note (N2), never from a receipt, so the only admitted value is `inferred`.
STOCK_ANCESTOR_COMMIT = "ec2b5c59f7ae81dc57dac2a3346cb4c0ef9fad0d"
# What names that ancestor (N2), in fixed words: a receipt cannot say more of it.
STOCK_ANCESTOR_TOOLCHAIN = ("trust-ec2b5c59 (1.99.0-dev), the build of ec2b5c59f7 of 2026-09-01 from a checkout whose "
                            "config was genesis mode (a stock nightly under Trust names), named by the root build's "
                            "config; read from a config file and a host note, not from a receipt")
ROOT_COMMIT = "6986546eaafc7620e49331269685dbd1b2900ba3"
# The host chain, oldest first (the design's literal): the root, then the commit of
# each rung; the cross-check's stage0 is 29ebb403de's build, the producer's 6dad0d786f's.
CHAIN_COMMITS = (ROOT_COMMIT, "20565c3255adf151f9eb920e89cdf83c38f84abe", "29ebb403de7a102850d6cb10a62d5cc3baf723ed",
                 "6dad0d786fa63187a5e611b440953c94a04cbfca")
# Why bin/targo-trust and bin/ty may differ (N5), in fixed words: a hypothesis, not a finding.
NOT_REPRODUCED_HYPOTHESIS = ("LLVM LoopSimplify ordering under ThinLTO in trust_ir_build, fixed on main by 43f29371e7, "
                             "which is not an ancestor of the commit; a hypothesis, not a finding at this commit")
COHORT_MINT_HOST = "aarch64-apple-darwin"
# scripts/seed_input_closure.py OPEN_FAMILIES, by name, sorted: carried, none
# struck (scripts/tests/fixed_point_first_host_test.py holds the two equal).
OPEN_INPUT_FAMILIES = (
    "auxiliary-process-custody", "bootstrap-python-imports", "complete-dependency-resolution",
    "git-dependency-authority", "ignored-generated-source-inputs", "installed-canonical-union",
    "native-compiler-resources", "portable-proof-anchor",
)
# The root every build ran at; the tree digests hold only there (N9: two links
# of stage2 point into it). A test moves the parent.
BUILD_ROOT_PARENT = "/var/tmp/trust-seed"
BUILD_SCOPE = "<build>/<host>/stage2 after x.py build --stage 2 compiler/rustc library/std"
BUILD_DRIVER = "each build's own stage0 cargo"
FIXED_POINT_STAGE0 = "pinned-archives"
BUILD_WORDS = ("build", "--stage", "2", "compiler/rustc", "library/std")
STEP_USER = "trust-seed"
VERDICTS = ("identical", "compiler-and-std-identical")
SHARED_SOURCE_ARCHIVE = "bytes pinned by cohort_mint_host"
SHARED_HOST_LOCAL_MEMBER = "builder-config"
SHARED_BYTES = ("identical", "recompressed-differs")
MAX_CONTROLS = 3
# seed_staircase.py MAX_CENSUS_GAP_S (held equal by the test).
MAX_CENSUS_GAP_S = 120.0
# Machine code: never archive-only. An executable that is not machine code (a
# `#!` script, or a member with an execute bit) may be archive-only, and each one
# is named in the receipt's archive_only_executables, so a reviewer sees what
# ships with no build's row to compare it with.
CODE_KINDS = ("elf", "ar")
EXECUTABLE_KINDS = ("script", "executable")
INSTALLED_TOPS = ("bin/", "lib/", "libexec/")
# Where native-outputs.json rows live: what x.py built of LLVM and lld.
NATIVE_TOPS = ("llvm/", "lld/")
# C12 the tool rule, for every key of both configs, each matched by its last dotted
# part. A key whose last part starts `download-` must be false (no prebuilt compiler
# or LLVM). A Rust tool key names a file under <build_root>/stage0/. A host tool key
# names one of HOST_TOOLS (ccache may instead be false: true runs `ccache` by its
# name). Every other key that makes bootstrap, or a tool it drives, run a program,
# or link prebuilt machine code into what it builds, is an unbound key (UNBOUND_KEYS:
# every such key of src/bootstrap/src/core/config/toml/*.rs, read where bootstrap
# consumes it), and a config that sets one is refused whatever it holds (a path under
# <build_root>, a name found on PATH, a library or a directory of them, or arguments
# that name a program for a compiler or linker to run), because no record binds what
# it runs or links. An unbound key may hold only the settings UNBOUND_KEY_SETTINGS
# gives it: false for a switch (it then runs nothing), and true too where true builds
# the runtime in-tree with the bound compilers (profiler, optimized-compiler-builtins).
# A triple key (TRIPLE_KEYS: build.build, build.host, build.target) is not set: a seed
# builds for the host bootstrap detects and no other triple, whose C compiler,
# archiver and linker cc-rs would find by name on PATH, and a path there names a target
# specification whose linker rustc runs. An unbound key is matched on tables too
# (llvm.build-config is one); the Rust, host and triple keys are matched on values
# only, so a table named like one (pgo.rustc, build.tool.cargo, [build], [target]) is
# not held to their rule. No name is in two of the four lists. No string holds a `..`
# path part: a relative path then resolves under the directory it is read from (x.py
# runs in <build_root>/src), and an absolute one stays under <build_root>. A key named
# profile is the base config's top-level profile = "compiler" (PROFILES), the
# recreator's: bootstrap merges src/bootstrap/defaults/bootstrap.<profile>.toml under
# the config, a file the evidence does not hold, so the tests hold compiler's to this
# rule (tools's sets tidy-extra-checks). Only the rung config includes another file,
# and it departs from the recreator's only in the job count. default-linker (the
# linker a built compiler runs when no target linker is set), ccache (a launcher
# around every C and C++ compile) and runner (a wrapper around every test program) run
# a host program, so each is a host tool key. A key that names in-tree sources or data
# (codegen-backends, the pgo and profile-* paths), or that selects a host library the
# linker finds on its own search path (llvm-libunwind, libzstd, static-libstdcpp: the
# open native-compiler-resources family, OPEN_INPUT_FAMILIES), is not an unbound key.
RUST_TOOL_KEYS = ("rustc", "cargo", "rustdoc", "rustfmt", "cargo-clippy", "clippy", "llvm-config", "llvm-filecheck",
                  "gdb", "lldb", "nodejs", "npm", "jsondocck", "jsondoclint", "reuse")
HOST_TOOL_KEYS = ("python", "cc", "cxx", "linker", "ar", "ranlib", "default-linker", "ccache", "runner")
# What each unbound key makes the build do, for the refusal's words.
UNBOUND_KEYS = {
    # [build] (toml/build.rs)
    "yarn": "run yarn, which installs and runs tidy's and rustdoc-gui's JavaScript tools",
    "windows-rc": "run the resource compiler a Windows compiler's build script runs (RUSTC_WINDOWS_RC)",
    "sde": "run Intel's SDE emulator, which intrinsic-test runs its programs under",
    "compiletest-diff-tool": "run the diff program compiletest runs on a failed test's output",
    "tidy-extra-checks": "run the linters and formatters tidy installs and runs for each check it names",
    "android-ndk": "run the NDK clang that compiles and links for an Android target",
    "patch-binaries-for-nix": "run nix-build and patchelf, by their names, over downloaded binaries",
    "compiler-test-fixture": "load and run a retained compiler sysroot's libraries in compiler library tests",
    "optimized-compiler-builtins": "link the prebuilt compiler-rt builtins archive a path names (LLVM_COMPILER_RT_LIB) "
                                   "in place of compiler-builtins' own code, into every program stage 1 compiles and "
                                   "the std the build ships",
    # [llvm] (toml/llvm.rs)
    "clang-cl": "run the clang-cl that compiles LLVM and that bootstrap runs for its resource directory",
    "use-linker": "run the linker LLVM's build links with (LLVM_USE_LINKER)",
    "thin-lto": "run the ld.lld gcc's -fuse-ld=lld finds by its name, for LLVM's links (LLVM_ENABLE_LLD) and, when "
                "no in-tree lld is requested, the other CMake builds'",
    "offload-clang-dir": "run the clang and clang++ LLVM's offload build compiles with",
    "build-config": "run what its CMake definitions name for LLVM's build: compilers, linker, archiver or launcher",
    "cflags": "run what its C compiler arguments name for the compiler to run (-fuse-ld=, -B)",
    "cxxflags": "run what its C++ compiler arguments name for the compiler to run (-fuse-ld=, -B)",
    "ldflags": "run what its linker arguments name for the compiler driver to run (-fuse-ld=, -B)",
    # [rust] and [target.<triple>] (toml/rust.rs, toml/target.rs)
    "bootstrap-override-lld": "link Rust code with the lld found by its name on PATH (true, external) or, for each "
                              "stage-0 link, with the stage0's own rust-lld (self-contained), which a stage0 "
                              "admission does not bind (it binds trustc, cargo, targo, trustdoc, trustfmt, the driver "
                              "and the std dylib)",
    "rustflags": "run what its rustc arguments name for rustc to run (-Clinker=, -Clink-arg=-fuse-ld=)",
    "musl-root": "run the musl-gcc under it, a musl target's C compiler when none is set",
    "musl-libdir": "link the prebuilt libc and crt objects under it, copied into a musl target's self-contained "
                   "sysroot, into every program linked for that target",
    "wasi-root": "link the prebuilt wasi libc and crt objects under it, copied into a wasi target's sysroot, into "
                 "every program linked for that target",
    "qemu-rootfs": "run the emulator remote-test-client starts for a target's tests, and the system it boots",
    "profiler": "link the prebuilt profiler runtime archive a path names (LLVM_PROFILER_RT_LIB) in place of the "
                "in-tree one into profiler_builtins, which the build ships beside std and every instrumented "
                "program links",
    "llvm-zstd-pkg-config-dir": "link the prebuilt libzstd the pkg-config file under it names into rustc_llvm "
                                "(LLVM_ZSTD_PC_DIR)",
    "wasm-proc-macros": "run the C compiler and linker cc-rs finds by name on PATH for wasm32-wasip2, a target no "
                        "table names tools for",
}
# The only settings of an unbound key a config may hold.
UNBOUND_KEY_SETTINGS = {
    "patch-binaries-for-nix": (False,), "bootstrap-override-lld": (False,), "thin-lto": (False,),
    "wasm-proc-macros": (False,), "optimized-compiler-builtins": (False, True), "profiler": (False, True),
}
TRIPLE_KEYS = ("build", "host", "target")
PROFILES = ("compiler",)
HOST_TOOLS = ("/usr/bin/python3", "/usr/bin/gcc", "/usr/bin/g++", "/usr/bin/cc", "/usr/bin/c++", "/usr/bin/ar",
              "/usr/bin/ranlib")
BENIGN_DEPARTURES = ("build.jobs",)
# C12 what bootstrap.py reads. Before x.py's Rust bootstrap parses a config as TOML,
# src/bootstrap/bootstrap.py reads it line by line with a pattern (get_toml_static,
# _toml_top_level_include) and builds and runs bootstrap with what it read: among
# them build.rustc and build.cargo, build-dir, bootstrap-cache-path,
# patch-binaries-for-nix, profile, include, and the build triple's cc, cxx, linker, ar
# and ranlib. The two read a config alike only when it is written one key to a line,
# so a config breaks lines with \n alone (str.splitlines also breaks at
# CONFIG_LINE_BREAKS, which TOML reads inside a comment or a string), and each line is
# blank, a comment, a [table] header of bare keys, or `bare-key = value` with the value
# in the one spelling both read alike (`_value_form`): a non-empty "string" without
# escapes, true, false, a decimal integer, or a one-line [list] of those. A
# multi-line string or array, a trailing comment, a quoted or dotted key and an
# inline table are refused: a line reader reads each otherwise. Then every key
# bootstrap.py reads is a key the tool rule walks, in the same table, with the same
# value, and every key the walk holds is one bootstrap.py can read.
CONFIG_LINE_BREAKS = "\r\x0b\x0c\x1c\x1d\x1e\x85\u2028\u2029"
CONFIG_BLANK_LINE = re.compile(r"[ \t]*(#.*)?")
CONFIG_HEADER_LINE = re.compile(r"[ \t]*\[[A-Za-z0-9_-]+(\.[A-Za-z0-9_-]+)*\][ \t]*")
CONFIG_KEY_LINE = re.compile(r"[ \t]*([A-Za-z0-9_-]+)[ \t]*=[ \t]*(.*?)[ \t]*")
# C15 the host tools the base config names (config_host_tools: every value the C12
# walk lets through as one of HOST_TOOLS). Each is bound in inputs.json's host_tools
# by its path: path, real path, sha256, version line and when it was `measured`, at
# setup, or at record for a root set up before setup measured these. A key that
# names a role's tool must name the file bound to that role (cc, linker and
# default-linker the cc, cxx the c++, python the python); ar and ranlib
# (PATH_BOUND_TOOL_KEYS) have no measured role and are bound by their path alone.
# Any other key that names a host tool (ccache, runner, a key added later) is
# refused: no role binds what it runs. Each role a key maps to is bound (path,
# real path, sha256, version line), and a role whose path a config names is the
# file bound there.
CONFIG_TOOL_ROLES = {"cc": "cc", "linker": "cc", "default-linker": "cc", "cxx": "c++", "python": "python"}
PATH_BOUND_TOOL_KEYS = ("ar", "ranlib")
MEASURED = ("setup", "record")
CONFIG_TOOL = re.compile("(" + "|".join(re.escape(tool) for tool in HOST_TOOLS) + "):(" + "|".join(MEASURED) + ")")
# The account search (T7) is bounded: a login is at most this long and a home at
# most this many path segments deep; `normalise` refuses an account the search
# could not find again.
MAX_LOGIN = 64
MAX_HOME_SEGMENTS = 16
# The stage0 files an admission names (seed_staircase.py IDENTITY_FILES and globs).
STAGE0_FILES = ("bin/trustc", "bin/cargo", "bin/targo", "bin/trustdoc", "bin/trustfmt")
STAGE0_KEYS = {"rustc": "trustc", "cargo": "cargo", "rustdoc": "trustdoc", "rustfmt": "trustfmt"}
# C7 the jobserver (docs/OPEN_ISSUES.md BOOTSTRAP-JOBSERVER-PROBE-1). Every run was handed
# one FIFO jobserver by seed_staircase.py run --fifo-jobserver: MAKEFLAGS names it in
# GNU make 4.4's spelling, for the job count the rung config sets (build.jobs, its one
# benign departure), at a path directly under <build_root>/ledger/tmp; the run record's
# `jobserver` is that FIFO, preloaded with jobs - 1 tokens, every one of them there
# again when x.py had exited (but for the deficit SEED-TOKEN-LEAK-STAGE0-1, below,
# excuses) and the path still the FIFO's. Without it the
# cross-check's Cargo (29ebb403de) handed build scripts a pipe jobserver that their
# compiler probes could not reach, and a probe's cfg was lost or the build died. GNU
# make before 4.4 cannot read the fifo: spelling a build step hands it, so `jobserver`
# also names the make adapter first on x.py's PATH, <build_root>/ledger/pathbin/make,
# by its sha256 (one adapter for every run), and the make it ran, which is the make
# inputs.json's host_tools binds by path and sha256.
MAKEFLAGS_FIFO = re.compile(r"-j([1-9][0-9]*) --jobserver-auth=fifo:(\S+)")
# C7 SEED-TOKEN-LEAK-STAGE0-1 (docs/DECISION_QUEUE.md), the one imbalance a run may end
# with. A trustc built from a commit that does not contain d57cafb60f7 ("release jobserver
# helpers between compiler sessions") can exit holding a jobserver token
# (docs/OPEN_ISSUES.md RUSTC-FRONTEND-TOKEN-LEAK-1). A run whose FIFO held fewer tokens at the end than it was
# preloaded with is accepted only when x.py exited 0, its process census ended
# watched-exited with abandoned_children 0 (nothing outlived x.py), the FIFO's path was
# unchanged, the count is not below none, and its stage0 commit is one of
# TOKEN_LEAK_STAGE0_COMMITS: the chain commits that do not contain the fix, fixed here
# because this module runs no git (scripts/tests/fixed_point_first_host_test.py holds the
# set equal to `git merge-base --is-ancestor`). The receipt's jobserver_token_deficits names
# every such run as <label>:<given>-><returned>, recomputed from the run records. A surplus,
# or a deficit under any other stage0 (the producer's 6dad0d786f, the seed's), is refused.
TOKEN_LEAK_RULE = "SEED-TOKEN-LEAK-STAGE0-1"
TOKEN_LEAK_ISSUE = "docs/OPEN_ISSUES.md RUSTC-FRONTEND-TOKEN-LEAK-1"
TOKEN_LEAK_FIX_COMMIT = "d57cafb60f7402341e75016970c419528194feb6"  # gitleaks:allow (a git commit id, not a credential)
TOKEN_LEAK_STAGE0_COMMITS = ("6986546eaafc7620e49331269685dbd1b2900ba3", "20565c3255adf151f9eb920e89cdf83c38f84abe",
                             "29ebb403de7a102850d6cb10a62d5cc3baf723ed")
TOKEN_DEFICIT = re.compile(r"([a-z][a-z0-9-]*):(0|[1-9][0-9]*)->(0|[1-9][0-9]*)")
ACCOUNT_DOMAIN = b"trust-seed-fixed-point-account-v1"

ROLES = ("producer", "fixed-point", "cross-check")
ROLE_FIELD = {"producer": "producer", "fixed-point": "fixed_point", "cross-check": "cross_check"}
ROLE_LABEL = {"producer": "p-build", "fixed-point": "f-build", "cross-check": "s-build"}
DIST_RUNS = (("producer-dist", "p-dist"), ("producer-full", "p-full"),
             ("producer-manifest-tool", "p-manifest-tool"))
FIXED_EVIDENCE = ("base-config.toml", "rung-config.toml", "archive-members.json", "native-outputs.json",
                  "inputs.json", "chain.json")

IDENTITY_KEYS = ("schema", "kind", "host", "source_commit", "source_commit_date", "source_version")
DISCLOSURE_KEYS = (*(key for key, _ in DISCLOSURE), "stock_built_ancestor", "stock_built_ancestor_commit",
                   "stock_built_ancestor_toolchain", "root_commit", "chain_commits", "cohort_mint_host",
                   "open_input_families")
BUILD_KEYS = (
    "build_root", "build_scope", "build_driver",
    "producer_stage0_commit", "producer_stage0_compiler_sha256", "producer_stage0_driver_sha256",
    "producer_stage0_cargo_sha256",
    "cross_check_stage0_commit", "cross_check_stage0_compiler_sha256", "cross_check_stage0_driver_sha256",
    "cross_check_stage0_cargo_sha256",
    "fixed_point_stage0", "fixed_point_stage0_compiler_sha256", "fixed_point_stage0_driver_sha256",
    "fixed_point_stage0_cargo_sha256",
    "controls", "base_config_sha256", "rung_config_sha256", "config_generator_commit", "config_departures",
    "dist_components", "orchestration_commit", "orchestration_sha256", "private_home",
    "clean_lean_inputs_sha256", "cargo_home_inputs_sha256", "native_outputs_sha256", "host_c_compiler",
    "config_host_tools", "account_home_sha256", "account_login_sha256",
)
RESULT_KEYS = (
    "stage2_tree_sha256_producer", "stage2_tree_sha256_fixed_point", "stage2_tree_sha256_cross_check",
    "stage2_core_sha256", "fixed_point_verdict", "cross_check_verdict", "not_reproduced", "nondeterministic",
    "not_reproduced_cause_hypothesis", "compared_files", "rust_built_rows", "native_copied_rows",
    "archive_members", "archive_only", "archive_only_executables", "archive_bytes_total", "no_stock_evidence",
    "trap_hits",
    "process_census_flagged", "jobserver_token_deficits", "shared_source_archive", "shared_source_members",
    "shared_source_members_excluded", "shared_source_bytes",
)
# The host record's root_disclosure table: these receipt fields, verbatim.
DISCLOSED = (
    "root", "predecessor_pin", "lineage_disjoint_anchor", "double_compile_diverse",
    "independent_chain_reproduction", "producer_custody", "stock_built_ancestor", "stock_built_ancestor_commit",
    "root_commit", "producer_stage0_commit", "cross_check_stage0_commit", "fixed_point_verdict",
    "cross_check_verdict", "not_reproduced", "controls", "stage2_core_sha256", "native_outputs_sha256",
    "cohort_mint_host", "open_input_families", "replayed_on",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def json_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        require(key not in result, f"fixed-point evidence repeats the JSON key {key!r}")
        result[key] = value
    return result


def load_json(payload: bytes, what: str) -> dict:
    try:
        value = json.loads(payload.decode("utf-8"), object_pairs_hook=json_object)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError(f"fixed-point C2: {what} is not UTF-8 JSON: {error}") from error
    require(isinstance(value, dict), f"fixed-point C2: {what} is not a JSON object")
    return value


_SUPPORT = None


def mint_support():
    """scripts/mint_seed_support.py, loaded once, for its stage2 manifest rules
    (`stage2_records`, `records_sha256`, `confined_link`)."""
    global _SUPPORT
    if _SUPPORT is None:
        from importlib import util

        path = Path(__file__).with_name("mint_seed_support.py")
        if "__trust_source_loader__" in globals():
            _SUPPORT = __trust_source_loader__.module("trust_fixed_point_mint_support", path)  # noqa: F821
        else:
            spec = util.spec_from_file_location("trust_fixed_point_mint_support", path)
            require(spec is not None and spec.loader is not None, "missing compiler tree validator")
            module = util.module_from_spec(spec)
            spec.loader.exec_module(module)
            _SUPPORT = module
    return _SUPPORT


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def records_sha256(rows: list) -> str:
    return mint_support().records_sha256(rows)


# ---------------------------------------------------------------------------
# the account (decision T7): normalisation at record time, the search here


def account_digest(kind: str, value: str) -> str:
    """The receipt's account_home_sha256 / account_login_sha256 of a value."""
    return sha256(ACCOUNT_DOMAIN + b"\0" + kind.encode("ascii") + b"\0" + value.encode("utf-8"))


LOGIN_FORM = re.compile(rf"[A-Za-z0-9_.-]{{1,{MAX_LOGIN}}}")
HOME_FORM = re.compile(r"(/[^\s\"'<>,;:=\[\]{}()\\|`/]+)+")


def login_pattern(login: str) -> re.Pattern:
    """Where a text names the login: where it starts a word (no letter or digit
    before it) and is not continued by a letter. So `<login>_x`, `<login>2`,
    `<login>-x`, `<login>.x` and `/<login>/` all name it. After a letter or a digit
    it is part of another word: matching there would refuse every word that merely
    contains a short login (`dan` in `redundant`)."""
    return re.compile(rf"(?<![A-Za-z0-9]){re.escape(login)}(?![A-Za-z])")


def account_problem(account: tuple[str, str]) -> str | None:
    """Why the T7 search (`account_found`) could not find this account again, or None."""
    home, login = account
    if LOGIN_FORM.fullmatch(login) is None:
        return (f"the login is not 1 to {MAX_LOGIN} of the characters A-Z a-z 0-9 _ . -, so the validator's "
                "search for it, which knows it only by a digest, cannot find it")
    if HOME_FORM.fullmatch(home) is None or home.count("/") > MAX_HOME_SEGMENTS:
        return (f"the home is not an absolute path of at most {MAX_HOME_SEGMENTS} segments without spaces, quotes "
                "or separators, so the validator's search for it cannot find it")
    return None


def normalise(payload: bytes, account: tuple[str, str]) -> tuple[bytes, int]:
    """The tracked copy of a raw evidence file: every occurrence of the account's
    home replaced by `<home>` and of its login (as `login_pattern` finds it) by
    `<account>`, the longer first, in keys, values and link targets alike; and how
    many were replaced. A file that is not UTF-8 is refused (evidence is text), and
    so is an account `account_found` could not search for."""
    home, login = account
    problem = account_problem(account)
    if problem:
        raise ValueError(f"fixed-point T7: the invoking account cannot be recorded: {problem}")
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"fixed-point T7: an evidence file is not UTF-8 text: {error}") from error
    steps = []
    if len(home) > 1:
        steps.append((len(home), lambda value: (value.replace(home, "<home>"), value.count(home))))
    if login:
        pattern = login_pattern(login)
        steps.append((len(login), lambda value: pattern.subn("<account>", value)))
    count = 0
    for _, step in sorted(steps, key=lambda item: -item[0]):
        text, replaced = step(text)
        count += replaced
    return text.encode("utf-8"), count


HOME_RUN = re.compile(r"/[^\s\"'<>,;:=\[\]{}()\\|`]*")
LOGIN_RUN = re.compile(r"[A-Za-z0-9_.-]+")


def _home_candidates(text: str) -> set[str]:
    """Every run of 1 to MAX_HOME_SEGMENTS whole segments of every path-like run
    (from a slash to the next slash or the run's end): linear in the slashes."""
    found: set[str] = set()
    for run in set(HOME_RUN.findall(text)):
        slashes = [index for index, char in enumerate(run) if char == "/"]
        ends = [*slashes[1:], len(run)]
        for number, start in enumerate(slashes):
            for end in ends[number:number + MAX_HOME_SEGMENTS]:
                if end > start + 1:
                    found.add(run[start:end])
    return found


def _login_candidates(text: str) -> set[str]:
    """Every substring of at most MAX_LOGIN characters that `login_pattern`
    could match: it starts where no letter or digit precedes it and ends where no
    letter follows it."""
    found: set[str] = set()
    for run in set(LOGIN_RUN.findall(text)):
        starts = [0, *(index for index in range(1, len(run)) if not run[index - 1].isascii()
                       or not run[index - 1].isalnum())]
        ends = [*(index for index in range(1, len(run)) if not (run[index].isascii() and run[index].isalpha())),
                len(run)]
        for start in starts:
            for end in ends:
                if start < end <= start + MAX_LOGIN:
                    found.add(run[start:end])
    return found


def _strings(value: object) -> list[str]:
    if isinstance(value, dict):
        return [item for key, inner in value.items() for item in (str(key), *_strings(inner))]
    if isinstance(value, list):
        return [item for inner in value for item in _strings(inner)]
    return [value] if isinstance(value, str) else []


def decoded_texts(payload: bytes, name: str) -> list[str]:
    """The text of a tracked file, and for JSON and TOML also its decoded strings
    and keys (an escape spells a home or login the raw bytes do not)."""
    texts = [payload.decode("utf-8", "replace")]
    try:
        if name.endswith(".json"):
            texts.append("\n".join(_strings(json.loads(texts[0]))))
        elif name.endswith(".toml"):
            texts.append("\n".join(_strings(tomllib.loads(texts[0]))))
    except (ValueError, tomllib.TOMLDecodeError):
        pass
    return texts


def account_found(payload: bytes, home_sha256: str, login_sha256: str, *, name: str) -> str | None:
    """'home' or 'login' when `payload` (the tracked file `name`) names the account
    the two digests stand for, as text or in its decoded strings and keys, else None."""
    texts = decoded_texts(payload, name)
    if any(account_digest("home", item) == home_sha256 for text in texts for item in _home_candidates(text)):
        return "home"
    if any(account_digest("login", item) == login_sha256 for text in texts for item in _login_candidates(text)):
        return "login"
    return None


# A path that starts a home directory: /home/<seg> or /Users/<seg>, where nothing
# that continues a path comes before it. `<account>` is the only admitted <seg>.
PERSONAL_HOME = re.compile(r"(?<![A-Za-z0-9._~+@%-])/(?:home|Users)/(?!<account>(?![^/\s\"']))[^/\s\"'\\]")


def personal_home_found(payload: bytes, name: str) -> bool:
    """Whether the tracked file names any personal home directory but `<home>`,
    whatever the receipt's digests say: a receipt carrying another account's
    digests cannot make a home it never replaced pass (T7)."""
    return any(PERSONAL_HOME.search(text) for text in decoded_texts(payload, name))


# ---------------------------------------------------------------------------
# the receipt


def evidence_names(controls: int) -> tuple[str, ...]:
    """Every evidence file of a record with `controls` control builds, in order."""
    numbered = tuple(f"control-{number}" for number in range(1, controls + 1))
    return (*(f"stage2-{role}.json" for role in (*ROLES, *numbered)),
            *(f"run-{role}.json" for role in ("producer", *(name for name, _ in DIST_RUNS), "fixed-point",
                                              "cross-check", *numbered)),
            *(f"admission-{role}.json" for role in ROLES), *FIXED_EVIDENCE)


def evidence_field(name: str) -> str:
    return "evidence_" + re.sub(r"[-.]", "_", name.rsplit(".", 1)[0])


def receipt_keys(controls: int) -> tuple[str, ...]:
    evidence = tuple(f"{evidence_field(name)}_{suffix}" for name in evidence_names(controls)
                     for suffix in ("sha256", "raw_sha256", "normalised_count"))
    return (*IDENTITY_KEYS, *DISCLOSURE_KEYS, *BUILD_KEYS, *evidence, *RESULT_KEYS)


class Receipt:
    """A parsed SEED-FIXED-POINT: its fields, its compiler_file rows (path ->
    sha256) and its compiler_link rows (path -> target)."""

    def __init__(self, fields: dict[str, str], files: dict[str, str], links: dict[str, str]):
        self.fields, self.files, self.links = fields, files, links


def confined_path(path: str) -> bool:
    return bool(path) and not path.startswith("/") and all(part not in ("", ".", "..") for part in path.split("/"))


def parse_receipt(payload: bytes) -> Receipt:
    """B1: the strict parser. Unique keys, one row per stage2 path, every row
    inside stage2, at least one compiler_file row."""
    require(isinstance(payload, bytes) and 0 < len(payload) <= MAX_PROOF_BYTES,
            "fixed-point B1: the receipt is empty or over its 4 MiB bound")
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"fixed-point B1: the receipt is not UTF-8: {error}") from error
    require("\r" not in text and "\0" not in text, "fixed-point B1: the receipt carries a CR or NUL byte")
    fields: dict[str, str] = {}
    files: dict[str, str] = {}
    links: dict[str, str] = {}
    for number, line in enumerate(text.split("\n"), 1):
        if not line or line.startswith("#"):
            continue
        key, separator, value = line.partition("=")
        require(bool(separator) and KEY.fullmatch(key) is not None and value != "",
                f"fixed-point B1: receipt line {number} is not a key=value line")
        if key in ("compiler_file", "compiler_link"):
            identity, space, path = value.partition(" ")
            require(bool(space) and confined_path(path),
                    f"fixed-point B1: receipt line {number} names a path that escapes stage2: {path!r}")
            require(path not in files and path not in links,
                    f"fixed-point B1: receipt line {number} repeats the compared path {path!r}")
            if key == "compiler_file":
                require(SHA.fullmatch(identity) is not None,
                        f"fixed-point B1: receipt line {number} has no exact sha256 for {path!r}")
                files[path] = identity
            else:
                require(bool(identity), f"fixed-point B1: receipt line {number} has no link target")
                links[path] = identity
            continue
        require(key not in fields, f"fixed-point B1: the receipt repeats the field {key}")
        fields[key] = value
    require(bool(files), "fixed-point B1: the receipt has no compiler_file rows")
    return Receipt(fields, files, links)


def render_receipt(fields: dict[str, str], files: dict[str, str], links: dict[str, str]) -> bytes:
    """SEED-FIXED-POINT bytes: the fields in receipt_keys order, then every row."""
    controls = fields.get("controls", "")
    require(controls in tuple(str(number) for number in range(MAX_CONTROLS + 1)),
            f"fixed-point B1: controls {controls!r} is not 0 to {MAX_CONTROLS}")
    keys = receipt_keys(int(controls))
    require(set(fields) == set(keys), "fixed-point B1: the fields to render are not the receipt's field set: "
            f"missing {sorted(set(keys) - set(fields))[:3]}, extra {sorted(set(fields) - set(keys))[:3]}")
    for key, value in fields.items():
        require(isinstance(value, str) and value != "" and "\n" not in value and "\r" not in value,
                f"fixed-point B1: the field {key} is not a one-line value")
    lines = [
        "# SEED-FIXED-POINT: a first Linux seed admitted as a fixed point of an unpinned host chain",
        "# (scripts/fixed_point_linux_seed.py record; validated by scripts/seed_fixed_point.py).",
        "# compiler_file rows are every regular file of the producer's stage2; compiler_link rows its",
        "# links that stay inside stage2. The commits name the dev history.",
        *(f"{key}={fields[key]}" for key in keys),
        *(f"compiler_file={files[path]} {path}" for path in sorted(files)),
        *(f"compiler_link={links[path]} {path}" for path in sorted(links)),
        "",
    ]
    return "\n".join(lines).encode("utf-8")


def member_rows(receipt_bytes: bytes) -> dict[str, str]:
    """The receipt's compiler_file rows by path: what the recreator binds the
    archive members it hashes on every capture to."""
    return dict(parse_receipt(receipt_bytes).files)


def split_list(value: str) -> list[str]:
    return [] if value == "none" else value.split(",")


def join_list(items) -> str:
    items = sorted(items)
    return ",".join(items) if items else "none"


def evidence_sha256(fields: dict[str, str]) -> str:
    """One digest of every evidence file's digest, by name (the host record's
    evidence_sha256)."""
    names = evidence_names(int(fields["controls"]))
    return sha256("".join(f"{name} {fields[evidence_field(name) + '_sha256']}\n" for name in sorted(names))
                  .encode("utf-8"))


def root_disclosure(fields: dict[str, str]) -> dict[str, str]:
    return {key: fields[key] for key in DISCLOSED}


def build_root(fields: dict[str, str]) -> str:
    return f"{BUILD_ROOT_PARENT}/{fields['source_commit'][:10]}"


def require_canonical(receipt_bytes: bytes, receipt: Receipt) -> None:
    """B1: the receipt is exactly `render_receipt` of its own fields and rows, so
    it says nothing its fields do not (no free comment) and has one form."""
    try:
        canonical = render_receipt(receipt.fields, receipt.files, receipt.links)
    except ValueError as error:
        raise ValueError(f"fixed-point B1: the receipt cannot be rendered from its own fields: {error}") from error
    require(receipt_bytes == canonical, "fixed-point B1: the receipt is not the canonical rendering of its own "
            "fields and rows (seed_fixed_point.render_receipt): a comment, an extra, a moved or a reordered line "
            "is refused")


def validate_receipt(receipt: Receipt, pins: dict[str, str], host: str, *, allowed: tuple[str, ...],
                     components: tuple[str, ...]) -> None:
    """B2-B7 and the receipt's own form: every field there, no other, each well
    formed; the literals the record discloses unchanged. `allowed` are the files a
    build by the pinned seed may fail to reproduce and `components` the x.py dist
    components of a seed cohort (seed_host_ledger.COMPONENTS)."""
    fields = receipt.fields
    mint = sorted(key for key in fields if key.startswith(("pinned_seed_", "ddc_")) or key == "self_host_proof")
    require(not mint, f"fixed-point B5: the receipt uses the mint vocabulary ({', '.join(mint[:3])}); a fixed "
            "point has no pinned predecessor and no double compile")
    controls = fields.get("controls", "")
    require(COUNT.fullmatch(controls) is not None and int(controls) <= MAX_CONTROLS,
            f"fixed-point C5: controls = {controls!r}: at most {MAX_CONTROLS} control builds are admitted")
    keys = receipt_keys(int(controls))
    missing = [key for key in keys if key not in fields]
    normalisation = [key for key in missing if key.endswith(("_raw_sha256", "_normalised_count"))
                     or key.startswith("account_")]
    require(not normalisation, "fixed-point T7: the receipt lacks its normalisation fields "
            f"({', '.join(normalisation[:3])}{', ...' if len(normalisation) > 3 else ''}): the tracked evidence is "
            "not bound to the raw records it was made from")
    require(not missing, f"fixed-point B1: the receipt lacks {', '.join(missing[:4])}"
            f"{', ...' if len(missing) > 4 else ''}")
    extra = sorted(set(fields) - set(keys))
    require(not extra, f"fixed-point B1: the receipt has fields this kind does not define: {', '.join(extra[:4])}")
    # B2 identity and the build's fixed literals.
    version = pins.get("compiler_version", "")
    require(version.endswith("-trust"), "fixed-point B2: the pinned compiler version is not Trust-owned")
    expected = {"schema": RECEIPT_SCHEMA, "kind": KIND, "host": host,
                "source_commit": pins.get("compiler_git_commit_hash"), "source_commit_date": pins.get("compiler_date"),
                "source_version": version[:-len("-trust")], "build_scope": BUILD_SCOPE, "build_driver": BUILD_DRIVER,
                "fixed_point_stage0": FIXED_POINT_STAGE0}
    for key, value in expected.items():
        require(fields[key] == value, f"fixed-point B2: {key} = {fields[key]!r}, and the pins and this kind "
                f"say {value!r}")
    root = build_root(fields)
    require(fields["build_root"] == root, f"fixed-point B2: build_root = {fields['build_root']!r}, and every "
            f"build of this commit ran at {root!r} (the tree digests hold only there)")
    require(fields["private_home"] == f"{root}/home", f"fixed-point B2: private_home = {fields['private_home']!r}, "
            f"not {root}/home")
    # B3 disclosure literals.
    for key, value in DISCLOSURE:
        require(fields[key] == value, f"fixed-point B3: {key} = {fields[key]!r}; this kind discloses exactly "
                f"{value!r}, and nothing may claim more")
    require(fields["cohort_mint_host"] == COHORT_MINT_HOST,
            f"fixed-point B3: cohort_mint_host = {fields['cohort_mint_host']!r}, not {COHORT_MINT_HOST}")
    require(fields["root_commit"] == ROOT_COMMIT, f"fixed-point B3: root_commit = {fields['root_commit']!r}, not "
            f"the chain's root {ROOT_COMMIT}")
    # B4 the stock-built ancestor: inferred, never recorded and never denied.
    require(fields["stock_built_ancestor"] == STOCK_ANCESTOR,
            f"fixed-point B4: stock_built_ancestor = {fields['stock_built_ancestor']!r}; the only admitted value "
            f"is {STOCK_ANCESTOR!r} (it is read from a config file and a host note, not a receipt)")
    require(fields["stock_built_ancestor_commit"] == STOCK_ANCESTOR_COMMIT,
            f"fixed-point B4: stock_built_ancestor_commit = {fields['stock_built_ancestor_commit']!r}, not "
            f"{STOCK_ANCESTOR_COMMIT}")
    require(fields["stock_built_ancestor_toolchain"] == STOCK_ANCESTOR_TOOLCHAIN,
            f"fixed-point B4: stock_built_ancestor_toolchain = {fields['stock_built_ancestor_toolchain']!r:.80}; it "
            f"is the fixed words {STOCK_ANCESTOR_TOOLCHAIN[:40]!r}..., and a receipt cannot say more of the ancestor")
    # B6 the open input families: all eight, none struck.
    require(fields["open_input_families"] == ",".join(OPEN_INPUT_FAMILIES),
            f"fixed-point B6: open_input_families is not exactly the eight carried families "
            f"({','.join(OPEN_INPUT_FAMILIES)})")
    # B7 digests and commits.
    for key in keys:
        if key.endswith("_sha256"):
            require(SHA.fullmatch(fields[key]) is not None, f"fixed-point B7: {key} is not a sha256")
    for key in ("source_commit", "producer_stage0_commit", "cross_check_stage0_commit", "orchestration_commit",
                "config_generator_commit"):
        require(COMMIT.fullmatch(fields[key]) is not None, f"fixed-point B7: {key} is not a commit")
    commits = (fields["producer_stage0_commit"], fields["cross_check_stage0_commit"], fields["source_commit"])
    require(len(set(commits)) == 3, "fixed-point B7: the producer's stage0, the cross-check's stage0 and the "
            "source are not three different commits")
    chain = fields["chain_commits"].split(",")
    require(all(COMMIT.fullmatch(commit) for commit in chain) and len(set(chain)) == len(chain),
            "fixed-point B7: chain_commits is not a list of distinct commits")
    require(chain[0] == fields["root_commit"] and chain[-1] == fields["producer_stage0_commit"]
            and fields["cross_check_stage0_commit"] in chain,
            "fixed-point B7: chain_commits does not start at the root, end at the producer's stage0 commit and "
            "hold the cross-check's")
    require(tuple(chain) == CHAIN_COMMITS, "fixed-point B3: chain_commits is not the host chain this kind admits "
            f"({', '.join(commit[:10] for commit in CHAIN_COMMITS)}, oldest first)")
    require(fields["config_generator_commit"] == fields["source_commit"],
            "fixed-point B7: the base config was not written by the source commit's own writer")
    # The result fields' form (their values are recomputed by capture_evidence).
    for key in ("compared_files", "rust_built_rows", "native_copied_rows", "archive_members", "archive_bytes_total",
                *(f"{evidence_field(name)}_normalised_count" for name in evidence_names(int(controls)))):
        require(COUNT.fullmatch(fields[key]) is not None, f"fixed-point B7: {key} is not a count")
    for name in evidence_names(int(controls)):
        field = evidence_field(name)
        if fields[f"{field}_normalised_count"] == "0":
            require(fields[f"{field}_raw_sha256"] == fields[f"{field}_sha256"],
                    f"fixed-point T7: {name} had nothing replaced and is not its raw record's bytes")
        else:
            require(fields[f"{field}_raw_sha256"] != fields[f"{field}_sha256"],
                    f"fixed-point T7: {name} had replacements and is its raw record's bytes")
    for key in ("fixed_point_verdict", "cross_check_verdict"):
        require(fields[key] in VERDICTS, f"fixed-point C6: {key} = {fields[key]!r} is not one of {VERDICTS}")
    for key, value in (("no_stock_evidence", "pass"), ("trap_hits", "0"), ("process_census_flagged", "0"),
                       ("shared_source_archive", SHARED_SOURCE_ARCHIVE), ("shared_source_members", "identical")):
        require(fields[key] == value, f"fixed-point B2: {key} = {fields[key]!r}, not {value!r}")
    deficits = split_list(fields["jobserver_token_deficits"])
    shaped = [TOKEN_DEFICIT.fullmatch(item) for item in deficits]
    require(deficits == sorted(set(deficits))
            and all(match is not None and int(match.group(2)) > int(match.group(3)) for match in shaped),
            f"fixed-point B7: jobserver_token_deficits = {fields['jobserver_token_deficits']!r:.80} is not 'none' or a "
            f"sorted list of <label>:<given>-><returned>, each with fewer returned ({TOKEN_LEAK_RULE})")
    require(fields["shared_source_bytes"] in SHARED_BYTES,
            f"fixed-point C13: shared_source_bytes = {fields['shared_source_bytes']!r} is not one of {SHARED_BYTES}")
    require(fields["shared_source_members_excluded"] in ("none", SHARED_HOST_LOCAL_MEMBER),
            "fixed-point C13: shared_source_members_excluded names a member other than the package-root "
            f"{SHARED_HOST_LOCAL_MEMBER}")
    for key, universe in (("not_reproduced", allowed), ("nondeterministic", allowed)):
        items = split_list(fields[key])
        require(items == sorted(set(items)) and all(item in universe for item in items),
                f"fixed-point C5: {key} = {fields[key]!r} is not a sorted list of {', '.join(universe)}")
    for key in ("archive_only", "archive_only_executables", "config_departures"):
        items = split_list(fields[key])
        require(items == sorted(set(items)) and all(items), f"fixed-point B7: {key} is not a sorted list")
    require(set(split_list(fields["archive_only_executables"])) <= set(split_list(fields["archive_only"])),
            "fixed-point C13: archive_only_executables names a member archive_only does not")
    require(all(DOTTED.fullmatch(item) for item in split_list(fields["config_departures"])),
            "fixed-point C12: config_departures is not a list of dotted config keys")
    if fields["not_reproduced"] == "none":
        require(fields["not_reproduced_cause_hypothesis"] == "none",
                "fixed-point C5: a hypothesis is given for files that were all reproduced")
    else:
        require(fields["not_reproduced_cause_hypothesis"] != "none",
                "fixed-point C5: not_reproduced lists files and no cause hypothesis is on record")
        require(fields["not_reproduced_cause_hypothesis"] == NOT_REPRODUCED_HYPOTHESIS,
                "fixed-point C5: not_reproduced_cause_hypothesis is not the fixed words of the one hypothesis on "
                f"record ({NOT_REPRODUCED_HYPOTHESIS[:40]!r}...); a receipt cannot claim more of the cause")
    words = fields["dist_components"].split(" ")
    require(all(WORD.fullmatch(word) for word in words) and len(set(words)) == len(words),
            "fixed-point C7: dist_components is not a list of x.py component words")
    require(sorted(words) == sorted(components), f"fixed-point C7: dist_components = "
            f"{fields['dist_components']!r:.80} is not exactly the seed cohort's components "
            f"({', '.join(sorted(components))}); the dist that made the pinned archives names every one")
    host_c = fields["host_c_compiler"].split(" ", 1)
    require(len(host_c) == 2 and SHA.fullmatch(host_c[0]) is not None and host_c[1].strip(),
            "fixed-point C15: host_c_compiler is not '<sha256> <version line>'")
    named = split_list(fields["config_host_tools"])
    require(named == sorted(set(named)) and all(CONFIG_TOOL.fullmatch(item) for item in named)
            and len({item.rsplit(":", 1)[0] for item in named}) == len(named),
            "fixed-point B7: config_host_tools is not a sorted list of '<host tool>:<setup|record>', one row a tool")
    require(int(fields["compared_files"]) == len(receipt.files),
            f"fixed-point C3: compared_files = {fields['compared_files']}, and the receipt has "
            f"{len(receipt.files)} compiler_file rows")


# ---------------------------------------------------------------------------
# what the evidence gives, computed (shared by `record` and the validator)


def checked_manifest(document: dict, host: str, what: str) -> dict:
    """C2: a trust-stage2-tree-v1 manifest whose digest is its records' and which
    holds a compiler, a driver and std."""
    support = mint_support()
    try:
        records = support.stage2_records(document, what)
    except support.WorkflowError as error:
        raise ValueError(f"fixed-point C2: {error}") from error
    files = {row["path"]: row["sha256"] for row in records if row["kind"] == "file"}
    require("bin/trustc" in files and any(re.fullmatch(r"lib/librustc_driver-[^/]+\.so", path) for path in files)
            and any(re.fullmatch(rf"lib/rustlib/{re.escape(host)}/lib/libstd-[^/]+\.rlib", path) for path in files),
            f"fixed-point C2: {what} has no compiler, driver or std")
    return document


def file_rows(manifest: dict) -> dict[str, str]:
    return {row["path"]: row["sha256"] for row in manifest["records"] if row["kind"] == "file"}


def link_rows(manifest: dict) -> dict[str, str]:
    support = mint_support()
    return {row["path"]: row["target"] for row in manifest["records"]
            if row["kind"] == "symlink" and support.confined_link(row)}


def core_sha256(manifest: dict, allowed: tuple[str, ...]) -> str:
    """The tree digest without the files a build by the pinned seed may fail to reproduce."""
    return records_sha256([row for row in manifest["records"] if row["path"] not in allowed])


def differing_paths(first: dict, second: dict) -> list[str]:
    left = {row["path"]: row for row in first["records"]}
    right = {row["path"]: row for row in second["records"]}
    return sorted(path for path in left.keys() | right.keys() if left.get(path) != right.get(path))


def verdict(producer: dict, other: dict) -> str:
    return "identical" if producer["records"] == other["records"] else "compiler-and-std-identical"


def reproduction(producer: dict, seeds: list[dict], allowed: tuple[str, ...]) -> tuple[list[str], list[str]]:
    """(not reproduced, nondeterministic) over the allowed files, from the
    producer's tree and every tree a build by the pinned seed made (C5). A file
    is reproduced only when a seed build gave the producer's bytes; one that is
    not is admitted only when the seed builds disagree among themselves. A file
    every seed build agrees on, against the producer, follows the stage0: refused.
    A file one of these trees has and another lacks is refused too: a build that
    did not make the file is not a second digest of it."""
    rows = {row["path"]: row for row in producer["records"]}
    seen = [{row["path"]: row for row in tree["records"]} for tree in seeds]
    not_reproduced, nondeterministic = [], []
    for path in allowed:
        mine = rows.get(path)
        present = {mine is not None, *(tree.get(path) is not None for tree in seen)}
        require(len(present) == 1, f"fixed-point C5: {path} is in some of the producer's and the pinned seed's "
                f"trees ({len(seeds)} of the seed's) and not in others: a build that did not make it gives no "
                "digest to compare, so neither 'reproduced' nor 'nondeterministic' can be judged")
        if mine is None:
            continue
        theirs = [json.dumps(tree.get(path), sort_keys=True) for tree in seen]
        if len(set(theirs)) > 1:
            nondeterministic.append(path)
        if json.dumps(mine, sort_keys=True) in theirs:
            continue
        require(len(set(theirs)) > 1,
                f"fixed-point C5: {path} has one digest in every build by the pinned seed ({len(seeds)}) and "
                "another in the producer's: the difference follows the stage0, and no record is admitted")
        not_reproduced.append(path)
    return sorted(not_reproduced), sorted(nondeterministic)


def token_deficit(run: dict) -> tuple[int, int] | None:
    """C7: (given, returned) when a run's FIFO jobserver held fewer tokens when x.py had
    exited than it was preloaded with, both whole numbers; None otherwise."""
    held = run.get("jobserver") if isinstance(run.get("jobserver"), dict) else {}
    given, returned = held.get("tokens"), held.get("tokens_at_end")
    if type(given) is int and type(returned) is int and returned < given:
        return given, returned
    return None


def token_deficits(runs) -> list[str]:
    """C7 SEED-TOKEN-LEAK-STAGE0-1: <label>:<given>-><returned> of every run whose
    jobserver came back short, sorted (the receipt's jobserver_token_deficits)."""
    found = []
    for run in runs:
        deficit = token_deficit(run)
        if deficit is not None:
            found.append(f"{run.get('label')}:{deficit[0]}->{deficit[1]}")
    return sorted(found)


def stage0_lacks_token_fix(commit: object) -> tuple[bool, str]:
    """SEED-TOKEN-LEAK-STAGE0-1's stage0 condition, from the fixed TOKEN_LEAK_STAGE0_COMMITS
    (this module runs no git): (whether it holds, what was decided)."""
    if isinstance(commit, str) and commit in TOKEN_LEAK_STAGE0_COMMITS:
        return True, f"its stage0 {commit[:10]} is a chain commit that does not contain {TOKEN_LEAK_FIX_COMMIT[:10]}"
    return False, (f"its stage0 commit {str(commit)[:10]!r} is not one of the chain commits that do not contain "
                   f"{TOKEN_LEAK_FIX_COMMIT[:10]} ({', '.join(chain[:10] for chain in TOKEN_LEAK_STAGE0_COMMITS)})")


def token_deficit_unexcused(run: dict, stage0_lacks_fix: bool, stage0: str) -> list[str]:
    """SEED-TOKEN-LEAK-STAGE0-1: the conditions a run whose jobserver came back short
    does not meet (empty: the deficit is excused). The stage0 condition is decided by
    the caller, `stage0` saying what was decided: here from TOKEN_LEAK_STAGE0_COMMITS,
    in the first-seed driver from the run's admission and git."""
    held = run.get("jobserver") if isinstance(run.get("jobserver"), dict) else {}
    census = run.get("process_census") if isinstance(run.get("process_census"), dict) else {}
    unmet = []
    if not _same(run.get("rc"), 0):
        unmet.append(f"x.py exited {run.get('rc')!r}, not 0")
    if census.get("ended") != "watched-exited" or not _same(census.get("abandoned_children"), 0):
        unmet.append(f"its process census ended {census.get('ended')!r} with abandoned_children "
                     f"{census.get('abandoned_children')!r}, not watched-exited with 0, so a process may have "
                     "outlived x.py holding the token")
    if held.get("path_unchanged") is not True:
        unmet.append("its jobserver's path did not name the FIFO when x.py had exited")
    returned = held.get("tokens_at_end")
    if type(returned) is not int or returned < 0:
        unmet.append(f"it counted {returned!r} token(s) at the end, not none or more")
    if not stage0_lacks_fix:
        unmet.append(stage0)
    return unmet


def token_deficit_refusal(given: int, returned: int, unmet: list[str]) -> str:
    """The words of a deficit SEED-TOKEN-LEAK-STAGE0-1 does not excuse."""
    return (f"{TOKEN_LEAK_RULE} ({TOKEN_LEAK_ISSUE}) does not excuse its jobserver's {returned} of the {given} "
            f"token(s) back: {'; '.join(unmet)}")


def _config(payload: bytes, what: str) -> dict:
    try:
        return tomllib.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        raise ValueError(f"fixed-point C12: {what} is not TOML: {error}") from error


def _flat(table: dict, prefix: str = "") -> list[tuple[str, object]]:
    """Every leaf of a TOML document as (dotted key, value)."""
    out = []
    for key, value in table.items():
        if isinstance(value, dict):
            out += _flat(value, f"{prefix}{key}.")
        else:
            out.append((f"{prefix}{key}", value))
    return out


def _keys(table: dict, prefix: str = "") -> list[tuple[str, object]]:
    """Every key of a TOML document, a table's own key included, as (dotted key,
    value), in document order and a table's key before the keys under it."""
    out = []
    for key, value in table.items():
        out.append((f"{prefix}{key}", value))
        if isinstance(value, dict):
            out += _keys(value, f"{prefix}{key}.")
    return out


def _value_form(value: object) -> str | None:
    """How a config value is spelled where bootstrap.py's line reader reads it as
    TOML does (C12 what bootstrap.py reads), or None for a value no spelling of
    which both read alike: an empty string (the reader reads its two quotes), an
    inline table, a float, a date, a nested list."""
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return f'"{value}"' if value and '"' not in value and "\\" not in value else None
    if isinstance(value, list):
        items = [None if isinstance(item, list) else _value_form(item) for item in value]
        return None if None in items else "[" + ", ".join(items) + "]"
    return None


def check_config_lines(payload: bytes, what: str) -> None:
    """C12 what bootstrap.py reads: one config, already read as TOML, is written one
    key to a line in the spelling bootstrap.py's line reader reads as TOML does."""
    text = payload.decode("utf-8")
    for char in CONFIG_LINE_BREAKS:
        require(char not in text, f"fixed-point C12: {what} holds {char!r}, which bootstrap.py's line reader "
                "(str.splitlines) reads as a line break and TOML does not: a config breaks lines with \\n alone")
    for number, line in enumerate(text.split("\n"), 1):
        if CONFIG_BLANK_LINE.fullmatch(line) or CONFIG_HEADER_LINE.fullmatch(line):
            continue
        match = CONFIG_KEY_LINE.fullmatch(line)
        form = None
        if match is not None:
            try:
                form = _value_form(tomllib.loads(line)[match.group(1)])
            except tomllib.TOMLDecodeError:
                form = None
        require(form is not None and form == match.group(2),
                f"fixed-point C12: {what} line {number} is {line[:120]!r}, which bootstrap.py's line reader "
                "(src/bootstrap/bootstrap.py get_toml_static) does not read as TOML does: a config is written one "
                "key to a line, each line blank, a comment, a [table] header of bare keys, or bare-key = a "
                "non-empty \"string\" without escapes, true, false, a decimal integer or a one-line [list] of those")


def _settings_words(settings: tuple) -> str:
    if not settings:
        return "does not set it"
    return f"sets it only to {' or '.join(str(setting).lower() for setting in settings)}"


def check_config_tools(document: dict, root: str, what: str) -> None:
    """C12 the tool rule over every key of one config: no download, every Rust
    tool under <root>/stage0, every host tool one of HOST_TOOLS, no unbound key but
    at a setting UNBOUND_KEY_SETTINGS admits, no triple key, no profile but the
    top-level compiler, no tool by a relative name, no `..` path part, and no other
    absolute path outside <root>."""
    for key, value in _keys(document):
        last = key.rsplit(".", 1)[-1]
        if last in UNBOUND_KEYS:
            settings = UNBOUND_KEY_SETTINGS.get(last, ())
            require(type(value) is bool and value in settings,
                    f"fixed-point C12: {what} sets {key} = {value!r}, which makes the build {UNBOUND_KEYS[last]}, "
                    f"and no record binds that: a config {_settings_words(settings)}")
        if isinstance(value, dict):
            continue
        if last.startswith("download-"):
            require(value is False, f"fixed-point C12: {what} sets {key} = {value!r}: a prebuilt compiler or LLVM "
                    "is never fetched; every download key is false")
        elif last in RUST_TOOL_KEYS or last.startswith("initial-"):
            require(isinstance(value, str) and value.startswith(f"{root}/stage0/") and ".." not in value.split("/"),
                    f"fixed-point C12: {what} names {key} = {value!r}, outside {root}/stage0: every Rust tool a "
                    "build runs is its admitted stage0's")
        elif last in HOST_TOOL_KEYS:
            require(value in HOST_TOOLS or (last == "ccache" and value is False),
                    f"fixed-point C12: {what} names {key} = {value!r}, which is not one of the named host tools "
                    f"({', '.join(HOST_TOOLS)}){' or false' if last == 'ccache' else ''}")
        elif last in TRIPLE_KEYS:
            require(False, f"fixed-point C12: {what} sets {key} = {value!r}: a seed builds for the host bootstrap "
                    "detects and no other triple; another triple's C compiler, archiver and linker are found by "
                    "name on PATH (cc-rs), and a path names a target specification whose linker rustc runs")
        elif last == "profile":
            require(key == "profile" and value in PROFILES,
                    f"fixed-point C12: {what} sets {key} = {value!r}: bootstrap merges the defaults file of the "
                    "top-level profile (src/bootstrap/defaults/bootstrap.<profile>.toml) under the config, which the "
                    f"evidence does not hold, so the profile is the recreator's, {' or '.join(PROFILES)}, whose "
                    "defaults keep this rule")
        for item in value if isinstance(value, list) else [value]:
            if isinstance(item, str):
                require(".." not in item.split("/"), f"fixed-point C12: {what} names {key} = {item!r}, a path "
                        "that climbs out of the directory it is read from")
                if item.startswith("/") and item not in HOST_TOOLS:
                    require(item == root or item.startswith(f"{root}/"),
                            f"fixed-point C12: {what} names {key} = {item!r}, a path outside {root}")


def check_base_config(base: bytes, root: str) -> None:
    """C12 for the recreator's seed-mode config: TOML, read alike by bootstrap.py,
    includes nothing, the tool rule, and the compiler profile."""
    document = _config(base, "base-config.toml")
    check_config_lines(base, "base-config.toml")
    require("include" not in document, "fixed-point C12: base-config.toml includes another file; only the rung "
            "config includes, and only the base config")
    check_config_tools(document, root, "base-config.toml")
    require(document.get("profile") in PROFILES, f"fixed-point C12: base-config.toml sets no profile "
            f"({' or '.join(PROFILES)}, the recreator's): bootstrap then merges the dist profile's defaults when the "
            "checkout is not a git work tree, and its own built-in defaults when it is, and the evidence holds "
            "neither")


def config_host_tools(document: dict) -> dict[str, list[str]]:
    """Every host tool a config names, sorted, with the dotted keys that name it
    (sorted): each string value or list item, under any key, that is one of
    HOST_TOOLS, the values check_config_tools lets through as host tools. The
    driver measures and binds exactly these."""
    named: dict[str, list[str]] = {}
    for key, value in _flat(document):
        for item in value if isinstance(value, list) else [value]:
            if isinstance(item, str) and item in HOST_TOOLS:
                named.setdefault(item, []).append(key)
    return {path: sorted(set(keys)) for path, keys in sorted(named.items())}


def config_tools_field(named: dict[str, list[str]], tools: dict) -> str:
    """The receipt's config_host_tools: each tool the base config names and when
    inputs.json says it was measured (`<path>:<setup|record>`, sorted)."""
    return join_list(f"{path}:{(tools.get(path) or {}).get('measured')}" for path in named)


def bound_tool(row: object, path: str | None = None) -> bool:
    """A host tool row as the driver measures one: its absolute path (`path`,
    when given), absolute real path, sha256 and a version line."""
    return isinstance(row, dict) and isinstance(row.get("path"), str) and row["path"].startswith("/") \
        and (path is None or row["path"] == path) and isinstance(row.get("real"), str) \
        and row["real"].startswith("/") and SHA.fullmatch(str(row.get("sha256"))) is not None \
        and isinstance(row.get("version"), str) and row["version"].strip() != ""


def check_config_host_tools(base: bytes, inputs: dict, field: str) -> None:
    """C15: the host tools the base config names are bound in inputs.json, each by
    its path, and are the files the roles bound: cc, linker and default-linker
    name the cc, cxx the c++, python the python; ar and ranlib are bound by path
    alone, and any other key that names a host tool is refused. Every role a key
    maps to is bound, and a role measured at a path the config names is the file
    bound there. Each was measured at setup or at record, and config_host_tools
    says which, exactly."""
    named = config_host_tools(_config(base, "base-config.toml"))
    tools = inputs.get("host_tools")
    require(isinstance(tools, dict), "fixed-point C15: inputs.json has no host_tools table")
    for role in sorted(set(CONFIG_TOOL_ROLES.values())):
        require(bound_tool(tools.get(role)), f"fixed-point C15: inputs.json does not bind the {role} by its absolute "
                f"path, real path, sha256 and version line ({str(tools.get(role))[:120]}): the host tool a config "
                "key names is held to the file bound to its role")
    by_path = sorted(key for key in tools if key.startswith("/"))
    require(by_path == list(named), f"fixed-point C15: inputs.json binds the host tools {join_list(by_path)!r} by "
            f"path, and base-config.toml names {join_list(named)!r}: every host tool the base config names is "
            "bound by its path, and no other is")
    for path, keys in named.items():
        row = tools[path]
        require(bound_tool(row, path), f"fixed-point C15: inputs.json does not bind {path}, which base-config.toml "
                f"names ({', '.join(keys)}), by its path, real path, sha256 and version line")
        require(row.get("measured") in MEASURED, f"fixed-point C15: inputs.json says {path} was measured "
                f"{row.get('measured')!r}; a host tool the base config names is measured at setup or at record")
        for key in keys:
            last = key.rsplit(".", 1)[-1]
            role = CONFIG_TOOL_ROLES.get(last)
            if role is None:
                require(last in PATH_BOUND_TOOL_KEYS, f"fixed-point C15: base-config.toml names {key} = {path!r}, "
                        f"and {last} is not a key whose tool a role binds ({', '.join(CONFIG_TOOL_ROLES)}) nor "
                        f"one bound by its path alone ({', '.join(PATH_BOUND_TOOL_KEYS)}): no record says which "
                        "build step runs it")
                continue
            bound = tools[role]
            require((bound["real"], bound["sha256"]) == (row["real"], row["sha256"]),
                    f"fixed-point C15: base-config.toml names {key} = {path!r}, which is {row['real']} (sha256 "
                    f"{row['sha256'][:16]}), and the {role} inputs.json binds is {bound['real']} (sha256 "
                    f"{bound['sha256'][:16]}): a build would run a {role} the receipt does not name")
    for role, bound in sorted(tools.items()):
        if role.startswith("/") or not isinstance(bound, dict) or not isinstance(bound.get("path"), str) \
                or bound["path"] not in named:
            continue
        row = tools[bound["path"]]
        require((bound.get("real"), bound.get("sha256")) == (row["real"], row["sha256"]),
                f"fixed-point C15: inputs.json binds {bound['path']} as the {role} ({bound.get('real')}, sha256 "
                f"{str(bound.get('sha256'))[:16]}) and, where base-config.toml names it, as {row['real']} (sha256 "
                f"{row['sha256'][:16]}): one path is one file")
    expected = config_tools_field(named, tools)
    require(field == expected, f"fixed-point C15: config_host_tools = {field!r}, and base-config.toml and "
            f"inputs.json give {expected!r}")


def rung_departures(rung: bytes, root: str) -> list[str]:
    """C12: the rung config includes the base config, names every stage0 tool
    under <root>/stage0/bin, keeps the tool rule, and its other keys (sorted,
    dotted) are the departures from the recreator's config."""
    document = _config(rung, "rung-config.toml")
    check_config_lines(rung, "rung-config.toml")
    require(document.get("include") == [f"{root}/src/bootstrap.toml"],
            f"fixed-point C12: rung-config.toml does not include exactly {root}/src/bootstrap.toml")
    build = document.get("build")
    require(isinstance(build, dict), "fixed-point C12: rung-config.toml has no [build] table")
    for key, name in STAGE0_KEYS.items():
        require(build.get(key) == f"{root}/stage0/bin/{name}",
                f"fixed-point C12: rung-config.toml names build.{key} = {build.get(key)!r}, not "
                f"{root}/stage0/bin/{name}")
    check_config_tools({key: value for key, value in document.items() if key != "include"}, root, "rung-config.toml")
    fixed = {"include", *(f"build.{key}" for key in STAGE0_KEYS)}
    return sorted(key for key, _ in _flat(document) if key not in fixed)


def _member_kind(head: bytes, mode: int) -> str:
    """elf or ar (machine code); script (`#!`) or executable (an execute bit),
    which run; or other."""
    if head[:4] == b"\x7fELF":
        return "elf"
    if head[:8] in (b"!<arch>\n", b"!<thin>\n"):
        return "ar"
    if head[:2] == b"#!":
        return "script"
    if mode & 0o111:
        return "executable"
    return "other"


def _regular_file(path: Path, what: str) -> int:
    try:
        metadata = path.lstat()
    except OSError as error:
        raise ValueError(f"fixed-point C13: {what} {path} cannot be read: {error.strerror or error}") from error
    require(stat.S_ISREG(metadata.st_mode), f"fixed-point C13: {what} {path} is not a regular file")
    require(0 < metadata.st_size <= MAX_ARCHIVE_BYTES, f"fixed-point C13: {what} {path} is empty or too large")
    return metadata.st_size


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def archive_table(path: Path) -> dict:
    """One host archive, read as data and never unpacked: its sha256, size, and
    each bin/, lib/, libexec/ path its installer installs (the `file:` and `dir:`
    lines of each component's manifest.in), with type, mode, size, sha256, kind
    and link target. The evidence entry of archive-members.json."""
    size = _regular_file(path, "the pinned archive")
    before = _file_sha256(path)
    prefix = path.name.removesuffix(".tar.xz")
    rows: dict[str, dict] = {}
    texts: dict[str, bytes] = {}
    try:
        with tarfile.open(path, "r:xz") as bundle:
            for member in bundle:
                parts = member.name.split("/")
                require(parts[0] == prefix and "" not in parts and ".." not in parts,
                        f"fixed-point C13: {path.name} has the member {member.name!r} outside {prefix}")
                require(member.name not in rows, f"fixed-point C13: {path.name} lists {member.name!r} twice")
                row = {"type": "file" if member.isfile() else "dir" if member.isdir() else
                       "symlink" if member.issym() else "hardlink" if member.islnk() else "other",
                       "mode": member.mode, "bytes": member.size if member.isfile() else 0,
                       "sha256": None, "kind": None, "link": member.linkname or None}
                if member.isfile():
                    handle = bundle.extractfile(member)
                    require(handle is not None, f"fixed-point C13: {path.name}: {member.name} cannot be read")
                    digest, head, data = hashlib.sha256(), b"", []
                    for block in iter(lambda: handle.read(1 << 20), b""):
                        head = head or block[:8]
                        digest.update(block)
                        if parts[1:] == ["components"] or parts[2:] == ["manifest.in"]:
                            data.append(block)
                    row["sha256"], row["kind"] = digest.hexdigest(), _member_kind(head, member.mode)
                    if data:
                        texts[member.name] = b"".join(data)
                rows[member.name] = row
    except (tarfile.TarError, OSError, EOFError) as error:
        raise ValueError(f"fixed-point C13: {path} cannot be read as a .tar.xz: {error}") from error
    require(_file_sha256(path) == before, f"fixed-point C13: {path} changed while it was read")
    listed = texts.get(f"{prefix}/components")
    require(listed is not None, f"fixed-point C13: {path.name} has no {prefix}/components")
    installed: dict[str, dict] = {}
    for component in listed.decode("utf-8", "replace").split():
        manifest = texts.get(f"{prefix}/{component}/manifest.in")
        require(manifest is not None, f"fixed-point C13: {path.name} names {component} and has no manifest.in for it")
        base = f"{prefix}/{component}/"
        for line in manifest.decode("utf-8", "replace").splitlines():
            directive, _, listed_path = line.partition(":")
            require(directive in ("file", "dir") and confined_path(listed_path),
                    f"fixed-point C13: {path.name}: {base}manifest.in has the line {line!r}")
            if directive == "file":
                require(base + listed_path in rows, f"fixed-point C13: {path.name} lists {listed_path} and does not "
                        "carry it")
                chosen = [base + listed_path]
            else:
                chosen = [name for name in rows if name.startswith(base + listed_path + "/")]
            for name in chosen:
                row = rows[name]
                if row["type"] == "dir":
                    continue
                target = name[len(base):]
                require(target not in installed or installed[target]["sha256"] == row["sha256"],
                        f"fixed-point C13: {path.name} installs {target} twice with different bytes")
                installed[target] = {"path": target, **row}
    members = [installed[key] for key in sorted(installed) if key.startswith(INSTALLED_TOPS)]
    return {"name": path.name, "sha256": before, "bytes": size, "members": members,
            "members_sha256": records_sha256(members)}


def shared_tables(path: Path) -> dict:
    """A shared source archive's member table by prepare.py's rule
    (compare_shared_archives: every member by name, type, mode, size, sha256 and
    link, one canonical JSON line each): its digest whole and without the
    package-root builder-config (the config of the host that ran x.py dist,
    which install.sh never installs), the member count, and builder-config's own
    digest."""
    _regular_file(path, "the shared archive")
    prefix = path.name.removesuffix(".tar.xz")
    rows = []
    try:
        with tarfile.open(path, "r:xz") as bundle:
            for member in bundle:
                kind = ("file" if member.isfile() else "dir" if member.isdir() else "symlink" if member.issym()
                        else "hardlink" if member.islnk() else f"type-{member.type!r}")
                digest = None
                if member.isfile():
                    handle = bundle.extractfile(member)
                    require(handle is not None, f"fixed-point C13: {path.name}: {member.name} cannot be read")
                    digest = hashlib.sha256(handle.read()).hexdigest()
                rows.append({"path": member.name, "type": kind, "mode": member.mode,
                             "size": member.size if member.isfile() else 0, "sha256": digest,
                             "link": member.linkname or None})
    except (tarfile.TarError, OSError, EOFError) as error:
        raise ValueError(f"fixed-point C13: {path} cannot be read as a .tar.xz: {error}") from error
    rows.sort(key=lambda row: row["path"])
    require(len({row["path"] for row in rows}) == len(rows), f"fixed-point C13: {path.name} lists a member twice")
    local = f"{prefix}/{SHARED_HOST_LOCAL_MEMBER}"

    def digest(selected: list[dict]) -> str:
        return sha256("".join(json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n"
                              for row in selected).encode("utf-8"))

    return {"members": len(rows), "member_table_sha256": digest(rows),
            "member_table_without_host_local_sha256": digest([row for row in rows if row["path"] != local]),
            "host_local_sha256": next((row["sha256"] for row in rows if row["path"] == local
                                       and row["type"] == "file"), None)}


def shared_entry(pinned: Path, pinned_sha256: str, this_run: Path, kept: dict) -> dict:
    """archive-members.json's `shared`: the pinned shared archive and this run's
    dist of it, each by its tables (`shared_tables`), beside prepare.py's record
    of keeping the pinned one (`kept`: its trust-stage0-shared-kept.json row)."""
    mine, theirs = shared_tables(this_run), shared_tables(pinned)
    return {"name": pinned.name, "pinned_sha256": pinned_sha256, "this_run_sha256": kept.get("this_run_sha256"),
            "members": theirs["members"], "pinned_member_table_sha256": theirs["member_table_sha256"],
            "pinned_member_table_without_host_local_sha256": theirs["member_table_without_host_local_sha256"],
            "pinned_host_local_sha256": theirs["host_local_sha256"],
            "this_run_dist": {"sha256": _file_sha256(this_run), **mine},
            "excluded": [{field: item.get(field) for field in ("path", "pinned_sha256", "this_run_sha256")}
                         for item in kept.get("excluded") or []]}


# ---------------------------------------------------------------------------
# the evidence


def evidence_listing(seed_root: Path, host: str) -> list[str]:
    """The names under host-proofs/<host>/fixed-point, read without following links."""
    path = seed_root
    for part in ("host-proofs", host, EVIDENCE_DIR):
        path = path / part
        try:
            metadata = path.lstat()
        except OSError as error:
            raise ValueError(f"fixed-point C1: {path} cannot be read: {error.strerror or error}") from error
        require(stat.S_ISDIR(metadata.st_mode), f"fixed-point C1: {path} is not a directory")
    with os.scandir(path) as entries:
        return sorted(entry.name for entry in entries)


def _tool_problems(run: dict, root: str, ninja: dict) -> list[str]:
    """C7: the tools the run names are what its stage0 and inputs.json say, not
    believed from its own booleans: each config tool is the stage0 file at its
    path with that file's digest, the stage0 it observed is the admitted one,
    and the tool directories on its PATH hold only the bound ninja."""
    problems = []
    stage0 = run.get("stage0_sha256") if isinstance(run.get("stage0_sha256"), dict) else {}
    tools = (run.get("config_tools") or {}).get("tools")
    if not isinstance(tools, dict) or set(tools) != set(STAGE0_KEYS):
        problems.append(f"its config_tools name {sorted(tools) if isinstance(tools, dict) else tools!r}, not the "
                        f"four stage0 tools {', '.join(sorted(STAGE0_KEYS))}")
    else:
        for key, name in sorted(STAGE0_KEYS.items()):
            tool = tools[key] if isinstance(tools[key], dict) else {}
            path = f"{root}/stage0/bin/{name}"
            digest = stage0.get(f"bin/{name}")
            if tool.get("named") != path or tool.get("real") != path or digest is None or tool.get("sha256") != digest:
                problems.append(f"its config tool {key} is not {path} with the stage0's bin/{name} digest")
    observed = run.get("stage0_observed") or {}
    if observed.get("root") != f"{root}/stage0" or observed.get("sha256") != stage0 or not stage0:
        problems.append(f"the stage0 it observed is not {root}/stage0 with the digests it was admitted with")
    dirs = run.get("tool_dirs")
    entries = [entry for directory in dirs or [] if isinstance(directory, dict)
               for entry in directory.get("entries") or []] if isinstance(dirs, list) else None
    if not entries or not all(isinstance(entry, dict) and entry.get("name") == "ninja"
                              and entry.get("real") == ninja.get("path") and entry.get("sha256") == ninja.get("sha256")
                              for entry in entries):
        problems.append("the tool directories on its PATH do not hold exactly the ninja inputs.json binds")
    return problems


def rung_jobs(rung: bytes) -> object:
    """C7: the job count every run read, the rung config's build.jobs (None when unset)."""
    build = _config(rung, "rung-config.toml").get("build")
    return build.get("jobs") if isinstance(build, dict) else None


def _jobserver_problems(run: dict, root: str, jobs: object, make: object) -> list[str]:
    """C7: the run was handed the FIFO jobserver of MAKEFLAGS_FIFO's comment, and it
    balanced; its make adapter ran `make`, inputs.json's host_tools row."""
    if type(jobs) is not int or jobs < 1:
        return [f"the rung config's build.jobs is {jobs!r}, not the job count a FIFO jobserver advertises"]
    problems = []
    flags = (run.get("environment") or {}).get("MAKEFLAGS")
    match = MAKEFLAGS_FIFO.fullmatch(flags) if isinstance(flags, str) else None
    path = match.group(2) if match else None
    tmp = f"{root}/ledger/tmp/"
    name = path[len(tmp):] if path is not None and path.startswith(tmp) else ""
    if match is None or int(match.group(1)) != jobs or name in ("", ".", "..") or "/" in name:
        problems.append(f"its environment's MAKEFLAGS is {flags!r}, not -j{jobs} --jobserver-auth=fifo:<a FIFO in "
                        f"{root}/ledger/tmp>: it was not handed the FIFO jobserver every run is handed")
        path = None
    held = run.get("jobserver") if isinstance(run.get("jobserver"), dict) else {}
    wanted = {"kind": "fifo", "path": path, "jobs": jobs, "tokens": jobs - 1, "tokens_at_end": jobs - 1,
              "path_unchanged": True}
    # SEED-TOKEN-LEAK-STAGE0-1 (TOKEN_LEAK_RULE's comment): a deficit of the preloaded
    # count is excused only when every condition holds, and is refused by name otherwise.
    deficit = token_deficit(run) if _same(held.get("tokens"), jobs - 1) else None
    unmet = token_deficit_unexcused(run, *stage0_lacks_token_fix(run.get("stage0_commit"))) \
        if deficit is not None else []
    if deficit is not None and not unmet:
        del wanted["tokens_at_end"]
    moved = sorted(key for key, value in wanted.items() if type(held.get(key)) is not type(value)
                   or held.get(key) != value)
    if path is None or moved:
        problems.append(f"its jobserver record is not the FIFO its MAKEFLAGS names with {jobs - 1} token(s) "
                        f"preloaded, all there again when x.py had exited, its path unchanged (it differs in "
                        f"{', '.join(moved) or 'the path'})")
    if deficit is not None and unmet:
        problems.append(token_deficit_refusal(*deficit, unmet))
    if not bound_tool(make):
        return problems + [f"inputs.json's host_tools binds no make by its path, real path, sha256 and version line "
                           f"({str(make)[:120]}), and the run's make adapter runs one"]
    adapter = held.get("make_adapter") if isinstance(held.get("make_adapter"), dict) else {}
    wanted = {"path": f"{root}/ledger/pathbin/make", "make": make["path"], "make_sha256": make["sha256"]}
    moved = sorted(key for key, value in wanted.items() if not _same(adapter.get(key), value))
    if moved or not SHA.fullmatch(str(adapter.get("sha256"))) or not isinstance(adapter.get("sha256"), str):
        problems.append(f"its jobserver record does not name the make adapter at {wanted['path']} by its sha256, "
                        f"running the make inputs.json binds ({make['path']}, sha256 {make['sha256'][:16]}) (it "
                        f"differs in {', '.join(moved) or 'sha256'})")
    return problems


def _same(value: object, wanted: object) -> bool:
    """Equal and of one type: JSON's true is not the count 1."""
    return type(value) is type(wanted) and value == wanted


def _run_problems(run: dict, label_base: str, words: list[str], fields: dict, lean_library: str,
                  ninja: dict, jobs: object, make: object) -> list[str]:
    """C7: why a run record is not a clean run of this build line at the root."""
    root = fields["build_root"]
    label = run.get("label")
    problems = []
    if run.get("kind") != "rung" or run.get("schema") != STAIRCASE_SCHEMA:
        problems.append("it is not a seed_staircase.py run record")
    if not isinstance(label, str) or not re.fullmatch(rf"{re.escape(label_base)}(-[2-9]|-[1-9][0-9]+)?", label):
        problems.append(f"its label {label!r} is not {label_base} or a later attempt of it")
    if run.get("rc") != 0:
        problems.append(f"x.py exited {run.get('rc')!r}")
    if run.get("commit") != fields["source_commit"]:
        problems.append(f"it built {run.get('commit')!r}")
    if run.get("worktree") != f"{root}/src":
        problems.append(f"it ran in {run.get('worktree')!r}, not {root}/src")
    if run.get("argv") != ["x.py", "--config", f"{root}/ledger/rung.bootstrap.toml", *words]:
        problems.append(f"its argv is {run.get('argv')!r}, not the fixed line for its role")
    if run.get("no_stock_evidence") is not True:
        problems.append("its no-stock evidence is not true")
    if run.get("trap_hits") != []:
        problems.append("a stock Rust tool name was reached (trap hits)")
    if "sampler_died" in run:
        problems.append("its process census died before the build ended")
    census = run.get("process_census") or {}
    gap = census.get("max_gap_s")
    if census.get("flagged") or census.get("ended") != "watched-exited" or isinstance(gap, bool) or \
            not isinstance(gap, (int, float)) or gap > MAX_CENSUS_GAP_S:
        problems.append("its process census flagged a process or did not watch the build to its end")
    built = run.get("build_census") or {}
    files = built.get("rustc_info_files")
    if built.get("clean") is not True or isinstance(files, bool) or not isinstance(files, int) or files <= 0:
        problems.append("its build census is not clean or read no .rustc_info.json")
    for key in ("stage0_matches_admission", "stage0_runtime_unchanged", "tool_dirs_unchanged"):
        if run.get(key) is not True:
            problems.append(f"{key} is not true")
    config = run.get("config_tools") or {}
    if config.get("matches_admission") is not True or config.get("config_sha256") != fields["rung_config_sha256"]:
        problems.append("the config x.py read is not the tracked rung config, or names tools the admission does not")
    environment = run.get("environment") or {}
    expected = {"HOME": fields["private_home"], "USER": STEP_USER, "CARGO_HOME": f"{root}/ledger/cargo-home",
                "TMPDIR": f"{root}/ledger/tmp", "CARGO_NET_OFFLINE": "true",
                "CLEAN_OLEAN_PINNED_LEAN_LIB": lean_library, "CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1",
                "TRUST_STAIRCASE_RUNG": label}
    if "LOGNAME" in environment:
        expected["LOGNAME"] = STEP_USER
    problems += [f"its environment's {key} is {environment.get(key)!r}, not {value!r}"
                 for key, value in expected.items() if environment.get(key) != value]
    if "SSH_AUTH_SOCK" in environment:
        problems.append("it was handed an SSH_AUTH_SOCK")
    lean = run.get("clean_lean") or {}
    if lean.get("unchanged") is not True or lean.get("library") != lean_library or \
            (lean.get("before") or {}).get("manifest_sha256") != fields["clean_lean_inputs_sha256"]:
        problems.append("the Lean library it was given is not the bound one, or changed under the build")
    tool = run.get("tool") or {}
    if tool.get("sha256") != fields["orchestration_sha256"] or tool.get("modified_in_checkout") is not False or \
            not COMMIT.fullmatch(str(tool.get("checkout_head"))):
        problems.append("it was not run by the recorded seed_staircase.py, unmodified in a checkout")
    return problems + _tool_problems(run, root, ninja) + _jobserver_problems(run, root, jobs, make)


def capture_evidence(seed_root: Path, pins: dict[str, str], host: str, receipt: Receipt, receipt_bytes: bytes,
                     surface: dict, surface_bytes: bytes, read_proof, *, payloads: dict[str, str],
                     allowed: tuple[str, ...]) -> dict:
    """C1-C16 over the tracked evidence; returns the digest of the files it read
    (evidence_sha256's rule, from their bytes) and their size. `payloads` are the
    nine pinned archive rows of `host` (seed_host_ledger.host_payloads)."""
    fields = receipt.fields
    controls = int(fields["controls"])
    names = evidence_names(controls)
    root = fields["build_root"]
    # C1 every file there, nothing else, each its receipt digest.
    listed = evidence_listing(seed_root, host)
    require(listed == sorted(names), f"fixed-point C1: host-proofs/{host}/{EVIDENCE_DIR} holds "
            f"{sorted(set(listed) - set(names))[:3] or 'no extra file'} beyond, and lacks "
            f"{sorted(set(names) - set(listed))[:3] or 'nothing'} of, the files this receipt binds")
    prefix = f"host-proofs/{host}/{EVIDENCE_DIR}/"
    files: dict[str, bytes] = {}
    for name in names:
        payload = read_proof(seed_root, prefix + name)
        field = evidence_field(name) + "_sha256"
        require(sha256(payload) == fields[field], f"fixed-point C1: {name} has sha256 {sha256(payload)}, and the "
                f"receipt's {field} is {fields[field]}")
        files[name] = payload
    total = sum(map(len, files.values()))
    require(total <= MAX_TOTAL_EVIDENCE_BYTES, "fixed-point C1: the evidence exceeds its aggregate bound")
    # T7 the account, by the receipt's own digests, and any personal home whatever they say.
    for name, payload in (*files.items(), (RECEIPT_NAME, receipt_bytes), ("seed-surface.json", surface_bytes)):
        found = account_found(payload, fields["account_home_sha256"], fields["account_login_sha256"], name=name)
        require(found is None, f"fixed-point T7: {name} still names the invoking account's {found}; tracked "
                "evidence names it only as <home> and <account>")
        require(not personal_home_found(payload, name), f"fixed-point T7: {name} names a home directory "
                "(/home/<name> or /Users/<name>) that is not <home>: whatever account the receipt's digests stand "
                "for, tracked evidence names a home only as <home>")
    # T7 each tracked file is its raw record with `normalised_count` replacements:
    # every replacement left a token, and tokens there mean something was replaced.
    for name, payload in files.items():
        count = int(fields[f"{evidence_field(name)}_normalised_count"])
        tokens = sum(payload.decode("utf-8", "replace").count(token) for token in ("<home>", "<account>"))
        require(count <= tokens and (count > 0 or tokens == 0), f"fixed-point T7: {name} holds {tokens} <home> "
                f"or <account> token(s), and the receipt says {count} were replaced in its raw record")
    docs = {name: load_json(payload, name) for name, payload in files.items() if name.endswith(".json")}
    # C2 the manifests; C3 the rows; tree digests.
    numbered = [f"control-{number}" for number in range(1, controls + 1)]
    trees = {role: checked_manifest(docs[f"stage2-{role}.json"], host, f"stage2-{role}.json")
             for role in (*ROLES, *numbered)}
    producer = trees["producer"]
    produced_files = file_rows(producer)
    require(receipt.files == produced_files and int(fields["compared_files"]) == len(produced_files),
            "fixed-point C3: the compiler_file rows are not exactly the producer manifest's files")
    require(receipt.links == link_rows(producer),
            "fixed-point C3: the compiler_link rows are not exactly the producer manifest's links inside stage2")
    for role in ROLES:
        key = f"stage2_tree_sha256_{ROLE_FIELD[role]}"
        require(trees[role]["sha256"] == fields[key], f"fixed-point C2: {key} is not the digest of "
                f"stage2-{role}.json")
    # C4 one core for every tree.
    core = core_sha256(producer, allowed)
    for role, tree in trees.items():
        outside = [path for path in differing_paths(producer, tree) if path not in allowed]
        require(not outside and core_sha256(tree, allowed) == core,
                f"fixed-point C4: the {role} tree differs from the producer's outside {', '.join(allowed)} "
                f"({', '.join(outside[:3])}); no library, driver or entrypoint can be excused")
    require(core == fields["stage2_core_sha256"], "fixed-point C4: stage2_core_sha256 is not the core digest the "
            "manifests give")
    # C5 reproduced means a build by the pinned seed gave the producer's bytes.
    seeds = [trees["fixed-point"], *(trees[role] for role in numbered)]
    not_reproduced, nondeterministic = reproduction(producer, seeds, allowed)
    require(join_list(not_reproduced) == fields["not_reproduced"],
            f"fixed-point C5: not_reproduced = {fields['not_reproduced']!r}, and the manifests give "
            f"{join_list(not_reproduced)!r}")
    require(join_list(nondeterministic) == fields["nondeterministic"],
            f"fixed-point C5: nondeterministic = {fields['nondeterministic']!r}, and the manifests give "
            f"{join_list(nondeterministic)!r}")
    # C6 the verdicts.
    for role in ("fixed-point", "cross-check"):
        key = f"{ROLE_FIELD[role]}_verdict"
        require(verdict(producer, trees[role]) == fields[key], f"fixed-point C6: {key} = {fields[key]!r}, and "
                f"the manifests give {verdict(producer, trees[role])!r}")
    # C15 first: the inputs every run is held to.
    inputs = docs["inputs.json"]
    lean = inputs.get("clean_lean_inputs") or {}
    lean_library = str(lean.get("library", ""))
    require(inputs.get("schema") == INPUTS_SCHEMA and inputs.get("commit") == fields["source_commit"]
            and inputs.get("host") == host and inputs.get("root") == root,
            "fixed-point C15: inputs.json is not the inputs of this commit, host and root")
    require((inputs.get("cargo_home_inputs") or {}).get("sha256") == fields["cargo_home_inputs_sha256"]
            and lean.get("sha256") == fields["clean_lean_inputs_sha256"],
            "fixed-point C15: inputs.json does not carry the receipt's cargo-home and Lean input digests")
    require(lean_library.startswith(f"{root}/inputs/lean/") and lean_library.endswith("/lib/lean"),
            f"fixed-point C15: the Lean library {lean_library!r} is not a copy under {root}/inputs/lean")
    cc = (inputs.get("host_tools") or {}).get("cc") or {}
    require(f"{cc.get('sha256')} {cc.get('version')}" == fields["host_c_compiler"],
            "fixed-point C15: host_c_compiler is not the C compiler inputs.json records")
    cargo = inputs.get("cargo_home_inputs") or {}
    embedded = cargo.get("manifest") if isinstance(cargo.get("manifest"), dict) else {}
    require(embedded.get("schema") == "trust-cargo-home-inputs-v1" and isinstance(embedded.get("trees"), dict)
            and embedded["trees"] and embedded.get("fingerprint") == cargo.get("fingerprint")
            and embedded.get("trees") == cargo.get("trees") and SHA.fullmatch(str(cargo.get("fingerprint"))),
            "fixed-point C15: inputs.json's cargo-home manifest is not a trust-cargo-home-inputs-v1 manifest of the "
            "fingerprint and trees it records")
    ninja = inputs.get("ninja") or {}
    require(ninja.get("path") == f"{root}/tools/ninja" and SHA.fullmatch(str(ninja.get("sha256"))),
            f"fixed-point C15: inputs.json's ninja is not the copy at {root}/tools/ninja with a sha256")
    # C7 every run record.
    runs: dict[str, dict] = {}
    words = {**{role: list(BUILD_WORDS) for role in (*ROLES, *numbered)},
             "producer-dist": ["dist", "--stage", "2", *fields["dist_components"].split(" ")],
             "producer-full": ["build", "--stage", "2"],
             "producer-manifest-tool": ["build", "--stage", "2", "src/tools/build-manifest"]}
    bases = {**ROLE_LABEL, **{f"control-{number}": f"c{number}-build" for number in range(1, controls + 1)},
             **dict(DIST_RUNS)}
    jobs, make = rung_jobs(files["rung-config.toml"]), (inputs.get("host_tools") or {}).get("make")
    for role, base in bases.items():
        run = docs[f"run-{role}.json"]
        problems = _run_problems(run, base, words[role], fields, lean_library, ninja, jobs, make)
        require(not problems, f"fixed-point C7: run-{role}.json is not a clean run: {'; '.join(problems[:4])}")
        runs[role] = run
    labels = [run["label"] for run in runs.values()]
    require(len(set(labels)) == len(labels), "fixed-point C7: two run records carry one label")
    jobservers = sorted({run["environment"]["MAKEFLAGS"] for run in runs.values()})
    require(len(jobservers) == 1, f"fixed-point C7: the runs were handed {len(jobservers)} jobservers "
            f"({'; '.join(jobservers[:2])}); the roles differ only in their stage0, so every run is handed one")
    adapters = sorted({run["jobserver"]["make_adapter"]["sha256"] for run in runs.values()})
    require(len(adapters) == 1, f"fixed-point C7: the runs reached make through {len(adapters)} make adapters "
            f"(sha256 {', '.join(sha[:16] for sha in adapters[:2])}); every run is handed one")
    # Every run SEED-TOKEN-LEAK-STAGE0-1 excused a deficit for (each run above is clean) is disclosed.
    deficits = join_list(token_deficits(runs.values()))
    require(fields["jobserver_token_deficits"] == deficits,
            f"fixed-point C7: jobserver_token_deficits = {fields['jobserver_token_deficits']!r}, and the run records "
            f"give {deficits!r}: every run whose jobserver came back short is disclosed ({TOKEN_LEAK_RULE})")
    require((runs["producer"].get("tool") or {}).get("checkout_head") == fields["orchestration_commit"],
            "fixed-point C7: orchestration_commit is not the checkout run-producer.json's seed_staircase.py ran from")
    # C8 each manifest is its run's tree.
    for role in (*ROLES, *numbered):
        produced = (runs[role].get("produced") or {}).get("sha256")
        mine = file_rows(trees[role])
        require(isinstance(produced, dict) and "bin/trustc" in produced
                and any(path.startswith("lib/librustc_driver-") for path in produced)
                and all(mine.get(path) == digest for path, digest in produced.items()),
                f"fixed-point C8: stage2-{role}.json is not the tree run-{role}.json says it produced")
    # C8 for the dist runs: dist, the full build and the manifest tool each left
    # the producer's compared identity files (seed_staircase.py's `produced`, the
    # same paths as the producer run's), so the archives are of the compared
    # compiler. This covers those files, not every file of stage2.
    identity_paths = set(runs["producer"]["produced"]["sha256"])
    for role, _ in DIST_RUNS:
        produced = (runs[role].get("produced") or {}).get("sha256")
        require(isinstance(produced, dict) and set(produced) == identity_paths
                and all(produced_files.get(path) == digest for path, digest in produced.items()),
                f"fixed-point C8: run-{role}.json left a stage2 whose identity files are not the producer's "
                "compared rows (or it records none)")
    # C9 admissions.
    admissions = {role: docs[f"admission-{role}.json"] for role in ROLES}
    role_commit = {"producer": fields["producer_stage0_commit"], "fixed-point": fields["source_commit"],
                   "cross-check": fields["cross_check_stage0_commit"]}
    for role, admission in admissions.items():
        digests = admission.get("sha256")
        require(admission.get("kind") == "stage0-admission" and not admission.get("refusals")
                and isinstance(digests, dict),
                f"fixed-point C9: admission-{role}.json is not a clean stage0 admission")
        require(admission.get("commit") == runs[role].get("stage0_commit") == role_commit[role]
                and digests == runs[role].get("stage0_sha256"),
                f"fixed-point C9: admission-{role}.json is not the stage0 run-{role}.json ran, or not the "
                "receipt's commit for that role")
        drivers = [digest for path, digest in digests.items() if path.startswith("lib/librustc_driver-")]
        prefix_field = ROLE_FIELD[role]
        require(len(drivers) == 1 and fields[f"{prefix_field}_stage0_compiler_sha256"] == digests.get("bin/trustc")
                and fields[f"{prefix_field}_stage0_driver_sha256"] == drivers[0]
                and fields[f"{prefix_field}_stage0_cargo_sha256"] == digests.get("bin/cargo"),
                f"fixed-point C9: the receipt's {prefix_field} stage0 digests are not admission-{role}.json's")
    for role, _ in DIST_RUNS:
        require(runs[role].get("stage0_sha256") == admissions["producer"]["sha256"]
                and runs[role].get("stage0_commit") == fields["producer_stage0_commit"],
                f"fixed-point C9: run-{role}.json did not run the producer's stage0")
    # C11 three different compilers.
    trustc = [admissions[role]["sha256"].get("bin/trustc") for role in ROLES]
    require(len(set(trustc)) == 3 and all(trustc), "fixed-point C11: the producer, fixed-point and cross-check "
            "stage0 compilers are not three different bin/trustc; a repeat cannot stand in for either")
    # C12 configs.
    require(sha256(files["base-config.toml"]) == fields["base_config_sha256"]
            and sha256(files["rung-config.toml"]) == fields["rung_config_sha256"],
            "fixed-point C12: base_config_sha256 or rung_config_sha256 is not its tracked file's digest")
    check_base_config(files["base-config.toml"], root)
    # C15 the host tools the base config names: bound, and the roles' files.
    check_config_host_tools(files["base-config.toml"], inputs, fields["config_host_tools"])
    departures = rung_departures(files["rung-config.toml"], root)
    require(join_list(departures) == fields["config_departures"],
            f"fixed-point C12: the rung config departs from the recreator's in {join_list(departures)!r}, and "
            f"config_departures says {fields['config_departures']!r}")
    require(set(departures) <= set(BENIGN_DEPARTURES), f"fixed-point C12: the rung config departs from the "
            f"recreator's in {', '.join(sorted(set(departures) - set(BENIGN_DEPARTURES)))}; a rung config departs "
            f"only in {', '.join(BENIGN_DEPARTURES)}")
    # C10 the fixed point's stage0 is the producer's compared files ...
    fixed = admissions["fixed-point"]["sha256"]
    require(all(path in fixed for path in STAGE0_FILES)
            and any(path.startswith("lib/librustc_driver-") for path in fixed)
            and any(path.startswith("lib/libstd-") for path in fixed),
            "fixed-point C10: admission-fixed-point.json does not name the compiler, cargo, targo, trustdoc, "
            "trustfmt, the driver and the std dylib")
    for path, digest in sorted(fixed.items()):
        require(produced_files.get(path) == digest, f"fixed-point C10: the fixed-point stage0's {path} is not the "
                "producer's row at that path: the fixed point was not built by the producer's compiler")
    for role in numbered:
        require(runs[role].get("stage0_sha256") == fixed and runs[role].get("stage0_commit") == fields["source_commit"],
                f"fixed-point C10: run-{role}.json did not run the fixed point's stage0")
    # C13 archive members joined to the producer's rows; ... and the archive members (C10).
    members = _check_members(docs["archive-members.json"], fields, host, payloads, producer, surface)
    for path, digest in sorted(fixed.items()):
        require((members.get(path) or {}).get("sha256") == digest, f"fixed-point C10: the fixed-point stage0's "
                f"{path} is not the pinned archive member at that path: the fixed point was not built by the "
                "archive compiler")
    # C14 native outputs.
    native = docs["native-outputs.json"]
    rows = native.get("rows")
    require(native.get("schema") == NATIVE_SCHEMA and isinstance(rows, list) and rows
            and all(isinstance(row, dict) and set(row) == {"path", "kind", "bytes", "sha256"}
                    and row["kind"] in CODE_KINDS and SHA.fullmatch(str(row["sha256"])) for row in rows)
            and len({row["path"] for row in rows}) == len(rows) and native.get("files") == len(rows),
            "fixed-point C14: native-outputs.json is not a table of ELF and ar files")
    outside = sorted(str(row["path"]) for row in rows if not str(row["path"]).startswith(NATIVE_TOPS)
                     or ".." in str(row["path"]).split("/"))
    require(not outside, f"fixed-point C14: native-outputs.json lists {outside[:1]}, which is not under "
            f"{' or '.join(NATIVE_TOPS)}: only what x.py built of LLVM and lld counts as copied native code")
    require(records_sha256(rows) == native.get("sha256") == fields["native_outputs_sha256"],
            "fixed-point C14: native-outputs.json does not hash to native_outputs_sha256")
    native_digests = {row["sha256"] for row in rows}
    copied = sum(1 for digest in produced_files.values() if digest in native_digests)
    require(int(fields["native_copied_rows"]) == copied
            and int(fields["rust_built_rows"]) == len(produced_files) - copied,
            f"fixed-point C14: native_copied_rows / rust_built_rows are {fields['native_copied_rows']} / "
            f"{fields['rust_built_rows']}, and the tables give {copied} / {len(produced_files) - copied}")
    # T7-adjacent: every run's no-stock fields, summed.
    require(all(not run.get("trap_hits") for run in runs.values())
            and all(not (run.get("process_census") or {}).get("flagged") for run in runs.values()),
            "fixed-point C7: a run has trap hits or flagged processes")
    # C16 the chain.
    _check_chain(docs["chain.json"], fields)
    digest = sha256("".join(f"{name} {sha256(files[name])}\n" for name in sorted(names)).encode("utf-8"))
    return {"sha256": digest, "bytes": total}


def _check_members(document: dict, fields: dict, host: str, payloads: dict[str, str], producer: dict,
                   surface: dict) -> dict[str, dict]:
    """C13 over archive-members.json; returns every member by installed path."""
    rows = {row["path"]: row for row in producer["records"]}
    shared_key = next((key for key in payloads if "/trust-src-" in key), None)
    require(shared_key is not None, "fixed-point A4: the pins have no shared trust-src archive")
    expected = {Path(key).name: digest for key, digest in payloads.items() if key != shared_key}
    archives = document.get("archives")
    require(document.get("schema") == MEMBERS_SCHEMA and document.get("host") == host
            and isinstance(archives, list), "fixed-point C13: archive-members.json is not this host's member table")
    by_name = {}
    for entry in archives:
        require(isinstance(entry, dict) and entry.get("name") in expected and entry["name"] not in by_name,
                f"fixed-point C13: archive-members.json names an archive outside the pin: {entry!r:.80}")
        by_name[entry["name"]] = entry
    require(set(by_name) == set(expected), "fixed-point C13: archive-members.json does not cover the eight host "
            "archives")
    members: dict[str, dict] = {}
    archive_only, executables, total, size = set(), set(), 0, 0
    for name, entry in sorted(by_name.items()):
        require(entry.get("sha256") == expected[name], f"fixed-point C13: {name} in archive-members.json has "
                "another sha256 than its pin")
        listed = entry.get("members")
        require(isinstance(listed, list) and records_sha256(listed) == entry.get("members_sha256")
                and isinstance(entry.get("bytes"), int) and not isinstance(entry.get("bytes"), bool),
                f"fixed-point C13: {name}'s member list is not its members_sha256")
        size += entry["bytes"]
        for member in listed:
            path = member.get("path")
            require(isinstance(path, str) and path.startswith(INSTALLED_TOPS),
                    f"fixed-point C13: {name} lists a member outside bin/, lib/, libexec/: {path!r}")
            total += 1
            earlier = members.get(path)
            require(earlier is None or earlier.get("sha256") == member.get("sha256"),
                    f"fixed-point C13: two archives install {path} with different bytes")
            members[path] = member
            row = rows.get(path)
            if row is None:
                require(member.get("kind") not in CODE_KINDS,
                        f"fixed-point C13: {name} ships the {member.get('kind')} file {path}, and the producer's "
                        "stage2 has no row for it: machine code cannot be archive-only")
                require(member.get("kind") in (*EXECUTABLE_KINDS, "other", None),
                        f"fixed-point C13: {name} lists {path} with the kind {member.get('kind')!r}")
                archive_only.add(path)
                if member.get("kind") in EXECUTABLE_KINDS:
                    executables.add(path)
            elif member.get("type") == "file":
                require(row["kind"] == "file" and row["sha256"] == member.get("sha256"),
                        f"fixed-point C13: {name} ships {path} with other bytes than the producer's row")
            elif member.get("type") == "symlink":
                require(row["kind"] == "symlink" and row.get("target") == member.get("link"),
                        f"fixed-point C13: {name} ships the link {path} with another target than the producer's")
            else:
                raise ValueError(f"fixed-point C13: {name} ships {path} as a {member.get('type')!r}")
    require(join_list(archive_only) == fields["archive_only"],
            f"fixed-point C13: archive_only = {fields['archive_only']!r}, and the members give "
            f"{join_list(archive_only)!r}")
    require(join_list(executables) == fields["archive_only_executables"],
            f"fixed-point C13: archive_only_executables = {fields['archive_only_executables']!r}, and the members "
            f"give {join_list(executables)!r}: every script or executable no build's row compares is named")
    require(int(fields["archive_members"]) == total and int(fields["archive_bytes_total"]) == size,
            f"fixed-point C13: archive_members / archive_bytes_total are {fields['archive_members']} / "
            f"{fields['archive_bytes_total']}, and the table gives {total} / {size}")
    for name, digest in surface["entrypoint_sha256"].items():
        member, row = members.get(f"bin/{name}"), rows.get(f"bin/{name}")
        require(member is not None and row is not None and row.get("kind") == "file"
                and member.get("sha256") == row.get("sha256") == digest,
                f"fixed-point C13: the surface entrypoint {name} is not one archive member, the producer's row "
                "and the surface digest at once")
    # (A not-reproduced file's member is held to the producer's row by the file rule above.)
    _check_shared(document.get("shared") or {}, fields, Path(shared_key).name, payloads[shared_key])
    return members


def _check_shared(shared: dict, fields: dict, name: str, pinned_sha256: str) -> None:
    """C13 for the shared source archive: shared_source_members=identical is
    recomputed, not believed. This run's dist of trust-src and the pinned one
    have one member table outside the package-root builder-config; builder-config
    is excluded exactly when the whole tables differ, and then it is a real
    difference: the pinned host's config against this run's, which is the rung
    config x.py dist read (bootstrap writes the --config file there)."""
    excluded = shared.get("excluded")
    this_run = shared.get("this_run_dist") if isinstance(shared.get("this_run_dist"), dict) else {}
    digests = (shared.get("this_run_sha256"), shared.get("pinned_member_table_sha256"),
               shared.get("pinned_member_table_without_host_local_sha256"), this_run.get("sha256"),
               this_run.get("member_table_sha256"), this_run.get("member_table_without_host_local_sha256"))
    require(shared.get("name") == name and shared.get("pinned_sha256") == pinned_sha256
            and all(SHA.fullmatch(str(digest)) for digest in digests)
            and isinstance(shared.get("members"), int) and shared["members"] > 0 and isinstance(excluded, list),
            "fixed-point C13: archive-members.json does not bind the pinned shared source archive and this run's "
            "dist of it by their member tables")
    outside_local = shared["pinned_member_table_without_host_local_sha256"]
    require(this_run["member_table_without_host_local_sha256"] == outside_local,
            f"fixed-point C13: this run's {name} and the pinned one have different member tables outside the "
            f"package-root {SHARED_HOST_LOCAL_MEMBER}: shared_source_members is not identical")
    whole = this_run["member_table_sha256"] == shared["pinned_member_table_sha256"]
    paths = sorted(str((row or {}).get("path")) if isinstance(row, dict) else repr(row) for row in excluded)
    said = join_list(paths)
    require(said == fields["shared_source_members_excluded"],
            f"fixed-point C13: the shared archive's member tables were compared excluding {paths}, and the "
            f"receipt says {fields['shared_source_members_excluded']!r}")
    require(said == ("none" if whole else SHARED_HOST_LOCAL_MEMBER),
            f"fixed-point C13: the member tables are {'equal' if whole else 'different'} whole, and the comparison "
            f"excluded {paths}: {SHARED_HOST_LOCAL_MEMBER} is excluded exactly when it is what differs")
    if not whole:
        [row] = excluded
        require(row.get("pinned_sha256") == shared.get("pinned_host_local_sha256")
                and row.get("this_run_sha256") == this_run.get("host_local_sha256")
                and SHA.fullmatch(str(row.get("pinned_sha256"))) and SHA.fullmatch(str(row.get("this_run_sha256")))
                and row["pinned_sha256"] != row["this_run_sha256"],
                f"fixed-point C13: the excluded {SHARED_HOST_LOCAL_MEMBER} is not the two archives' own member, or "
                "is one file in both: an exclusion must be of a real difference")
        require(row["this_run_sha256"] == fields["rung_config_sha256"],
                f"fixed-point C13: this run's {SHARED_HOST_LOCAL_MEMBER} is not the rung config x.py dist read "
                "(rung_config_sha256)")
    same = "identical" if shared["this_run_sha256"] == shared["pinned_sha256"] else "recompressed-differs"
    require(same == fields["shared_source_bytes"], f"fixed-point C13: shared_source_bytes = "
            f"{fields['shared_source_bytes']!r}, and the digests give {same!r}")


def _check_chain(chain: dict, fields: dict) -> None:
    """C16: the path-free chain summary names the chain the receipt names and
    the two chain compilers as outputs of their rungs."""
    require(chain.get("schema") == CHAIN_SCHEMA and isinstance(chain.get("NOT_A_LINEAGE_RECORD"), str)
            and chain["NOT_A_LINEAGE_RECORD"].strip(),
            "fixed-point C16: chain.json lacks its schema or the NOT_A_LINEAGE_RECORD marker")
    root, rungs = chain.get("root") or {}, chain.get("rungs")
    require(root.get("commit") == fields["root_commit"] and SHA.fullmatch(str(root.get("compiler_sha256")))
            and isinstance(rungs, list) and rungs, "fixed-point C16: chain.json has no root or no rungs")
    # Every compiler the chain ran, by digest, with the commit it is a build of:
    # the root's, then each rung's output. A rung runs only one of them.
    built = {root["compiler_sha256"]: {root["commit"]}}
    commits = [root["commit"]]
    for rung in rungs:
        require(isinstance(rung, dict) and isinstance(rung.get("label"), str)
                and all(COMMIT.fullmatch(str(rung.get(key))) for key in ("commit", "stage0_commit"))
                and all(SHA.fullmatch(str(rung.get(key))) for key in ("stage0_compiler_sha256",
                                                                      "produced_compiler_sha256", "record_sha256")),
                "fixed-point C16: a chain rung is malformed")
        require(rung["stage0_commit"] in {commit for made in built.values() for commit in made},
                f"fixed-point C16: chain rung {rung['label']} was built by {rung['stage0_commit'][:10]}, which no "
                "earlier rung or the root produced")
        require(rung["stage0_commit"] in built.get(rung["stage0_compiler_sha256"], set()),
                f"fixed-point C16: chain rung {rung['label']} ran the compiler {rung['stage0_compiler_sha256'][:16]}, "
                f"which is not the root's or an earlier rung's build of {rung['stage0_commit'][:10]}")
        require(rung.get("rc") == 0 and rung.get("no_stock_evidence") is True,
                f"fixed-point C16: chain rung {rung['label']} is not a clean build (rc {rung.get('rc')!r}, no-stock "
                f"evidence {rung.get('no_stock_evidence')!r}): every rung from the root is a clean Trust build")
        built.setdefault(rung["produced_compiler_sha256"], set()).add(rung["commit"])
        if rung["commit"] not in commits:
            commits.append(rung["commit"])
    require(commits == fields["chain_commits"].split(","), f"fixed-point C16: chain.json's commits "
            f"{[commit[:10] for commit in commits]} are not chain_commits")
    for role in ("producer", "cross_check"):
        commit, digest = fields[f"{role}_stage0_commit"], fields[f"{role}_stage0_compiler_sha256"]
        require(any(rung["commit"] == commit and rung["produced_compiler_sha256"] == digest
                    and rung.get("rc") == 0 and rung.get("no_stock_evidence") is True for rung in rungs),
                f"fixed-point C16: chain.json does not name the {role} stage0 ({digest[:16]}) as the clean output "
                f"of a rung that built {commit[:10]}")
    origin = chain.get("origin") or {}
    stamps = origin.get("provenance")
    lines = origin.get("config_lines")
    require(isinstance(stamps, list) and isinstance(lines, list) and lines
            and {fields["root_commit"], fields["stock_built_ancestor_commit"]}
            <= {str((row or {}).get("reported_commit")) for row in stamps}
            and all(isinstance(line, str) and fields["stock_built_ancestor_commit"][:8] in line for line in lines),
            "fixed-point C16: chain.json's origin does not carry the root's and the stock-built ancestor's build "
            "stamps and the config line naming the ancestor")


def check_archive_joins(seed_root: Path, payloads: dict[str, str], host: str, read_proof, *,
                        archive_root: Path, this_run_shared: Path | None = None) -> int:
    """The full archive-to-evidence join over the real pinned archives (for
    `record`, `verify` and the exit test): each of the eight host archives read
    again and its member table equal to archive-members.json's entry, and the
    shared archive's tables and builder-config equal to what it records. Where
    this run's dist of the shared archive is still there (`record`, on the
    producing host), its tables are read again too. Returns the number of
    members joined."""
    document = load_json(read_proof(seed_root, f"host-proofs/{host}/{EVIDENCE_DIR}/archive-members.json"),
                         "archive-members.json")
    entries = {entry.get("name"): entry for entry in document.get("archives") or [] if isinstance(entry, dict)}
    shared = document.get("shared") or {}
    joined = 0
    for key, digest in sorted(payloads.items()):
        path = archive_root / key
        if "/trust-src-" in key:
            table = shared_tables(path)
            require(_file_sha256(path) == digest, f"fixed-point C13: {path} is not the pinned shared archive")
            recorded = {"members": shared.get("members"),
                        "member_table_sha256": shared.get("pinned_member_table_sha256"),
                        "member_table_without_host_local_sha256":
                            shared.get("pinned_member_table_without_host_local_sha256"),
                        "host_local_sha256": shared.get("pinned_host_local_sha256")}
            require(recorded == table, f"fixed-point C13: the pinned {path.name}'s member table is not the one "
                    "archive-members.json records")
            require(all((row or {}).get("pinned_sha256") == table["host_local_sha256"]
                        for row in shared.get("excluded") or []),
                    f"fixed-point C13: the excluded {SHARED_HOST_LOCAL_MEMBER} is not the pinned {path.name}'s")
            if this_run_shared is not None:
                mine = {"sha256": _file_sha256(this_run_shared), **shared_tables(this_run_shared)}
                require(shared.get("this_run_dist") == mine, f"fixed-point C13: this run's {this_run_shared} read "
                        "again is not the this_run_dist archive-members.json records")
            continue
        table = archive_table(path)
        require(table["sha256"] == digest, f"fixed-point C13: {path} has sha256 {table['sha256']}, and the pin "
                f"is {digest}")
        require(entries.get(path.name) == table, f"fixed-point C13: {path.name} read again is not the member "
                "table archive-members.json records")
        joined += len(table["members"])
    return joined
