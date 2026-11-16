#!/usr/bin/env python3
"""The build half of a first Linux seed: builds of one commit that differ only in stage0.

`src/stage0` pins a seed for aarch64-apple-darwin only (docs/PLAN.md, PKG-S6). A first
Linux seed is admitted from Trust-built compilers alone: the pinned compiler commit is
built on this host by the host chain's newest compiler (the producer), by the archives
made from the producer's own build (the fixed point) and by an older chain compiler
(the cross-check), and the stage2 trees are compared. This script is the part that
builds. It makes one neutral root, runs every build in it through
`seed_staircase.py run` (trap shims, process and build census) and leaves under the
root what a validator needs to judge the builds. Of its own it says only "this build
ended clean" and "these two trees differ in these entries". It admits nothing into the
checkout: it reads the parent's src/stage0 and channel manifest from git and writes a
candidate pin under the root, never bootstrap/trust-stage0 or src/stage0 of a checkout.
Its last steps carry that pin to a branch (`commit`, in a clone under the root, judged
by the branch's own scripts and real door), judge a clone of the branch (`verify`) and
upload this host's archives (`publish`); none of them pushes.

    plan     print every command of setup, the builds, dist and prepare, in order; run nothing
    setup    make the root: the checkout, its base config, every non-Rust input by digest
    build    --role producer | fixed-point | cross-check | control: one build of the commit
    dist     the dist archives and the channel manifest, from the producer's tree
    prepare  join the archives to the parent's pin (prepare.py --merge-existing
             --keep-existing-shared) and install the pinned archives into seed/
    record   the host record and its evidence under prepared/, validated by
             scripts/seed_fixed_point.py with a candidate door (the real one stays empty)
    commit   the add-host branch, in a new clone under the root: the pin, the proofs and
             the one-line door entry, then the corpus re-pin; nothing is pushed
    verify   in a clone of that branch with the 17 archives placed (and nothing else the
             judges read that is not the commit's): both host records through the
             recreator's capture and the real door, the archive join and the push rows;
             --rebuild --produced <root> --work <W> is the package exit test, and writes
             <W>/exit-test.json, bound to the head, receipt and pin it passed with
    publish  --exit-test <W>: the eight Linux archives that exit test passed with, to the
             pin's release, never over other bytes, read back into a new directory and
             checked against the pins
    status   what is done and what is next, read from the files under the root

THE ROOT (default /var/tmp/trust-seed/<the commit's first ten digits>):

    src/                         the checkout, every submodule at its pin. src/bootstrap.toml
                                 is its own seed-mode base config; src/build is the build
    home/                        HOME of every step; empty when x.py starts
    tools/ninja                  the one declared non-Rust build tool (`run --tool-dir`)
    stage0/  stage0.json         the compiler the current role builds from: always at this
                                 path, so one rung config serves every role. An earlier
                                 role's copy stays beside it as stage0.<label>/ (+ .json)
    seed/                        the pinned archives as installed: stage0 of fixed-point and
                                 control, used only as kept/prepare.json records it
    prepare/admit-dist/          `stage-artifacts` of dist/ (the trustc-dev handoff's source)
    prepare/admit-pinned/        `stage-artifacts` of the five pinned archives seed/ is installed from
    prepare/installed.json       seed/ is whole (an install stopped before it is made again)
    prepare/seed-surface.json    `validate-seed` of seed/
    prepare/stage0.candidate     the candidate src/stage0: the parent's head, prepare.py's section
    prepare/archive-members.json each pinned host archive's installed files, joined to p.stage2.json
    prepare/<step>.out .err      what each helper printed
    prepared/bootstrap/trust-stage0/  prepare.py's output root: the parent's pinned archives and
                                 this host's, the two-host channel manifest, the admission, the
                                 record of the shared archive kept; prepared/src-stage0 its section
    kept/prepare.json            prepare's record: every input and output by digest
    inputs/inputs.json           what setup measured; its presence says setup is done
    inputs/sources.json          where setup copied from (host-local: the invoker's paths), one
                                 key per part of setup, written when that part is done
    inputs/seed-config.json      `seed_staircase.py seed-config` output (the base config's sha256)
    inputs/lean/<toolchain>/     the copy of the Lean toolchain the Clean pin names
    inputs/clean-lean-inputs.json   `mint_seed_support.py clean-lean-inputs` of that copy
    inputs/cargo-home-inputs.json   `mint_seed_support.py cargo-home-inputs` (names its source)
    ledger/                      the one staircase ledger: trap/, trap.log, pathbin/, tmp/,
                                 logs/, rungs.jsonl, cargo-home/, rung.bootstrap.toml, and per
                                 label <label>.admission.json, .run.json, .run.stderr, .closure.log
    kept/<label>.attempt.json    what a build was given, written before x.py starts
    kept/<label>.native-before.json  .native-after.json   every ELF and ar file of LLVM and lld
    kept/<stem>.build.json       a role's clean build (stems p, f, s, c1, c2, c3)
    kept/<stem>.stage2.json      that build's stage2 manifest (trust-stage2-tree-v1)
    kept/<label>.not-clean.json  a build that ended, and not clean
    kept/<label>-tree/           an earlier build's whole tree, moved out of src/build
    kept/<label>-unfinished/     the tree of a build that did not end clean
    kept/<label>.home-before/  .tmp-before/  .cargo-trust-before/   what an earlier step left
                                 in home/, ledger/tmp/ and the cargo home's trust/ (the
                                 compiler's Clean fact store), set aside so `label` starts
                                 with none of it
    kept/current-tree.json       which label's tree is in src/build
    kept/dist.json  dist/        the dist step's record and a copy of what it packaged
    kept/dist.not-clean.json     a dist that ran and is not usable; with
    kept/p-after-dist.stage2.json   the producer's stage2 as dist left it, when it moved
    prepared/bootstrap/trust-stage0/host-proofs/<host>/   `record`'s output: SEED-FIXED-POINT,
                                 seed-surface.json, host-record.json, fixed-point/ (tracked
                                 copies: the account's home is <home> and its login <account>)
    record/raw/                  each evidence file as this host holds it (host-local, never tracked)
    record/staging/              a record proposed and refused by its validator, kept to read
    kept/record.json             `record`'s own record: the candidate door, every raw digest
    commit/repo/                 `commit`'s clone of this script's checkout, holding the branch
    commit/work/                 its private files (messages, blobs); never tracked
    kept/commit.json             `commit`'s record: the parent, both commits, every path
    publish/download[-N]/        `publish`'s read-back of the release, one new directory a run
    kept/publish.json            `publish`'s record: what was uploaded, what was read back
    driver.lock                  held by the one step that is running

LABELS. Every x.py invocation has its own: p-build, then p-dist, p-full and
p-manifest-tool (the dist step), f-build, s-build, c1-build .. c3-build. A label is
used once: a build that is started again is <label>-2, then <label>-3.

WHAT THE ROLES SHARE. The four roles differ only in the compiler copied to stage0/ and
in the label. Before a build starts, the checkout, the base and rung config, the build
line, the job count, the linker setting, the driver's environment, the tool directory,
the cargo home's three input trees, the Lean copy, the host's C toolchain (cc, c++, ld,
cmake, make and python by role, and every host tool the base config names by its path: the
build runs /usr/bin/gcc where the config says so, not cc), whether the compiler may
keep Clean kernel facts under the cargo home, the jobserver, and the bytes of the two
scripts that write the build's trap shims, environment and config tail
(seed_staircase.py, linux_refresh_toolchain.py) are measured again and compared with
what setup and every earlier role recorded; a difference is a refusal and nothing is
started. A root set up before setup measured the config's host tools has no row for
them and builds nothing more. Every role starts with an empty home/, ledger/tmp/ and no
cargo-home/trust/.

THE JOBSERVER (docs/OPEN_ISSUES.md BOOTSTRAP-JOBSERVER-PROBE-1). Every x.py run of a root
(the four roles, the three dist runs, and both legs of verify --rebuild) is given a FIFO
jobserver: `seed_staircase.py run --fifo-jobserver` makes ledger/tmp/jobserver.fifo with
jobs - 1 tokens, holds it for the run and hands x.py MAKEFLAGS="-j<jobs>
--jobserver-auth=fifo:<path>", which Bootstrap forwards to Cargo. Without it the
cross-check's Cargo (29ebb403de) gives build scripts a pipe jobserver by descriptor
number, Trust std hands their compiler probes fds 0-2 only, and the bootstrap shim
refuses each probe: the build dies of SIGPIPE or silently loses a cfg. GNU make before
4.4 (this host's 4.3) stops on the fifo: spelling, and openssl-sys's build script hands
make the jobserver that way, so the run also puts ledger/pathbin/make first on x.py's
PATH: an adapter that hands the host's make the FIFO as two descriptors on it. setup
records the arrangement in inputs.json and the make among the host tools; every role and
dist compares both, and a run record that does not show them is not clean: MAKEFLAGS, the
FIFO, the job count and its tokens, a path still the FIFO's when x.py had exited, every
token back, and the adapter seed_staircase.py writes for the record's python and the make
setup bound. A count at the end that is not jobs - 1 means a process ended holding a
token or something wrote one it never took; the build is then not clean (`--again` runs
it anew), and its records keep the count. One deficit is excused, SEED-TOKEN-LEAK-STAGE0-1
(docs/DECISION_QUEUE.md): a trustc built from a commit that does not contain d57cafb60f7
can exit holding a token (docs/OPEN_ISSUES.md RUSTC-FRONTEND-TOKEN-LEAK-1), so a run whose
stage0 commit, as its admission records it, is a host chain commit
(seed_fixed_point.CHAIN_COMMITS) that git in this script's checkout says does not contain
that fix, and that the validator's TOKEN_LEAK_STAGE0_COMMITS names, may end short when x.py
exited 0, its process census ended watched-exited with no abandoned child, the FIFO's path
was unchanged and the count is not below none. The build record keeps what was decided
(`jobserver_token_deficit`), and the receipt names the run in jobserver_token_deficits. A
surplus, and a deficit under any other stage0, stays not clean. Every dist run, like every
role, starts with an empty ledger/tmp, so a FIFO a killed run left is set aside, not in the
way. A root set up before this arrangement records none and builds nothing more: its
earlier builds ran without one.

THE ACCOUNT. A root whose path names the invoking account is refused: every record
names the root many times. Nothing else is refused for it, because this host's
evidence names the account whatever the driver does (the chain compilers' std carries
their build paths, which the staircase's census records, and their rust-src links
point into the home). Each build record, dist.json and inputs.json list instead where
the account is named (`account_named_in`), without spelling it, for `record` to judge.

EVERY STEP IS RESUMABLE. A step that is done says so and is not repeated. A build that
was interrupted is started again under the next label, from an empty build directory
(for every role but the producer: plus the producer's LLVM and lld). A build that
ended and was not clean is started again only with `--again`. A run that ended while
this script was not there to read it (killed without passing the stop on) left its
whole record under `.partial`, and is judged from it, not run again. An argument a
part of setup refused can be given right under the same root; one that a finished
part used cannot be changed.

PREPARE (design step 9) admits only a dist that finished clean (dist.json, no
dist.not-clean.json, dist/ still its archives). It reads the parent's src/stage0 and
channel manifest at --parent from this script's checkout (the manifest by the hash the
pin names) and hashes the parent's pinned archives in --cohort against their rows; it
never unpacks or runs one. prepare.py keeps the parent's shared trust-src (only the
package-root builder-config may differ, see prepare.py) and adds this host's eight
archives. seed/ is installed from the PINNED archives, not from dist/: prepare.py
strips names the pin forbids (bin/rustdoc of the trustc archive, measured on this
host), so dist/ as installed is not the pin as installed. Each installed bin/, lib/,
libexec/ file must be the producer's stage2 row at its path (an elf or ar file with no
row refuses), and every file of seed/ must be a pinned member, byte for byte, but the
installer's own bookkeeping under lib/rustlib. Each part is whole or redone: admit-*
and prepared/ are made under `.partial` and renamed, seed/ is whole once
installed.json is written; a refusal writes no kept/prepare.json, and no role builds
from seed/ without it.

RECORD (design step 13) writes the record only from a root where the producer, dist,
prepare, the fixed point, the cross-check and every control a difference needed are
built clean, and refuses with the command of the first step that is not. It reads the
evidence from the files above (each checked against the digest its step recorded),
the host chain's CHAIN-UNPINNED-ROOT.json (--chain) and the origin's build stamps and
config (--origin-provenance, --origin-config). THE ACCOUNT, for it: every tracked copy
has the invoking account's home replaced by `<home>` and its login by `<account>`; the
raw file's sha256 and the count replaced go into the receipt, the raw file stays in
record/raw/, and a tracked file that still names the account (an escaped spelling, the
surface) or any other personal home is refused, as is an account the validator could
not search for. inputs.json must still be the bytes every build and prepare recorded.
Each host tool the base config names is bound in the tracked inputs.json as setup
measured it ("measured": "setup", only when every build's record was held to that
same row), or, for a root set up before setup measured these, measured by `record`
itself ("measured": "record", only when no build was held to a row for it); the
receipt's config_host_tools lists which. It writes nothing under prepared/ until the validator
(seed_host_ledger.capture_fixed_point_record, every rule, with a door naming this
receipt held in memory, and seed_fixed_point.check_archive_joins over the real
archives and this run's dist of the shared trust-src) accepts what it proposes. It never edits the door, src/stage0, the seed
ledger or a checkout.

COMMIT (design step 14) builds the add-host branch in a new clone of this script's
checkout under the root (<root>/commit/repo, made as commit.partial and renamed when
whole), never in a checkout a person works in; it writes no object, ref, index or file
there. --parent must be the commit `prepare` joined (kept/prepare.json), or a
descendant of it whose src/stage0 and bootstrap/trust-stage0 are the same objects;
anything else is a refusal that says to prepare again. Before writing it holds the
parent to the design's transaction rules (T2-T6, T8, T10-T12): the parent pins the
commit and not this host, history never pinned this host with other digests, the
parent ledger is one mint record of the commit, the candidate is the parent's pin
plus exactly this host's eight rows and one new manifest hash, every pinned archive is
in prepared/ with its pinned bytes, the orchestration commit is an ancestor of the
parent and holds the seed_staircase.py the runs recorded, and the Darwin pack state is
given. Commit 1 carries exactly the pin (src/stage0, the four channel manifest files,
the admission), seed-ledger.toml rendered with every host in its title and the
`[release.mint]` compatibility line aterm's seed-pin switch reads, the Linux proofs
and evidence, and the one-line door entry (host, commit, receipt sha256) in
scripts/seed_host_ledger.py. In the clone, both host records are then captured by the
branch's own seed_host_ledger.py with that real door (the Darwin one against the
parent's pins too). Commit 2 is `check_corpus_membership.py --write` run there at
commit 1, which must add exactly the new tracked .json and .toml and drop nothing.
The branch is created (create-only) only when both commits hold and its path list is
exactly the expected one. kept/commit.json records it.

VERIFY (design step 15) runs in a clone of the branch (--repo, default this script's
checkout), with the 17 pinned archives placed under bootstrap/trust-stage0/dist/<date>/.
It judges with the clone's own scripts: every pinned archive by its pin and no other
archive there, the real door names this receipt, recreate_bootstrap's
capture_validated_seed_lineage for this host and for the cohort's mint host (no errors,
an internal admission, both records), the full archive join, then
check_seed_freshness.py, check_ledger_pins.py --rev and check_corpus_membership.py
--rev: any red is a refusal. It writes nothing in the clone. `verify --rebuild
--produced <root> --work <dir>` (design step 16) adds two builds: leg 1 builds the
clone's own source in seed mode from the pinned archives and requires a validated
capture and a lineage whose root names the fixed-point admission; leg 2 makes the root
again at the recorded build_root (the produced one moved aside, named by --produced),
regenerates both configs and compares their digests, copies the produced LLVM and lld,
builds the commit from the pinned archives as installed, and compares its stage2 with
the receipt's rows outside not_reproduced. Native outputs that are not the recorded
ones exit 3, "not comparable", which is not a pass. Each part is done once (its file
under --work or the replay root says so).

PUBLISH (design step 17) reads the release repo and tag from the branch's ledger, holds
each of this host's eight archives in prepared/ to the branch's pins, lists the
release's assets with agh, refuses an asset of the same name that holds other bytes
(or whose bytes agh cannot say), uploads the rest with `agh release upload` (never
--clobber, and nothing is ever deleted), lists again, downloads each into a new empty
directory under <root>/publish and checks its sha256 against the pin. Only then does
it print the landing step. It runs agh with the invoker's own environment (agh holds
the credential); --agh names the executable.

EXTENSION POINTS. `scout` (design steps 2-4) is not in this script and is not stubbed:
it is absent from the parser.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: select the supported interpreter before importing stdlib tomllib.
# Imported helpers retain their authenticating driver's interpreter.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_os.execv(_floor_path, [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]])
    _floor_sys.exit("fixed_point_linux_seed.py requires Python 3.11+ (tomllib); none found on PATH")

import argparse
import ast
import contextlib
import fcntl
import functools
import hashlib
import json
import os
import platform
import pwd
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tarfile
import time
import tomllib
import types
from pathlib import Path

HERE = Path(__file__).resolve().parent
# Nothing is written outside the root, the script's own directory included: without
# this, importing the two sibling modules leaves their bytecode beside them (a `plan`
# started as `python3 scripts/fixed_point_linux_seed.py plan` wrote
# scripts/__pycache__/linux_refresh_toolchain.*.pyc). Every Python this script starts
# is started with -B.
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
try:
    import linux_refresh_toolchain as refresh
finally:
    sys.path.remove(str(HERE))

Refusal = refresh.Refusal
STAIRCASE = HERE / "seed_staircase.py"
MINT_SUPPORT = HERE / "mint_seed_support.py"
# The scripts whose bytes a build record names.
DRIVER_SCRIPTS = ("fixed_point_linux_seed.py", "seed_staircase.py", "mint_seed_support.py",
                  "linux_refresh_toolchain.py")
# Of those, the ones that hand the build what it is given (trap shims, environment,
# config tail) and judge its run: compared across roles. This script gains its later
# subcommands between roles, and mint_seed_support.py only measures, so those two are
# recorded and not compared.
GIVEN_BY = ("seed_staircase.py", "linux_refresh_toolchain.py")
# Where the compiler keeps Clean kernel facts under a cargo home (crates/trust-certify
# src/clean_fact.rs at the commit: no flag moves or disables it).
FACT_STORE = ("trust", "results", "v1", "clean-kernel-facts-v1")
# The closure checker's own refusal line (scripts/bootstrap_dependency_closure.py).
CLOSURE_REFUSED = "bootstrap dependency closure REFUSED:"

# The compiler commit of the 2026-11-07 pin.
COMMIT = "82bb867eddb94599f68194f701c766f2b6f5a02f"
# Resolve only the system temporary directory; a linked trust-seed/root still refuses.
ROOT_PARENT = Path("/var/tmp").resolve() / "trust-seed"
# Where this host's chain and ledger are (docs/SEED_STAIRCASE.md); `~` is the invoker's home.
PRODUCER_STAGE0 = "~/linux-selfhost-20261106/r3-stage2"
CROSS_CHECK_STAGE0 = "~/linux-selfhost-20261106/r2-29ebb403de/build/{host}/stage2"
CARGO_HOME_SOURCE = "~/linux-selfhost-20261110/cargo-home"
NINJA_SOURCE = "~/linux-selfhost-20261110/tools/ninja"

# The x.py words of every compared build. A bare `x.py build` is stage 1 here, so
# every invocation names its stage.
BUILD_LINE = ("build", "--stage", "2", "compiler/rustc", "library/std")
STEMS = {"producer": "p", "fixed-point": "f", "cross-check": "s"}
ROLES = (*STEMS, "control")
CONTROL_LIMIT = 3
# The only stage2 files a build by the pinned seed may fail to reproduce (the
# 43f29371e7 ThinLTO fix is not an ancestor of the commit).
UNREPRODUCED_ALLOWED = ("bin/targo-trust", "bin/ty")
# The dist step's x.py runs after the component list is read from the checkout
# (the order of scripts/mint_and_prove_seed.sh): dist, then the full build that
# puts stage2 back, then the tool that writes the channel manifest.
DIST_LABELS = ("p-dist", "p-full", "p-manifest-tool")
DIST_SERVER = "https://trust.invalid"
CHANNEL = "trust"
ASSET_LIMIT_BYTES = 2 * 1024 ** 3
STEP_USER = "trust-seed"
# What x.py and its python leave in a checkout that git ignores: the base config,
# the build, its own build-lock state, and `__pycache__/` directories. Anything else
# ignored is a refusal. (x.py's lock state is its own and is left where it is.)
IGNORED_ALLOWED = ("bootstrap.toml", "build/", ".trust-build-lock/", ".trust-build-lock.breaks",
                   ".trust-build-lock.guard")
INPUTS_SCHEMA = "trust-fixed-point-linux-seed-inputs-v1"
BUILD_SCHEMA = "trust-fixed-point-linux-seed-build-v1"
NATIVE_SCHEMA = "trust-fixed-point-linux-seed-native-outputs-v1"
DIST_SCHEMA = "trust-fixed-point-linux-seed-dist-v1"
PREPARE_SCHEMA = "trust-fixed-point-linux-seed-prepare-v1"
MEMBERS_SCHEMA = "trust-fixed-point-linux-seed-archive-members-v1"
RECORD_SCHEMA = "trust-fixed-point-linux-seed-record-v1"
# `record` (design step 13). The host chain and the origin evidence it summarises
# in chain.json, as this host keeps them (`~` is the invoker's home).
CHAIN_RECORD = "~/linux-selfhost-20261106/CHAIN-UNPINNED-ROOT.json"
ORIGIN_PROVENANCE = ("~/trust-linux-ay-seal-6986546e-20260928/artifacts/trust-6986546e/PROVENANCE",
                     "~/toolchains/trust-ec2b5c59/PROVENANCE")
ORIGIN_CONFIG = "~/trust-linux-ay-bootstrap-config-proposal.toml"
# What names the chain root's builder (N2) and why bin/targo-trust and bin/ty may
# differ (N5) are fixed words of the validator (seed_fixed_point.py
# STOCK_ANCESTOR_TOOLCHAIN, NOT_REPRODUCED_HYPOTHESIS): a receipt cannot say more.
# prepare (design step 9). The preparer is this checkout's: it has --keep-existing-shared.
PREPARE_PY = HERE.parent / "src" / "tools" / "trust-stage0-dist" / "prepare.py"
# Where the parent's pinned archives were fetched to (read as data: hashed, copied).
COHORT_DIR = ROOT_PARENT / "cohort"
PARENT_MANIFEST = "bootstrap/trust-stage0/dist/{date}/channel-rust-trust.toml"
# The CPU is shared with other builds: prepare.py repacks at most this many archives at once.
ARCHIVE_JOBS = 6
# What rust-installer's install.sh writes under the prefix that no archive member is.
INSTALLER_BOOKKEEPING = re.compile(
    r"lib/rustlib/(components|rust-installer-version|uninstall\.sh|install\.log|manifest-[A-Za-z0-9._-]+)")
# An installed file of these kinds is code: it must have the producer's stage2 row.
CODE_KINDS = ("elf", "ar")
INSTALLED_TOPS = ("bin/", "lib/", "libexec/")
# commit, verify, publish (design steps 14-17).
COMMIT_SCHEMA = "trust-fixed-point-linux-seed-commit-v1"
PUBLISH_SCHEMA = "trust-fixed-point-linux-seed-publish-v1"
EXIT_TEST_SCHEMA = "trust-fixed-point-linux-seed-exit-test-v1"
SEED_DIR = "bootstrap/trust-stage0"
LEDGER_FILE = f"{SEED_DIR}/seed-ledger.toml"
ADMISSION_FILE = f"{SEED_DIR}/trust-stage0-admission.json"
# The four channel manifest files a pin carries, `{date}` its date.
MANIFEST_FILES = ("dist/channel-rust-trust.toml", "dist/channel-rust-trust.toml.sha256",
                  "dist/{date}/channel-rust-trust.toml", "dist/{date}/channel-rust-trust.toml.sha256")
# THE DOOR, as it lands (empty) and as the add-host commit rewrites that one line.
DOOR_FILE = "scripts/seed_host_ledger.py"
EMPTY_DOOR_LINE = "FIXED_POINT_FIRST_HOSTS: dict[str, dict[str, str]] = {}"
DOOR_PREFIX = "FIXED_POINT_FIRST_HOSTS: dict[str, dict[str, str]] = "
CORPUS_SCRIPT = "scripts/check_corpus_membership.py"
# Each corpus by the suffix its rule selects (check_corpus_membership.CORPORA): the
# JSON rule takes files under 1 MiB, outside first-party/ and vendor/.
CORPUS_MANIFESTS = {".json": "crates/trust-json/tests/corpus_manifest.txt",
                    ".toml": "crates/trust-toml/tests/corpus_manifest.txt"}
CORPUS_EXCLUDED = ("first-party/", "vendor/")
CORPUS_JSON_CAP = 1 << 20
DARWIN_PACK_STATES = ("published", "not-published")
# What the clone checks out of commit 1 to judge it: the scripts that judge (and the
# identity module mint_seed_support.py loads at import), the pin, the corpus manifests.
COMMIT_VIEW = ("scripts", "src/stage0", "src/bootstrap/stage0_identity.py", SEED_DIR,
               *CORPUS_MANIFESTS.values())
# What verify's judges read from a clone's working tree, held there to the commit's
# bytes (view_problems): every judge and its libraries, the seed directory and
# bootstrap/'s root records, the pin, and what check_seed_freshness.py reads beside it.
VERIFY_VIEW = ("scripts", "bootstrap", "src/stage0", "src/rust-compat-version", "src/bootstrap/stage0_identity.py")
# prepare.py's STAGE0_ADMISSION_SCHEMA, the admission a branch carries.
ADMISSION_SCHEMA = "trust.stage0-payload-root-admission.v1"
BRANCH_NAME = re.compile(r"[A-Za-z0-9._/-]+")
IDENTITY = re.compile(r"(.+?) <([^<>\s]+@[^<>\s]+)>")
# verify --rebuild (design step 16).
SEED_LABEL = "verify-seed"
REPLAY_LABEL = "replay-build"
SEED_BUILD_JOBS = 20


class NotComparable(Refusal):
    """verify --rebuild: the replay's native outputs are not the record's, so its
    stage2 cannot be compared with the receipt. Exit 3, which is not a pass."""


def say(text: str) -> None:
    print(f"fixed-point-linux-seed: {text}", flush=True)


# ---------------------------------------------------------------------------
# small helpers


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def rows_sha256(rows: list[dict]) -> str:
    """One digest of a table: each row as one canonical JSON line (the rule of
    `mint_seed_support.records_sha256`)."""
    digest = hashlib.sha256()
    for row in rows:
        digest.update(json.dumps(row, separators=(",", ":"), sort_keys=True).encode("utf-8") + b"\n")
    return digest.hexdigest()


def read_json(path: Path, what: str) -> dict:
    try:
        value = json.loads(path.read_text())
    except OSError as error:
        raise Refusal(f"{what} cannot be read: {path}: {error.strerror or error}") from error
    except ValueError as error:
        raise Refusal(f"{what} is not JSON: {path}: {error}") from error
    if not isinstance(value, dict):
        raise Refusal(f"{what} is not a JSON object: {path}")
    return value


def write_json(path: Path, value: object) -> None:
    """Visible under its name only when whole."""
    partial = path.with_name(path.name + ".partial")
    partial.write_text(json.dumps(value, indent=1, sort_keys=True) + "\n")
    partial.replace(path)


def brief(value: object, limit: int = 160) -> str:
    text = json.dumps(value, sort_keys=True)
    return text if len(text) <= limit else text[:limit] + " ..."


def account_of_invoker() -> tuple[str, str]:
    """(home, login) of whoever started this script, read before its environment is replaced."""
    try:
        entry = pwd.getpwuid(os.getuid())
        return entry.pw_dir, entry.pw_name
    except KeyError:
        return os.environ.get("HOME", ""), os.environ.get("USER", "")


def names_account(text: str, account: tuple[str, str]) -> str | None:
    """The account's home or login as `text` spells it, or None. The login is
    found where seed_fixed_point.login_pattern finds it (where it starts a word
    and no letter continues it), so what `record` checks and what the validator
    searches for agree."""
    home, login = account
    if len(home) > 1 and home in text:
        return home
    if login and re.search(rf"(?<![A-Za-z0-9]){re.escape(login)}(?![A-Za-z])", text):
        return login
    return None


def account_mentions(value: object, account: tuple[str, str]) -> list[str]:
    """Where a JSON value spells the account's home or login, without spelling it:
    dotted keys, `[]` for any element of a list, `<key>` for a key that names it."""
    found: set[str] = set()

    def walk(item: object, at: str) -> None:
        if isinstance(item, dict):
            for key, inner in item.items():
                step = "<key>" if names_account(str(key), account) else str(key)
                if step == "<key>":
                    found.add(f"{at}.<key>".lstrip("."))
                walk(inner, f"{at}.{step}")
        elif isinstance(item, list):
            for inner in item:
                walk(inner, f"{at}[]")
        elif isinstance(item, str) and names_account(item, account):
            found.add(at.lstrip(".") or "(the whole value)")

    walk(value, "")
    return sorted(found)


def account_links(top: Path, account: tuple[str, str]) -> list[str]:
    """The symbolic links under `top` whose target names the account (a chain
    compiler's lib/rustlib/src/rust points into the worktree it was built in)."""
    found = []
    for directory, dirnames, filenames in os.walk(top):
        dirnames.sort()
        for name in sorted(dirnames + filenames):
            path = Path(directory) / name
            if path.is_symlink() and names_account(os.readlink(path), account):
                found.append(path.relative_to(top).as_posix())
    return found


def fact_store_state(cargo_home: Path) -> dict:
    """Whether the compiler keeps Clean kernel facts under `cargo_home` when a build
    starts: the rule of `private_root` in crates/trust-certify/src/clean_fact.rs at the
    commit. The deepest part of the store's path that exists is resolved, and it and
    every ancestor must be this user's or root's and writable by no one else; else
    there is no store and every elaboration is checked afresh. Every build starts with
    cargo-home/trust set aside, so that deepest part is the cargo home (or, before
    setup made it, its deepest ancestor that exists): what an earlier step left under
    trust/ is not what the next build sees, and is not measured."""
    existing = cargo_home
    while not os.path.lexists(existing) and existing != existing.parent:
        existing = existing.parent
    real = Path(os.path.realpath(existing))
    for ancestor in (real, *real.parents):
        info = os.stat(ancestor)
        if info.st_uid not in (os.geteuid(), 0) or info.st_mode & 0o022:
            return {"kept": False, "because": f"{ancestor} is group- or world-writable, or another user's"}
    return {"kept": True, "because": None}


def fact_store_words(state: dict, cargo_home: Path) -> str:
    if state["kept"]:
        return (f"the compiler keeps Clean kernel facts under {cargo_home.joinpath(*FACT_STORE)}; every role starts "
                "with none (what a step left there is set aside into kept/<label>.cargo-trust-before)")
    return (f"the compiler keeps no Clean kernel facts under {cargo_home} ({state['because']}), so no role "
            "imports another's")


def closure_reason(text: str) -> tuple[str, bool]:
    """(the closure checker's own reason, whether it ran out of its time budget).
    Its last lines are a `prepare` command for a person to run, which fetches: that
    is not the reason, and this script does not repeat it."""
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    refused = [line for line in lines if line.startswith(CLOSURE_REFUSED)]
    reason = refused[-1] if refused else refresh.last_line(text)
    return reason, bool(re.search(r"budget expired|deadline", reason))


@functools.lru_cache(maxsize=None)
def staircase():
    """scripts/seed_staircase.py as a module (`tool_dir_record`, `mint_support`)."""
    sys.path.insert(0, str(HERE))
    try:
        import seed_staircase
    finally:
        sys.path.remove(str(HERE))
    return seed_staircase


def jobserver_arrangement(ledger: Path, jobs: int) -> dict:
    """The FIFO jobserver `seed_staircase.py run --fifo-jobserver` gives every x.py run
    of `ledger` for `jobs` (THE JOBSERVER, at the top): its path and MAKEFLAGS as that
    script spells them, and the tokens it preloads."""
    module = staircase()
    path = module.fifo_jobserver_path(ledger)
    return {"kind": "fifo", "path": str(path), "jobs": jobs, "tokens": jobs - 1,
            "makeflags": module.fifo_jobserver_makeflags(path, jobs),
            "make_adapter": str(module.make_adapter_path(ledger))}


def same(value: object, wanted: object) -> bool:
    """Equal and of one type: JSON's true is not the count 1."""
    return type(value) is type(wanted) and value == wanted


# What the stage0 condition of SEED-TOKEN-LEAK-STAGE0-1 says of a run whose admission was
# not judged (the verify --rebuild legs): it is not met.
TOKEN_STAGE0_NOT_JUDGED = ("no stage0 admission was judged for this run, and the rule excuses only a run whose "
                           "admitted stage0 is a host chain compiler that does not contain the fix")
# How git is asked whether a stage0 contains the fix: of the commits as they are, not as a
# replace ref or a graft file says they are (either can hide the fix from a commit that
# contains it; a shallow history, which can too, is refused outright).
TOKEN_LEAK_GIT_ENV = {"GIT_NO_REPLACE_OBJECTS": "1", "GIT_GRAFT_FILE": os.devnull}


def token_leak_stage0(plan: Plan, admission: dict | None, record: dict) -> tuple[bool, str]:
    """SEED-TOKEN-LEAK-STAGE0-1's stage0 condition (THE JOBSERVER, at the top), decided
    from the run's admission and git: (True, why) when the admission is still the file
    the run was given (`admission`: its path and sha256), the stage0 commit it records is
    the one the run record names and one of the host chain's
    (seed_fixed_point.CHAIN_COMMITS), git in this script's checkout (whole, and read
    without replace refs or grafts) answers that the fix is not its ancestor, and the
    validator's TOKEN_LEAK_STAGE0_COMMITS names it too; (False, why not) otherwise, and
    whenever git cannot answer. The validator, which runs no git, decides it from that set
    alone, so this never excuses a run the validator would refuse."""
    module = validator()
    fix = module.TOKEN_LEAK_FIX_COMMIT
    path = Path(str((admission or {}).get("path")))
    try:
        given = sha256_file(path) == (admission or {}).get("sha256")
        commit = json.loads(path.read_text()).get("commit") if given else None
    except (OSError, ValueError, AttributeError):
        return False, f"its admission {path} cannot be read as the stage0 admission it was given"
    if not given:
        return False, f"its admission {path} is not the file the run was given"
    if record.get("stage0_commit") != commit:
        return False, (f"the run record's stage0_commit {brief(record.get('stage0_commit'))} is not its "
                       f"admission's {brief(commit)}")
    if not isinstance(commit, str) or commit not in module.CHAIN_COMMITS:
        return False, (f"its stage0 commit {brief(commit, 60)} is not one of the host chain's "
                       f"({', '.join(chain[:10] for chain in module.CHAIN_COMMITS)})")
    repo = plan.source_repo()
    env = {**os.environ, **TOKEN_LEAK_GIT_ENV}
    shallow = git_call(repo, "rev-parse", "--is-shallow-repository", env=env)
    said = shallow.stdout.decode("utf-8", "replace").strip()
    if shallow.returncode or said != "false":
        return False, (f"git in {repo} answers {said[:40]!r} (exit {shallow.returncode}) to rev-parse "
                       f"--is-shallow-repository, not 'false': a shallow history cannot show whether {commit[:10]} "
                       f"contains {fix[:10]}")
    for rev in (fix, commit):
        held = git_call(repo, "rev-parse", "--verify", "--quiet", f"{rev}^{{commit}}", env=env)
        if held.returncode or held.stdout.decode("utf-8", "replace").strip() != rev:
            return False, (f"git in {repo} does not hold {rev[:10]}, so whether {commit[:10]} contains "
                           f"{fix[:10]} is not known")
    answer = git_call(repo, "merge-base", "--is-ancestor", fix, commit, env=env).returncode
    if answer == 0:
        return False, f"its stage0 {commit[:10]} contains {fix[:10]} (git in {repo})"
    if answer != 1:
        return False, f"git in {repo} could not say whether {commit[:10]} contains {fix[:10]} (it exited {answer})"
    if commit not in module.TOKEN_LEAK_STAGE0_COMMITS:
        named = ", ".join(chain[:10] for chain in module.TOKEN_LEAK_STAGE0_COMMITS)
        return False, (f"git in {repo} says {commit[:10]} does not contain {fix[:10]}, but the validator's "
                       f"TOKEN_LEAK_STAGE0_COMMITS ({named}) does not name it, and this script excuses no stage0 "
                       "the validator would refuse")
    return True, f"its stage0 {commit[:10]} is a host chain commit that does not contain {fix[:10]} (git in {repo})"


def token_deficit_judged(record: dict, tokens: int, stage0: tuple[bool, str] | None) -> dict | None:
    """SEED-TOKEN-LEAK-STAGE0-1 for a run record whose FIFO was preloaded with `tokens`:
    None when it did not come back short of them; otherwise the rule, the counts, what
    was decided of its stage0 (`stage0`, token_leak_stage0's answer; None is a no) and
    the conditions it does not meet (seed_fixed_point.token_deficit_unexcused), none
    when the deficit is excused."""
    module = validator()
    held = record.get("jobserver") if isinstance(record.get("jobserver"), dict) else {}
    deficit = module.token_deficit(record) if same(held.get("tokens"), tokens) else None
    if deficit is None:
        return None
    lacks_fix, decided = stage0 if stage0 is not None else (False, TOKEN_STAGE0_NOT_JUDGED)
    return {"rule": module.TOKEN_LEAK_RULE, "issue": module.TOKEN_LEAK_ISSUE, "given": deficit[0],
            "returned": deficit[1], "stage0": decided,
            "unmet": module.token_deficit_unexcused(record, lacks_fix, decided)}


def token_leak_judgement(plan: Plan, admission: dict | None, record: dict,
                         inputs: dict) -> tuple[tuple[bool, str] | None, dict | None]:
    """(the stage0 decision, the judgement) of SEED-TOKEN-LEAK-STAGE0-1 for a run of this
    root given `admission`; (None, None) when its jobserver did not come back short."""
    tokens = plan.jobserver(inputs["jobs"])["tokens"]
    if token_deficit_judged(record, tokens, None) is None:
        return None, None
    stage0 = token_leak_stage0(plan, admission, record)
    return stage0, token_deficit_judged(record, tokens, stage0)


def token_deficit_accepted(label: str, judged: dict) -> str:
    """The words of a deficit SEED-TOKEN-LEAK-STAGE0-1 excused."""
    return (f"{label}: its jobserver held {judged['returned']} of the {judged['given']} token(s) when x.py had exited, "
            f"and {judged['rule']} accepts it ({judged['issue']}: a trustc without the fix can exit holding a token): "
            f"{judged['stage0']}; x.py exited 0, its process census ended watched-exited with no abandoned child, "
            "and the FIFO's path was unchanged. Its records keep the count, and the receipt names the run in "
            "jobserver_token_deficits")


def jobserver_problems(record: dict, arrangement: dict, stage0: tuple[bool, str] | None = None) -> list[str]:
    """Why a `seed_staircase.py run` record does not show the FIFO jobserver
    `arrangement` (empty: it does). A count of tokens at the end that is not the
    count preloaded is a problem (seed_staircase.FifoJobserver says what it means),
    but for a deficit SEED-TOKEN-LEAK-STAGE0-1 excuses; `stage0` is
    token_leak_stage0's answer for the run (None: not judged, so not excused)."""
    problems = []
    flags = (record.get("environment") or {}).get("MAKEFLAGS")
    if flags != arrangement["makeflags"]:
        problems.append(f"the build's MAKEFLAGS was {flags!r}, not {arrangement['makeflags']!r}")
    held = record.get("jobserver")
    if not isinstance(held, dict):
        return problems + ["the run record shows no jobserver: x.py was not given the FIFO jobserver every run of "
                           "this root is given (seed_staircase.py run --fifo-jobserver)"]
    problems += [f"its jobserver's {key} was {held.get(key)!r}, not {arrangement[key]!r}"
                 for key in ("kind", "path", "jobs", "tokens") if not same(held.get(key), arrangement[key])]
    at_end, tokens = held.get("tokens_at_end"), arrangement["tokens"]
    judged = token_deficit_judged(record, tokens, stage0) if not same(at_end, tokens) else None
    if not same(at_end, tokens) and (judged is None or judged["unmet"]):
        why = ("no count was taken" if type(at_end) is not int else
               "a process ended holding a token, or outlived x.py with one" if at_end < tokens else
               "something wrote a token it never took")
        problems.append(f"its jobserver held {at_end!r} token(s) when x.py had exited, not the {tokens} it was given: "
                        f"{why}")
        if judged is not None:
            problems.append(validator().token_deficit_refusal(judged["given"], judged["returned"], judged["unmet"]))
    if held.get("path_unchanged") is not True:
        problems.append(f"its jobserver's path {held.get('path')} did not name the FIFO when x.py had exited: a client "
                        "that opened the path after it changed did not reach the jobserver")
    adapter = held.get("make_adapter")
    if not isinstance(adapter, dict):
        return problems + [f"its jobserver record names no make adapter ({brief(adapter)}): GNU make before 4.4, which "
                           "a build step runs, stops on the FIFO's fifo: spelling unless the adapter hands it over"]
    make, python = adapter.get("make"), record.get("python")
    if not same(adapter.get("path"), arrangement["make_adapter"]):
        problems.append(f"its make adapter was {adapter.get('path')!r}, not {arrangement['make_adapter']!r}")
    if not (isinstance(make, str) and make.startswith("/") and isinstance(python, str)):
        problems.append(f"its make adapter names the make {make!r} and the record the python {python!r}, not two "
                        "absolute paths")
    elif adapter.get("sha256") != hashlib.sha256(staircase().make_adapter_text(python, make).encode()).hexdigest():
        problems.append(f"its make adapter (sha256 {str(adapter.get('sha256'))[:16]}) is not the one "
                        f"seed_staircase.py writes for {python} and {make}")
    return problems


def make_problems(record: dict, bound: object) -> list[str]:
    """Why the make a run's adapter ran is not the make setup bound (`bound`, its
    host_tools row; THE JOBSERVER): every role is built with one make."""
    adapter = (record.get("jobserver") or {}).get("make_adapter") if isinstance(record.get("jobserver"), dict) else None
    ran = (adapter.get("make"), adapter.get("make_sha256")) if isinstance(adapter, dict) else (None, None)
    wanted = (bound.get("path"), bound.get("sha256")) if isinstance(bound, dict) else None
    if wanted is None:
        return ["setup bound no make (inputs.json's host_tools has no make row), and a build step runs make through "
                "the jobserver's adapter"]
    if ran != wanted:
        return [f"its make adapter ran {ran[0]!r} (sha256 {str(ran[1])[:16]}), not the make setup bound, "
                f"{wanted[0]!r} (sha256 {str(wanted[1])[:16]})"]
    return []


def tree_identity(top: Path, what: str) -> dict:
    """Entry count and digest of a tree, by the mint's own walk (`tree_records`):
    every entry's path, kind, mode, and bytes or link target."""
    if top.is_symlink() or not top.is_dir():
        raise Refusal(f"{what} is not a directory: {top}")
    support = staircase().mint_support()
    try:
        records = support.tree_records(top, what)
    except (support.WorkflowError, OSError) as error:
        raise Refusal(f"{what} could not be measured: {top}: {error}") from error
    return {"entries": len(records), "sha256": support.records_sha256(records)}


def captured(command: list[str], doing: str, *, env: dict[str, str], cwd: Path | None = None) -> str:
    """What a command printed; a command that fails is a refusal with its last words."""
    try:
        done = subprocess.run(command, capture_output=True, text=True, errors="replace", env=env, cwd=cwd)
    except OSError as error:
        raise Refusal(f"{doing}: `{shlex.join(command)}` could not be started: {error.strerror or error}") from error
    if done.returncode:
        # seed_staircase.py prints its refusal as JSON on stdout; the others say theirs on stderr.
        try:
            printed = json.loads(done.stdout)
        except ValueError:
            printed = None
        reason = printed.get("refused") if isinstance(printed, dict) else None
        raise Refusal(f"{doing}: `{shlex.join(command)}` {refresh.ended(done.returncode)}, and "
                      + (f"its reason is: {reason}" if reason else
                         f"the last line it printed on stderr is: {refresh.last_line(done.stderr)}"))
    return done.stdout


def said(partial: Path, stderr: Path | None = None) -> str:
    """Why a staircase command refused, from the JSON it printed (or its stderr)."""
    try:
        value = json.loads(partial.read_text())
    except (OSError, ValueError):
        value = None
    if isinstance(value, dict) and value.get("refused"):
        return str(value["refused"])
    if isinstance(value, dict) and value.get("refusals"):
        return "; ".join(map(str, value["refusals"]))
    if stderr is not None and stderr.is_file():
        return refresh.last_line(stderr.read_text(errors="replace"))
    return f"it printed no reason; what it printed is {partial}"


def remove_own(path: Path) -> None:
    """Remove a tree this script left unfinished under its own `.partial` name."""
    if path.is_symlink() or path.is_file():
        path.unlink()
    elif path.exists():
        refresh.must(["chmod", "-R", "u+w", str(path)], f"the unfinished {path} could not be made removable")
        shutil.rmtree(path)


def free_name(path: Path) -> Path:
    """`path`, or the first of `path`-2, -3, ... that does not exist."""
    number, candidate = 1, path
    while candidate.exists() or candidate.is_symlink():
        number += 1
        candidate = path.with_name(f"{path.name}-{number}")
    return candidate


def object_kind(path: Path) -> str | None:
    try:
        with open(path, "rb") as handle:
            head = handle.read(8)
    except OSError:
        return None
    if head[:4] == b"\x7fELF":
        return "elf"
    if head in (b"!<arch>\n", b"!<thin>\n"):
        return "ar"
    return None


def native_table(build_host: Path) -> dict:
    """Every ELF and ar file under the build outputs no Rust compiler makes
    (`build/<host>/llvm` and `lld`), by path, kind, size and sha256."""
    rows = []
    for name in refresh.NATIVE_OUTPUTS:
        for directory, dirnames, filenames in os.walk(build_host / name):
            dirnames.sort()
            for filename in sorted(filenames):
                path = Path(directory) / filename
                if path.is_symlink() or not path.is_file():
                    continue
                kind = object_kind(path)
                if kind is not None:
                    rows.append({"path": path.relative_to(build_host).as_posix(), "kind": kind,
                                 "bytes": path.stat().st_size, "sha256": sha256_file(path)})
    return {"schema": NATIVE_SCHEMA, "files": len(rows), "sha256": rows_sha256(rows), "rows": rows}


def native_changes(before: dict, after: dict) -> dict:
    first = {row["path"]: row["sha256"] for row in before["rows"]}
    second = {row["path"]: row["sha256"] for row in after["rows"]}
    return {"changed": sorted(path for path in first.keys() & second.keys() if first[path] != second[path]),
            "removed": sorted(first.keys() - second.keys()), "added": sorted(second.keys() - first.keys())}


def changes_summary(moved: dict) -> dict:
    return {**{key: len(paths) for key, paths in moved.items()},
            "first": (moved["changed"] + moved["removed"] + moved["added"])[:5]}


def manifest_rows(path: Path) -> dict[str, dict]:
    manifest = read_json(path, "a stage2 manifest")
    rows = manifest.get("records")
    if manifest.get("schema") != "trust-stage2-tree-v1" or not isinstance(rows, list):
        raise Refusal(f"{path} is not a trust-stage2-tree-v1 manifest")
    return {str(row.get("path")): row for row in rows if isinstance(row, dict)}


def differing(first: dict[str, dict], second: dict[str, dict]) -> list[str]:
    return sorted(path for path in first.keys() | second.keys() if first.get(path) != second.get(path))


def first_difference(mine: dict, theirs: dict) -> str | None:
    for key in sorted(mine.keys() | theirs.keys()):
        if mine.get(key) != theirs.get(key):
            return key
    return None


def ignored_entries(src: Path) -> list[str]:
    """What git ignores in the checkout (submodules are not descended into)."""
    listing = refresh.git(src, "status", "--porcelain", "--ignored", "--ignore-submodules=none")
    return sorted(line[3:] for line in listing.splitlines() if line.startswith("!! "))


def unexpected_ignored(entries: list[str]) -> list[str]:
    return [entry for entry in entries
            if entry not in IGNORED_ALLOWED and not entry.rstrip("/").endswith("__pycache__")]


def entries_of(directory: Path) -> list[str]:
    return sorted(entry.name for entry in directory.iterdir()) if directory.is_dir() else []


def trap_lines(ledger: Path) -> list[str]:
    log = ledger / "trap.log"
    return log.read_text(errors="replace").splitlines() if log.is_file() else []


# ---------------------------------------------------------------------------
# the plan: paths, commands and the one environment


class Plan:
    """The root's paths and every command of the build half. A test overrides the
    command methods with small scripts, so the control flow runs for real."""

    def __init__(self, args: argparse.Namespace, host: str, commit: str,
                 account: tuple[str, str] | None = None, driver: Path = HERE):
        self.args, self.host, self.commit = args, host, commit
        self.account = account_of_invoker() if account is None else account
        self.driver = driver
        self.root: Path = args.root
        self.src = self.worktree = self.root / "src"
        self.home, self.tools, self.inputs = self.root / "home", self.root / "tools", self.root / "inputs"
        self.ledger, self.kept = self.root / "ledger", self.root / "kept"
        self.stage0, self.seed, self.dist = self.root / "stage0", self.root / "seed", self.root / "dist"
        # Set by `setup` (from the checkout's Clean pin) or read from inputs.json.
        self.lean_library: Path | None = None
        # The invoker's environment, read before `adopt` replaces it: only `publish`'s
        # agh runs with it (agh holds the release credential).
        self.invoker_env = dict(os.environ)

    # files ------------------------------------------------------------------
    def file(self, label: str, suffix: str) -> Path:
        return self.ledger / f"{label}.{suffix}"

    def inputs_file(self) -> Path:
        return self.inputs / "inputs.json"

    def rung_config(self) -> Path:
        return self.ledger / "rung.bootstrap.toml"

    def build_dir(self) -> Path:
        return self.src / "build"

    def stage2(self) -> Path:
        return self.build_dir() / self.host / "stage2"

    def attempt(self, label: str) -> Path:
        return self.kept / f"{label}.attempt.json"

    def not_clean(self, label: str) -> Path:
        return self.kept / f"{label}.not-clean.json"

    def record(self, stem: str) -> Path:
        return self.kept / f"{stem}.build.json"

    def manifest_path(self, stem: str) -> Path:
        return self.kept / f"{stem}.stage2.json"

    def native(self, label: str, when: str) -> Path:
        return self.kept / f"{label}.native-{when}.json"

    def current_tree(self) -> Path:
        return self.kept / "current-tree.json"

    def dist_record(self) -> Path:
        return self.kept / "dist.json"

    def prepare_dir(self) -> Path:
        return self.root / "prepare"

    def prepared(self) -> Path:
        return self.root / "prepared"

    def output_root(self, prepared: Path | None = None) -> Path:
        return (prepared or self.prepared()) / "bootstrap" / "trust-stage0"

    def prepare_record(self) -> Path:
        return self.kept / "prepare.json"

    def bootstrap(self) -> Path:
        """Where bootstrap.py builds Bootstrap (asked for by `refresh.construct_bootstrap`)."""
        return self.build_dir() / "bootstrap" / "debug" / "bootstrap"

    # the environment --------------------------------------------------------
    def env(self) -> dict[str, str]:
        """The whole environment of every step: nothing of the invoker's. HOME is
        what `seed_staircase.py run` records (Path.home()), USER and LOGNAME what it
        copies, and with no SSH_AUTH_SOCK here it hands the build none."""
        return {"HOME": str(self.home), "USER": STEP_USER, "LOGNAME": STEP_USER, "LANG": "C.UTF-8",
                "PATH": f"{self.ledger / 'trap'}:/usr/bin:/bin", "TMPDIR": str(self.ledger / "tmp"),
                "CARGO_HOME": str(self.ledger / "cargo-home"),
                "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null"}

    def construct_env(self, label: str) -> dict[str, str]:
        return {**self.env(), "RUST_BOOTSTRAP_CONFIG": str(self.rung_config())}

    # commands ---------------------------------------------------------------
    def staircase(self, *words: str) -> list[str]:
        return [sys.executable, "-B", str(STAIRCASE), *words]

    def mint(self, *words: str) -> list[str]:
        return [sys.executable, "-I", "-S", "-B", str(MINT_SUPPORT), *words]

    def seed_config(self) -> list[str]:
        return self.staircase("seed-config", "--worktree", str(self.src))

    def lean_inputs(self, out: Path) -> list[str]:
        return self.mint("clean-lean-inputs", "--root", str(self.src), "--library", str(self.lean_library),
                         "--output", str(out))

    def lean_verify(self, manifest: Path, digest: str) -> list[str]:
        return self.mint("verify-clean-lean-inputs", str(self.src), str(manifest),
                         "--library", str(self.lean_library), "--sha256", digest)

    def cargo_home_inputs(self, source: Path, destination: Path, out: Path) -> list[str]:
        return self.mint("cargo-home-inputs", "--source", str(source), "--destination", str(destination),
                         "--output", str(out))

    def admit(self) -> list[str]:
        return self.staircase("admit", str(self.stage0), "--repo", str(self.src), "--target", self.commit)

    def config(self, out: Path) -> list[str]:
        return self.staircase("config", "--base", str(self.src / "bootstrap.toml"),
                              "--stage0", str(self.stage0), "--out", str(out))

    def closure(self) -> list[str]:
        return [sys.executable, "-I", "-S", "-B", str(self.src / "scripts" / "bootstrap_dependency_closure.py"),
                "check", "--repo-root", str(self.src), "--targo", str(self.stage0 / "bin" / "cargo"),
                "--timeout", str(refresh.PREPARE_TIMEOUT_S)]

    def construct(self) -> list[str]:
        return [sys.executable, str(self.src / "x.py"), "--version"]

    def xpy(self, words: tuple[str, ...] | list[str]) -> list[str]:
        """The x.py arguments of an invocation: one config for every role."""
        return ["--config", str(self.rung_config()), *words]

    def run(self, label: str, words: tuple[str, ...] | list[str], admission: Path) -> list[str]:
        return self.staircase("run", "--worktree", str(self.src), "--label", label, "--ledger", str(self.ledger),
                              "--offline", "--clean-lean-lib", str(self.lean_library),
                              "--tool-dir", str(self.tools), "--stage0-admission", str(admission),
                              "--fifo-jobserver", "--", *self.xpy(words))

    def jobserver(self, jobs: int) -> dict:
        """The jobserver every x.py run of this root is given (THE JOBSERVER, at the top)."""
        return jobserver_arrangement(self.ledger, jobs)

    def manifest(self, tree: Path, out: Path) -> list[str]:
        return self.mint("stage2-manifest", str(tree), str(out))

    def dist_components(self) -> list[str]:
        return self.mint("dist-components", str(self.src))

    def manifest_tool(self) -> list[str]:
        return self.mint("build-manifest-tool", "--build", str(self.build_dir()), "--host", self.host)

    def channel_manifest(self, tool: str, date: str) -> list[str]:
        packaged = str(self.build_dir() / "dist")
        return [tool, packaged, packaged, date, DIST_SERVER, CHANNEL]

    def stage2_unchanged(self) -> list[str]:
        return self.mint("verify-stage2-unchanged", str(self.manifest_path("p")), str(self.stage2()))

    def commit_date(self) -> str:
        return refresh.git(self.src, "log", "-1", "--date=short", "--pretty=format:%cd")

    # prepare --------------------------------------------------------------------
    def version(self) -> list[str]:
        return self.mint("version", str(self.src))

    def stage_artifacts(self, dist: Path, work: Path, version: str) -> list[str]:
        return self.mint("stage-artifacts", "--dist", str(dist), "--work", str(work), "--version", version,
                         "--host", self.host, "--commit", self.commit, "--manifest", str(work / "seed-inputs.json"))

    def install(self, installer: Path) -> list[str]:
        return [str(installer), f"--prefix={self.seed}", "--disable-ldconfig"]

    def validate_seed(self, version: str, out: Path) -> list[str]:
        return self.mint("validate-seed", "--seed", str(self.seed), "--version", version, "--host", self.host,
                         "--output", str(out))

    def carried(self) -> list[str]:
        return self.mint("verify-archives-carry-compared", "--seed", str(self.seed), "--manifest",
                         str(self.manifest_path("p")), "--host", self.host)

    def handoff(self, admitted: Path, work: Path, output_root: Path) -> list[str]:
        return self.mint("rustc-dev-handoff", "--root", str(PREPARE_PY.parents[3]), "--input-manifest",
                         str(admitted), "--work", str(work), "--output-root", str(output_root))

    def prepare_py(self, input_dist: Path, output_root: Path, stage0_output: Path, date: str,
                   server: str) -> list[str]:
        return [sys.executable, "-I", "-B", str(PREPARE_PY), "--input-dist", str(input_dist),
                "--source-channel", CHANNEL, "--owned-channel", CHANNEL, "--archive-format", "xz",
                "--jobs", str(getattr(self.args, "archive_jobs", ARCHIVE_JOBS)), "--stage0-seed-only", "--git-commit-hash", self.commit,
                "--date", date, "--dist-server", server, "--output-root", str(output_root),
                "--stage0-output", str(stage0_output), "--merge-existing", "--keep-existing-shared"]

    def source_repo(self) -> Path:
        """The checkout --parent is read from and `commit` clones: this script's."""
        return HERE.parent

    def parent_commit(self) -> str:
        """--parent, resolved in this script's checkout."""
        found = refresh.git(self.source_repo(), "rev-parse", "--verify", f"{self.args.parent}^{{commit}}")
        if not re.fullmatch(r"[0-9a-f]{40}", found):
            raise Refusal(f"--parent {self.args.parent} is not a commit of {self.source_repo()}")
        return found

    def parent_file(self, commit: str, path: str) -> bytes:
        done = subprocess.run(["git", "-C", str(self.source_repo()), "show", f"{commit}:{path}"], capture_output=True)
        if done.returncode:
            raise Refusal(f"{path} cannot be read at the parent {commit[:10]}: "
                          f"{done.stderr.decode(errors='replace').strip()}. Nothing was started")
        return done.stdout

    def host_tools(self) -> dict:
        """The host's C toolchain and python by role (cc, c++, ld, cmake, make, python),
        and every host tool the base config names, keyed by its path."""
        return {**self.role_tools(), **self.config_tools()}

    def config_tools(self) -> dict:
        """Every host tool the base config names (`named_host_tools`), keyed by its
        path, measured now; None for one that is not an executable file."""
        config = self.src / "bootstrap.toml"
        try:
            payload = config.read_bytes()
        except OSError as error:
            raise Refusal(f"the base config {config} cannot be read for the host tools it names: "
                          f"{error.strerror or error}. Nothing was started and nothing was recorded") from error
        return {path: self.host_tool(path) for path in named_host_tools(payload, str(config))}

    # commit, verify, publish ------------------------------------------------
    def commit_dir(self) -> Path:
        return self.root / "commit"

    def repo_module(self, repo: Path, name: str):
        """scripts/<name>.py of `repo`, loaded afresh under its own module name: the
        judge of a branch is the branch's own code (its door, its validator)."""
        import importlib.util
        path = repo / "scripts" / f"{name}.py"
        spec = importlib.util.spec_from_file_location(
            f"fixed_point_linux_seed_{name}_{hashlib.sha256(str(path).encode()).hexdigest()[:12]}", path)
        if spec is None or spec.loader is None or not path.is_file():
            raise Refusal(f"{path} cannot be loaded: the clone does not carry it")
        module = importlib.util.module_from_spec(spec)
        # Registered under its own name (a dataclass looks its module up there); a load that
        # fails is not left behind.
        sys.modules[spec.name] = module
        was, sys.dont_write_bytecode = sys.dont_write_bytecode, True
        try:
            spec.loader.exec_module(module)
        except BaseException:
            sys.modules.pop(spec.name, None)
            raise
        finally:
            sys.dont_write_bytecode = was
        return module

    def seed_capture(self, recreate, repo: Path, host: str, build_root: Path | None = None) -> dict:
        """recreate_bootstrap's capture of the clone's pinned seed for `host`."""
        return recreate.capture_validated_seed_lineage(
            repo, host, **({"build_root": build_root} if build_root is not None else {}))

    def corpus(self, repo: Path, *words: str) -> list[str]:
        return [sys.executable, "-I", "-B", str(repo / CORPUS_SCRIPT), *words]

    def freshness(self, repo: Path) -> list[str]:
        return [sys.executable, "-B", str(repo / "scripts" / "check_seed_freshness.py")]

    def ledger_pins(self, repo: Path, rev: str) -> list[str]:
        return [sys.executable, "-I", "-B", str(repo / "scripts" / "check_ledger_pins.py"), "--rev", rev]

    def verify_env(self) -> dict[str, str]:
        """verify's own environment: the operating system's tools and nothing of the
        invoker's Rust; HOME stays the invoker's (nothing is written there)."""
        return {"HOME": self.invoker_env.get("HOME", "/nonexistent"), "USER": self.invoker_env.get("USER", ""),
                "LANG": "C.UTF-8", "PATH": "/usr/bin:/bin", "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_CONFIG_GLOBAL": "/dev/null"}

    def agh(self, *words: str) -> list[str]:
        return [str(self.args.agh), *words]

    def agh_env(self) -> dict[str, str]:
        return dict(self.invoker_env)

    # verify --rebuild, leg 1: the clone's own source in seed mode -------------
    def leg_env(self, work: Path) -> dict[str, str]:
        """Leg 1's environment: a private home, the ledger's cargo home and tmp, OS tools."""
        ledger_dir = work / "ledger"
        return {"HOME": str(work / "home"), "USER": STEP_USER, "LOGNAME": STEP_USER, "LANG": "C.UTF-8",
                "PATH": f"{ledger_dir / 'trap'}:/usr/bin:/bin", "TMPDIR": str(ledger_dir / "tmp"),
                "CARGO_HOME": str(ledger_dir / "cargo-home"), "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_CONFIG_GLOBAL": "/dev/null"}

    def seed_sysroot(self, payloads: Path, stage0_file: Path, out: Path) -> list[str]:
        return self.staircase("seed-sysroot", "--payloads", str(payloads), "--stage0-file", str(stage0_file),
                              "--out", str(out))

    def admit_for(self, stage0: Path, repo: Path, target: str) -> list[str]:
        return self.staircase("admit", str(stage0), "--repo", str(repo), "--target", target)

    def seed_config_for(self, worktree: Path) -> list[str]:
        return self.staircase("seed-config", "--worktree", str(worktree))

    def closure_for(self, worktree: Path, stage0: Path, verb: str) -> list[str]:
        return [sys.executable, "-I", "-S", "-B", str(worktree / "scripts" / "bootstrap_dependency_closure.py"),
                verb, "--repo-root", str(worktree), "--targo", str(stage0 / "bin" / "cargo"),
                "--timeout", str(refresh.PREPARE_TIMEOUT_S)]

    def construct_for(self, worktree: Path) -> list[str]:
        return [sys.executable, str(worktree / "x.py"), "--version"]

    def run_seed_mode(self, worktree: Path, ledger: Path, admission: Path, lean: Path, tools: Path,
                      jobs: int) -> list[str]:
        return self.staircase("run", "--worktree", str(worktree), "--label", SEED_LABEL, "--ledger", str(ledger),
                              "--seed-mode", "--offline", "--clean-lean-lib", str(lean), "--tool-dir", str(tools),
                              "--stage0-admission", str(admission), "--fifo-jobserver", "--",
                              "build", "--stage", "2", "-j", str(jobs), "compiler/rustc", "library/std")

    def lineage(self, admission: Path, run: Path, stage2: Path, repo: Path) -> list[str]:
        return self.staircase("lineage", "--root-admission", str(admission), "--rung", str(run),
                              "--final-stage2", str(stage2), "--repo", str(repo))

    # verify --rebuild, leg 2: the root again at the recorded path ----------
    def replay_plan(self, root: Path) -> "Plan":
        """The plan of the recorded root: every path and command of the original roles."""
        return type(self)(argparse.Namespace(**{**vars(self.args), "root": root}), self.host, self.commit,
                          self.account, self.driver)

    def checkout_for(self, repo: Path, commit: str, target: Path) -> list[str]:
        """A clean clone of `commit` with every submodule, from `repo` and its module store."""
        return refresh.clone_rung(repo, commit, target)

    # measurements a test replaces -------------------------------------------
    def role_tools(self) -> dict:
        """The host's C toolchain, make (the jobserver's adapter runs it) and python,
        by path, real path, version line and sha256."""
        rows: dict = {}
        for name in ("cc", "c++", "ld", "cmake", "make"):
            # make where the jobserver's adapter finds it: the OS directories of x.py's PATH.
            found = staircase().real_make([]) if name == "make" else shutil.which(name, path="/usr/bin:/bin")
            rows[name] = None if found is None else self.host_tool(found)
        real = os.path.realpath(sys.executable)
        rows["python"] = {"path": sys.executable, "real": real, "sha256": sha256_file(Path(real)),
                          "version": platform.python_version()}
        return rows

    def host_tool(self, path: str) -> dict | None:
        """One host tool by path, real path, sha256 and the first line `--version`
        prints; None when the path is not an executable file."""
        real = os.path.realpath(path)
        if not (os.path.isfile(real) and os.access(real, os.X_OK)):
            return None
        try:
            printed = subprocess.run([path, "--version"], capture_output=True, text=True, errors="replace",
                                     env=self.env()).stdout.splitlines()
            version = printed[0].strip() if printed else "(it printed no version line)"
        except OSError as error:
            version = f"(it could not be started: {error.strerror or error})"
        return {"path": path, "real": real, "sha256": sha256_file(Path(real)), "version": version}

    def live(self) -> list[str]:
        """Processes an earlier step left running: `seed_staircase.py` over this
        ledger, or anything that carries a rung's environment for it."""
        mine, found = {os.getpid(), os.getppid()}, []
        cargo_home = f"CARGO_HOME={self.ledger / 'cargo-home'}".encode()
        for entry in Path("/proc").iterdir():
            if not entry.name.isdigit() or int(entry.name) in mine:
                continue
            try:
                words = [word.decode(errors="replace") for word in (entry / "cmdline").read_bytes().split(b"\0")
                         if word]
                environment = (entry / "environ").read_bytes().split(b"\0")
            except OSError:
                continue
            line = " ".join(words)
            runner = "seed_staircase.py" in line and str(self.ledger) in line
            member = cargo_home in environment and any(v.startswith(b"TRUST_STAIRCASE_RUNG=") for v in environment)
            if runner or member:
                found.append(f"pid {entry.name}: {line[:200]}")
        return found


# ---------------------------------------------------------------------------
# running a step


def adopt(plan: Plan) -> None:
    """Replace this process's own environment with the step environment, so that
    everything it starts, directly or through an imported helper, has only that."""
    os.environ.clear()
    os.environ.update(plan.env())
    os.umask(0o022)


@contextlib.contextmanager
def locked(plan: Plan):
    """One step at a time under a root."""
    path = plan.root / "driver.lock"
    handle = open(path, "a+")
    try:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            handle.seek(0)
            holder = handle.read().strip() or "it does not say which"
            raise Refusal(f"another step of this script is running under {plan.root} ({path}: {holder}). "
                          "Nothing was started or changed. `status` reads the root without the lock; "
                          "run this again when that step has ended") from None
        handle.seek(0)
        handle.truncate()
        handle.write(f"pid {os.getpid()}, started {time.strftime('%Y-%m-%dT%H:%M:%S%z')}\n")
        handle.flush()
        try:
            yield
        finally:
            handle.seek(0)
            handle.truncate()       # an empty file: no step is running
    finally:
        handle.close()


def run_recorded(command: list[str], out: Path, stderr: Path, *, env: dict[str, str],
                 cwd: Path) -> tuple[int, list[str]]:
    """`seed_staircase.py run`: its record in `out` (under that name only when it
    exits 0, else beside it as `.partial`) and its messages in `stderr`.

    A stop request to this script (^C, TERM, HUP) is passed to that program and
    waited out: it stops x.py, lets the process census finish and writes its record.
    `subprocess.run` would kill it on ^C, and x.py, which runs in its own session,
    would go on unobserved."""
    partial = out.with_name(out.name + ".partial")
    asked: list[str] = []
    with open(partial, "wb") as sink, open(stderr, "wb") as errors:
        try:
            child = subprocess.Popen(command, stdout=sink, stderr=errors, env=env, cwd=cwd)
        except OSError as error:
            raise Refusal(f"`{shlex.join(command)}` could not be started: {error.strerror or error}") from error

        def forward(signum: int, _frame: object) -> None:
            asked.append(signal.Signals(signum).name)
            with contextlib.suppress(ProcessLookupError):
                child.send_signal(signum)

        previous = {signum: signal.signal(signum, forward)
                    for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)}
        try:
            code = child.wait()
        finally:
            for signum, handler in previous.items():
                signal.signal(signum, handler)
    if code == 0:
        partial.replace(out)
    return code, asked


def require_setup(plan: Plan) -> dict:
    """inputs.json of a finished setup of this commit, host and root."""
    path = plan.inputs_file()
    if not path.is_file():
        raise Refusal(f"setup of {plan.root} is not done ({path} is not there). Nothing was started. "
                      f"Run: {shlex.join(command_line(plan, 'setup'))}")
    inputs = read_json(path, "the setup record")
    for key, mine in (("schema", INPUTS_SCHEMA), ("commit", plan.commit), ("host", plan.host),
                      ("root", str(plan.root))):
        if inputs.get(key) != mine:
            raise Refusal(f"{path} is a setup with {key} = {inputs.get(key)!r}, and this command is for "
                          f"{mine!r}. Nothing was started; name the root that belongs to this commit")
    plan.lean_library = Path(inputs["lean"]["library"])
    return inputs


def preflight(plan: Plan) -> None:
    """What would make every later hour worthless, asked before anything starts."""
    named = names_account(str(plan.root), plan.account)
    if named:
        raise Refusal(
            f"the root, {plan.root}, names the invoking account ({named}). Every record names the root many "
            "times (the worktree, HOME, the ledger, every path the build census reads), so every one of them "
            "would name the account. Nothing was started. Use a root whose path does not name the account, "
            f"such as the default {ROOT_PARENT / plan.commit[:10]}")
    named = names_account(str(plan.driver), plan.account)
    if named:
        say(f"note: this script's directory, {plan.driver}, names the invoking account ({named}): the run "
            "records name it (`tool.path`). Every build record lists where the account is named "
            "(`account_named_in`); the chain compilers name it in any case")
    lines = trap_lines(plan.ledger)
    if lines:
        raise Refusal(f"{plan.ledger / 'trap.log'} has {len(lines)} line(s): a stock Rust tool name was reached "
                      f"by an earlier step under this root (the first: {lines[0]!r}), and no record can be "
                      "written from a root whose trap log is not empty. Nothing was started and nothing was "
                      "removed. Read the log to see which step reached it; the builds belong in a new --root")
    alive = plan.live()
    if alive:
        raise Refusal(f"an earlier build under {plan.root} is still running ({'; '.join(alive[:3])}"
                      + (f"; and {len(alive) - 3} more" if len(alive) > 3 else "")
                      + "). Nothing was started. Wait for it, or stop it by sending TERM to the "
                      "seed_staircase.py process, which stops x.py and writes its record")


def command_line(plan: Plan, *words: str) -> list[str]:
    """A command of this script for this root, with only the options that are not the defaults."""
    root = [] if plan.root == ROOT_PARENT / plan.commit[:10] else ["--root", str(plan.root)]
    commit = [] if plan.commit == COMMIT else ["--commit", plan.commit]
    return ["python3", str(plan.driver / "fixed_point_linux_seed.py"), *words, *root, *commit]


# ---------------------------------------------------------------------------
# setup (design step 6)


def lean_directory(pin: str) -> str:
    """The elan directory name of a Clean pin (the rule of `mint_seed_support.clean_lean_inputs`)."""
    if not re.fullmatch(r"leanprover/lean4:v[0-9A-Za-z.+-]+", pin):
        raise Refusal(f"the Clean pin {pin!r} is not a leanprover/lean4 toolchain name")
    return pin.replace("/", "--").replace(":", "---", 1)


def default_lean(plan: Plan, directory: str) -> Path:
    """Where elan installed the pinned toolchain for the invoker (`resolve` read
    ELAN_HOME before the environment was replaced)."""
    return plan.args.elan_home / "toolchains" / directory


def setup_sources(plan: Plan) -> dict:
    args = plan.args
    return {"repo": str(args.repo), "cargo_home": str(args.cargo_home), "ninja": str(args.ninja),
            "lean_toolchain": str(args.lean_toolchain) if args.lean_toolchain else None,
            "elan_home": str(args.elan_home),
            "jobs": args.jobs, "linker": "self-contained" if args.lld else "system"}


# The arguments each part of setup uses. A part's keys are written to sources.json
# when that part is done, so an argument a part refused can be corrected under the
# same root, and an argument a done part used cannot be changed.
SOURCE_KEYS = {"the checkout": ("repo",), "the ninja copy": ("ninja",),
               "the Lean copy": ("lean_toolchain", "elan_home"), "the cargo home copy": ("cargo_home",),
               "the setup record": ("jobs", "linker")}


def check_sources(plan: Plan) -> None:
    """Refuse an argument other than the one a done part of setup used."""
    kept = plan.inputs / "sources.json"
    if not kept.is_file():
        return
    was, now = read_json(kept, "the record of what setup copied from"), setup_sources(plan)
    for key in sorted(was):
        if key in now and was[key] != now[key]:
            part = next((name for name, keys in SOURCE_KEYS.items() if key in keys), "a part of setup")
            raise Refusal(f"setup of {plan.root} was started with {key} = {was[key]!r} ({kept}), and this command "
                          f"names {now[key]!r}. That part of setup ({part}) is done with it and every role shares "
                          "what setup made, so nothing was changed. Give the same arguments, or set up another "
                          "--root")


def bind_sources(plan: Plan, part: str) -> None:
    kept = plan.inputs / "sources.json"
    was = read_json(kept, "the record of what setup copied from") if kept.is_file() else {}
    now = setup_sources(plan)
    write_json(kept, {**was, **{key: now[key] for key in SOURCE_KEYS[part]}})


def jobs_problem(jobs: int) -> str | None:
    if jobs >= 1:
        return None
    return (f"--jobs is {jobs}, and every build needs at least 1. Nothing was set up. Give the job count "
            f"every role builds with, for example --jobs {os.cpu_count() or 1} (this host's CPUs)")


def step_checkout(plan: Plan) -> None:
    if plan.src.exists():
        problems = refresh.worktree_problems(plan.src, plan.commit)
        if problems:
            raise Refusal(f"{plan.src} is not a clean checkout of {plan.commit[:10]}: {'; '.join(problems)}. "
                          "Nothing was changed. Put right what is listed, or move the directory aside and "
                          "run setup again to clone it anew")
        say(f"checkout: {plan.src} is there and clean")
        return
    partial = plan.root / "src.partial"
    remove_own(partial)
    say(f"checkout: cloning {plan.commit[:10]} from {plan.args.repo}")
    try:
        done = refresh.clone_rung(plan.args.repo, plan.commit, partial)
    except Refusal as refusal:
        raise Refusal(f"the checkout could not be made from {plan.args.repo}: {refusal}. Nothing else was changed, "
                      f"and the unfinished clone {partial} is removed by the next run. Name with --repo a "
                      f"checkout that holds {plan.commit[:10]} and whose own .git has a module store for every "
                      "submodule (the main worktree of a clone whose submodules are initialised), and run "
                      "setup again") from refusal
    partial.rename(plan.src)
    problems = refresh.worktree_problems(plan.src, plan.commit)
    if problems:
        raise Refusal(f"the clone at {plan.src} is not a clean checkout of {plan.commit[:10]}: "
                      f"{'; '.join(problems)}. It is kept as it is; move it aside and run setup again")
    say("checkout: submodules " + (", ".join(done) or "(none)"))


def step_base_config(plan: Plan) -> dict:
    out, config = plan.inputs / "seed-config.json", plan.src / "bootstrap.toml"
    if not out.is_file():
        if config.exists():
            raise Refusal(f"{config} exists and {out} does not record it, so it is not known to be the "
                          "checkout's own seed-mode config. Nothing was changed. Remove that file and run "
                          "setup again")
        messages = plan.inputs / "seed-config.stderr"
        if refresh.to_file(plan.seed_config(), out, env=plan.env(), cwd=plan.root, stderr=messages):
            raise Refusal(f"the checkout's base config could not be written: `{shlex.join(plan.seed_config())}` "
                          f"refused: {said(out.with_name(out.name + '.partial'), messages)}. Nothing else was "
                          "changed; the same command line runs this step again")
    recorded = read_json(out, "the seed-config record")
    if not config.is_file() or recorded.get("sha256") != sha256_file(config):
        raise Refusal(f"{config} is not the file {out} records (sha256 {recorded.get('sha256')}). Nothing was "
                      "changed. Remove both files and run setup again")
    say(f"base config: {config} (sha256 {recorded['sha256'][:16]})")
    return {"path": str(config), "sha256": recorded["sha256"]}


def named_host_tools(payload: bytes, where: str) -> dict[str, list[str]]:
    """The host tools a base config names, each with the keys that name it: the
    validator's own walk (seed_fixed_point.config_host_tools), so what setup
    binds is what C15 holds the record to."""
    try:
        document = tomllib.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        raise Refusal(f"the base config {where} is not TOML, so the host tools it names cannot be read: {error}. "
                      "Nothing was started and nothing was recorded") from error
    return validator().config_host_tools(document)


def step_ninja(plan: Plan) -> dict:
    target = plan.tools / "ninja"
    if not target.is_file():
        real = Path(os.path.realpath(plan.args.ninja))
        if not real.is_file() or not os.access(real, os.X_OK):
            raise Refusal(f"--ninja {plan.args.ninja} is not an executable file (it resolves to {real}). "
                          "Nothing was copied. Name the ninja the LLVM build is to use")
        partial = plan.root / "ninja.partial"
        shutil.copyfile(real, partial)
        partial.chmod(0o755)
        partial.replace(target)
    extra = [name for name in entries_of(plan.tools) if name != "ninja"]
    if extra:
        raise Refusal(f"{plan.tools} holds more than ninja ({', '.join(extra)}); it is put on the build's PATH "
                      "whole. Nothing was changed. Remove what is listed")
    row = {"path": str(target), "bytes": target.stat().st_size, "sha256": sha256_file(target)}
    say(f"ninja: {target} (sha256 {row['sha256'][:16]})")
    return row


def step_lean(plan: Plan) -> dict:
    pin_file = plan.src / "first-party" / "clean" / "lean-toolchain"
    try:
        pin = pin_file.read_text().strip()
    except OSError as error:
        raise Refusal(f"the Clean pin cannot be read: {pin_file}: {error.strerror or error}") from error
    directory = lean_directory(pin)
    target = plan.inputs / "lean" / directory
    plan.lean_library = target / "lib" / "lean"
    if not target.exists():
        source = plan.args.lean_toolchain or default_lean(plan, directory)
        physical = Path(os.path.realpath(source))
        if not (physical / "lib" / "lean").is_dir():
            raise Refusal(f"the Lean toolchain {pin}, which {pin_file} names, is not installed at {source} "
                          "(no lib/lean there). Nothing was copied, and this script fetches nothing. Name "
                          "an installed copy with --lean-toolchain")
        target.parent.mkdir(parents=True, exist_ok=True)
        say(f"lean: copying {physical}")
        refresh.copy_tree(physical, target)
    manifest = plan.inputs / "clean-lean-inputs.json"
    if not manifest.is_file():
        partial = manifest.with_name(manifest.name + ".partial")
        partial.unlink(missing_ok=True)
        captured(plan.lean_inputs(partial), f"the Lean copy {target} could not be bound to the Clean pin",
                 env=plan.env(), cwd=plan.root)
        partial.replace(manifest)
    bound = read_json(manifest, "the Clean Lean input manifest")
    entries = bound.get("installation_entries") or []
    row = {"toolchain": pin, "directory": directory, "library": str(plan.lean_library),
           "manifest": str(manifest), "manifest_sha256": sha256_file(manifest),
           "fingerprint": bound.get("fingerprint"), "entries": len(entries), "entries_sha256": rows_sha256(entries)}
    say(f"lean: {target} ({row['entries']} entries, manifest sha256 {row['manifest_sha256'][:16]})")
    return row


def step_cargo_home(plan: Plan) -> dict:
    target, manifest = plan.ledger / "cargo-home", plan.inputs / "cargo-home-inputs.json"
    if not (target.is_dir() and manifest.is_file()):
        if target.exists() or manifest.exists():
            raise Refusal(f"of {target} and {manifest} only one is there, so the cargo home is not known to be "
                          "the copy the manifest binds. Nothing was changed. Move what is there aside and run "
                          "setup again")
        partial, draft = target.with_name("cargo-home.partial"), manifest.with_name(manifest.name + ".partial")
        remove_own(partial)
        draft.unlink(missing_ok=True)
        say(f"cargo home: copying registry/index, registry/cache and git/db of {plan.args.cargo_home}")
        try:
            captured(plan.cargo_home_inputs(plan.args.cargo_home, partial, draft),
                     f"the cargo home could not be filled from {plan.args.cargo_home}", env=plan.env(), cwd=plan.root)
        except Refusal as refusal:
            raise Refusal(f"{refusal}. The unfinished copy is {partial}; the same command line removes it and "
                          "copies again. (A cargo home another build is fetching into can change under the "
                          "copy: copy when it is at rest)") from refusal
        partial.rename(target)
        draft.replace(manifest)
    bound = read_json(manifest, "the cargo home input manifest")
    row = {"path": str(target), "manifest": str(manifest), "manifest_sha256": sha256_file(manifest),
           "fingerprint": bound.get("fingerprint"), "trees": bound.get("trees")}
    say(f"cargo home: {target} (fingerprint {str(row['fingerprint'])[:16]})")
    return row


def setup(plan: Plan) -> int:
    problem = jobs_problem(plan.args.jobs)
    if problem:
        raise Refusal(problem)
    for directory in (plan.home, plan.tools, plan.inputs, plan.ledger, plan.kept, plan.ledger / "tmp"):
        directory.mkdir(parents=True, exist_ok=True)
    check_sources(plan)
    if plan.inputs_file().is_file():
        require_setup(plan)
        say(f"setup: already done ({plan.inputs_file()}); not repeated")
        return 0
    step_checkout(plan)
    bind_sources(plan, "the checkout")
    base = step_base_config(plan)
    ninja = step_ninja(plan)
    bind_sources(plan, "the ninja copy")
    lean = step_lean(plan)
    bind_sources(plan, "the Lean copy")
    cargo_home = step_cargo_home(plan)
    bind_sources(plan, "the cargo home copy")
    refresh.write_traps(plan.ledger)
    tools = plan.host_tools()
    missing = [name for name in ("cc", "c++", "ld") if not tools.get(name)]
    if missing:
        raise Refusal(f"/usr/bin:/bin has no {', '.join(missing)}: the build's C toolchain is a declared "
                      "input and is taken from there. Nothing was recorded; everything copied so far is kept")
    absent = [key for key, row in tools.items() if key.startswith("/") and row is None]
    if absent:
        raise Refusal(f"the base config names {', '.join(absent)}, and that is not an executable file here: every "
                      "host tool the base config names is a declared input, bound by its bytes. Nothing was "
                      "recorded; everything copied so far is kept")
    bind_sources(plan, "the setup record")
    # Where the host-local inputs name the account (sources.json, and the cargo home
    # manifest's `source`), for `record` to judge; inputs.json itself names no source.
    mentions = {path.name: account_mentions(read_json(path, "a setup input record"), plan.account)
                for path in sorted(plan.inputs.glob("*.json")) if path != plan.inputs_file()}
    store = fact_store_state(plan.ledger / "cargo-home")
    write_json(plan.inputs_file(), {
        "schema": INPUTS_SCHEMA, "commit": plan.commit, "host": plan.host, "root": str(plan.root),
        "build_line": list(BUILD_LINE), "jobs": plan.args.jobs, "linker": setup_sources(plan)["linker"],
        "base_config": base, "ninja": ninja, "lean": lean, "cargo_home": cargo_home, "host_tools": tools,
        "environment": plan.env(), "clean_fact_store": store, "jobserver": plan.jobserver(plan.args.jobs),
        "account_named_in": {name: found for name, found in mentions.items() if found}})
    say(f"clean fact store: {fact_store_words(store, plan.ledger / 'cargo-home')}")
    say(f"setup: done ({plan.inputs_file()}). Next: {shlex.join(command_line(plan, 'build', '--role', 'producer'))}")
    if names_account(str(plan.root), plan.account):
        say(f"note: the root, {plan.root}, names the invoking account; `build` refuses that before it starts")
    if names_account(str(plan.driver), plan.account):
        say(f"note: this script's directory, {plan.driver}, names the invoking account; the run records will "
            "name it (`tool.path`), and every build record says where the account is named")
    return 0


# ---------------------------------------------------------------------------
# what every role shares, measured before a build


def cargo_home_trees(plan: Plan) -> dict:
    """The three trees cargo reads offline, measured as `cargo-home-inputs` binds them."""
    support = staircase().mint_support()
    trees: dict = {}
    for relative in support.CARGO_HOME_INPUT_TREES:
        tree = plan.ledger / "cargo-home" / relative
        trees[relative] = tree_identity(tree, f"cargo home tree {relative}") if tree.exists() else None
    return trees


def shared_facts(plan: Plan, inputs: dict) -> dict:
    """Everything a role is given other than its stage0 and its label, measured now."""
    module = staircase()
    try:
        tool_dir = module.tool_dir_record([plan.tools])
    except module.Refusal as refusal:
        raise Refusal(f"the tool directory {plan.tools} is not what setup made: {refusal}. Nothing was "
                      "started") from refusal
    manifest = Path(inputs["lean"]["manifest"])
    captured(plan.lean_verify(manifest, inputs["lean"]["manifest_sha256"]),
             f"the Lean copy {plan.lean_library} is no longer what setup bound ({manifest}); nothing was started",
             env=plan.env(), cwd=plan.root)
    return {"commit": plan.commit, "host": plan.host, "root": str(plan.root),
            "inputs_sha256": sha256_file(plan.inputs_file()),
            "base_config_sha256": sha256_file(plan.src / "bootstrap.toml"),
            "rung_config": str(plan.rung_config()), "rung_config_sha256": sha256_file(plan.rung_config()),
            "build_line": list(BUILD_LINE), "jobs": inputs["jobs"], "linker": inputs["linker"],
            "environment": plan.env(), "tool_dir": tool_dir,
            "cargo_home": cargo_home_trees(plan),
            "lean": {"library": str(plan.lean_library), "manifest_sha256": inputs["lean"]["manifest_sha256"]},
            "host_tools": plan.host_tools(),
            "clean_fact_store": fact_store_state(plan.ledger / "cargo-home"),
            "jobserver": plan.jobserver(inputs["jobs"]),
            "scripts": {name: sha256_file(HERE / name) for name in GIVEN_BY}}


def require_jobserver(plan: Plan, inputs: dict, label: str) -> None:
    """Refuse a build in a root whose setup recorded no jobserver (THE JOBSERVER)."""
    if isinstance(inputs.get("jobserver"), dict):
        return
    raise Refusal(f"{label} would be given a FIFO jobserver, as every x.py run is since BOOTSTRAP-JOBSERVER-PROBE-1 "
                  f"(seed_staircase.py run --fifo-jobserver), and {plan.inputs_file()} records none, so this root was "
                  "set up before every run was given one: its earlier builds ran without it, and the roles may differ "
                  "only in their stage0. Nothing was started and nothing was changed. Set up a new --root and build "
                  "every role in it")


def require_shared(plan: Plan, inputs: dict, shared: dict, label: str) -> None:
    """Refuse a build whose shared facts are not setup's and every earlier role's."""
    require_jobserver(plan, inputs, label)
    against = {"base_config_sha256": inputs["base_config"]["sha256"], "cargo_home": inputs["cargo_home"]["trees"],
               "host_tools": inputs["host_tools"], "environment": inputs["environment"],
               "jobs": inputs["jobs"], "linker": inputs["linker"], "build_line": inputs["build_line"],
               "clean_fact_store": inputs.get("clean_fact_store"), "jobserver": inputs["jobserver"]}
    for key, was in against.items():
        if shared[key] == was:
            continue
        # A root set up before setup measured the host tools the base config names
        # has no row for them; said as such, not as a changed tool.
        unbound = sorted(path for path in shared[key] if path.startswith("/") and path not in was) \
            if key == "host_tools" and isinstance(was, dict) else []
        if unbound:
            them = "it" if len(unbound) == 1 else "them"
            raise Refusal(f"{label} would run {', '.join(unbound)}, which the base config names, and setup did not "
                          f"bind {them}: {plan.inputs_file()} has no row for {them}, so this root was set up before "
                          "setup measured the host tools the base config names. Nothing was started and nothing "
                          "was changed. A build runs only what setup bound: set up a new --root and build every "
                          "role in it")
        entry = first_difference(shared[key], was) if isinstance(shared[key], dict) and isinstance(was, dict) \
            else None
        raise Refusal(f"{label} would not be given what setup recorded: {key} is {brief(shared[key])} now "
                      f"and was {brief(was)} at setup ({plan.inputs_file()}). Nothing was started and "
                      "nothing was changed. A build must share this with every other role; find what "
                      "changed it, or set up a new --root and build every role in it"
                      + (f" (the first entry of {key} that differs: {entry})" if entry is not None else ""))
    declared = {entry["name"]: entry["sha256"] for row in shared["tool_dir"] for entry in row["entries"]}
    if declared != {"ninja": inputs["ninja"]["sha256"]}:
        raise Refusal(f"{plan.tools} is not what setup made, the one file ninja with sha256 "
                      f"{inputs['ninja']['sha256'][:16]}: it holds {brief(declared)}. Nothing was started")
    for path in sorted(plan.kept.glob("*.build.json")):
        earlier = read_json(path, "an earlier role's build record")
        key = first_difference(shared, earlier.get("shared") or {})
        if key is not None:
            hint = (f". {' and '.join(GIVEN_BY)} write the build's trap shims, environment and config tail and "
                    "judge its run: run every role from one checkout of them at one commit" if key == "scripts"
                    else "")
            mine, theirs = shared.get(key), (earlier.get("shared") or {}).get(key)
            entry = first_difference(mine, theirs) if isinstance(mine, dict) and isinstance(theirs, dict) else None
            raise Refusal(f"{label} would not be given what {earlier.get('label')} was given: {key} is "
                          f"{brief(mine)} now and was {brief(theirs)} for that build ({path})"
                          + (f" (the first entry of {key} that differs: {entry})" if entry is not None else "")
                          + f". The roles differ only in their stage0, so nothing was started and nothing was "
                          f"changed{hint}")


# ---------------------------------------------------------------------------
# a role's stage0


def stage0_source(plan: Plan, role: str) -> Path:
    if role in ("fixed-point", "control"):
        if plan.args.stage0 is not None:
            raise Refusal(f"the {role} build is built from the pinned archives as installed ({plan.seed}) and "
                          "from nothing else; --stage0 is for the producer and the cross-check")
        if not plan.prepare_record().is_file():
            raise Refusal(f"{plan.seed} is not prepared ({plan.prepare_record()} is not there): the {role} build's "
                          "stage0 is the pinned archives as installed, and the `prepare` step admits and installs "
                          "them. Nothing was started and everything built so far is kept. Run: "
                          f"{shlex.join(command_line(plan, 'prepare'))}; the cross-check needs no seed: "
                          f"{shlex.join(command_line(plan, 'build', '--role', 'cross-check'))}")
        prepared = read_json(plan.prepare_record(), "the prepare record")
        for key, mine in (("schema", PREPARE_SCHEMA), ("commit", plan.commit), ("host", plan.host),
                          ("root", str(plan.root))):
            if prepared.get(key) != mine:
                raise Refusal(f"{plan.prepare_record()} has {key} = {prepared.get(key)!r}, not {mine!r}. Nothing was "
                              "started")
        if not plan.seed.is_dir() or tree_identity(plan.seed, "the installed seed") != \
                (prepared.get("seed") or {}).get("tree"):
            raise Refusal(f"{plan.seed} is not the tree {plan.prepare_record()} records as the pinned archives "
                          f"installed. Nothing was started. A seed that changed after prepare is no stage0 for the "
                          f"{role} build; set up a new --root")
        return plan.seed
    source = plan.args.stage0
    if not (source / "bin" / "trustc").is_file():
        raise Refusal(f"--stage0 {source} has no bin/trustc. Nothing was started. Name the {role} compiler: "
                      "a chain stage2 or a sealed toolchain")
    return source


def install_stage0(plan: Plan, source: Path, label: str) -> dict:
    """Make stage0/ a copy of `source`, entry for entry, unless it already is one.
    A copy of another compiler is kept beside it under the label that used it."""
    marker = plan.root / "stage0.json"
    given = tree_identity(source, "the stage0 to copy")
    if plan.stage0.exists() and not marker.is_file():
        # Only this script puts a tree here, and only whole (copy_tree renames a finished
        # copy into place); the marker follows once the copy is measured. A stop between
        # the two leaves a finished copy without its marker: measure it again.
        say(f"{label}: {plan.stage0} has no marker ({marker}); measuring it against {source}")
        if tree_identity(plan.stage0, "the installed stage0") != given:
            raise Refusal(f"{plan.stage0} exists, {marker} does not say what it is a copy of, and it is not a copy "
                          f"of {source} entry for entry. Nothing was changed. Move it aside and run this again")
        now = {"label": label, "source": str(source), "tree": given}
        write_json(marker, now)
        return now
    if plan.stage0.exists():
        was = read_json(marker, "the stage0 marker")
        if was.get("tree") == given and tree_identity(plan.stage0, "the installed stage0") == given:
            return was
        # A sibling of stage0/: a read-only tree cannot be moved to another directory.
        aside, number = plan.root / f"stage0.{was.get('label')}", 1
        while aside.exists() or aside.with_name(aside.name + ".json").exists():
            number += 1
            aside = plan.root / f"stage0.{was.get('label')}.{number}"
        plan.stage0.rename(aside)
        marker.rename(aside.with_name(aside.name + ".json"))
        say(f"{label}: the stage0 of {was.get('label')} is kept as {aside}")
    say(f"{label}: copying {source} to {plan.stage0} ({given['entries']} entries)")
    refresh.copy_tree(source, plan.stage0)
    if tree_identity(plan.stage0, "the installed stage0") != given:
        plan.stage0.rename(plan.root / "stage0.partial")
        raise Refusal(f"the copy of {source} is not that tree entry for entry (did it change under the copy?). "
                      f"The copy is set aside as {plan.root / 'stage0.partial'} and the next run copies again")
    now = {"label": label, "source": str(source), "tree": given}
    write_json(marker, now)
    return now


def linker_fact(plan: Plan, inputs: dict, label: str) -> dict:
    """The linker setting is setup's and the same for every role; whether this
    stage0 could serve the other setting is recorded beside it."""
    ships = all(path.is_file() for path in refresh.self_contained_lld(plan.stage0, plan.host))
    if inputs["linker"] == "self-contained" and not ships:
        missing = [str(path) for path in refresh.self_contained_lld(plan.stage0, plan.host) if not path.is_file()]
        raise Refusal(f"setup chose the self-contained linker (--lld) for every role, and the stage0 of {label} "
                      f"ships none: no {', '.join(missing)}. The roles cannot differ in their linker, so "
                      "nothing was started. Set up a new --root without --lld: the system linker is the one "
                      "setting every stage0 can use")
    return {"setting": inputs["linker"], "stage0_ships_self_contained_lld": ships}


# ---------------------------------------------------------------------------
# labels and the build tree


def labels_used(plan: Plan, base: str) -> list[str]:
    used, number = [], 1
    while plan.attempt(base if number == 1 else f"{base}-{number}").is_file():
        used.append(base if number == 1 else f"{base}-{number}")
        number += 1
    return used


def adopt_finished_run(plan: Plan, label: str) -> None:
    """A run that ended while this script was not there to read it (killed without
    passing the stop on: SIGKILL, the out-of-memory killer) left its whole record
    under `.partial`. Judge it as the script would have: a record of x.py exiting 0
    is the run's record; any other ended the build not clean."""
    if plan.not_clean(label).is_file() or plan.file(label, "run.json").is_file():
        return
    partial = plan.file(label, "run.json.partial")
    try:
        record = json.loads(partial.read_text())
    except (OSError, ValueError):
        return
    if not (isinstance(record, dict) and record.get("kind") == "rung" and record.get("label") == label
            and record.get("end")) or plan.live():
        return
    if record.get("rc") == 0:
        partial.replace(plan.file(label, "run.json"))
        say(f"{label}: its run ended while this script was not there to read it, and left its whole record; "
            f"that record is now {plan.file(label, 'run.json')}")
        return
    attempt = read_json(plan.attempt(label), "the record of what the build was given")
    write_json(plan.not_clean(label), {**attempt, "problems": [
        "its run ended while this script was not there to judge it", *refresh.rung_problems(record)],
        "finished": record.get("end")})


def next_label(plan: Plan, base: str, doing: str) -> tuple[str, str | None]:
    """(the label to use, the label to resume judging or None). A label whose run
    left a record is resumed; one that ended not clean needs `--again`; one that
    left nothing was interrupted and is followed by the next."""
    used = labels_used(plan, base)
    if used:
        last = used[-1]
        adopt_finished_run(plan, last)
        if plan.not_clean(last).is_file():
            was = read_json(plan.not_clean(last), "the record of a build that was not clean")
            if not plan.args.again:
                why = "; ".join(was.get("problems") or ["(no reason recorded)"])
                raise Refusal(f"{last} ended and was not clean: {why}. Its record is {plan.not_clean(last)}, "
                              f"x.py's output {plan.ledger / 'logs' / (last + '.log')}, "
                              f"and nothing of it was removed. Nothing was started. To {doing} again as "
                              f"{base}-{len(used) + 1}, give the same command line with --again")
        elif plan.file(last, "run.json").is_file():
            return last, last
        else:
            say(f"{last} was started and left no record (interrupted, or x.py did not exit 0 and this "
                f"script was stopped before it said so); {base}-{len(used) + 1} follows it")
    return (base if not used else f"{base}-{len(used) + 1}"), None


def set_aside_tree(plan: Plan, label: str) -> None:
    """Move whatever is in src/build out of the way of `label`, unless it is
    `label`'s own tree being prepared."""
    build, pointer = plan.build_dir(), plan.current_tree()
    if not build.exists():
        return
    if not pointer.is_file():
        raise Refusal(f"{build} exists and {pointer} does not say which build made it. Nothing was changed. "
                      "Move it aside (it may be hours of work) and run this again")
    current = read_json(pointer, "the record of which build's tree is in src/build")
    if current.get("label") == label and not plan.attempt(label).is_file():
        return
    target = plan.kept / (f"{current.get('label')}-tree" if current.get("clean")
                          else f"{current.get('label')}-unfinished")
    if target.exists():
        raise Refusal(f"{build} is the tree of {current.get('label')} and {target} already exists, so it cannot "
                      "be kept there. Nothing was changed. Move one of them aside")
    build.rename(target)
    pointer.unlink()
    say(f"{label}: the tree of {current.get('label')} is kept as {target}")


def producer_tree(plan: Plan) -> Path:
    """Where the producer's build tree is now: in src/build until another role starts."""
    producer = read_json(plan.record("p"), "the producer's build record")
    kept = plan.kept / f"{producer['label']}-tree"
    if kept.is_dir():
        return kept
    pointer = plan.current_tree()
    if pointer.is_file() and read_json(
            pointer, "the record of which build's tree is in src/build").get("label") == producer["label"]:
        return plan.build_dir()
    raise Refusal(f"the producer's build tree is neither {kept} nor in {plan.build_dir()}: every other role "
                  "links the LLVM and lld it built. Nothing was started; put the tree back where it was")


# ---------------------------------------------------------------------------
# build (design steps 7, 10, 11, 12)


def control_state(plan: Plan) -> dict:
    """What the builds by the pinned seed say about the files the producer's tree
    and theirs differ in (design step 12; nothing here admits anything)."""
    producer = manifest_rows(plan.manifest_path("p"))
    seeds = [("f", manifest_rows(plan.manifest_path("f")))]
    for number in range(1, CONTROL_LIMIT + 1):
        if plan.record(f"c{number}").is_file():
            seeds.append((f"c{number}", manifest_rows(plan.manifest_path(f"c{number}"))))
    moved = sorted({path for _, rows in seeds for path in differing(producer, rows)})
    decided, undecided, absent = {}, [], []
    for path in (path for path in moved if path in UNREPRODUCED_ALLOWED):
        # A build that did not make the file gives no digest of it: not a second one.
        if len({producer.get(path) is not None, *(rows.get(path) is not None for _, rows in seeds)}) > 1:
            absent.append(path)
            continue
        seen = [brief(rows.get(path), 10 ** 6) for _, rows in seeds]
        if brief(producer.get(path), 10 ** 6) in seen:
            decided[path] = "reproduced: a build by the pinned seed gave the producer's bytes"
        elif len(set(seen)) > 1:
            decided[path] = "nondeterministic: two builds by the pinned seed gave different bytes"
        else:
            undecided.append(path)
    return {"controls": len(seeds) - 1, "outside": [path for path in moved if path not in UNREPRODUCED_ALLOWED],
            "absent": absent, "decided": decided, "undecided": undecided}


def control_stem(plan: Plan) -> str:
    if not plan.record("f").is_file():
        raise Refusal(f"a control repeats the fixed-point build, and there is no clean one yet "
                      f"({plan.record('f')} is not there). Nothing was started. Run: "
                      f"{shlex.join(command_line(plan, 'build', '--role', 'fixed-point'))}")
    state = control_state(plan)
    allowed = " and ".join(UNREPRODUCED_ALLOWED)
    if state["outside"]:
        raise Refusal(f"the builds by the pinned seed differ from the producer's tree in {len(state['outside'])} "
                      f"entr{'y' if len(state['outside']) == 1 else 'ies'} other than {allowed} (the first: "
                      f"{state['outside'][0]}). A control decides only those two files; for any other the "
                      "rule is that no record is written. Nothing was started; every tree and manifest is kept")
    if state["absent"]:
        raise Refusal(f"{state['absent'][0]} is in some of the producer's and the pinned seed's trees and not in "
                      "others: a build that did not make it gives no digest, so no control can decide it, and the "
                      "rule is that no record is written. Nothing was started; every tree and manifest is kept")
    if not state["decided"] and not state["undecided"]:
        raise Refusal("the fixed-point build's tree is the producer's, entry for entry: there is nothing for a "
                      "control to decide. Nothing was started")
    if not state["undecided"]:
        raise Refusal("every file the fixed-point build did not reproduce is already decided ("
                      + "; ".join(f"{path}: {how}" for path, how in sorted(state["decided"].items()))
                      + "). Nothing was started")
    if state["controls"] >= CONTROL_LIMIT:
        raise Refusal(f"{CONTROL_LIMIT} controls are built, and {', '.join(state['undecided'])} still has one "
                      "digest in every build by the pinned seed and another in the producer's: the difference "
                      "follows the stage0, and the rule is that no record is written. Nothing was started; "
                      "every tree and manifest is kept")
    return f"c{state['controls'] + 1}"


def compare_with_producer(plan: Plan, stem: str) -> dict:
    moved = differing(manifest_rows(plan.manifest_path("p")), manifest_rows(plan.manifest_path(stem)))
    return {"with": "p", "identical": not moved, "differing": moved,
            "outside_allowed": [path for path in moved if path not in UNREPRODUCED_ALLOWED]}


def say_comparison(plan: Plan, role: str, record: dict) -> int:
    """A clean build's tree against the producer's, in words; 1 when the stop rule holds."""
    found = record.get("comparison")
    if found is None:
        return 0
    label, allowed = record["label"], " and ".join(UNREPRODUCED_ALLOWED)
    if found["identical"]:
        say(f"{label}: its stage2 is the producer's, entry for entry")
        return 0
    if found["outside_allowed"]:
        say(f"{label}: its stage2 is NOT the producer's in {len(found['outside_allowed'])} entr"
            f"{'y' if len(found['outside_allowed']) == 1 else 'ies'} other than {allowed} (the first: "
            f"{found['outside_allowed'][0]}; all of them are in {plan.record(record['stem'])}). The rule is "
            "that no record is written; both trees and both manifests are kept")
        return 1
    say(f"{label}: its stage2 differs from the producer's only in {', '.join(found['differing'])}"
        + (f". Next: {shlex.join(command_line(plan, 'build', '--role', 'control'))}" if role == "fixed-point" else ""))
    return 0


def set_aside_before(plan: Plan, label: str, name: str, directory: Path, remake: bool) -> dict | None:
    """What an earlier step left in `directory`, moved whole to kept/<label>.<name>-before
    (and `directory` made again, empty, when `remake`); None when it held nothing."""
    left = entries_of(directory)
    moved = None
    if left:
        aside = free_name(plan.kept / f"{label}.{name}-before")
        directory.rename(aside)
        moved = {"entries": left, "kept": str(aside)}
    if remake:
        directory.mkdir(parents=True, exist_ok=True)
    return moved


def start(plan: Plan, role: str, stem: str, label: str, inputs: dict) -> dict:
    """Everything up to the moment x.py is started; returns what the build is given.
    Every part is skipped or redone harmlessly when already done, so a run stopped
    here is run again under the same label."""
    problems = refresh.worktree_problems(plan.src, plan.commit)
    if problems:
        raise Refusal(f"{plan.src} is not a clean checkout of {plan.commit[:10]}: {'; '.join(problems)}. Nothing "
                      "was started and nothing was changed. Put right what is listed")
    ignored = ignored_entries(plan.src)
    if unexpected_ignored(ignored):
        raise Refusal(f"{plan.src} holds ignored files a build does not leave: "
                      f"{', '.join(unexpected_ignored(ignored))}. "
                      "Nothing was started and nothing was removed. Remove them, or say why they are there")
    source = stage0_source(plan, role)
    set_aside_tree(plan, label)
    host_dir = plan.build_dir() / plan.host
    host_dir.mkdir(parents=True, exist_ok=True)
    write_json(plan.current_tree(), {"label": label, "stem": stem, "role": role, "clean": False})
    stage0 = install_stage0(plan, source, label)
    linker = linker_fact(plan, inputs, label)
    if role != "producer":
        tree = producer_tree(plan)
        for name in refresh.NATIVE_OUTPUTS:
            if (tree / plan.host / name).is_dir() and not (host_dir / name).exists():
                say(f"{label}: copying the producer's {name}")
                refresh.copy_tree(tree / plan.host / name, host_dir / name)
    say(f"{label}: measuring the native outputs it starts with")
    native = native_table(host_dir)
    write_json(plan.native(label, "before"), native)
    if role != "producer":
        final = read_json(plan.dist_record(), "the dist record")["native_outputs"]["after"]
        if native["sha256"] != final["sha256"]:
            raise Refusal(f"the LLVM and lld copied for {label} are not the producer's ({native['files']} files, "
                          f"digest {native['sha256'][:16]}; the producer's tree had {final['files']}, "
                          f"{final['sha256'][:16]}, after dist). Nothing was started. The copy is in "
                          f"{host_dir}; remove it and run this again to copy anew")

    admission = plan.file(label, "admission.json")
    if refresh.to_file(plan.admit(), admission, env=plan.env(), cwd=plan.root):
        raise Refusal(f"seed_staircase.py admit refused the stage0 of {label} ({plan.stage0}, a copy of "
                      f"{stage0['source']}): {said(admission.with_name(admission.name + '.partial'))}. "
                      "Nothing was built; the copy is kept")
    admitted = read_json(admission, "the stage0 admission")
    trustc = (admitted.get("sha256") or {}).get("bin/trustc")
    for other, path in ((other, plan.record(other)) for other in ("p", "f", "s") if other != stem):
        if not path.is_file():
            continue
        theirs = read_json(path, "an earlier role's build record")["stage0"]
        if role == "control" and other == "f" and theirs["tree"] != stage0["tree"]:
            raise Refusal(f"{label} repeats the fixed-point build, and its stage0 is not that build's "
                          f"({plan.seed} changed since {theirs['label']}). Nothing was built")
        if role != "control" and theirs["trustc_sha256"] == trustc:
            raise Refusal(f"the stage0 of {label} has the bin/trustc of {theirs['label']}'s (sha256 {trustc}). "
                          "The producer, the fixed point and the cross-check are three different compilers; "
                          "the same one twice shows nothing. Nothing was built")

    draft = plan.file(label, "bootstrap.toml.draft")
    draft.unlink(missing_ok=True)
    captured(plan.config(draft), f"{label}: the rung config could not be written", env=plan.env(), cwd=plan.root)
    text = draft.read_text()
    if refresh.last_table(text) != "[build]":
        raise Refusal(f"{draft} does not end in its [build] table, so a job count cannot be appended to it")
    text += refresh.config_tail(inputs["jobs"], inputs["linker"] == "self-contained")
    draft.unlink()
    config = plan.rung_config()
    if not config.is_file():
        partial = config.with_name(config.name + ".partial")
        partial.write_text(text)
        partial.replace(config)
    elif config.read_text() != text:
        raise Refusal(f"the rung config {label} would be built with is not {config}, the one the earlier builds "
                      "used, byte for byte. Nothing was built and that file was not changed")

    refresh.write_traps(plan.ledger)
    say(f"{label}: checking the offline dependency closure")
    log = plan.file(label, "closure.log")
    if refresh.to_file(plan.closure(), log, env=plan.env(), cwd=plan.src, merge=True):
        printed = log.with_name(log.name + ".partial")
        reason, out_of_time = closure_reason(printed.read_text(errors="replace"))
        if out_of_time:
            raise Refusal(f"the offline dependency check for the stage0 of {label} did not finish in its "
                          f"{refresh.PREPARE_TIMEOUT_S} s budget: {reason} (all it printed: {printed}). Nothing was "
                          f"built, and the cargo home is kept as the check left it (it unpacks crate sources "
                          "under registry/src, which no role's comparison reads). The same command line runs the "
                          "check again")
        raise Refusal(f"the cargo home does not hold this commit's dependency closure for the stage0 of {label}: "
                      f"`{shlex.join(plan.closure())}` refused: {reason} (all it printed: {printed}). Nothing was "
                      "built and the cargo home is kept. This script fetches nothing: the `prepare` command the "
                      "check names fetches from the network, and a cargo home filled that way is no longer the "
                      "one setup bound, so it belongs in a new --root after it is filled")
    if "--trust-build-tree-lock" in (plan.src / "x.py").read_text(errors="replace"):
        refresh.construct_bootstrap(plan, label)
    problems = refresh.worktree_problems(plan.src, plan.commit)
    if problems:
        raise Refusal(f"the dependency check left {plan.src} other than a clean checkout: {'; '.join(problems)}. "
                      "Nothing was built")
    say(f"{label}: measuring what every role shares")
    shared = shared_facts(plan, inputs)
    require_shared(plan, inputs, shared, label)

    set_aside = {}
    # cargo-home/trust is the compiler's Clean fact store (when the root's ancestors
    # allow one): no role starts with facts an earlier step wrote.
    for name, directory, remake in (("home", plan.home, True), ("tmp", plan.ledger / "tmp", True),
                                    ("cargo-trust", plan.ledger / "cargo-home" / "trust", False)):
        moved = set_aside_before(plan, label, name, directory, remake)
        if moved is not None:
            set_aside[name] = moved
    lines = trap_lines(plan.ledger)
    if lines:
        raise Refusal(f"a step before x.py reached a stock Rust tool name: {plan.ledger / 'trap.log'} has "
                      f"{len(lines)} line(s), the first {lines[0]!r}. Nothing was built")
    return {"schema": BUILD_SCHEMA, "role": role, "stem": stem, "label": label,
            "stage0": {"path": str(plan.stage0), "tree": stage0["tree"], "commit": admitted.get("commit"),
                       "trustc_sha256": trustc, "label": label},
            "linker": linker, "shared": shared,
            "admission": {"path": str(admission), "sha256": sha256_file(admission)},
            "native_before": {"path": str(plan.native(label, "before")), "files": native["files"],
                              "sha256": native["sha256"]},
            "worktree": {"ignored_before": ignored}, "set_aside_before": set_aside, "trap_log_lines_before": 0,
            "driver": {name: sha256_file(HERE / name) for name in DRIVER_SCRIPTS},
            "started": time.strftime("%Y-%m-%dT%H:%M:%S%z")}


def run_problems(plan: Plan, record: dict, label: str, words: tuple[str, ...] | list[str], inputs: dict,
                 stage0: tuple[bool, str] | None = None) -> list[str]:
    """Why a run record is not the clean record of this invocation (empty: it is).
    `stage0` is SEED-TOKEN-LEAK-STAGE0-1's decision for the run (token_leak_stage0)."""
    problems = refresh.rung_problems(record)
    environment = record.get("environment") or {}
    expected = {"label": label, "worktree": str(plan.src), "commit": plan.commit, "argv": ["x.py", *plan.xpy(words)]}
    problems += [f"the record's {key} is {brief(record.get(key))}, not {brief(mine)}"
                 for key, mine in expected.items() if record.get(key) != mine]
    given = {"HOME": str(plan.home), "USER": STEP_USER, "LOGNAME": STEP_USER, "CARGO_NET_OFFLINE": "true",
             "CARGO_HOME": str(plan.ledger / "cargo-home"), "TMPDIR": str(plan.ledger / "tmp"),
             "CLEAN_OLEAN_PINNED_LEAN_LIB": str(plan.lean_library), "CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1",
             "TRUST_STAIRCASE_RUNG": label}
    problems += [f"the build's {key} was {environment.get(key)!r}, not {mine!r}"
                 for key, mine in given.items() if environment.get(key) != mine]
    if "SSH_AUTH_SOCK" in environment:
        problems.append("the build was handed an SSH_AUTH_SOCK")
    lean = record.get("clean_lean") or {}
    if lean.get("unchanged") is not True:
        problems.append(f"the Lean library changed under the build, or was not measured: {brief(lean)}")
    elif (lean.get("before") or {}).get("manifest_sha256") != inputs["lean"]["manifest_sha256"]:
        problems.append("the Lean library the build was given is not the one setup bound")
    if (record.get("config_tools") or {}).get("config_sha256") != sha256_file(plan.rung_config()):
        problems.append(f"the config x.py read is not {plan.rung_config()}")
    return problems + jobserver_problems(record, plan.jobserver(inputs["jobs"]), stage0) \
        + make_problems(record, (inputs.get("host_tools") or {}).get("make"))


def account_named_in(plan: Plan, record: dict, given: dict) -> dict:
    """Where this build's evidence names the invoking account (THE ACCOUNT, at the top)."""
    marker = plan.root / "stage0.json"
    source = read_json(marker, "the stage0 marker").get("source") if marker.is_file() else None
    admission = Path((given.get("admission") or {}).get("path") or plan.file(given["label"], "admission.json"))
    return {"run_record": account_mentions(record, plan.account),
            "admission": account_mentions(read_json(admission, "the stage0 admission"), plan.account)
            if admission.is_file() else [],
            "stage0_links": account_links(plan.stage0, plan.account) if plan.stage0.is_dir() else [],
            "stage0_source": names_account(str(source or ""), plan.account) is not None,
            "driver_directory": names_account(str(plan.driver), plan.account) is not None}


def finish(plan: Plan, role: str, given: dict, inputs: dict) -> int:
    """Judge a build whose run left its record, and write the build's own record.
    Reads only files, so a run stopped here is run again and resumes here."""
    stem, label = given["stem"], given["label"]
    run_path = plan.file(label, "run.json")
    record = read_json(run_path, "the run record")
    stage0, deficit = token_leak_judgement(plan, given.get("admission"), record, inputs)
    problems = run_problems(plan, record, label, BUILD_LINE, inputs, stage0)
    host_dir = plan.build_dir() / plan.host
    say(f"{label}: measuring what the build left")
    before = read_json(plan.native(label, "before"), "the native outputs before the build")
    after = native_table(host_dir)
    write_json(plan.native(label, "after"), after)
    moved = native_changes(before, after)
    if role != "producer" and after["sha256"] != before["sha256"]:
        named = (moved["changed"] + moved["removed"] + moved["added"])[:3]
        problems.append(f"x.py did not leave the producer's LLVM and lld as they were ({len(moved['changed'])} "
                        f"changed, {len(moved['removed'])} removed, {len(moved['added'])} added; the first: "
                        f"{', '.join(named)}), so this build is not comparable with the producer's")
    lines = trap_lines(plan.ledger)
    if len(lines) != given["trap_log_lines_before"]:
        problems.append(f"the trap log grew by {len(lines) - given['trap_log_lines_before']} line(s)")
    dirty = refresh.worktree_problems(plan.src, plan.commit)
    ignored = ignored_entries(plan.src)
    problems += [f"the checkout is not clean after the build: {problem}" for problem in dirty]
    if unexpected_ignored(ignored):
        problems.append("the build left ignored files that are not its own: " + ", ".join(unexpected_ignored(ignored)))
    cargo_home = cargo_home_trees(plan)
    if tree_identity(plan.stage0, "the installed stage0") != given["stage0"]["tree"]:
        problems.append(f"{plan.stage0} is not the tree the build was started from")
    for earlier in sorted(plan.kept.glob("*.build.json")):
        theirs = read_json(earlier, "an earlier role's build record")
        was = {key: value for key, value in (theirs.get("run_environment") or {}).items()
               if key != "TRUST_STAIRCASE_RUNG"}
        now = {key: value for key, value in (record.get("environment") or {}).items() if key != "TRUST_STAIRCASE_RUNG"}
        key = first_difference(now, was)
        if key is not None:
            problems.append(f"x.py's {key} was {now.get(key)!r} and was {was.get(key)!r} for {theirs.get('label')}")

    clean = not problems
    manifest = plan.manifest_path(stem) if clean else plan.kept / f"{label}.not-clean.stage2.json"
    described = None
    if plan.stage2().is_dir():
        partial = manifest.with_name(manifest.name + ".partial")
        partial.unlink(missing_ok=True)
        manifest.unlink(missing_ok=True)
        captured(plan.manifest(plan.stage2(), partial),
                 f"{label}: no manifest of its stage2 could be written. The build is kept and is not built "
                 "again: the same command line resumes here", env=plan.env(), cwd=plan.root)
        partial.replace(manifest)
        rows = read_json(manifest, "the stage2 manifest")
        described = {"path": str(manifest), "sha256": sha256_file(manifest), "tree_sha256": rows.get("sha256"),
                     "records": len(rows.get("records") or [])}
    elif clean:
        clean, problems = False, [f"x.py exited 0 and left no {plan.stage2()}"]
    result = {**given, "commit": plan.commit, "host": plan.host, "root": str(plan.root),
              "run": {"path": str(run_path), "sha256": sha256_file(run_path), "rc": record.get("rc"),
                      "no_stock_evidence": record.get("no_stock_evidence"), "elapsed_s": record.get("elapsed_s")},
              "run_environment": record.get("environment"), "jobserver_token_deficit": deficit,
              "config": {"path": str(plan.rung_config()), "sha256": sha256_file(plan.rung_config()),
                         "base_sha256": sha256_file(plan.src / "bootstrap.toml")},
              "stage2_manifest": described,
              "native_after": {"path": str(plan.native(label, "after")), "files": after["files"],
                               "sha256": after["sha256"], "against_before": changes_summary(moved)},
              "trap_log_lines_after": len(lines),
              "worktree": {**given["worktree"], "ignored_after": ignored, "problems_after": dirty},
              "left_after": {"home": entries_of(plan.home), "tmp": entries_of(plan.ledger / "tmp"),
                             "cargo-trust": entries_of(plan.ledger / "cargo-home" / "trust")},
              "account_named_in": account_named_in(plan, record, given),
              "cargo_home_after": {"trees": cargo_home, "unchanged": cargo_home == given["shared"]["cargo_home"]},
              "problems": problems, "finished": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    if clean and role != "producer":
        result["comparison"] = compare_with_producer(plan, stem)
    write_json(plan.current_tree(), {"label": label, "stem": stem, "role": role, "clean": clean})
    if not clean:
        write_json(plan.not_clean(label), result)
        raise Refusal(not_clean_words(plan, label, problems, f"build the {role} role"))
    write_json(plan.record(stem), result)
    say(f"{label}: clean build, {record.get('elapsed_s')} s; its record is {plan.record(stem)} and its stage2 "
        f"manifest {manifest}")
    if deficit is not None:
        say(token_deficit_accepted(label, deficit))
    if not result["cargo_home_after"]["unchanged"]:
        say(f"{label}: NOTE the build wrote into the cargo home's input trees (the record's cargo_home_after "
            "has both digests); the next role would not start from the cargo home this one started from, "
            "and will be refused")
    return say_comparison(plan, role, result)


def not_clean_words(plan: Plan, label: str, problems: list[str], doing: str) -> str:
    base = re.sub(r"-\d+$", "", label) if re.fullmatch(r".*-(build|dist|full|manifest-tool)-\d+", label) else label
    return (f"{label} is not a clean build: {'; '.join(problems)}. Kept: its record {plan.not_clean(label)}, "
            f"the run record {plan.file(label, 'run.json')} (`.partial` when x.py did not exit 0), x.py's "
            f"output {plan.ledger / 'logs' / (label + '.log')}, the messages {plan.file(label, 'run.stderr')}, "
            f"and the build tree. To {doing} again under the label {base}-{len(labels_used(plan, base)) + 1}, "
            "give the same command line with --again")


def run_label(plan: Plan, label: str, words: tuple[str, ...] | list[str], admission: Path) -> tuple[int, list[str]]:
    say(f"{label}: x.py {' '.join(plan.xpy(words))} (its output: {plan.ledger / 'logs' / (label + '.log')})")
    return run_recorded(plan.run(label, words, admission), plan.file(label, "run.json"),
                        plan.file(label, "run.stderr"), env=plan.env(), cwd=plan.root)


def failed_run_problems(plan: Plan, label: str, code: int, asked: list[str]) -> list[str]:
    partial = plan.file(label, "run.json.partial")
    try:
        record = json.loads(partial.read_text())
    except (OSError, ValueError):
        record = None
    problems = [f"seed_staircase.py run {refresh.ended(code)}"
                + (f" after this script was sent {', '.join(asked)}" if asked else "")]
    if isinstance(record, dict) and record.get("kind") == "rung":
        problems += refresh.rung_problems(record)
    else:
        problems.append("it started no build: " + said(partial, plan.file(label, "run.stderr")))
    return problems


def build(plan: Plan, role: str) -> int:
    inputs = require_setup(plan)
    if role != "producer" and not plan.record("p").is_file():
        raise Refusal(f"the {role} build is compared with the producer's and links its LLVM, and there is no "
                      f"clean producer build yet ({plan.record('p')} is not there). Nothing was started. Run: "
                      f"{shlex.join(command_line(plan, 'build', '--role', 'producer'))}")
    stem = STEMS.get(role) or next((f"c{n}" for n in range(1, CONTROL_LIMIT + 1)
                                    if labels_used(plan, f"c{n}-build") and not plan.record(f"c{n}").is_file()),
                                   None) or control_stem(plan)
    if plan.record(stem).is_file():
        record = read_json(plan.record(stem), "the build record")
        say(f"{role}: already built clean as {record['label']} ({plan.record(stem)}); not repeated")
        return say_comparison(plan, role, record)
    if role != "producer" and not plan.dist_record().is_file():
        raise Refusal(f"the dist step runs in the producer's build tree, and the {role} build moves that tree "
                      f"out of {plan.build_dir()}; dist is not done ({plan.dist_record()} is not there). "
                      f"Nothing was started. Run: {shlex.join(command_line(plan, 'dist'))}")
    require_jobserver(plan, inputs, f"the {role} build")
    preflight(plan)
    label, resumed = next_label(plan, f"{stem}-build", f"build the {role} role")
    if resumed is not None:
        say(f"{label}: x.py ended and left its record; resuming at the measurements")
        return finish(plan, role, read_json(plan.attempt(label), "the record of what the build was given"), inputs)
    given = start(plan, role, stem, label, inputs)
    write_json(plan.attempt(label), given)
    code, asked = run_label(plan, label, BUILD_LINE, plan.file(label, "admission.json"))
    if code:
        problems = failed_run_problems(plan, label, code, asked)
        write_json(plan.not_clean(label), {**given, "problems": problems,
                                           "finished": time.strftime("%Y-%m-%dT%H:%M:%S%z")})
        raise Refusal(not_clean_words(plan, label, problems, f"build the {role} role"))
    return finish(plan, role, given, inputs)


# ---------------------------------------------------------------------------
# dist (design step 8)


def dist_words(components: list[str]) -> dict[str, list[str]]:
    return {"p-dist": ["dist", "--stage", "2", *components], "p-full": ["build", "--stage", "2"],
            "p-manifest-tool": ["build", "--stage", "2", "src/tools/build-manifest"]}


def archive_table(directory: Path) -> list[dict]:
    return [{"name": path.name, "bytes": path.stat().st_size, "sha256": sha256_file(path)}
            for path in sorted(directory.iterdir()) if path.is_file() and not path.is_symlink()]


def stage2_moved(plan: Plan, components: list[str], runs: list[dict], said_by_helper: str) -> str:
    """The words, and the kept record, of a producer's stage2 that is not what was
    recorded before dist: a manifest of the tree as dist left it, and how it differs."""
    before, after = plan.manifest_path("p"), plan.kept / "p-after-dist.stage2.json"
    partial = after.with_name(after.name + ".partial")
    partial.unlink(missing_ok=True)
    captured(plan.manifest(plan.stage2(), partial),
             f"verify-stage2-unchanged refused ({said_by_helper}), and no manifest of the stage2 dist left could be "
             "written either. Nothing was copied out; every tree is kept", env=plan.env(), cwd=plan.root)
    partial.replace(after)
    first, second = manifest_rows(before), manifest_rows(after)
    moved = differing(first, second)
    outside = [path for path in moved if path not in UNREPRODUCED_ALLOWED]
    found = {"entries_before": len(first), "entries_after": len(second), "differing": len(moved),
             "outside_allowed": len(outside), "first": moved[:10]}
    problem = (f"the producer's stage2 is not what {before} recorded before dist: {len(moved)} of its "
               f"{len(first)} entries differ in {after}, {len(outside)} of them outside "
               f"{' and '.join(UNREPRODUCED_ALLOWED)}" + (f" (the first: {', '.join(moved[:10])})" if moved else
                                                          " (none: the helper refused for another reason)"))
    write_json(plan.kept / "dist.not-clean.json", {
        "schema": DIST_SCHEMA, "commit": plan.commit, "host": plan.host, "root": str(plan.root),
        "components": components, "runs": runs, "stage2_after_dist": {"manifest": str(after), **found},
        "helper": said_by_helper, "problems": [problem], "finished": time.strftime("%Y-%m-%dT%H:%M:%S%z")})
    return (f"{problem}. {said_by_helper}. The other roles are compared with the tree {before} records, and "
            "whether the archives in build/dist are of that tree is not established either way. Kept: both "
            f"manifests, every archive in {plan.build_dir() / 'dist'}, the producer's tree and "
            f"{plan.kept / 'dist.not-clean.json'}; nothing was copied out. Every run of dist in this root reaches "
            "this check again, so the builds cannot go on past dist here: read the two manifests for what the "
            "dist runs rebuilt, and build the roles anew in a new --root")


def dist(plan: Plan) -> int:
    inputs = require_setup(plan)
    if plan.dist_record().is_file():
        was = read_json(plan.dist_record(), "the dist record")
        say(f"dist: already done ({plan.dist_record()}: {len(was.get('archives') or [])} files, "
            f"{was.get('archive_bytes_total')} bytes); not repeated")
        return 0
    if not plan.record("p").is_file():
        raise Refusal(f"dist packages the producer's build, and there is no clean one yet ({plan.record('p')} is "
                      f"not there). Nothing was started. Run: "
                      f"{shlex.join(command_line(plan, 'build', '--role', 'producer'))}")
    producer = read_json(plan.record("p"), "the producer's build record")
    require_jobserver(plan, inputs, "dist")
    preflight(plan)
    pointer = read_json(plan.current_tree(), "the record of which build's tree is in src/build") \
        if plan.current_tree().is_file() else {}
    if pointer.get("label") != producer["label"] or not plan.stage2().is_dir():
        raise Refusal(f"{plan.build_dir()} is not the producer's tree ({plan.current_tree()} names "
                      f"{pointer.get('label')!r}, the producer is {producer['label']}). dist runs in that tree "
                      "and nowhere else. Nothing was started")
    marker = read_json(plan.root / "stage0.json", "the stage0 marker")
    if marker.get("tree") != producer["stage0"]["tree"] or \
            tree_identity(plan.stage0, "the installed stage0") != producer["stage0"]["tree"]:
        raise Refusal(f"{plan.stage0} is not the producer's stage0 any more. dist is built by the compiler that "
                      "built the tree. Nothing was started")
    problems = refresh.worktree_problems(plan.src, plan.commit)
    if problems:
        raise Refusal(f"{plan.src} is not a clean checkout of {plan.commit[:10]}: {'; '.join(problems)}. Nothing "
                      "was started")
    host_dir = plan.build_dir() / plan.host
    components = captured(plan.dist_components(), "the dist component list could not be read from the checkout",
                          env=plan.env(), cwd=plan.root).split()
    if not components:
        raise Refusal(f"`{shlex.join(plan.dist_components())}` named no component. Nothing was started")
    before_path = plan.native("p-dist", "before")
    if not before_path.is_file():
        say("dist: measuring the native outputs it starts with")
        write_json(before_path, native_table(host_dir))
    before = read_json(before_path, "the native outputs before dist")
    if before["sha256"] != producer["native_after"]["sha256"]:
        raise Refusal(f"the LLVM and lld in {host_dir} are not what the producer's build left ({before['files']} "
                      f"files, digest {before['sha256'][:16]}; then {producer['native_after']['files']}, "
                      f"{producer['native_after']['sha256'][:16]}). Something changed the producer's tree after "
                      f"its build. Nothing was started; {before_path} has the table")
    require_shared(plan, inputs, shared_facts(plan, inputs), "dist")
    admission = Path(producer["admission"]["path"])
    runs = []
    for base in DIST_LABELS:
        words = dist_words(components)[base]
        label, resumed = next_label(plan, base, "run this part of dist")
        if resumed is None:
            # Every dist run starts with an empty ledger/tmp, as every role does: a run
            # killed before it could remove its FIFO jobserver left it there, and the
            # next run's would be refused.
            moved = set_aside_before(plan, label, "tmp", plan.ledger / "tmp", True)
            write_json(plan.attempt(label), {"schema": BUILD_SCHEMA, "role": "dist", "label": label,
                                             "set_aside_before": {"tmp": moved} if moved else {},
                                             "started": time.strftime("%Y-%m-%dT%H:%M:%S%z")})
            code, asked = run_label(plan, label, words, admission)
            if code:
                found = failed_run_problems(plan, label, code, asked)
                write_json(plan.not_clean(label), {"label": label, "problems": found})
                raise Refusal(not_clean_words(plan, label, found, "run this part of dist"))
        record = read_json(plan.file(label, "run.json"), "the run record")
        stage0, deficit = token_leak_judgement(plan, producer["admission"], record, inputs)
        found = run_problems(plan, record, label, words, inputs, stage0)
        if found:
            write_json(plan.not_clean(label), {"label": label, "problems": found})
            raise Refusal(not_clean_words(plan, label, found, "run this part of dist"))
        if deficit is not None:
            say(token_deficit_accepted(label, deficit))
        if resumed is not None:
            say(f"{label}: already run clean; not repeated")
        runs.append({"label": label, "argv": record.get("argv"), "elapsed_s": record.get("elapsed_s"),
                     "run": {"path": str(plan.file(label, "run.json")),
                             "sha256": sha256_file(plan.file(label, "run.json"))}})

    packaged, log = plan.build_dir() / "dist", plan.ledger / "p-channel-manifest.log"
    tool = captured(plan.manifest_tool(), "the build-manifest tool was not found in the producer's tree",
                    env=plan.env(), cwd=plan.root).strip()
    command = plan.channel_manifest(tool, plan.commit_date())
    say(f"dist: writing the channel manifest ({shlex.join(command)})")
    if refresh.to_file(command, log, env=plan.env(), cwd=plan.root, merge=True):
        raise Refusal(f"the channel manifest could not be written: `{shlex.join(command)}` failed, and its last "
                      f"line is: {refresh.last_line(log.with_name(log.name + '.partial').read_text(errors='replace'))} "
                      f"(all of it: {log}.partial). The archives in {packaged} are kept; the same command "
                      "line runs this step again and no x.py run is repeated")
    try:
        captured(plan.stage2_unchanged(), "verify-stage2-unchanged", env=plan.env(), cwd=plan.root)
    except Refusal as refusal:
        raise Refusal(stage2_moved(plan, components, runs, str(refusal))) from refusal
    archives = archive_table(packaged)
    names = [row["name"] for row in archives]
    absent = [component for component in components
              if not any(re.fullmatch(rf"{re.escape(component)}-\d.*\.tar\.xz", name) for name in names)]
    found = [f"no .tar.xz archive of {component}" for component in absent]
    # The limit is a release's per-asset limit, and the .tar.xz archives are what is published.
    over = [row for row in archives if row["name"].endswith(".tar.xz") and row["bytes"] > plan.args.asset_limit_bytes]
    found += [f"{row['name']} is {row['bytes']} bytes, over the asset limit of {plan.args.asset_limit_bytes}"
              for row in over]
    say("dist: measuring what it left")
    after = native_table(host_dir)
    write_json(plan.native("p-dist", "after"), after)
    moved = native_changes(before, after)
    if moved["changed"] or moved["removed"]:
        found.append(f"dist changed {len(moved['changed'])} and removed {len(moved['removed'])} of the LLVM and "
                     f"lld files the producer's build linked (the first: {(moved['changed'] + moved['removed'])[0]})")
    lines = trap_lines(plan.ledger)
    if lines:
        found.append(f"the trap log has {len(lines)} line(s)")
    found += [f"the checkout is not clean after dist: {problem}"
              for problem in refresh.worktree_problems(plan.src, plan.commit)]
    result = {"schema": DIST_SCHEMA, "commit": plan.commit, "host": plan.host, "root": str(plan.root),
              "components": components, "runs": runs, "channel_manifest_command": command,
              "archives": archives, "archive_bytes_total": sum(row["bytes"] for row in archives),
              "asset_limit_bytes": plan.args.asset_limit_bytes,
              "native_outputs": {"before": {"files": before["files"], "sha256": before["sha256"]},
                                 "after": {"files": after["files"], "sha256": after["sha256"]},
                                 "against_before": changes_summary(moved)},
              "trap_log_lines": len(lines), "problems": found,
              "account_named_in": {run["label"]: account_mentions(
                  read_json(Path(run["run"]["path"]), "the run record"), plan.account) for run in runs},
              "finished": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    if found:
        write_json(plan.kept / "dist.not-clean.json", result)
        raise Refusal(f"dist ran and is not usable: {'; '.join(found)}. This is the stop before the hours of the "
                      f"other builds. Kept: every archive in {packaged}, the record "
                      f"{plan.kept / 'dist.not-clean.json'} "
                      "and the producer's tree. Nothing was copied out; the same command line measures again "
                      "and repeats no x.py run")
    if not plan.dist.exists():
        refresh.copy_tree(packaged, plan.dist)
    if archive_table(plan.dist) != archives:
        raise Refusal(f"{plan.dist} is not the copy of {packaged} file for file. Nothing was recorded. Move it "
                      "aside and run this again")
    if moved["added"]:
        say(f"dist: NOTE it added {len(moved['added'])} LLVM or lld file(s) the producer's build did not have "
            f"(the first: {moved['added'][0]}); the later roles are given the tree as dist left it")
    write_json(plan.dist_record(), result)
    (plan.kept / "dist.not-clean.json").unlink(missing_ok=True)
    largest = max((row for row in archives if row["name"].endswith(".tar.xz")), key=lambda row: row["bytes"])
    say(f"dist: done; {len(archives)} files, {result['archive_bytes_total']} bytes; the largest .tar.xz is "
        f"{largest['name']}, {largest['bytes']} bytes (limit {plan.args.asset_limit_bytes}); copied to "
        f"{plan.dist}; its record is {plan.dist_record()}")
    say(f"next: {shlex.join(command_line(plan, 'prepare'))} (admits the archives and installs them into "
        f"{plan.seed}), then {shlex.join(command_line(plan, 'build', '--role', 'fixed-point'))}; the cross-check "
        f"can run now: {shlex.join(command_line(plan, 'build', '--role', 'cross-check'))}")
    return 0


# ---------------------------------------------------------------------------
# prepare (design step 9)


@functools.lru_cache(maxsize=None)
def support():
    """scripts/mint_seed_support.py as a module, loaded once."""
    return staircase().mint_support()


@functools.lru_cache(maxsize=None)
def stage0_prepare():
    """prepare.py (PREPARE_PY) as a module, loaded once and never written beside."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("fixed_point_linux_seed_prepare", PREPARE_PY)
    module = importlib.util.module_from_spec(spec)
    was, sys.dont_write_bytecode = sys.dont_write_bytecode, True
    try:
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = was
    return module


def shared_comparison(plan: Plan, name: str, pinned: Path, date: str) -> dict:
    """prepare.py's comparison of the shared archive `name`, made again from inputs
    that do not live in prepared/: this host's dist archive that `name` stands for
    (by the dist's channel manifest), repacked under prepare/ and compared member by
    member with the pinned `pinned` by prepare.py's own `compare_shared_archives`.
    The fields trust-stage0-shared-kept.json records for it."""
    prep = stage0_prepare()
    manifest = tomllib.loads((plan.dist / f"channel-rust-{CHANNEL}.toml").read_text(encoding="utf-8"))
    sources = sorted({
        Path(str(package["target"]["*"]["xz_url"])).name for package in (manifest.get("pkg") or {}).values()
        if isinstance(package, dict) and isinstance(package.get("target"), dict)
        and prep.manifest_target_is_built(package["target"].get("*"))
        and prep.stage0_tarball_filename(Path(str(package["target"]["*"]["xz_url"])).name,
                                         source_channel=CHANNEL, owned_channel=CHANNEL) == name})
    if len(sources) != 1:
        raise ValueError(f"the channel manifest of {plan.dist} lists {len(sources)} '*' archive(s) for {name}")
    side = plan.prepare_dir() / "shared-again.partial"
    remove_own(side)
    side.mkdir()
    try:
        this_run = side / name
        prep.repack_owned_tarball(prep.source_tarball(plan.dist, sources[0], date), this_run,
                                  old_filename=sources[0], new_filename=name, source_channel=CHANNEL,
                                  owned_channel=CHANNEL)
        compared = prep.compare_shared_archives(this_run, pinned, prep.tarball_prefix(name))
        return {"this_run_sha256": sha256_file(this_run), "members": compared["members"],
                "pinned_member_table_sha256": compared["pinned_member_table_sha256"],
                "excluded": compared["excluded"]}
    finally:
        remove_own(side)


def text_rows(text: str, what: str) -> dict[str, str]:
    """The key=value records of a src/stage0 text (the rule of `read_stage0_pin`)."""
    fields: dict[str, str] = {}
    for number, line in enumerate(text.splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        key, separator, value = line.partition("=")
        if not separator or not key.strip() or not value.strip():
            raise Refusal(f"{what}:{number} is not a key=value record: {line!r}")
        if key.strip() in fields:
            raise Refusal(f"{what}:{number} repeats the key {key.strip()!r}")
        fields[key.strip()] = value.strip()
    return fields


def pinned_rows(fields: dict[str, str]) -> dict[str, str]:
    return {key: value for key, value in fields.items() if key.startswith("dist/") and key.endswith(".tar.xz")}


def member_kind(head: bytes) -> str:
    if head[:4] == b"\x7fELF":
        return "elf"
    if head[:8] in (b"!<arch>\n", b"!<thin>\n"):
        return "ar"
    return "other"


def installer_line_problem(line: str) -> str | None:
    """Why install.sh would not install the plain path a manifest.in line shows
    (None: it would): `while read _directive` (no -r) rewrites a backslash and drops
    leading or trailing blanks; the directive is the text before the first ':'; a
    path is relative with no empty, '.' or '..' component (prepare.py's own rule)."""
    if "\\" in line:
        return "a backslash, which `read` without -r rewrites"
    if line != line.strip():
        return "leading or trailing whitespace, which `read` drops"
    if any(ord(char) < 0x20 or ord(char) == 0x7F for char in line) or len(line.splitlines()) > 1:
        return "a control or line-separator character"
    directive, colon, listed = line.partition(":")
    if not colon or directive not in ("file", "dir"):
        return "no file: or dir: directive"
    if not listed or any(part in ("", ".", "..") for part in listed.split("/")):
        return "an empty or absolute path, or an empty, '.' or '..' component"
    return None


def archive_members(path: Path) -> dict:
    """One pass over a pinned .tar.xz, read as data and never unpacked: its package
    root, the component directories its `components` names, and what its installer
    installs from each (the `file:` and `dir:` lines of `<component>/manifest.in`)
    by install path, mode, size, sha256 and kind (elf, ar, other) -- plus the digest
    of its whole member table. Every member must be a regular file or a directory
    (install.sh's `cp` follows a link, so a link installs bytes no row holds), every
    manifest.in line a path install.sh reads as written, every `dir:` line must
    select a member, and every regular file under a component's bin/, lib/ or
    libexec/ must be one a line installs (bootstrap's stage0 unpack extracts all of
    them, not only the listed ones)."""
    prefix = path.name.removesuffix(".tar.xz")

    def refuse(why: str) -> Refusal:
        return Refusal(f"{path} {why}. No prepare record was written, so no role builds from the seed; the "
                       "archive is kept where it is. Next: find what put that member or line in the archive (the "
                       "dist that built it, or prepare.py's repack) and run prepare again from archives without it")

    rows, texts = [], {}
    try:
        with tarfile.open(path, "r:xz") as bundle:
            for member in bundle:
                parts = member.name.split("/")
                if parts[0] != prefix or any(part in ("", ".", "..") for part in parts):
                    raise refuse(f"has the member {member.name!r} outside its package root {prefix}, or a name "
                                 "with an empty, '.' or '..' component")
                if not (member.isfile() or member.isdir()):
                    kind = "symlink" if member.issym() else "hardlink" if member.islnk() else f"type {member.type!r}"
                    raise refuse(f"has the member {member.name!r}, a {kind}"
                                 f"{' to ' + repr(member.linkname) if member.linkname else ''}: every member must be "
                                 "a regular file or a directory, since install.sh's cp copies what a link points at")
                row = {"path": member.name, "type": "file" if member.isfile() else "dir" if member.isdir()
                       else "symlink" if member.issym() else "hardlink" if member.islnk() else "other",
                       "mode": member.mode, "bytes": member.size if member.isfile() else 0,
                       "sha256": None, "kind": None, "link": member.linkname or None}
                if member.isfile():
                    handle = bundle.extractfile(member)
                    digest, head = hashlib.sha256(), b""
                    for block in iter(lambda: handle.read(1 << 20), b""):
                        head = head or block[:8]
                        digest.update(block)
                        if parts[1:] == ["components"] or parts[2:] == ["manifest.in"]:
                            texts[member.name] = texts.get(member.name, b"") + block
                    row["sha256"], row["kind"] = digest.hexdigest(), member_kind(head)
                rows.append(row)
    except (tarfile.TarError, OSError, EOFError) as error:
        raise Refusal(f"{path} cannot be read as a .tar.xz: {error}") from error
    by_path = {row["path"]: row for row in rows}
    if len(by_path) != len(rows):
        raise refuse("lists a member twice")
    listed = texts.get(f"{prefix}/components")
    if listed is None:
        raise refuse(f"has no regular file {prefix}/components, so what its installer installs is unknown")
    # install.sh splits components with `for _component in $_components`: on space, tab and newline only.
    odd = sorted({byte for byte in listed if not re.fullmatch(rb"[A-Za-z0-9._\- \t\n]", bytes([byte]))})
    if odd:
        raise refuse(f"has {prefix}/components with bytes other than letters, digits, '.', '_', '-', space, tab and "
                     f"newline ({bytes(odd)!r}): install.sh splits it on space, tab and newline only, so the "
                     "components it reads are not the ones another split shows")
    components = [word.decode("ascii") for word in re.split(rb"[ \t\n]+", listed) if word]
    installed: dict[str, dict] = {}
    covered: set[str] = set()
    for component in components:
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", component):
            raise refuse(f"names the component {component!r} in {prefix}/components, which is not one directory "
                         "below the package root")
        manifest = texts.get(f"{prefix}/{component}/manifest.in")
        if manifest is None:
            raise refuse(f"names the component {component} and has no {prefix}/{component}/manifest.in")
        base = f"{prefix}/{component}/"
        # Split on "\n" only, as install.sh's `while read` does.
        lines = manifest.decode("utf-8", "replace").split("\n")
        if lines and lines[-1] == "":
            lines.pop()
        for line in lines:
            why = installer_line_problem(line)
            if why is not None:
                raise refuse(f"has the line {line!r} in {base}manifest.in, which is not a file: or dir: path "
                             f"install.sh reads as written ({why})")
            directive, _, listed_path = line.partition(":")
            chosen = [by_path[base + listed_path]] if directive == "file" and base + listed_path in by_path else \
                [] if directive == "file" else \
                [row for row in rows if row["path"].startswith(base + listed_path + "/")]
            if directive == "file" and not chosen:
                raise refuse(f"lists {listed_path} in {base}manifest.in, which the archive does not carry")
            if directive == "dir" and not chosen:
                raise refuse(f"lists the directory {listed_path} in {base}manifest.in, and no member is below "
                             f"{base}{listed_path}/: a dir: line must select what install.sh copies")
            covered.update(row["path"] for row in chosen)
            for row in chosen:
                if row["type"] == "dir":
                    continue
                target = row["path"][len(base):]
                if target in installed and installed[target]["sha256"] != row["sha256"]:
                    raise refuse(f"installs {target} twice with different bytes")
                installed[target] = {"path": target, "component": component, "type": row["type"],
                                     "mode": row["mode"], "bytes": row["bytes"], "sha256": row["sha256"],
                                     "kind": row["kind"], "link": row["link"]}
        unlisted = sorted(row["path"] for row in rows if row["type"] == "file" and row["path"] not in covered
                          and row["path"][len(base):].startswith(INSTALLED_TOPS) and row["path"].startswith(base))
        if unlisted:
            raise refuse(f"carries {len(unlisted)} file(s) under {base}(bin|lib|libexec)/ that no manifest.in line "
                         f"installs ({unlisted[:3]}): bootstrap's stage0 unpack extracts every member there, so "
                         "each must be one the installer installs and the stage2 join compares")
    return {"name": path.name, "prefix": prefix, "components": components, "members": len(rows),
            "members_sha256": rows_sha256(rows), "installed": [installed[key] for key in sorted(installed)]}


def join_members(archive: dict, stage2: dict[str, dict]) -> list[dict]:
    """Each installed bin/, lib/, libexec/ file of an archive against the producer's
    stage2 row at its path: same, differs, or none."""
    joined = []
    for row in archive["installed"]:
        if not row["path"].startswith(INSTALLED_TOPS):
            continue
        theirs = stage2.get(row["path"])
        if theirs is None:
            verdict = "none"
        elif row["type"] == "file":
            verdict = "same" if theirs.get("kind") == "file" and theirs.get("sha256") == row["sha256"] else "differs"
        else:
            verdict = "same" if theirs.get("kind") == row["type"] and theirs.get("target") == row["link"] \
                else "differs"
        joined.append({"path": row["path"], "type": row["type"], "kind": row["kind"], "sha256": row["sha256"],
                       "stage2": verdict})
    return joined


def tree_files(top: Path) -> dict[str, dict]:
    """Every file and link under `top` by path, as `archive_members` lists an installed one."""
    found = {}
    for directory, dirnames, filenames in os.walk(top):
        dirnames.sort()
        for name in sorted(dirnames + filenames):
            path = Path(directory) / name
            relative = path.relative_to(top).as_posix()
            if path.is_symlink():
                found[relative] = {"type": "symlink", "link": os.readlink(path)}
            elif path.is_file():
                found[relative] = {"type": "file", "sha256": sha256_file(path), "mode": path.stat().st_mode & 0o777}
    return found


def seed_problems(seed: Path, installed: dict[str, dict]) -> tuple[list[str], list[str]]:
    """(problems, the installer's own files) of an installed seed against what the
    pinned archives install: every file must be one of their members, byte for
    byte, and every member must be there; the only other files are the installer's
    bookkeeping under lib/rustlib."""
    files = tree_files(seed)
    bookkeeping = sorted(path for path in files if INSTALLER_BOOKKEEPING.fullmatch(path) and path not in installed)
    problems = []
    for path, row in sorted(files.items()):
        if path in bookkeeping:
            continue
        member = installed.get(path)
        if member is None:
            problems.append(f"{path} is in the seed and no pinned archive installs it")
        elif row["type"] != member["type"] or row.get("sha256") != member["sha256"] or \
                row.get("link") != member["link"]:
            problems.append(f"{path} is not the pinned member's bytes")
    problems += [f"{path} is installed by a pinned archive and is not in the seed"
                 for path in sorted(set(installed) - set(files))]
    return problems, bookkeeping


def prepare_steps_say(plan: Plan, name: str, started: float, steps: dict) -> None:
    steps[name] = round(time.monotonic() - started, 1)
    say(f"prepare: {name} done ({steps[name]} s)")


def run_logged(plan: Plan, name: str, command: list[str], doing: str) -> str:
    """A helper whose output is kept as prepare/<name>.out and .err; a failure is a refusal."""
    out, err = plan.prepare_dir() / f"{name}.out", plan.prepare_dir() / f"{name}.err"
    with open(out, "wb") as sink, open(err, "wb") as errors:
        try:
            code = subprocess.run(command, stdout=sink, stderr=errors, env=plan.env(), cwd=plan.root).returncode
        except OSError as error:
            raise Refusal(f"{doing}: `{shlex.join(command)}` could not be started: {error.strerror or error}") \
                from error
    if code:
        raise Refusal(f"{doing}: `{shlex.join(command)}` {refresh.ended(code)}, and the last line it printed on "
                      f"stderr is: {refresh.last_line(err.read_text(errors='replace'))} (all of it: {err}, {out})")
    return out.read_text(errors="replace")


def require_clean_dist(plan: Plan) -> tuple[dict, dict]:
    """(dist.json, the producer's build record) of a dist that finished clean, with
    the copy in <root>/dist still its archives file for file."""
    if not plan.record("p").is_file():
        raise Refusal(f"prepare admits the producer's dist, and there is no clean producer build ({plan.record('p')} "
                      f"is not there). Nothing was started. Run: "
                      f"{shlex.join(command_line(plan, 'build', '--role', 'producer'))}")
    for path, why in ((plan.kept / "dist.not-clean.json", "dist ran and is not usable"),
                      (plan.kept / "p-after-dist.stage2.json", "the producer's stage2 moved during dist")):
        if path.is_file():
            raise Refusal(f"{why} ({path}): the archives are not known to be of the compared tree. Nothing was "
                          "started; prepare admits only a dist that finished clean")
    if not plan.dist_record().is_file():
        raise Refusal(f"dist is not done ({plan.dist_record()} is not there). Nothing was started. Run: "
                      f"{shlex.join(command_line(plan, 'dist'))}")
    dist_record = read_json(plan.dist_record(), "the dist record")
    if dist_record.get("schema") != DIST_SCHEMA or dist_record.get("problems") or \
            dist_record.get("commit") != plan.commit or dist_record.get("host") != plan.host:
        raise Refusal(f"{plan.dist_record()} is not the record of a clean dist of {plan.commit[:10]} on {plan.host} "
                      f"(schema {dist_record.get('schema')!r}, problems {dist_record.get('problems')!r}). Nothing "
                      "was started")
    if not plan.dist.is_dir() or archive_table(plan.dist) != dist_record.get("archives"):
        raise Refusal(f"{plan.dist} is not the dist {plan.dist_record()} records, file for file. Nothing was "
                      "started; it is the copy prepare admits, and it must not change after dist")
    if not plan.manifest_path("p").is_file():
        raise Refusal(f"the producer's stage2 manifest {plan.manifest_path('p')} is not there. Nothing was started")
    return dist_record, read_json(plan.record("p"), "the producer's build record")


def read_parent(plan: Plan) -> dict:
    """The pin the seed joins: src/stage0 and its channel manifest at --parent, read
    from git and bound by digest. It must pin this commit, and not this host."""
    commit = plan.parent_commit()
    stage0_bytes = plan.parent_file(commit, "src/stage0")
    fields = text_rows(stage0_bytes.decode("utf-8"), f"{commit[:10]}:src/stage0")
    for key, mine in (("compiler_git_commit_hash", plan.commit), ("rustfmt_git_commit_hash", plan.commit)):
        if fields.get(key) != mine:
            raise Refusal(f"the parent {commit[:10]} pins {key} = {fields.get(key)!r}, and this root builds {mine}. "
                          "Nothing was started; the seed joins the pin of its own commit. Give --parent a commit "
                          f"whose src/stage0 pins {mine[:10]}")
    date, version = fields.get("compiler_date", ""), fields.get("compiler_version", "")
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", date) or not version.endswith("-trust") or not fields.get("dist_server"):
        raise Refusal(f"the parent {commit[:10]}'s src/stage0 declares no usable compiler_date, compiler_version or "
                      f"dist_server ({date!r}, {version!r}). Nothing was started")
    rows = pinned_rows(fields)
    mine = [key for key in rows if key.endswith(f"-{plan.host}.tar.xz")]
    if mine:
        raise Refusal(f"the parent {commit[:10]} already pins {plan.host} ({mine[0]} and {len(mine) - 1} more). "
                      "Nothing was started; a host is added to a pin once")
    if not rows or any(not key.startswith(f"dist/{date}/") for key in rows):
        raise Refusal(f"the parent {commit[:10]}'s src/stage0 pins no archive, or one outside dist/{date}/. "
                      "Nothing was started")
    manifest_path = PARENT_MANIFEST.format(date=date)
    manifest = plan.parent_file(commit, manifest_path)
    if hashlib.sha256(manifest).hexdigest() != fields.get("compiler_channel_manifest_hash"):
        raise Refusal(f"the parent {commit[:10]}'s {manifest_path} has sha256 "
                      f"{hashlib.sha256(manifest).hexdigest()}, and its src/stage0 pins "
                      f"compiler_channel_manifest_hash = {fields.get('compiler_channel_manifest_hash')}. "
                      "Nothing was started")
    # The manifest is part of the pin too: one that lists this host as built already pins it.
    try:
        packages = tomllib.loads(manifest.decode("utf-8")).get("pkg")
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        packages = error
    if not isinstance(packages, dict):
        raise Refusal(f"the parent {commit[:10]}'s {manifest_path} is not a TOML channel manifest with a [pkg] table "
                      f"({packages!r}). Nothing was started. Give --parent a commit whose pin is one")
    built = sorted(f"pkg.{name}.target.{plan.host}" for name, package in packages.items()
                   if isinstance(package, dict) and isinstance(package.get("target"), dict)
                   and isinstance(package["target"].get(plan.host), dict)
                   and package["target"][plan.host].get("xz_url"))
    if built:
        raise Refusal(f"the parent {commit[:10]}'s {manifest_path} already lists {plan.host} as built ({built[0]} and "
                      f"{len(built) - 1} more). Nothing was started; a host is added to a pin once. Give --parent a "
                      f"commit whose pin does not name {plan.host}")
    return {"commit": commit, "stage0": stage0_bytes, "fields": fields, "rows": rows, "date": date,
            "version": version, "server": fields["dist_server"], "manifest_path": manifest_path,
            "manifest": manifest}


def check_cohort(plan: Plan, parent: dict) -> list[dict]:
    """The pinned archives, read as data (hashed, never unpacked or run): each must be
    the bytes the parent pins."""
    cohort, rows = plan.args.cohort, []
    for key, digest in sorted(parent["rows"].items()):
        path = cohort / Path(key).name
        if path.is_symlink() or not path.is_file():
            raise Refusal(f"the pinned archive {Path(key).name} is not a regular file in {cohort}. Nothing was "
                          "started. Fetch the parent's pinned archives into --cohort (each is checked against "
                          "src/stage0)")
        actual = sha256_file(path)
        if actual != digest:
            raise Refusal(f"{path} has sha256 {actual}, and the parent {parent['commit'][:10]} pins {digest}. Nothing "
                          "was started; fetch the pinned archive again")
        rows.append({"name": path.name, "bytes": path.stat().st_size, "sha256": actual})
    return rows


def linux_rows(plan: Plan, parent: dict, version: str) -> list[str]:
    """The pin rows this host adds: every seed component but the shared source archive."""
    return sorted(f"dist/{parent['date']}/{component}-{version}-trust-{plan.host}.tar.xz"
                  for component in support().SEED_COMPONENTS if component != "trust-src")


def manifest_problems(plan: Plan, parent: dict, merged: dict, candidate: dict[str, str]) -> list[str]:
    """Every table of the merged channel manifest but this host's targets must be
    the parent's, and this host's must be the archives the candidate pins."""
    before = tomllib.loads(parent["manifest"].decode("utf-8"))
    problems = [f"the manifest's {key} changed" for key in sorted(before.keys() | merged.keys())
                if key != "pkg" and before.get(key) != merged.get(key)]
    old, new = before.get("pkg") or {}, merged.get("pkg") or {}
    if set(old) != set(new):
        problems.append(f"the manifest's packages changed: {sorted(set(old) ^ set(new))}")
    for name in sorted(set(old) & set(new)):
        mine, theirs = dict(new[name]), dict(old[name])
        targets, earlier = mine.pop("target", {}), theirs.pop("target", {})
        if mine != theirs:
            problems.append(f"pkg.{name} changed outside its targets")
        for triple in sorted(set(targets) | set(earlier)):
            if triple == plan.host:
                continue
            if targets.get(triple) != earlier.get(triple):
                problems.append(f"pkg.{name}.target.{triple} changed")
        entry = targets.get(plan.host)
        if isinstance(entry, dict) and entry.get("xz_url"):
            key = f"dist/{entry['xz_url'].split('/dist/', 1)[-1]}"
            if candidate.get(key) != entry.get("xz_hash") or \
                    entry["xz_url"] != f"{parent['server'].rstrip('/')}/{key}":
                problems.append(f"pkg.{name}.target.{plan.host} is not the archive the candidate pins ({key})")
    return problems


def verify_prepared(plan: Plan, parent: dict, version: str) -> dict:
    """The candidate src/stage0 and the output root, read from files: the parent's
    rows and shared archive unchanged, this host's rows added, every archive the
    bytes its row pins, nothing else in the output root, and the kept record of the
    shared archive what its comparison gives when made again (`shared_comparison`)."""
    output = plan.output_root()
    date, dated = parent["date"], plan.output_root() / "dist" / parent["date"]
    generated = (plan.prepared() / "src-stage0").read_text()
    try:
        text = support().splice_stage0(parent["stage0"].decode("utf-8"), generated)
    except support().WorkflowError as error:
        raise Refusal(f"the candidate src/stage0 could not be made from the parent's and {plan.prepared()}/src-stage0: "
                      f"{error}") from error
    candidate_path = plan.prepare_dir() / "stage0.candidate"
    partial = candidate_path.with_name(candidate_path.name + ".partial")
    partial.write_text(text)
    partial.replace(candidate_path)
    fields = text_rows(text, str(candidate_path))
    manifest_bytes = (output / "dist" / "channel-rust-trust.toml").read_bytes()
    manifest_hash = hashlib.sha256(manifest_bytes).hexdigest()
    problems = []
    for key, was in sorted(parent["fields"].items()):
        now = fields.get(key)
        if key in ("compiler_channel_manifest_hash", "rustfmt_channel_manifest_hash"):
            if now != manifest_hash or now == was:
                problems.append(f"{key} is {now!r}: not the new manifest's sha256 {manifest_hash}")
        elif now != was:
            problems.append(f"the parent's {key} = {was} is {now!r} in the candidate")
    added = sorted(set(fields) - set(parent["fields"]))
    expected = linux_rows(plan, parent, version)
    if added != expected:
        problems.append(f"the candidate adds {added}, and this host adds exactly {expected}")
    pins = pinned_rows(fields)
    archives = sorted(path.name for path in dated.iterdir() if path.name.endswith(".tar.xz")) if dated.is_dir() else []
    if archives != sorted(Path(key).name for key in pins):
        problems.append(f"{dated} holds {len(archives)} archives, and the candidate pins {len(pins)} "
                        f"(other: {sorted(set(archives) ^ {Path(key).name for key in pins})[:5]})")
    hashed = {}
    for key, digest in sorted(pins.items()):
        path = dated / Path(key).name
        if path.is_file() and not path.is_symlink():
            hashed[key] = sha256_file(path)
            if hashed[key] != digest:
                problems.append(f"{path} has sha256 {hashed[key]}, and the candidate pins {digest}")
        elif path.exists() or path.is_symlink():
            problems.append(f"{path} is not a regular file (prepare.py writes each pinned archive as one)")
    expected_files = {f"dist/{date}/{Path(key).name}" for key in pins} | {
        "dist/channel-rust-trust.toml", "dist/channel-rust-trust.toml.sha256",
        f"dist/{date}/channel-rust-trust.toml", f"dist/{date}/channel-rust-trust.toml.sha256",
        "trust-stage0-admission.json", "trust-stage0-shared-kept.json"}
    expected_directories = {"dist", f"dist/{date}", "artifacts", "artifacts-with-llvm-assertions",
                            f"artifacts/{plan.commit}", f"artifacts-with-llvm-assertions/{plan.commit}"}
    stray, stray_directories, links = [], [], []
    for directory, dirnames, filenames in os.walk(output):
        # A link to a directory is listed in dirnames and not followed: it is judged, never walked.
        for name in dirnames + filenames:
            path = Path(directory) / name
            relative = path.relative_to(output).as_posix()
            if path.is_symlink():
                links.append(relative)
            elif name in dirnames:
                if relative not in expected_directories:
                    stray_directories.append(relative)
            elif relative not in expected_files and not re.fullmatch(
                    rf"artifacts(-with-llvm-assertions)?/{plan.commit}/trustc-dev-{re.escape(version)}-trust-"
                    rf"{re.escape(plan.host)}\.tar\.xz", relative):
                stray.append(relative)
    if stray:
        problems.append(f"the output root holds files prepare.py does not write: {sorted(stray)[:5]}")
    if stray_directories:
        problems.append(f"the output root holds directories prepare.py does not make: {sorted(stray_directories)[:5]}")
    if links:
        problems.append(f"the output root holds links, which prepare.py does not write: {sorted(links)[:5]}")
    if (output / "dist" / date / "channel-rust-trust.toml").read_bytes() != manifest_bytes:
        problems.append("the dated channel manifest is not the latest one")
    admission = read_json(output / "trust-stage0-admission.json", "prepare.py's admission")
    if admission.get("manifest_hash") != manifest_hash or admission.get("git_commit_hash") != plan.commit or \
            {row.get("relative_path"): row.get("sha256") for row in admission.get("payloads") or []} != pins:
        problems.append("trust-stage0-admission.json does not admit exactly the candidate's archives and manifest")
    kept = read_json(output / "trust-stage0-shared-kept.json", "prepare.py's record of the shared archive")
    # The host-independent archives: no triple after the channel.
    shared = sorted(Path(key).name for key in parent["rows"] if Path(key).name.endswith(f"-{version}-trust.tar.xz"))
    kept_rows = {row.get("filename"): row for row in kept.get("kept") or []}
    for name in shared:
        row = kept_rows.get(name)
        if row is None or row.get("pinned_sha256") != parent["rows"][f"dist/{date}/{name}"] or \
                any(item.get("path") != "builder-config" for item in row.get("excluded") or []):
            problems.append(f"{output}/trust-stage0-shared-kept.json does not say {name} was kept with at most "
                            "builder-config excluded")
        if fields.get(f"dist/{date}/{name}") != parent["rows"][f"dist/{date}/{name}"]:
            problems.append(f"the shared {name} is not the parent's pinned bytes in the candidate")
        if row is None:
            continue
        # The record lives in prepared/, which made-by.json does not bind: its comparison is made again.
        import lzma  # what an xz stream that does not decode raises
        try:
            again = shared_comparison(plan, name, dated / name, date)
        except (ValueError, OSError, EOFError, KeyError, TypeError, tarfile.TarError, tomllib.TOMLDecodeError,
                lzma.LZMAError, Refusal) as error:
            problems.append(f"the comparison of {name} with this host's dist could not be made again ({error})")
            continue
        moved = sorted(key for key, value in again.items() if row.get(key) != value)
        if moved:
            problems.append(f"{output}/trust-stage0-shared-kept.json records {name} with another {', '.join(moved)} "
                            f"than its comparison made again from {plan.dist} and the pinned archive")
    problems += manifest_problems(plan, parent, tomllib.loads(manifest_bytes.decode("utf-8")), fields)
    if problems:
        raise Refusal(f"the prepared seed in {plan.prepared()} is not the parent's pin plus this host: "
                      f"{'; '.join(problems[:6])}{'; ...' if len(problems) > 6 else ''}. Nothing was installed "
                      f"from it; the candidate is {candidate_path}. The output root is kept as it is; move "
                      f"{plan.prepared()} aside to prepare it again")
    return {"candidate": {"path": str(candidate_path), "sha256": sha256_file(candidate_path)},
            "rows": {"kept": len(parent["rows"]), "added": added},
            "manifest": {"path": str(output / "dist" / "channel-rust-trust.toml"), "sha256": manifest_hash},
            "archives": [{"name": Path(key).name, "sha256": hashed[key]} for key in sorted(pins)],
            "admission": {"path": str(output / "trust-stage0-admission.json"),
                          "sha256": sha256_file(output / "trust-stage0-admission.json")},
            "shared": shared,
            "shared_kept": {"path": str(output / "trust-stage0-shared-kept.json"),
                            "sha256": sha256_file(output / "trust-stage0-shared-kept.json"),
                            "kept": [{key: row.get(key) for key in ("filename", "pinned_sha256", "this_run_sha256",
                                                                    "excluded")} for row in kept_rows.values()]},
            "generated": {"path": str(plan.prepared() / "src-stage0"),
                          "sha256": sha256_file(plan.prepared() / "src-stage0")},
            "made_by": read_json(plan.prepared() / "made-by.json", "the record of what made prepared/")}


def admit(plan: Plan, label: str, dist: Path, version: str, steps: dict) -> dict:
    """`stage-artifacts` of the five installable components in `dist`, into
    prepare/<label>/ (whole, or not there)."""
    work = plan.prepare_dir() / label
    if not (work / "seed-inputs.json").is_file():
        partial = work.with_name(work.name + ".partial")
        remove_own(partial)
        remove_own(work)
        partial.mkdir(parents=True)
        started = time.monotonic()
        run_logged(plan, f"{label}.stage-artifacts", plan.stage_artifacts(dist, partial, version),
                   f"the archives in {dist} were not admitted (the unfinished {partial} is removed by the next run)")
        partial.rename(work)
        prepare_steps_say(plan, label, started, steps)
    admitted = read_json(work / "seed-inputs.json", "the admitted seed-input manifest")
    if admitted.get("source_commit") != plan.commit or admitted.get("host") != plan.host:
        raise Refusal(f"{work / 'seed-inputs.json'} admits {admitted.get('source_commit')} on {admitted.get('host')}, "
                      f"not {plan.commit} on {plan.host}. Nothing was installed")
    for row in admitted.get("artifacts") or []:
        source = dist / str(row.get("filename"))
        if not source.is_file() or sha256_file(source) != row.get("sha256"):
            raise Refusal(f"{source} is not the archive {work / 'seed-inputs.json'} admitted (sha256 "
                          f"{row.get('sha256')}). Nothing was installed; move {work} aside and run prepare again")
    return {"path": str(work / "seed-inputs.json"), "sha256": sha256_file(work / "seed-inputs.json"),
            "artifacts": [{key: row.get(key) for key in ("filename", "sha256")} for row in admitted["artifacts"]]}


def make_prepared(plan: Plan, parent: dict, cohort: list[dict], steps: dict) -> None:
    """<root>/prepared: the handoff, the parent's manifest and pinned archives, then
    prepare.py over this host's dist; renamed into place only when prepare.py exits 0,
    with made-by.json naming what made it. A prepared/ made by another prepare.py, dist
    or parent is not adopted."""
    maker = {"schema": "trust-fixed-point-linux-seed-prepared-maker-v1",
             "prepare.py": sha256_file(PREPARE_PY),
             "admitted_dist": sha256_file(plan.prepare_dir() / "admit-dist" / "seed-inputs.json"),
             "dist_record": sha256_file(plan.dist_record()), "parent_commit": parent["commit"]}
    made_by = plan.prepared() / "made-by.json"
    if plan.prepared().is_dir():
        try:
            was = json.loads(made_by.read_text()) if made_by.is_file() and not made_by.is_symlink() else None
        except (OSError, ValueError):
            was = "unreadable"
        if was != maker:
            said = ("is not there" if was is None else "is not a JSON object" if not isinstance(was, dict) else
                    "differs in " + ", ".join(sorted(key for key in maker.keys() | was.keys()
                                                     if was.get(key) != maker.get(key))))
            raise Refusal(f"{plan.prepared()} was not made by this run's prepare.py, admitted dist, dist record and "
                          f"parent ({made_by} {said}). Nothing was changed or installed. Move {plan.prepared()} aside "
                          "and run prepare again (prepare.py runs again over this host's dist)")
        return
    partial = plan.root / "prepared.partial"
    remove_own(partial)
    output = plan.output_root(partial)
    started = time.monotonic()
    run_logged(plan, "rustc-dev-handoff", plan.handoff(plan.prepare_dir() / "admit-dist" / "seed-inputs.json",
                                                       plan.prepare_dir() / "admit-dist", output),
               "the trustc-dev handoff prepare.py checks could not be laid out")
    dated = output / "dist" / parent["date"]
    dated.mkdir(parents=True, exist_ok=True)
    for path in (output / "dist" / "channel-rust-trust.toml", dated / "channel-rust-trust.toml"):
        path.write_bytes(parent["manifest"])
    for row in cohort:
        target = dated / row["name"]
        shutil.copyfile(plan.args.cohort / row["name"], target)
        if sha256_file(target) != row["sha256"]:
            raise Refusal(f"the copy {target} is not the pinned archive (sha256 {row['sha256']}). The unfinished "
                          f"{partial} is removed by the next run")
    run_logged(plan, "prepare.py", plan.prepare_py(plan.dist, output, partial / "src-stage0", parent["date"],
                                                   parent["server"]),
               f"prepare.py refused to join this host's archives to the parent's pin (the unfinished {partial} is "
               "removed by the next run)")
    write_json(partial / made_by.name, maker)
    partial.rename(plan.prepared())
    prepare_steps_say(plan, "prepared", started, steps)


def install_seed(plan: Plan, admitted: dict, version: str, steps: dict) -> dict:
    """<root>/seed: the five installable components of the pinned archives, each by
    its own install.sh, at the path every later role reads. A seed without the
    marker is an unfinished install of this step's own, removed and made again."""
    marker, begun = plan.prepare_dir() / "installed.json", plan.prepare_dir() / "installing.json"
    if marker.is_file():
        was = read_json(marker, "the record of the installed seed")
        if was.get("admitted_sha256") != admitted["sha256"] or \
                tree_identity(plan.seed, "the installed seed") != was.get("tree"):
            raise Refusal(f"{plan.seed} is not the tree {marker} records (or was installed from other admitted "
                          "archives). Nothing was changed. Move the seed and the marker aside and run prepare again")
        return was
    if (plan.seed.exists() or plan.seed.is_symlink()) and not begun.is_file():
        raise Refusal(f"{plan.seed} exists, and this step did not start installing it ({begun} is not there): "
                      "prepare removes only an install of its own that stopped. Nothing was changed. Move it aside "
                      "and run prepare again")
    write_json(begun, {"admitted_sha256": admitted["sha256"]})
    # A new install is not the seed an earlier validate-seed examined: its surface goes too.
    for stale in (plan.prepare_dir() / "seed-surface.json", plan.prepare_dir() / "seed-surface.json.partial"):
        stale.unlink(missing_ok=True)
    remove_own(plan.seed)
    started = time.monotonic()
    work = Path(admitted["path"]).parent
    plan.seed.mkdir()
    for component in support().COMPONENTS:
        package = f"{component}-{version}-trust-{plan.host}"
        run_logged(plan, f"install-{component}", plan.install(work / "unpack" / component / package / "install.sh"),
                   f"{package}'s install.sh did not install it into {plan.seed} (the unfinished seed is removed by "
                   "the next run)")
    now = {"admitted_sha256": admitted["sha256"], "tree": tree_identity(plan.seed, "the installed seed"),
           "components": list(support().COMPONENTS)}
    write_json(marker, now)
    begun.unlink()
    prepare_steps_say(plan, "install", started, steps)
    return now


def prepare_seed(plan: Plan) -> int:
    require_setup(plan)
    if plan.prepare_record().is_file():
        was = read_json(plan.prepare_record(), "the prepare record")
        tree = (was.get("seed") or {}).get("tree") or {}
        if not plan.seed.is_dir() or tree_identity(plan.seed, "the installed seed") != tree:
            raise Refusal(f"{plan.seed} is not the seed {plan.prepare_record()} records. Nothing was changed. A "
                          "seed that changed after prepare is no stage0 for any role; set up a new --root")
        archives = len((was.get("prepared") or {}).get("archives") or [])
        say(f"prepare: already done ({plan.prepare_record()}: {archives} archives, seed {tree.get('entries')} "
            "entries); not repeated")
        return 0
    dist_record, producer = require_clean_dist(plan)
    preflight(plan)
    plan.prepare_dir().mkdir(exist_ok=True)
    steps: dict = {}
    trap_before = len(trap_lines(plan.ledger))
    version = captured(plan.version(), "the version of the commit could not be read", env=plan.env(),
                       cwd=plan.root).strip()
    parent = read_parent(plan)
    if parent["version"] != f"{version}-trust":
        raise Refusal(f"the parent pins compiler_version {parent['version']}, and the checkout is {version}. "
                      "Nothing was started")
    cohort = check_cohort(plan, parent)
    say(f"prepare: the parent {parent['commit'][:10]} pins {len(parent['rows'])} archives of {plan.commit[:10]} "
        f"({parent['date']}); each is in {plan.args.cohort} with its pinned bytes")
    admitted_dist = admit(plan, "admit-dist", plan.dist, version, steps)
    make_prepared(plan, parent, cohort, steps)
    prepared = verify_prepared(plan, parent, version)
    say(f"prepare: the candidate keeps the parent's {prepared['rows']['kept']} rows and adds "
        f"{len(prepared['rows']['added'])}; {prepared['candidate']['path']}")
    admitted_pinned = admit(plan, "admit-pinned", plan.output_root() / "dist" / parent["date"], version, steps)
    installed = install_seed(plan, admitted_pinned, version, steps)
    surface = plan.prepare_dir() / "seed-surface.json"
    if not surface.is_file():
        started = time.monotonic()
        draft = surface.with_name(surface.name + ".partial")
        draft.unlink(missing_ok=True)
        run_logged(plan, "validate-seed", plan.validate_seed(version, draft),
                   f"validate-seed refused the installed seed {plan.seed}")
        draft.replace(surface)
        prepare_steps_say(plan, "validate-seed", started, steps)
    try:
        seen = json.loads(surface.read_text()).get("tree")
    except (OSError, ValueError, AttributeError):
        seen = None
    if not isinstance(seen, dict) or [seen.get("sha256"), seen.get("entries")] != \
            [installed["tree"]["sha256"], installed["tree"]["entries"]]:
        raise Refusal(f"{surface} is validate-seed's surface of another tree ({seen!r}), and the seed installed "
                      f"is {installed['tree']}: validate-seed did not examine this seed. No prepare record was "
                      f"written; the seed and {plan.prepared()} are kept. Move {surface} aside and run prepare again "
                      "(validate-seed runs again over this seed)")
    carried = run_logged(plan, "verify-archives-carry-compared", plan.carried(),
                         f"the pinned archives, installed at {plan.seed}, do not carry the producer's compared bytes")
    started = time.monotonic()
    stage2 = manifest_rows(plan.manifest_path("p"))
    members, problems, installed_by = [], [], {}
    for row in prepared["archives"]:
        path = plan.output_root() / "dist" / parent["date"] / row["name"]
        if row["name"] in prepared["shared"]:
            # The parent's bytes (verify_prepared): only its member table's digest is recorded.
            table = archive_members(path)
            members.append({"name": row["name"], "sha256": row["sha256"], "shared": True,
                            "members": table["members"], "members_sha256": table["members_sha256"]})
            continue
        if not row["name"].endswith(f"-{plan.host}.tar.xz"):
            continue        # another host's pinned archive: the parent's bytes, not opened
        table = archive_members(path)
        joined = join_members(table, stage2)
        for item in joined:
            if item["stage2"] == "differs":
                problems.append(f"{row['name']} ships {item['path']} with other bytes than the producer's stage2 "
                                "row at that path")
            elif item["stage2"] == "none" and item["kind"] in CODE_KINDS:
                problems.append(f"{row['name']} ships the {item['kind']} file {item['path']}, and the producer's "
                                "stage2 has no row at that path")
        if row["name"].split(f"-{version}-trust-")[0] in support().COMPONENTS:
            for item in table["installed"]:
                if item["path"] in installed_by and installed_by[item["path"]]["sha256"] != item["sha256"]:
                    problems.append(f"two pinned archives install {item['path']} with different bytes")
                installed_by[item["path"]] = item
        members.append({"name": row["name"], "sha256": row["sha256"], "members": table["members"],
                        "members_sha256": table["members_sha256"], "components": table["components"],
                        "installed": table["installed"], "joined": joined})
    joined_rows = [item for archive in members for item in archive.get("joined", [])]
    counts = {verdict: sum(item["stage2"] == verdict for item in joined_rows)
              for verdict in ("same", "differs", "none")}
    counts["none_by_kind"] = {kind: sum(item["stage2"] == "none" and item["kind"] == kind for item in joined_rows)
                              for kind in ("elf", "ar", "other")}
    table_path = plan.prepare_dir() / "archive-members.json"
    write_json(table_path, {"schema": MEMBERS_SCHEMA, "commit": plan.commit, "host": plan.host,
                            "stage2": {"path": str(plan.manifest_path("p")),
                                       "sha256": sha256_file(plan.manifest_path("p"))},
                            "counts": counts, "archives": members})
    seed_wrong, bookkeeping = seed_problems(plan.seed, installed_by)
    problems += seed_wrong
    if tree_identity(plan.seed, "the installed seed") != installed["tree"]:
        problems.append(f"{plan.seed} changed after it was installed (validate-seed runs its tools)")
    prepare_steps_say(plan, "members", started, steps)
    if problems:
        raise Refusal(f"the pinned archives or the seed installed from them are not the producer's compared tree: "
                      f"{'; '.join(problems[:6])}{'; ...' if len(problems) > 6 else ''} ({len(problems)} in all). "
                      f"No prepare record was written, so no role builds from {plan.seed}. Kept: {plan.prepared()}, "
                      f"{plan.seed} and the member table {table_path}")
    lines = trap_lines(plan.ledger)
    if len(lines) != trap_before:
        raise Refusal(f"a step of prepare reached a stock Rust tool name: {plan.ledger / 'trap.log'} grew by "
                      f"{len(lines) - trap_before} line(s) (the first new: {lines[trap_before]!r}). No prepare "
                      "record was written")
    record = {
        "schema": PREPARE_SCHEMA, "commit": plan.commit, "host": plan.host, "root": str(plan.root),
        "inputs_sha256": sha256_file(plan.inputs_file()), "version": version,
        "dist": {"path": str(plan.dist_record()), "sha256": sha256_file(plan.dist_record()),
                 "archives": len(dist_record["archives"])},
        "producer": {"record_sha256": sha256_file(plan.record("p")), "label": producer.get("label"),
                     "stage2_manifest": {"path": str(plan.manifest_path("p")),
                                         "sha256": sha256_file(plan.manifest_path("p"))}},
        "parent": {"commit": parent["commit"], "src_stage0_sha256": hashlib.sha256(parent["stage0"]).hexdigest(),
                   "manifest_path": parent["manifest_path"],
                   "manifest_sha256": hashlib.sha256(parent["manifest"]).hexdigest(),
                   "date": parent["date"], "dist_server": parent["server"], "rows": len(parent["rows"])},
        "cohort": {"path": str(plan.args.cohort), "archives": cohort},
        "admitted_dist": admitted_dist, "prepared": prepared, "admitted_pinned": admitted_pinned,
        "seed": {"path": str(plan.seed), "tree": installed["tree"], "installed_from": "the pinned archives",
                 "files_checked": len(installed_by), "installer_bookkeeping": bookkeeping},
        "surface": {"path": str(surface), "sha256": sha256_file(surface)},
        "carried_compared_files": int(carried.strip() or 0),
        "members": {"path": str(table_path), "sha256": sha256_file(table_path), "counts": counts},
        "driver": {**{name: sha256_file(HERE / name) for name in DRIVER_SCRIPTS},
                   "prepare.py": sha256_file(PREPARE_PY)},
        "archive_jobs": getattr(plan.args, "archive_jobs", ARCHIVE_JOBS), "steps_s": steps,
        "trap_log_lines": len(lines),
        "finished": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    record["account_named_in"] = account_mentions(record, plan.account)
    write_json(plan.prepare_record(), record)
    say(f"prepare: done. The seed {plan.seed} is the pinned archives as installed ({installed['tree']['entries']} "
        f"entries); {counts['same']} archive files are the producer's stage2 rows, {counts['none']} have no row "
        f"(none of them elf or ar); the record is {plan.prepare_record()}. Next: "
        f"{shlex.join(command_line(plan, 'build', '--role', 'fixed-point'))}")
    return 0


# ---------------------------------------------------------------------------
# record (design step 13)


@functools.lru_cache(maxsize=None)
def ledger():
    """scripts/seed_host_ledger.py as a module: the host record, the door and,
    through it, the fixed-point evidence validator (seed_fixed_point.py)."""
    sys.path.insert(0, str(HERE))
    try:
        import seed_host_ledger
    finally:
        sys.path.remove(str(HERE))
    return seed_host_ledger


def validator():
    return ledger().fixed_point_module()


def record_record(plan: Plan) -> Path:
    return plan.kept / "record.json"


def host_proofs(plan: Plan, seed_root: Path | None = None) -> Path:
    return (seed_root or plan.output_root()) / "host-proofs" / plan.host


def record_roles(plan: Plan) -> dict[str, dict]:
    """The clean build record of every role the record needs, by its evidence
    name (producer, fixed-point, cross-check, control-N); a refusal names the
    first step that is not done and the command that does it."""
    def missing(what: str, *words: str) -> Refusal:
        return Refusal(f"{what}, so there is nothing to record yet. Nothing was written; every record, tree and "
                       f"manifest under {plan.root} is kept. Run: {shlex.join(command_line(plan, *words))}")

    if not plan.record("p").is_file():
        raise missing(f"the producer is not built clean ({plan.record('p')} is not there)",
                      "build", "--role", "producer")
    if not plan.dist_record().is_file() or (plan.kept / "dist.not-clean.json").is_file():
        raise missing(f"dist is not done clean ({plan.dist_record()})", "dist")
    if not plan.prepare_record().is_file():
        raise missing(f"prepare is not done ({plan.prepare_record()} is not there)", "prepare")
    if not plan.record("f").is_file():
        raise missing(f"the fixed point is not built clean ({plan.record('f')} is not there)",
                      "build", "--role", "fixed-point")
    if not plan.record("s").is_file():
        raise missing(f"the cross-check is not built clean ({plan.record('s')} is not there)",
                      "build", "--role", "cross-check")
    roles = {"producer": read_json(plan.record("p"), "the producer's build record"),
             "fixed-point": read_json(plan.record("f"), "the fixed point's build record"),
             "cross-check": read_json(plan.record("s"), "the cross-check's build record")}
    for number in range(1, CONTROL_LIMIT + 1):
        stem = f"c{number}"
        if plan.record(stem).is_file():
            roles[f"control-{number}"] = read_json(plan.record(stem), "a control's build record")
        elif labels_used(plan, f"{stem}-build"):
            raise missing(f"the control {stem} was started and is not built clean", "build", "--role", "control")
        elif any(plan.record(f"c{later}").is_file() for later in range(number + 1, CONTROL_LIMIT + 1)):
            raise Refusal(f"a later control is built and {plan.record(stem)} is not there: the controls are not "
                          "c1, c2, ... in order. Nothing was written")
    allowed = " and ".join(UNREPRODUCED_ALLOWED)
    for role in ("fixed-point", "cross-check"):
        found = roles[role].get("comparison") or {}
        if found.get("outside_allowed"):
            raise Refusal(f"the {role} tree differs from the producer's outside {allowed} (the first: "
                          f"{found['outside_allowed'][0]}): the rule is that no record is written. Nothing was "
                          "written; every tree and manifest is kept")
    state = control_state(plan)
    if state["outside"]:
        raise Refusal(f"the builds by the pinned seed differ from the producer's tree outside {allowed} (the first: "
                      f"{state['outside'][0]}): no record is written. Nothing was written")
    if state["absent"]:
        raise Refusal(f"{state['absent'][0]} is in some of the producer's and the pinned seed's trees and not in "
                      "others, so it is neither reproduced nor nondeterministic: no record is written. Nothing was "
                      "written")
    if state["undecided"]:
        if state["controls"] >= CONTROL_LIMIT:
            raise Refusal(f"{', '.join(state['undecided'])} has one digest in every build by the pinned seed and "
                          "another in the producer's after the last control: the difference follows the stage0, and "
                          "no record is written. Nothing was written")
        raise missing(f"{', '.join(state['undecided'])} is not decided yet (a control build decides it)",
                      "build", "--role", "control")
    for role, build in roles.items():
        if build.get("problems"):
            raise Refusal(f"the {role} build record {build.get('label')} lists problems: "
                          f"{'; '.join(build['problems'])[:300]}. Nothing was written")
    return roles


def record_checks(plan: Plan, roles: dict[str, dict], dist_record: dict, prepared: dict) -> None:
    """T7: what the receipt cannot say about itself, read from the root's records."""
    current = os.umask(0o022)
    os.umask(current)
    if current != 0o022:
        raise Refusal(f"the umask is {current:03o}, not 022: the tracked files would be written group- or "
                      "world-writable. Nothing was written. Run this with umask 022")
    # (A trap-log line refuses in preflight, which record_step runs first.)
    labels = []
    rungs = plan.ledger / "rungs.jsonl"
    if rungs.is_file():
        for number, line in enumerate(rungs.read_text().splitlines(), 1):
            try:
                labels.append(json.loads(line).get("label"))
            except (ValueError, AttributeError) as error:
                raise Refusal(f"{rungs}:{number} is not a run record: {error}. Nothing was written") from error
    repeated = sorted({label for label in labels if labels.count(label) > 1})
    if repeated:
        raise Refusal(f"{rungs} records the label {repeated[0]} more than once: two runs under one label cannot be "
                      "told apart. Nothing was written")
    # setup writes inputs.json once, and every build and prepare recorded its digest:
    # the inputs evidence is setup's record only while it is still those bytes.
    digest = sha256_file(plan.inputs_file())
    held = {f"the {role} build ({build.get('label')})": (build.get("shared") or {}).get("inputs_sha256")
            for role, build in roles.items()}
    held[f"prepare ({plan.prepare_record()})"] = prepared.get("inputs_sha256")
    for who, was in held.items():
        if was != digest:
            raise Refusal(f"{plan.inputs_file()} is not the setup record {who} was held to: its sha256 is "
                          f"{digest[:16]} now and was {str(was)[:16]} then. setup writes it once, so what it says "
                          "now is not evidence of what the builds ran with. Nothing was written. Restore setup's "
                          "record, or set up a new --root and build every role in it")
    final = dist_record["native_outputs"]["after"]["sha256"]
    if roles["producer"]["native_after"]["sha256"] != dist_record["native_outputs"]["before"]["sha256"]:
        raise Refusal("the LLVM and lld dist started with are not what the producer's build left. Nothing was written")
    for role, build in roles.items():
        if role == "producer":
            continue
        if not build["native_before"]["sha256"] == build["native_after"]["sha256"] == final:
            raise Refusal(f"the {role} build ({build['label']}) did not start and end with the LLVM and lld dist left "
                          f"(digest {final[:16]}): a native output changed between builds. Nothing was written")
    for role, build in roles.items():
        after = build.get("worktree") or {}
        if after.get("problems_after") or unexpected_ignored(after.get("ignored_after") or []) or \
                build.get("trap_log_lines_after") or build.get("trap_log_lines_before"):
            raise Refusal(f"the {role} build ({build['label']}) left the checkout unclean, stray ignored files or "
                          "trap-log lines. Nothing was written")
    problems = refresh.worktree_problems(plan.src, plan.commit)
    if problems or unexpected_ignored(ignored_entries(plan.src)):
        raise Refusal(f"{plan.src} is not a clean checkout of {plan.commit[:10]} now: "
                      f"{'; '.join(problems) or 'stray ignored files'}. Nothing was written")
    if tree_identity(plan.seed, "the installed seed") != (prepared.get("seed") or {}).get("tree"):
        raise Refusal(f"{plan.seed} is no longer the pinned archives as installed ({plan.prepare_record()}). "
                      "Nothing was written")


def checked_bytes(path: Path, digest: str | None, what: str) -> bytes:
    """A file a build record names, refused when it is not the bytes it recorded."""
    try:
        payload = path.read_bytes()
    except OSError as error:
        raise Refusal(f"{what} cannot be read: {path}: {error.strerror or error}. Nothing was written") from error
    if digest is not None and hashlib.sha256(payload).hexdigest() != digest:
        raise Refusal(f"{what} {path} is not the bytes its build recorded (sha256 {digest}): it changed after the "
                      "build. Nothing was written")
    return payload


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=1, sort_keys=True) + "\n").encode("utf-8")


def chain_summary(plan: Plan) -> dict:
    """chain.json: the host chain and the origin evidence, without the record's own paths."""
    args = plan.args
    source = read_json(args.chain, "the host chain record (--chain)")
    try:
        marker = source["NOT_A_LINEAGE_RECORD"]
        root = source["chain"]["root"]
        rungs = [{"label": invocation["label"], "commit": invocation["commit"],
                  "stage0_commit": invocation["stage0_commit"],
                  "stage0_compiler_sha256": invocation["stage0_sha256"]["bin/trustc"],
                  "produced_compiler_sha256": invocation["produced"]["sha256"]["bin/trustc"],
                  "rc": invocation["rc"], "no_stock_evidence": invocation["no_stock_evidence"],
                  "record_sha256": hashlib.sha256(json.dumps(invocation, sort_keys=True,
                                                             separators=(",", ":")).encode()).hexdigest()}
                 for rung in source["chain"]["rungs"] for invocation in rung["invocations"]]
        top = {"commit": root["commit"], "compiler_sha256": root["admission"]["sha256"]["bin/trustc"]}
    except (KeyError, TypeError) as error:
        raise Refusal(f"{args.chain} is not a staircase chain record with a NOT_A_LINEAGE_RECORD marker, a root "
                      f"admission and rungs of run records: {error!r} is missing. Nothing was written. Name the "
                      "host's CHAIN-UNPINNED-ROOT.json with --chain") from error
    stamps = []
    for path in args.origin_provenance:
        try:
            text = path.read_text(errors="replace")
        except OSError as error:
            raise Refusal(f"the origin build stamp {path} cannot be read: {error.strerror or error}. Nothing was "
                          "written. Name the PROVENANCE of the chain's root and of its builder with "
                          "--origin-provenance") from error
        keys = {line.partition("=")[0]: line.partition("=")[2] for line in text.splitlines()
                if re.match(r"(provenance_class|reported_commit|sealed_at|seal_name)=", line)}
        stamps.append({"file": str(path), **keys,
                       "build_stamp": [line for line in text.splitlines() if line.startswith("build_stamp:")]})
    ancestor = validator().STOCK_ANCESTOR_COMMIT
    try:
        lines = [line.strip() for line in plan.args.origin_config.read_text(errors="replace").splitlines()
                 if ancestor[:8] in line]
    except OSError as error:
        raise Refusal(f"the origin config {plan.args.origin_config} cannot be read: {error.strerror or error}. "
                      "Nothing was written. Name with --origin-config the config whose line names the "
                      f"{ancestor[:10]} compiler") from error
    if not lines:
        raise Refusal(f"{plan.args.origin_config} has no line naming {ancestor[:10]}: it is not the config that "
                      "names the chain root's builder. Nothing was written")
    return {"schema": validator().CHAIN_SCHEMA, "NOT_A_LINEAGE_RECORD": marker,
            "source": {"file": str(args.chain), "sha256": sha256_file(args.chain)},
            "root": top, "rungs": rungs,
            "origin": {"provenance": stamps, "config": str(plan.args.origin_config), "config_lines": lines}}


def this_run_shared(plan: Plan, dist_record: dict, pins: dict[str, str]) -> Path:
    """This run's dist of the shared source archive, checked to be the file dist.json records."""
    name = next(Path(key).name for key in ledger().host_payloads(pins, plan.host) if "/trust-src-" in key)
    row = next((row for row in dist_record.get("archives") or [] if row.get("name") == name), None)
    path = plan.dist / name
    if row is None or not path.is_file() or sha256_file(path) != row.get("sha256"):
        raise Refusal(f"this run's {path} is not the file dist.json records ({plan.dist_record()}): the shared "
                      "archive's member tables are compared with this run's dist of it. Nothing was written")
    return path


def archive_members_evidence(plan: Plan, pins: dict[str, str], dist_record: dict) -> bytes:
    """archive-members.json: each pinned host archive read again, and the shared
    archive's member tables, the pinned one's and this run's dist's, beside
    prepare.py's record of keeping the pinned one."""
    module = validator()
    payloads = ledger().host_payloads(pins, plan.host)
    kept = read_json(plan.output_root() / "trust-stage0-shared-kept.json", "prepare.py's record of the shared archive")
    archives, shared = [], None
    for key in sorted(payloads):
        path = plan.output_root() / key
        try:
            if "/trust-src-" in key:
                row = next((row for row in kept.get("kept") or [] if row.get("filename") == path.name), None)
                shared = module.shared_entry(path, payloads[key], this_run_shared(plan, dist_record, pins), row or {})
                if row is None or row.get("pinned_sha256") != payloads[key] or \
                        row.get("pinned_member_table_sha256") != shared["pinned_member_table_sha256"]:
                    raise Refusal(f"{plan.output_root() / 'trust-stage0-shared-kept.json'} does not record the "
                                  f"pinned {path.name} with the member table it has. Nothing was written")
            else:
                archives.append(module.archive_table(path))
        except ValueError as error:
            raise Refusal(f"the pinned archive {path} could not be joined: {error}. Nothing was written") from error
    return json_bytes({"schema": module.MEMBERS_SCHEMA, "host": plan.host, "archives": archives, "shared": shared})


def evidence_host_tools(plan: Plan, tools: dict, base: bytes, roles: dict[str, dict]) -> dict:
    """inputs.json's host_tools as setup bound them, with every host tool the base
    config (`base`, the tracked bytes) names marked with when it was measured: at
    setup, or now, at record, for a root set up before setup measured them. The
    receipt's config_host_tools says which; C15 holds each to its role's file.
    The validator cannot tell the two apart, so this does, from the role builds'
    records (`roles`): a row is setup's only when every build was held to that
    same row (its record's shared.host_tools, which require_shared compared with
    inputs.json before it started), and a tool is measured at record only when no
    build was held to a row for it. Anything between is refused."""
    held: dict[str, dict] = {}
    for role, build in roles.items():
        table = (build.get("shared") or {}).get("host_tools")
        if not isinstance(table, dict):
            raise Refusal(f"the {role} build record ({build.get('label')}) has no host_tools table, so what that "
                          "build was held to cannot be read. Nothing was written")
        held[role] = table
    rows = dict(tools)
    for path, keys in named_host_tools(base, "base-config.toml").items():
        holding = [role for role in sorted(held) if path in held[role]]
        if path in tools:
            if not isinstance(tools[path], dict):
                raise Refusal(f"{plan.inputs_file()} records {path}, which the base config names, as "
                              f"{brief(tools[path])}, not a measurement. Nothing was written")
            differ = [role for role in sorted(held) if held[role].get(path) != tools[path]]
            if differ:
                raise Refusal(f"{plan.inputs_file()} binds {path}, which the base config names, as setup measured "
                              f"it, and the {differ[0]} build ({roles[differ[0]].get('label')}) was not held to that "
                              f"row: its record has {brief(held[differ[0]].get(path))}. A row is setup's only when "
                              "every build was held to it; this one is not evidence of what the builds ran. Nothing "
                              "was written")
            rows[path] = {**tools[path], "measured": "setup"}
            continue
        if holding:
            raise Refusal(f"{plan.inputs_file()} has no row for {path}, which the base config names, and the "
                          f"{holding[0]} build ({roles[holding[0]].get('label')}) was held to one: setup's record "
                          "and the builds' records disagree on what setup bound. Nothing was written")
        row = plan.host_tool(path)
        if row is None:
            raise Refusal(f"the base config names {path} ({', '.join(keys)}); setup did not bind it and it is not "
                          "an executable file now, so the record cannot bind it either. Nothing was written")
        rows[path] = {**row, "measured": "record"}
        say(f"record: {path}, which the base config names ({', '.join(keys)}), was not measured at setup (a root set "
            f"up before setup measured these); measured now and disclosed as measured at record: {row['real']}, "
            f"sha256 {row['sha256'][:16]}")
    return rows


def inputs_evidence(plan: Plan, inputs: dict, base: bytes, roles: dict[str, dict]) -> bytes:
    lean, cargo = inputs["lean"], inputs["cargo_home"]
    cargo_manifest = checked_bytes(Path(cargo["manifest"]), cargo["manifest_sha256"], "the cargo home input manifest")
    checked_bytes(Path(lean["manifest"]), lean["manifest_sha256"], "the Clean Lean input manifest")
    return json_bytes({
        "schema": validator().INPUTS_SCHEMA, "commit": plan.commit, "host": plan.host, "root": str(plan.root),
        "cargo_home_inputs": {"sha256": cargo["manifest_sha256"], "fingerprint": cargo.get("fingerprint"),
                              "trees": cargo.get("trees"), "manifest": json.loads(cargo_manifest)},
        "clean_lean_inputs": {key: lean.get(key) for key in ("toolchain", "library", "fingerprint", "entries",
                                                             "entries_sha256")} | {"sha256": lean["manifest_sha256"]},
        "ninja": {key: inputs["ninja"].get(key) for key in ("path", "bytes", "sha256")},
        "host_tools": evidence_host_tools(plan, inputs["host_tools"], base, roles), "jobs": inputs["jobs"],
        "linker": inputs["linker"], "build_line": inputs["build_line"], "environment": inputs["environment"],
        "clean_fact_store": inputs.get("clean_fact_store")})


def raw_evidence(plan: Plan, roles: dict[str, dict], dist_record: dict, inputs: dict,
                 pins: dict[str, str]) -> dict[str, bytes]:
    """Every evidence file as this host holds it (the raw record, before the account is replaced)."""
    raw: dict[str, bytes] = {}
    stems = {"producer": "p", "fixed-point": "f", "cross-check": "s",
             **{role: f"c{role.rsplit('-', 1)[1]}" for role in roles if role.startswith("control-")}}
    for role, build in roles.items():
        manifest = build.get("stage2_manifest") or {}
        raw[f"stage2-{role}.json"] = checked_bytes(plan.manifest_path(stems[role]), manifest.get("sha256"),
                                                   f"the {role} stage2 manifest")
        raw[f"run-{role}.json"] = checked_bytes(Path(build["run"]["path"]), build["run"]["sha256"],
                                                f"the {role} run record")
        if not role.startswith("control-"):
            raw[f"admission-{role}.json"] = checked_bytes(Path(build["admission"]["path"]),
                                                          build["admission"]["sha256"], f"the {role} admission")
    names = {"p-dist": "producer-dist", "p-full": "producer-full", "p-manifest-tool": "producer-manifest-tool"}
    for run in dist_record.get("runs") or []:
        base = run["label"] if run["label"] in names else re.sub(r"-[0-9]+$", "", run["label"])
        if base not in names:
            raise Refusal(f"dist.json names the run {run['label']}, which is none of {', '.join(names)}. Nothing was "
                          "written")
        raw[f"run-{names[base]}.json"] = checked_bytes(Path(run["run"]["path"]), run["run"]["sha256"],
                                                       f"the {run['label']} run record")
    raw["base-config.toml"] = checked_bytes(plan.src / "bootstrap.toml", inputs["base_config"]["sha256"],
                                            "the base config")
    raw["rung-config.toml"] = checked_bytes(plan.rung_config(), roles["producer"]["config"]["sha256"],
                                            "the rung config")
    raw["native-outputs.json"] = checked_bytes(plan.native("p-dist", "after"), None, "the native outputs after dist")
    if read_json(plan.native("p-dist", "after"), "the native outputs")["sha256"] != \
            dist_record["native_outputs"]["after"]["sha256"]:
        raise Refusal(f"{plan.native('p-dist', 'after')} is not the table dist.json records. Nothing was written")
    raw["archive-members.json"] = archive_members_evidence(plan, pins, dist_record)
    raw["inputs.json"] = inputs_evidence(plan, inputs, raw["base-config.toml"], roles)
    raw["chain.json"] = json_bytes(chain_summary(plan))
    return raw


def receipt_fields(plan: Plan, docs: dict[str, dict], tracked: dict[str, bytes], raw: dict[str, bytes],
                   counts: dict[str, int], pins: dict[str, str], roles: dict[str, dict], dist_record: dict) -> dict:
    """The receipt's fields, each computed from the evidence the receipt binds."""
    module = validator()
    allowed = ledger().FIXED_POINT_UNREPRODUCED_ALLOWED
    controls = sum(1 for role in roles if role.startswith("control-"))
    producer = docs["stage2-producer.json"]
    seeds = [docs["stage2-fixed-point.json"], *(docs[f"stage2-control-{n}.json"] for n in range(1, controls + 1))]
    try:
        not_reproduced, nondeterministic = module.reproduction(producer, seeds, allowed)
        departures = module.rung_departures(tracked["rung-config.toml"], str(plan.root))
    except ValueError as error:
        raise Refusal(f"{error}. Nothing was written") from error
    files = module.file_rows(producer)
    native = {row["sha256"] for row in docs["native-outputs.json"]["rows"]}
    copied = sum(1 for digest in files.values() if digest in native)
    members = docs["archive-members.json"]
    produced = {row["path"]: row for row in producer["records"]}
    archive_only = sorted({member["path"] for archive in members["archives"] for member in archive["members"]
                           if member["path"] not in produced})
    executables = sorted({member["path"] for archive in members["archives"] for member in archive["members"]
                          if member["path"] not in produced and member["kind"] in module.EXECUTABLE_KINDS})
    chain = docs["chain.json"]
    commits = [chain["root"]["commit"]]
    for rung in chain["rungs"]:
        if rung["commit"] not in commits:
            commits.append(rung["commit"])
    admissions = {role: docs[f"admission-{role}.json"]["sha256"] for role in module.ROLES}
    cc = docs["inputs.json"]["host_tools"]["cc"]
    run = docs["run-producer.json"]
    fields = {
        "schema": module.RECEIPT_SCHEMA, "kind": module.KIND, "host": plan.host, "source_commit": plan.commit,
        "source_commit_date": pins["compiler_date"], "source_version": pins["compiler_version"][:-len("-trust")],
        **dict(module.DISCLOSURE),
        "stock_built_ancestor": module.STOCK_ANCESTOR, "stock_built_ancestor_commit": module.STOCK_ANCESTOR_COMMIT,
        "stock_built_ancestor_toolchain": module.STOCK_ANCESTOR_TOOLCHAIN, "root_commit": module.ROOT_COMMIT,
        "chain_commits": ",".join(commits), "cohort_mint_host": module.COHORT_MINT_HOST,
        "open_input_families": ",".join(module.OPEN_INPUT_FAMILIES),
        "build_root": str(plan.root), "build_scope": module.BUILD_SCOPE, "build_driver": module.BUILD_DRIVER,
        "fixed_point_stage0": module.FIXED_POINT_STAGE0, "controls": str(controls),
        "base_config_sha256": hashlib.sha256(tracked["base-config.toml"]).hexdigest(),
        "rung_config_sha256": hashlib.sha256(tracked["rung-config.toml"]).hexdigest(),
        "config_generator_commit": plan.commit, "config_departures": module.join_list(departures),
        "dist_components": " ".join(dist_record["components"]),
        "orchestration_commit": str((run.get("tool") or {}).get("checkout_head")),
        "orchestration_sha256": str((run.get("tool") or {}).get("sha256")),
        "private_home": str(plan.home),
        "clean_lean_inputs_sha256": docs["inputs.json"]["clean_lean_inputs"]["sha256"],
        "cargo_home_inputs_sha256": docs["inputs.json"]["cargo_home_inputs"]["sha256"],
        "native_outputs_sha256": docs["native-outputs.json"]["sha256"],
        "host_c_compiler": f"{cc.get('sha256')} {cc.get('version')}",
        "config_host_tools": module.config_tools_field(named_host_tools(tracked["base-config.toml"],
                                                                        "base-config.toml"),
                                                       docs["inputs.json"]["host_tools"]),
        "account_home_sha256": module.account_digest("home", plan.account[0]),
        "account_login_sha256": module.account_digest("login", plan.account[1]),
        "stage2_core_sha256": module.core_sha256(producer, allowed),
        "fixed_point_verdict": module.verdict(producer, docs["stage2-fixed-point.json"]),
        "cross_check_verdict": module.verdict(producer, docs["stage2-cross-check.json"]),
        "not_reproduced": module.join_list(not_reproduced), "nondeterministic": module.join_list(nondeterministic),
        "not_reproduced_cause_hypothesis": module.NOT_REPRODUCED_HYPOTHESIS if not_reproduced else "none",
        "compared_files": str(len(files)), "rust_built_rows": str(len(files) - copied),
        "native_copied_rows": str(copied),
        "archive_members": str(sum(len(archive["members"]) for archive in members["archives"])),
        "archive_only": module.join_list(archive_only), "archive_only_executables": module.join_list(executables),
        "archive_bytes_total": str(sum(archive["bytes"] for archive in members["archives"])),
        "no_stock_evidence": "pass", "trap_hits": "0", "process_census_flagged": "0",
        "jobserver_token_deficits": module.join_list(module.token_deficits(
            document for name, document in docs.items() if name.startswith("run-"))),
        "shared_source_archive": module.SHARED_SOURCE_ARCHIVE, "shared_source_members": "identical",
        "shared_source_members_excluded": module.join_list(item["path"] for item in members["shared"]["excluded"]),
        "shared_source_bytes": "identical" if members["shared"]["this_run_sha256"] ==
        members["shared"]["pinned_sha256"] else "recompressed-differs",
    }
    for role in module.ROLES:
        name = module.ROLE_FIELD[role]
        fields[f"stage2_tree_sha256_{name}"] = docs[f"stage2-{role}.json"]["sha256"]
        digests = admissions[role]
        if role != "fixed-point":
            fields[f"{name}_stage0_commit"] = docs[f"admission-{role}.json"].get("commit")
        fields[f"{name}_stage0_compiler_sha256"] = str(digests.get("bin/trustc"))
        fields[f"{name}_stage0_driver_sha256"] = next(
            (digest for path, digest in sorted(digests.items()) if path.startswith("lib/librustc_driver-")), "none")
        fields[f"{name}_stage0_cargo_sha256"] = str(digests.get("bin/cargo"))
    for name, payload in tracked.items():
        field = module.evidence_field(name)
        fields[f"{field}_sha256"] = hashlib.sha256(payload).hexdigest()
        fields[f"{field}_raw_sha256"] = hashlib.sha256(raw[name]).hexdigest()
        fields[f"{field}_normalised_count"] = str(counts[name])
    return {key: str(value) for key, value in fields.items()}


def record_account_problems(plan: Plan, named: dict[str, bytes]) -> list[str]:
    """Where a tracked file still names the invoking account (by its literal
    spelling, as text and, for JSON and TOML, in its decoded strings and keys), or
    any personal home but <home> (the validator's account-free rule)."""
    module = validator()
    found = []
    for name, payload in sorted(named.items()):
        if any(names_account(text, plan.account) for text in module.decoded_texts(payload, name)) or \
                module.personal_home_found(payload, name):
            found.append(name)
    return found


def write_tree(top: Path, files: dict[str, bytes]) -> None:
    for relative, payload in files.items():
        path = top / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(payload)


def validate_record(plan: Plan, seed_root: Path, pins: dict[str, str], record: dict, door: dict,
                    shared: Path | None) -> int:
    """Every validator rule with the candidate door, then the full archive join
    (with this run's dist of the shared archive, while it is there); a rule that
    fails is a Refusal naming it."""
    hosts = ledger()
    try:
        hosts.capture_fixed_point_record(seed_root, pins, plan.host, record, door=door)
        return validator().check_archive_joins(seed_root, hosts.host_payloads(pins, plan.host), plan.host,
                                               hosts.read_proof, archive_root=plan.output_root(),
                                               this_run_shared=shared)
    except (ValueError, OSError) as error:
        raise Refusal(f"the record is refused by its validator: {error}") from error


def record_step(plan: Plan) -> int:
    inputs = require_setup(plan)
    done, out = record_record(plan), host_proofs(plan)
    pins_path = plan.prepare_dir() / "stage0.candidate"
    if done.is_file():
        was = read_json(done, "the record step's record")
        pins = text_rows(pins_path.read_text(), str(pins_path))
        record = read_json(out / "host-record.json", "the written host record")
        try:
            shared = this_run_shared(plan, read_json(plan.dist_record(), "the dist record"), pins)
            joined = validate_record(plan, plan.output_root(), pins, record, was["door"], shared)
        except Refusal as refusal:
            raise Refusal(f"{refusal}. {done} says the record was written, and it no longer validates; nothing was "
                          f"changed. Move {out} and {done} aside and run record again") from refusal
        say(f"record: already done ({done}); its {joined} archive members join and every rule holds again")
        return 0
    problem = validator().account_problem(plan.account)
    if problem:
        raise Refusal(f"the invoking account cannot be recorded: {problem}. Nothing was written. Run record as an "
                      "account whose login and home the validator can search for")
    roles = record_roles(plan)
    dist_record = read_json(plan.dist_record(), "the dist record")
    prepared = read_json(plan.prepare_record(), "the prepare record")
    preflight(plan)
    record_checks(plan, roles, dist_record, prepared)
    if out.exists() or out.is_symlink():
        raise Refusal(f"{out} exists and {done} does not: it is not a record this step finished. Nothing was "
                      "changed. Move it aside and run record again")
    pins = text_rows(checked_bytes(pins_path, prepared["prepared"]["candidate"]["sha256"],
                                   "the candidate src/stage0").decode("utf-8"), str(pins_path))
    module = validator()
    raw = raw_evidence(plan, roles, dist_record, inputs, pins)
    tracked, counts = {}, {}
    for name, payload in raw.items():
        try:
            tracked[name], counts[name] = module.normalise(payload, plan.account)
        except ValueError as error:
            raise Refusal(f"{name}: {error}. Nothing was written") from error
    try:
        docs = {name: module.load_json(payload, name) for name, payload in tracked.items() if name.endswith(".json")}
    except ValueError as error:
        raise Refusal(f"{error}. Nothing was written") from error
    fields = receipt_fields(plan, docs, tracked, raw, counts, pins, roles, dist_record)
    files = module.file_rows(docs["stage2-producer.json"])
    links = module.link_rows(docs["stage2-producer.json"])
    try:
        receipt = module.render_receipt(fields, files, links)
    except ValueError as error:
        raise Refusal(f"the receipt could not be written: {error}. Nothing was written") from error
    surface = checked_bytes(Path(prepared["surface"]["path"]), prepared["surface"]["sha256"], "the seed surface")
    named = record_account_problems(plan, {**{f"fixed-point/{name}": payload for name, payload in tracked.items()},
                                           module.RECEIPT_NAME: receipt, "seed-surface.json": surface})
    if named:
        raise Refusal(f"{', '.join(named)} would name the invoking account after normalisation (an escaped or "
                      "otherwise spelled home or login), or a personal home directory (/home/<name>, /Users/<name>) "
                      "that is not the invoker's: tracked evidence is published and must not. Nothing was written; "
                      "the raw records are where they were")
    door = {plan.host: {"commit": plan.commit, "receipt_sha256": hashlib.sha256(receipt).hexdigest()}}
    try:
        record = ledger().make_fixed_point_host_record(pins, plan.host, receipt, surface, door=door)
    except ValueError as error:
        raise Refusal(f"the record is refused by its validator: {error}. Nothing was written") from error
    work = plan.root / "record"
    staging, raw_dir = work / "staging", work / "raw"
    remove_own(staging)
    remove_own(raw_dir)
    staged = host_proofs(plan, staging)
    write_tree(staged, {module.RECEIPT_NAME: receipt, "seed-surface.json": surface,
                        "host-record.json": ledger().record_bytes(record),
                        **{f"{module.EVIDENCE_DIR}/{name}": payload for name, payload in tracked.items()}})
    write_tree(raw_dir, raw)
    try:
        joined = validate_record(plan, staging, pins, record, door, this_run_shared(plan, dist_record, pins))
    except Refusal as refusal:
        raise Refusal(f"{refusal}. Nothing was written under {plan.output_root()}; what was proposed is kept in "
                      f"{staging} and the raw records in {raw_dir}") from refusal
    out.parent.mkdir(parents=True, exist_ok=True)
    staged.rename(out)
    write_json(done, {"schema": RECORD_SCHEMA, "commit": plan.commit, "host": plan.host, "root": str(plan.root),
                      "door": door, "receipt_sha256": door[plan.host]["receipt_sha256"],
                      "host_record_sha256": hashlib.sha256(ledger().record_bytes(record)).hexdigest(),
                      "evidence_sha256": record["evidence_sha256"], "controls": int(fields["controls"]),
                      "fixed_point_verdict": fields["fixed_point_verdict"],
                      "cross_check_verdict": fields["cross_check_verdict"],
                      "not_reproduced": fields["not_reproduced"], "archive_members_joined": joined,
                      "raw": {name: {"path": str(raw_dir / name), "sha256": fields[module.evidence_field(name) +
                                                                                   "_raw_sha256"],
                                     "normalised": counts[name]} for name in sorted(raw)},
                      "finished": time.strftime("%Y-%m-%dT%H:%M:%S%z")})
    say(f"record: written to {out} and accepted by every rule with the candidate door ({plan.host} at "
        f"{plan.commit[:10]}, receipt sha256 {door[plan.host]['receipt_sha256'][:16]}); fixed point "
        f"{fields['fixed_point_verdict']}, cross-check {fields['cross_check_verdict']}, not reproduced "
        f"{fields['not_reproduced']}, jobserver token deficits {fields['jobserver_token_deficits']} "
        f"(SEED-TOKEN-LEAK-STAGE0-1), {joined} archive members joined. The raw records stay host-local in "
        f"{raw_dir}. The door in scripts/seed_host_ledger.py is still empty: nothing is admitted until the "
        "add-host commit names this receipt")
    return 0


# ---------------------------------------------------------------------------
# git, read and written by the steps below


def git_call(repo: Path, *args: str, env: dict[str, str] | None = None,
             payload: bytes | None = None) -> subprocess.CompletedProcess:
    try:
        return subprocess.run(["git", "-C", str(repo), *args], input=payload, capture_output=True, env=env)
    except OSError as error:
        raise Refusal(f"git could not be started in {repo}: {error.strerror or error}") from error


def git_text(repo: Path, *args: str, what: str, env: dict[str, str] | None = None,
             payload: bytes | None = None) -> str:
    """What a git command printed; a failure is a refusal saying what it was for."""
    done = git_call(repo, *args, env=env, payload=payload)
    if done.returncode:
        raise Refusal(f"{what}: `git -C {repo} {' '.join(args[:4])}` {refresh.ended(done.returncode)}: "
                      f"{refresh.last_line(done.stderr.decode('utf-8', 'replace'))}")
    return done.stdout.decode("utf-8", "replace").strip()


def git_blob(repo: Path, rev: str, path: str) -> bytes | None:
    done = git_call(repo, "cat-file", "blob", f"{rev}:{path}")
    return done.stdout if done.returncode == 0 else None


def git_object(repo: Path, rev: str, path: str) -> str | None:
    done = git_call(repo, "rev-parse", "--verify", "--quiet", f"{rev}:{path}")
    return done.stdout.decode().strip() if done.returncode == 0 else None


def is_ancestor(repo: Path, older: str, newer: str) -> bool:
    return git_call(repo, "merge-base", "--is-ancestor", older, newer).returncode == 0


def changed_paths(repo: Path, older: str, newer: str) -> list[str]:
    return sorted(git_text(repo, "diff", "--no-renames", "--name-only", older, newer,
                           what=f"the paths {newer[:10]} changes could not be listed").splitlines())


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


# ---------------------------------------------------------------------------
# commit (design step 14)


def commit_record(plan: Plan) -> Path:
    return plan.kept / "commit.json"


def again_from_prepare(plan: Plan) -> str:
    return ("Nothing was written. The pin a branch carries is the one prepare joined and record proved: prepare "
            "and record are made again against the new parent (design steps 9 and 13), then commit")


def commit_parent(plan: Plan, prepared: dict) -> str:
    """--parent, as a commit: the one prepare joined, or a descendant of it whose
    src/stage0 and bootstrap/trust-stage0 are the same objects."""
    source, parent = plan.source_repo(), plan.parent_commit()
    used = str((prepared.get("parent") or {}).get("commit"))
    if parent == used:
        return parent
    if git_call(source, "cat-file", "-e", f"{used}^{{commit}}").returncode or not is_ancestor(source, used, parent):
        raise Refusal(f"--parent {plan.args.parent} is {parent[:10]}, and prepare joined {used[:10]} "
                      f"({plan.prepare_record()}), which is not an ancestor of it. {again_from_prepare(plan)}")
    moved = [path for path in ("src/stage0", SEED_DIR) if git_object(source, used, path) != git_object(source, parent, path)]
    if moved:
        raise Refusal(f"--parent {plan.args.parent} is {parent[:10]}, and {', '.join(moved)} moved there since "
                      f"{used[:10]}, the commit prepare joined. {again_from_prepare(plan)}")
    return parent


# T3 reads every src/stage0 of the parent's history but these two, which never pinned a
# Trust seed this flow could re-land (docs/DECISION_QUEUE.md SEED-T3-HISTORY-1). Each is
# skipped only while it still shows what excuses it (t3_not_a_pin), read without replace
# refs or grafts; otherwise its rows count like any other.
#   before-admission: a root commit, an ancestor of T3_ADMISSION_COMMIT (the Trust-native
#     stage0 admission every later pin descends from), which pins no row of the host and is
#     an ancestor of the parent.
#   conflicted: a blob with merge conflict markers, every row of the host on the incoming
#     side of a conflict (between ======= and >>>>>>>), none outside one or on its own side.
T3_ADMISSION_COMMIT = "88dad6b193a79cb29034c77a531bb81ef5743289"
T3_NOT_A_PIN = {
    "06efaa37ef8a01b2cf11f39715a885a3e4f8c10c": (
        "before-admission",
        "the repository's initial import (2026-05-24): its src/stage0 pinned 1.96.0-trust archives of edf3cc724f "
        "before the Trust-native stage0 admission 88dad6b193 (2026-06-23) replaced it with a seed that pins no "
        "Linux host"),
    "60669f9fc265bc6a0c1de331dd0834f687fe7d03": (
        "conflicted",
        "a mid-merge commit of the 1.101 upstream port (2026-10-16): its src/stage0 carries merge conflict markers, "
        "and its Linux rows are upstream's stock channel (rustc-beta-, cargo-beta-, rustc-nightly-) on the incoming "
        "side, which 488776ea1b removed"),
}
# How T3 reads history: the commits as they are, never as a replace ref, a graft file or a
# commit-graph file says they are (each could make a skipped commit id show other contents
# or ancestry, or hide a commit from rev-list's path filter).
T3_GIT_ENV = {**TOKEN_LEAK_GIT_ENV, "GIT_CONFIG_COUNT": "1", "GIT_CONFIG_KEY_0": "core.commitGraph",
              "GIT_CONFIG_VALUE_0": "false"}


def host_rows_on_incoming_side(text: str, host: str) -> bool | None:
    """Of a src/stage0 blob: None when it has no merge conflict marker; True when every
    row of `host` in it is on the incoming side of a conflict (between ======= and
    >>>>>>>); False when the markers are out of order or a row of `host` remains once the
    incoming sides are removed (outside a conflict, on its own side or in a diff3 base).
    Lines are split as stage0_payload_pins splits them, and that parser alone decides
    which rows remain; a marker counts only as git writes one, at the start of its line,
    so an indented one keeps the rows after it in what is read."""
    state, conflicted, kept = "outside", False, []
    for line in text.splitlines():
        word = line.rstrip()
        if word.startswith("<<<<<<<"):
            if state != "outside":
                return False
            state, conflicted = "ours", True
        elif word.startswith("|||||||"):
            if state != "ours":
                return False
            state = "base"
        elif word == "=======":
            if state not in ("ours", "base"):
                return False
            state = "theirs"
        elif word.startswith(">>>>>>>"):
            if state != "theirs":
                return False
            state = "outside"
        elif state != "theirs":
            kept.append(line)
    if state != "outside":
        return False
    if not conflicted:
        return None
    remaining = support().stage0_payload_pins("\n".join(kept))
    return not any(key.endswith(f"-{host}.tar.xz") for key in remaining)


def t3_not_a_pin(plan: Plan, parent: str, commit: str, text: str) -> str | None:
    """Why T3 does not read `commit`'s src/stage0 (`text`), or None when it does: the
    commit is in T3_NOT_A_PIN and still shows what excuses it there."""
    entry = T3_NOT_A_PIN.get(commit)
    if entry is None:
        return None
    kind, why = entry
    source, env = plan.source_repo(), {**os.environ, **T3_GIT_ENV}
    if kind == "conflicted":
        return why if host_rows_on_incoming_side(text, plan.host) is True else None
    if kind != "before-admission":
        return None
    parents = git_call(source, "rev-list", "--parents", "-n", "1", commit, env=env)
    if parents.returncode or parents.stdout.decode("utf-8", "replace").split() != [commit]:
        return None
    for ancestor, descendant in ((commit, T3_ADMISSION_COMMIT), (T3_ADMISSION_COMMIT, parent)):
        if git_call(source, "merge-base", "--is-ancestor", ancestor, descendant, env=env).returncode != 0:
            return None
    admitted = git_call(source, "cat-file", "blob", f"{T3_ADMISSION_COMMIT}:src/stage0", env=env)
    if admitted.returncode:
        return None
    rows = support().stage0_payload_pins(admitted.stdout.decode("utf-8", "replace"))
    return None if any(key.endswith(f"-{plan.host}.tar.xz") for key in rows) else why


def pinned_history(plan: Plan, parent: str) -> tuple[list[tuple[str, str, str]], dict[str, str]]:
    """(commit, row, digest) of every row of this host that src/stage0 ever pinned
    in the parent's history (T3), and the commits T3_NOT_A_PIN let it skip, each with
    why. --full-history: git's default simplification follows only the first parent of
    a merge TREESAME to it, and a side branch that pinned the host and unpinned it before
    the merge would not be read. Read without replace refs or grafts, and refused for a
    shallow history, which can hide a commit that pinned the host."""
    source, found, skipped = plan.source_repo(), [], {}
    env = {**os.environ, **T3_GIT_ENV}
    shallow = git_call(source, "rev-parse", "--is-shallow-repository", env=env)
    said = shallow.stdout.decode("utf-8", "replace").strip()
    if shallow.returncode or said != "false":
        raise Refusal(f"T3: git in {source} answers {said[:40]!r} (exit {shallow.returncode}) to rev-parse "
                      "--is-shallow-repository, not 'false': a shallow history can hide a commit that pinned "
                      f"{plan.host}. Nothing was written")
    for commit in git_text(source, "rev-list", "--full-history", parent, "--", "src/stage0", env=env,
                           what="the history of src/stage0 could not be read").split():
        blob = git_call(source, "cat-file", "blob", f"{commit}:src/stage0", env=env)
        if blob.returncode:
            # A path the commit deletes has no blob; one it has whose bytes cannot be read here
            # (a partial clone whose promisor cannot be reached) hides a row T3 must read.
            named = git_call(source, "rev-parse", "--verify", "--quiet", f"{commit}:src/stage0", env=env)
            if named.returncode == 0:
                raise Refusal(f"T3: {commit[:10]}'s src/stage0 (blob {named.stdout.decode('utf-8', 'replace')[:10]}) "
                              f"cannot be read in {source}: a history T3 cannot read can hide a commit that pinned "
                              f"{plan.host}. Nothing was written")
            continue
        text = blob.stdout.decode("utf-8", "replace")
        rows = [(key, value) for key, value in support().stage0_payload_pins(text).items()
                if key.endswith(f"-{plan.host}.tar.xz")]
        if not rows:
            continue
        why = t3_not_a_pin(plan, parent, commit, text)
        if why is not None:
            skipped[commit] = f"{len(rows)} row(s) of {plan.host} not read: {why}"
            continue
        found += [(commit, key, value) for key, value in rows]
    return found, skipped


def proof_files(plan: Plan, controls: int) -> dict[str, bytes]:
    """host-proofs/<host>/ under prepared/, file by file: exactly the receipt, the
    surface, the host record and the evidence files of a record with `controls`."""
    module, top = validator(), host_proofs(plan)
    found: dict[str, bytes] = {}
    odd = []
    for directory, dirnames, filenames in os.walk(top):
        dirnames.sort()
        for name in sorted(dirnames + filenames):
            path = Path(directory) / name
            relative = path.relative_to(top).as_posix()
            if path.is_symlink() or not (path.is_dir() or path.is_file()):
                odd.append(relative)
            elif path.is_file():
                found[relative] = path.read_bytes()
    expected = {module.RECEIPT_NAME, "seed-surface.json", "host-record.json",
                *(f"{module.EVIDENCE_DIR}/{name}" for name in module.evidence_names(controls))}
    if odd or set(found) != expected:
        raise Refusal(f"{top} is not the record `record` writes: "
                      + "; ".join(filter(None, (f"links or special files {odd[:3]}" if odd else "",
                                               f"other files {sorted(set(found) - expected)[:3]}"
                                               if set(found) - expected else "",
                                               f"missing {sorted(expected - set(found))[:3]}"
                                               if expected - set(found) else "")))
                      + ". Nothing was written. Move it aside and run record again")
    return found


def door_text(plan: Plan, parent: str, entry: dict) -> str:
    """The parent's scripts/seed_host_ledger.py with its one empty door line made
    the line that names `entry`; refused unless the parent's door is that one line."""
    text = plan.parent_file(parent, DOOR_FILE).decode("utf-8")
    lines = text.split("\n")
    doors = [number for number, line in enumerate(lines) if line.startswith("FIXED_POINT_FIRST_HOSTS")]
    if len(doors) != 1 or lines[doors[0]] != EMPTY_DOOR_LINE:
        raise Refusal(f"the parent's {DOOR_FILE} does not hold the door as it lands, the one line "
                      f"{EMPTY_DOOR_LINE!r} ({len(doors)} line(s) start FIXED_POINT_FIRST_HOSTS"
                      + (f"; the first is {lines[doors[0]][:120]!r}" if doors else "") + "). The door gains an entry "
                      "only in the add-host commit, by a one-line edit of the empty table. Nothing was written")
    line = DOOR_PREFIX + json.dumps(entry)
    if ast.literal_eval(line[len(DOOR_PREFIX):]) != entry:
        raise Refusal(f"the door line {line!r} does not read back as {entry!r}. Nothing was written")
    lines[doors[0]] = line
    return "\n".join(lines)


def commit_inputs(plan: Plan, parent: str, prepared: dict, recorded: dict) -> dict:
    """Everything commit 1 carries, read from the root and the parent and held to the
    transaction rules (T2-T6, T10, T11); nothing is written."""
    module, hosts = validator(), ledger()
    proofs = host_proofs(plan)
    receipt = checked_bytes(proofs / module.RECEIPT_NAME, recorded.get("receipt_sha256"), "the recorded receipt")
    checked_bytes(proofs / "host-record.json", recorded.get("host_record_sha256"), "the recorded host record")
    try:
        fields = module.parse_receipt(receipt).fields
    except ValueError as error:
        raise Refusal(f"the recorded receipt cannot be read: {error}. Nothing was written") from error
    record = read_json(proofs / "host-record.json", "the recorded host record")
    # T2: the parent pins this commit and not this host.
    parent_text = plan.parent_file(parent, "src/stage0").decode("utf-8")
    parent_fields = text_rows(parent_text, f"{parent[:10]}:src/stage0")
    for key in ("compiler_git_commit_hash", "rustfmt_git_commit_hash"):
        if parent_fields.get(key) != plan.commit:
            raise Refusal(f"T2: the parent {parent[:10]} pins {key} = {parent_fields.get(key)!r}, not {plan.commit}. "
                          "Nothing was written; the host joins the pin of its own commit")
    own = [key for key in pinned_rows(parent_fields) if key.endswith(f"-{plan.host}.tar.xz")]
    if own:
        raise Refusal(f"T2: the parent {parent[:10]} already pins {plan.host} ({own[0]}). Nothing was written; a "
                      "host is added to a pin once")
    # T5: the candidate is the parent's head and prepare.py's section, and adds exactly this host.
    candidate_path = plan.prepare_dir() / "stage0.candidate"
    candidate_bytes = checked_bytes(candidate_path, prepared["prepared"]["candidate"]["sha256"],
                                    "the candidate src/stage0")
    generated = checked_bytes(plan.prepared() / "src-stage0", prepared["prepared"]["generated"]["sha256"],
                              "prepare.py's src/stage0 section")
    try:
        spliced = support().splice_stage0(parent_text, generated.decode("utf-8"))
    except support().WorkflowError as error:
        raise Refusal(f"T5: the candidate cannot be made from the parent's src/stage0 again: {error}") from error
    if spliced.encode("utf-8") != candidate_bytes:
        raise Refusal(f"T5: {candidate_path} is not the parent {parent[:10]}'s src/stage0 head with prepare.py's "
                      f"section. {again_from_prepare(plan)}")
    candidate = text_rows(candidate_bytes.decode("utf-8"), str(candidate_path))
    date, version = parent_fields.get("compiler_date", ""), parent_fields.get("compiler_version", "")
    out = plan.output_root()
    manifest = checked_bytes(out / "dist" / "channel-rust-trust.toml", prepared["prepared"]["manifest"]["sha256"],
                             "the prepared channel manifest")
    manifest_hash = sha256_bytes(manifest)
    problems = []
    for key, was in sorted(parent_fields.items()):
        now = candidate.get(key)
        if key in ("compiler_channel_manifest_hash", "rustfmt_channel_manifest_hash"):
            if now != manifest_hash or now == was:
                problems.append(f"{key} is {now!r}, not the new manifest's sha256")
        elif now != was:
            problems.append(f"the parent's {key} is {now!r} in the candidate")
    added = sorted(set(candidate) - set(parent_fields))
    expected = linux_rows(plan, {"date": date}, version.removesuffix("-trust"))
    if added != expected:
        problems.append(f"the candidate adds {added[:3]}..., and this host adds exactly its eight rows")
    parent_manifest = plan.parent_file(parent, PARENT_MANIFEST.format(date=date))
    if sha256_bytes(parent_manifest) != parent_fields.get("compiler_channel_manifest_hash"):
        problems.append("the parent's channel manifest is not the one its src/stage0 pins")
    try:
        merged = tomllib.loads(manifest.decode("utf-8"))
        problems += manifest_problems(plan, {"manifest": parent_manifest, "server": parent_fields.get("dist_server", "")},
                                      merged, candidate)
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        problems.append(f"a channel manifest is not TOML: {error}")
    manifests = {}
    for name in MANIFEST_FILES:
        path = out / name.format(date=date)
        payload = path.read_bytes() if path.is_file() and not path.is_symlink() else None
        if payload is None:
            problems.append(f"{path} is not a regular file")
        elif name.endswith(".toml") and payload != manifest:
            problems.append(f"{path} is not the channel manifest the candidate pins")
        elif name.endswith(".sha256") and payload.decode("utf-8", "replace").split()[:1] != [manifest_hash]:
            problems.append(f"{path} does not name the manifest's sha256")
        manifests[f"{SEED_DIR}/{name.format(date=date)}"] = payload
    # T6: every pinned archive with its pinned bytes, and the admission names exactly them.
    pins = pinned_rows(candidate)
    for key, digest in sorted(pins.items()):
        path = out / key
        if path.is_symlink() or not path.is_file():
            problems.append(f"the pinned archive {key} is not a regular file in {out}")
        elif sha256_file(path) != digest:
            problems.append(f"{out / key} is not the bytes the candidate pins ({digest[:16]})")
    # The admission prepare.py wrote, held to the digest prepare recorded like the candidate and manifest.
    admission_bytes = checked_bytes(out / "trust-stage0-admission.json", prepared["prepared"]["admission"]["sha256"],
                                    "prepare.py's admission")
    try:
        admission = json.loads(admission_bytes)
    except ValueError:
        admission = {}
    if not isinstance(admission, dict) or admission.get("manifest_hash") != manifest_hash or \
            admission.get("git_commit_hash") != plan.commit or \
            {row.get("relative_path"): row.get("sha256") for row in admission.get("payloads") or []} != pins:
        problems.append("trust-stage0-admission.json does not admit exactly the candidate's archives and manifest")
    if problems:
        raise Refusal(f"T5/T6: the prepared pin is not the parent {parent[:10]}'s plus this host, with every archive: "
                      f"{'; '.join(problems[:6])}{'; ...' if len(problems) > 6 else ''}. Nothing was written. "
                      f"An archive that is missing is fetched (`agh release download`) or copied into "
                      f"{out / 'dist' / date}; anything else: prepare again")
    # T3: history never pinned this host with other digests.
    history, t3_skipped = pinned_history(plan, parent)
    other = [(commit, key, value) for commit, key, value in history if candidate.get(key) != value]
    if other:
        commit, key, value = other[0]
        raise Refusal(f"T3: {commit[:10]} in the parent's history pinned {key} = {value[:16]}..., and this cohort pins "
                      f"{str(candidate.get(key))[:16]}... ({len(other)} such row(s)). A host's archives are pinned once; "
                      "re-landing is allowed only for the identical cohort. Nothing was written")
    # T4: the parent ledger is one mint record of this commit, of the cohort's mint host.
    ledger_text = plan.parent_file(parent, LEDGER_FILE).decode("utf-8")
    try:
        release = tomllib.loads(ledger_text).get("release")
    except tomllib.TOMLDecodeError as error:
        raise Refusal(f"T4: the parent's {LEDGER_FILE} is not TOML: {error}. Nothing was written") from error
    tables = release.get("hosts") if isinstance(release, dict) else None
    if not isinstance(tables, dict) or len(tables) != 1:
        raise Refusal(f"T4: the parent's {LEDGER_FILE} has {len(tables) if isinstance(tables, dict) else 'no'} host "
                      "table(s), and the add-host commit joins exactly one, the cohort's mint record. Nothing was written")
    [(darwin, darwin_record)] = tables.items()
    if darwin != fields.get("cohort_mint_host") or not isinstance(darwin_record, dict) or \
            darwin_record.get("schema") != hosts.SCHEMA or darwin_record.get("source_commit") != plan.commit or \
            not isinstance(release.get("mint"), dict):
        raise Refusal(f"T4: the parent's host table is {darwin}'s with schema {darwin_record.get('schema')!r} at "
                      f"{darwin_record.get('source_commit')!r} ([release.mint] "
                      f"{'present' if isinstance(release.get('mint'), dict) else 'absent'}), and the receipt names the "
                      f"cohort's mint host {fields.get('cohort_mint_host')}: the add-host commit joins a mint record of "
                      f"{plan.commit[:10]} only. Nothing was written")
    # T11: the orchestration that ran the builds is in the parent's history, with the bytes the runs recorded.
    source = plan.source_repo()
    orchestration, script_sha256 = fields.get("orchestration_commit", ""), fields.get("orchestration_sha256", "")
    if git_call(source, "cat-file", "-e", f"{orchestration}^{{commit}}").returncode or \
            not is_ancestor(source, orchestration, parent):
        raise Refusal(f"T11: orchestration_commit {orchestration[:10]} (the checkout whose seed_staircase.py ran the "
                      f"builds) is not an ancestor of the parent {parent[:10]}. Nothing was written: a branch carries "
                      "evidence only of an orchestration its own history holds")
    script = git_blob(source, orchestration, "scripts/seed_staircase.py")
    if script is None or sha256_bytes(script) != script_sha256:
        raise Refusal(f"T11: scripts/seed_staircase.py at {orchestration[:10]} is not the bytes the runs recorded "
                      f"(orchestration_sha256 {script_sha256[:16]}). Nothing was written")
    # The door entry, the ledger (T10) and the proofs.
    entry = {plan.host: {"commit": plan.commit, "receipt_sha256": sha256_bytes(receipt)}}
    door = door_text(plan, parent, entry)
    try:
        ledger_out, tag = support().render_seed_ledger(
            ledger_text, candidate, candidate_bytes.decode("utf-8"), darwin,
            dict(darwin_record.get("reported_product_identities") or {}), dict(darwin_record.get("mint") or {}),
            host_records={darwin: darwin_record, plan.host: record}, title_hosts=True, mint_switch_line=True)
    except support().WorkflowError as error:
        raise Refusal(f"the two-host seed ledger cannot be rendered: {error}. Nothing was written") from error
    switch = [line for line in ledger_out.splitlines() if line.startswith("[release.mint]")]
    rendered = tomllib.loads(ledger_out).get("release") or {}
    if len(switch) != 1 or "mint" in rendered:
        raise Refusal(f"T10: the rendered ledger has {len(switch)} line(s) starting [release.mint], and TOML "
                      f"{'finds' if 'mint' in rendered else 'finds no'} release.mint table: aterm's seed-pin switch "
                      "needs exactly one such line and the ledger no such table. Nothing was written")
    if rendered.get("hosts") != {darwin: darwin_record, plan.host: record}:
        raise Refusal("the rendered ledger's host tables do not read back as the two records. Nothing was written")
    writes = {"src/stage0": candidate_bytes, LEDGER_FILE: ledger_out.encode("utf-8"),
              DOOR_FILE: door.encode("utf-8"), ADMISSION_FILE: admission_bytes, **manifests,
              **{f"{SEED_DIR}/host-proofs/{plan.host}/{relative}": payload
                 for relative, payload in proof_files(plan, int(fields["controls"])).items()}}
    bad = sorted(path for path in writes if path.endswith((".tar.xz", ".tar.gz", ".tar")) or ".this-run" in path)
    if bad:
        raise Refusal(f"T9: the add-host commit would carry {bad[0]}, an archive or a this-run file. Nothing was written")
    return {"fields": fields, "record": record, "receipt_sha256": entry[plan.host]["receipt_sha256"],
            "door_entry": entry, "door_line": DOOR_PREFIX + json.dumps(entry), "darwin": darwin,
            "t3_skipped": t3_skipped,
            "parent_fields": parent_fields, "candidate": candidate, "date": date, "tag": tag,
            "release_repo": rendered.get("repo"), "writes": writes, "manifest_sha256": manifest_hash}


def commit_message(plan: Plan, parent: str, prepared: dict, inputs: dict) -> str:
    fields, record, darwin = inputs["fields"], inputs["record"], inputs["darwin"]
    state = plan.args.darwin_pack_state
    pack = (f"* the {darwin} pack of {plan.commit[:10]}: published, so aterm's pack publisher is not held by this "
            "two-host src/stage0 section" if state == "published" else
            f"* the {darwin} pack of {plan.commit[:10]}: NOT published. aterm's pack publisher refuses that pack while "
            "main carries this two-host src/stage0 section (its generated section is not the Darwin re-pin's); the "
            "undo is to revert the two add-host commits, publish the pack, and land this branch again")
    return "\n".join([
        f"seed: add {plan.host} to the {inputs['date']} pin of {plan.commit[:10]}, a fixed point of an unpinned root",
        "",
        f"The first Linux seed (docs/PLAN.md PKG-S6), committed by scripts/fixed_point_linux_seed.py commit.",
        "It is not a mint. Its host record is the fixed-point kind: a build from it is graded",
        "unpinned-root-seed-ready, below internal-release-ready, and --require-immutable-lineage refuses it.",
        "",
        f"What the record discloses (host-proofs/{plan.host}/SEED-FIXED-POINT, root_disclosure):",
        *(f"* {key} = {value}" for key, value in sorted((record.get("root_disclosure") or {}).items())),
        "",
        f"* fixed point {fields['fixed_point_verdict']}, cross-check {fields['cross_check_verdict']}, not reproduced "
        f"{fields['not_reproduced']}, nondeterministic {fields['nondeterministic']}, controls {fields['controls']}",
        f"* jobserver token deficits {fields['jobserver_token_deficits']} (docs/DECISION_QUEUE.md "
        "SEED-TOKEN-LEAK-STAGE0-1)",
        f"* receipt sha256 {inputs['receipt_sha256']}; evidence sha256 {record.get('evidence_sha256')}",
        f"* the door: {DOOR_FILE} FIXED_POINT_FIRST_HOSTS gains one entry, {plan.host} at {plan.commit[:10]} with "
        "the receipt above",
        f"* {darwin}'s nine rows, host record and proofs keep their bytes; the ledger names both hosts and carries "
        "the [release.mint] line aterm's seed-pin switch reads",
        f"* archives: release {inputs['tag']} of {inputs['release_repo']}, not in this commit; "
        "`fixed_point_linux_seed.py publish` uploads this host's eight",
        pack,
        *(f"* T3 did not read {commit[:10]}'s src/stage0 (docs/DECISION_QUEUE.md SEED-T3-HISTORY-1): {why}"
          for commit, why in sorted(inputs["t3_skipped"].items())),
        f"* parent {parent}; prepare joined {prepared['parent']['commit']}",
        ""])


def manifest_members(text: str) -> set[str]:
    """The paths a corpus manifest pins: every line, trimmed, that is not blank or a comment."""
    return {line.strip() for line in text.splitlines() if line.strip() and not line.strip().startswith("#")}


def with_repin_note(text: str, note: list[str]) -> str:
    """`text` with `note` (comment lines) and a closing `#` after the header's last
    comment line, so the header stays the part before the first pinned path."""
    lines = text.split("\n")
    last = None
    for number, line in enumerate(lines):
        if line.strip().startswith("#"):
            last = number
        elif line.strip():
            break
    if last is None:
        raise Refusal("a corpus manifest has no header to note its re-pin in. Nothing was committed")
    lead = [] if lines[last].strip() == "#" else ["#"]
    return "\n".join([*lines[:last + 1], *lead, *note, "#", *lines[last + 1:]])


def corpus_repin(plan: Plan, repo: Path, parent: str, first: str, writes: dict[str, bytes]) -> dict[str, bytes]:
    """Commit 2's two manifests: check_corpus_membership.py --write in the clone at
    commit 1, holding it to add exactly the new tracked .json and .toml."""
    new = [path for path in writes if git_object(repo, parent, path) is None]
    expected = {".json": sorted(path for path in new if path.endswith(".json") and not path.startswith(CORPUS_EXCLUDED)
                                and len(writes[path]) < CORPUS_JSON_CAP),
                ".toml": sorted(path for path in new if path.endswith(".toml") and not path.startswith(CORPUS_EXCLUDED))}

    def run(*words: str) -> subprocess.CompletedProcess:
        return subprocess.run(plan.corpus(repo, *words), cwd=repo, capture_output=True, text=True, errors="replace")

    exact = run("--rev", parent)
    if exact.returncode:
        raise Refusal(f"the parent {parent[:10]}'s corpus manifests are not exact (check_corpus_membership.py --rev "
                      f"{refresh.ended(exact.returncode)}: {refresh.last_line(exact.stdout + exact.stderr)}), so a re-pin "
                      "here would carry other changes than this host's. No branch was made. Land the parent's re-pin on "
                      "main first, then commit against it")
    before = {suffix: (repo / manifest).read_text() for suffix, manifest in CORPUS_MANIFESTS.items()}
    written = run("--write")
    if written.returncode:
        raise Refusal(f"check_corpus_membership.py --write refused in the clone ({refresh.ended(written.returncode)}): "
                      f"{refresh.last_line(written.stdout + written.stderr)}. No branch was made")
    out = {}
    for suffix, manifest in CORPUS_MANIFESTS.items():
        after = (repo / manifest).read_text()
        old, now = manifest_members(before[suffix]), manifest_members(after)
        if now - old != set(expected[suffix]) or old - now:
            raise Refusal(f"the re-pin of {manifest} adds {sorted(now - old)[:3]} and drops {sorted(old - now)[:3]}, and "
                          f"this host's commit adds exactly {expected[suffix][:3]} and drops nothing. No branch was made")
        if not expected[suffix]:
            continue
        note = [f"# RE-PINNED {time.strftime('%Y-%m-%d')} with the add-host commit of the first Linux seed "
                f"({first[:10]}): +{len(expected[suffix])}/-0",
                f"#   documents, {len(old)} -> {len(now)}: the tracked evidence under {SEED_DIR}/host-proofs/"
                f"{plan.host}/.",
                "#   Regenerated by `python3 scripts/check_corpus_membership.py --write` from the index at that commit."]
        out[manifest] = with_repin_note(after, note).encode("utf-8")
        (repo / manifest).write_bytes(out[manifest])
    return out


def commit_tree(repo: Path, parent: str, writes: dict[str, bytes], message: str, env: dict[str, str],
                work: Path, name: str) -> str:
    """One commit on `parent` with `writes`, made in the clone's own index (no hook runs)."""
    git_text(repo, "read-tree", parent, what="the clone's index could not be set to the parent")
    for path, payload in sorted(writes.items()):
        blob = git_text(repo, "hash-object", "-w", "--no-filters", "--stdin", payload=payload,
                        what=f"{path} could not be stored")
        git_text(repo, "update-index", "--add", "--cacheinfo", f"100644,{blob},{path}",
                 what=f"{path} could not be staged")
    tree = git_text(repo, "write-tree", what="the tree could not be written")
    message_path = work / f"{name}.message"
    message_path.write_text(message, encoding="utf-8")
    return git_text(repo, "commit-tree", tree, "-p", parent, "-F", str(message_path), env=env,
                    what="the commit could not be made")


def judge_with_real_door(plan: Plan, repo: Path, inputs: dict) -> None:
    """Commit 1 as the branch's own seed_host_ledger.py sees it, with its real door:
    every host table captured against the branch's pins, the cohort mint host's
    against the parent's too (T4)."""
    try:
        hosts = plan.repo_module(repo, "seed_host_ledger")
        if hosts.FIXED_POINT_FIRST_HOSTS != inputs["door_entry"]:
            raise ValueError(f"its FIXED_POINT_FIRST_HOSTS is {hosts.FIXED_POINT_FIRST_HOSTS!r}, not the one entry "
                             f"{inputs['door_entry']!r}")
        release = tomllib.loads((repo / LEDGER_FILE).read_text(encoding="utf-8"))["release"]
        pins = text_rows((repo / "src" / "stage0").read_text(encoding="utf-8"), "the branch's src/stage0")
        seed_root = repo / SEED_DIR
        for name, table in sorted(release["hosts"].items()):
            hosts.select_host_record(release, name)
            hosts.capture_host_record(seed_root, pins, name, table)
        darwin = inputs["darwin"]
        hosts.capture_host_record(seed_root, inputs["parent_fields"], darwin, release["hosts"][darwin])
    except (ValueError, OSError, TypeError, KeyError, UnicodeError, tomllib.TOMLDecodeError) as error:
        raise Refusal(f"commit 1 is refused by the branch's own {DOOR_FILE} with its real door: {error}. No branch was "
                      f"made; what was built is kept in {plan.root / 'commit.partial'} and the next run makes it anew")


def make_branch(plan: Plan, parent: str, prepared: dict, inputs: dict) -> dict:
    args, final, partial = plan.args, plan.commit_dir(), plan.root / "commit.partial"
    remove_own(partial)
    partial.mkdir()
    repo, work = partial / "repo", partial / "work"
    work.mkdir()
    source = plan.source_repo()
    say(f"commit: cloning {source} into {repo} (no checkout)")
    git_text(plan.root, "clone", "--quiet", "--no-checkout", "--no-tags", str(source), str(repo),
             what=f"{source} could not be cloned")
    # The clone points nowhere: nothing it holds can be pushed from it by mistake.
    git_text(repo, "remote", "remove", "origin", what="the clone's remote could not be removed")
    git_text(repo, "cat-file", "-e", f"{parent}^{{commit}}", what=f"the clone does not hold the parent {parent[:10]}")
    name, email = IDENTITY.fullmatch(args.identity.strip()).groups()
    env = {**os.environ, "GIT_AUTHOR_NAME": name, "GIT_AUTHOR_EMAIL": email, "GIT_COMMITTER_NAME": name,
           "GIT_COMMITTER_EMAIL": email}
    writes = inputs["writes"]
    first = commit_tree(repo, parent, writes, commit_message(plan, parent, prepared, inputs), env, work, "commit-1")
    # T9, commit 1: exactly the listed paths, and the cohort mint host's proofs keep their blobs.
    listed = changed_paths(repo, parent, first)
    if listed != sorted(writes):
        raise Refusal(f"T9: commit 1 changes {sorted(set(listed) ^ set(writes))[:5]} other than the listed paths. No "
                      f"branch was made; what was built is kept in {partial}")
    darwin_proofs = f"{SEED_DIR}/host-proofs/{inputs['darwin']}"
    for path in git_text(repo, "ls-tree", "-r", "--name-only", parent, "--", darwin_proofs,
                         what="the cohort mint host's proofs could not be listed").splitlines():
        if git_object(repo, parent, path) != git_object(repo, first, path):
            raise Refusal(f"T4: {path} is another blob in commit 1. No branch was made")
    git_text(repo, "read-tree", first, what="the clone's index could not be set to commit 1")
    git_text(repo, "checkout", first, "--", *COMMIT_VIEW, what="commit 1 could not be checked out to be judged")
    judge_with_real_door(plan, repo, inputs)
    manifests = corpus_repin(plan, repo, parent, first, writes)
    second = commit_tree(repo, first, manifests, "\n".join([
        "seed: re-pin the JSON and TOML corpus manifests for the first Linux seed's evidence", "",
        f"`python3 scripts/check_corpus_membership.py --write` at {first[:10]}, the add-host commit: it adds",
        f"the tracked .json and .toml under {SEED_DIR}/host-proofs/{plan.host}/ and drops nothing.", ""]),
        env, work, "commit-2")
    whole, tail = changed_paths(repo, parent, second), changed_paths(repo, first, second)
    if whole != sorted({*writes, *manifests}) or tail != sorted(manifests) or not manifests or \
            not set(tail) <= set(CORPUS_MANIFESTS.values()):
        raise Refusal(f"T9: the branch changes {whole[:3]}... and commit 2 {tail}, not exactly the listed paths and "
                      f"commit 2 only corpus manifests. No branch was made; what was built is kept in {partial}")
    rejudged = subprocess.run(plan.corpus(repo, "--rev", second), cwd=repo, capture_output=True, text=True,
                              errors="replace")
    if rejudged.returncode:
        raise Refusal(f"check_corpus_membership.py --rev {second[:10]} is red on the branch tip: "
                      f"{refresh.last_line(rejudged.stdout + rejudged.stderr)}. No branch was made")
    # T8, create-only: a branch of this name is never moved.
    git_text(repo, "update-ref", f"refs/heads/{args.branch}", second, "0" * 40,
             what=f"the branch {args.branch} could not be created (it exists)")
    made = {"schema": COMMIT_SCHEMA, "commit": plan.commit, "host": plan.host, "root": str(plan.root),
            "parent": parent, "prepare_parent": prepared["parent"]["commit"], "branch": args.branch,
            "identity": args.identity, "darwin_pack_state": args.darwin_pack_state, "repo": str(final / "repo"),
            "t3_skipped": inputs["t3_skipped"],
            "commits": [first, second], "paths": {"commit-1": sorted(writes), "commit-2": sorted(manifests)},
            "receipt_sha256": inputs["receipt_sha256"], "door_line": inputs["door_line"],
            "ledger_sha256": sha256_bytes(writes[LEDGER_FILE]), "release": {"repo": inputs["release_repo"],
                                                                          "tag": inputs["tag"]},
            "finished": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    write_json(commit_record(plan), made)
    partial.rename(final)
    return made


def commit_next(plan: Plan, made: dict) -> str:
    repo, date = made["repo"], made.get("release", {}).get("tag", "")
    return (f"next (design step 15): git clone {repo} <V> && git -C <V> checkout {made['branch']}; copy the 17 pinned "
            f"archives from {plan.output_root() / 'dist'}/<date>/ into <V>/{SEED_DIR}/dist/<date>/; "
            f"python3 <V>/scripts/fixed_point_linux_seed.py verify. Nothing was pushed (release {date})")


def commit_step(plan: Plan) -> int:
    require_setup(plan)
    args = plan.args
    if args.darwin_pack_state not in DARWIN_PACK_STATES:
        raise Refusal(f"T12: --darwin-pack-state is {args.darwin_pack_state!r}: say whether the Darwin pack of "
                      f"{plan.commit[:10]} is published or not-published (read it before landing; the commit message "
                      "states the consequence). Nothing was written")
    if IDENTITY.fullmatch(args.identity.strip()) is None:
        raise Refusal(f"--identity {args.identity!r} is not 'Name <email>'. Nothing was written")
    if not BRANCH_NAME.fullmatch(args.branch) or args.branch.startswith("-") or ".." in args.branch:
        raise Refusal(f"--branch {args.branch!r} is not a plain branch name. Nothing was written")
    done, final, partial = commit_record(plan), plan.commit_dir(), plan.root / "commit.partial"
    if done.is_file():
        was = read_json(done, "the commit step's record")
        parent = plan.parent_commit()
        for key, mine in (("branch", args.branch), ("identity", args.identity),
                          ("darwin_pack_state", args.darwin_pack_state), ("parent", parent)):
            if was.get(key) != mine:
                raise Refusal(f"commit is done with {key} = {was.get(key)!r} ({done}), and this command gives "
                              f"{mine!r}. Nothing was changed. To make another branch, move {final} and {done} aside")
        if not final.exists() and partial.is_dir():
            partial.rename(final)
        tip = git_call(Path(was["repo"]), "rev-parse", "--verify", "--quiet", f"refs/heads/{args.branch}")
        if tip.returncode or tip.stdout.decode().strip() != was["commits"][-1]:
            raise Refusal(f"commit is done ({done}), and {args.branch} in {was['repo']} is not its tip "
                          f"{was['commits'][-1][:10]} any more. Nothing was changed")
        say(f"commit: already done ({done}): {args.branch} in {was['repo']} at {was['commits'][-1][:10]}; not repeated")
        say(commit_next(plan, was))
        return 0
    if not record_record(plan).is_file():
        raise Refusal(f"record is not done ({record_record(plan)} is not there), so there is nothing to commit. "
                      f"Nothing was written. Run: {shlex.join(command_line(plan, 'record'))}")
    recorded = read_json(record_record(plan), "the record step's record")
    prepared = read_json(plan.prepare_record(), "the prepare record")
    preflight(plan)
    if final.exists() or final.is_symlink():
        raise Refusal(f"{final} exists and {done} does not: it is not a branch this step finished. Nothing was "
                      "changed. Move it aside and run commit again")
    if git_call(plan.source_repo(), "rev-parse", "--verify", "--quiet", f"refs/heads/{args.branch}").returncode == 0:
        raise Refusal(f"T8: the branch {args.branch} exists in {plan.source_repo()}. A branch is made once and never "
                      "moved, and this one would be fetched beside it. Nothing was written. Name another --branch")
    parent = commit_parent(plan, prepared)
    inputs = commit_inputs(plan, parent, prepared, recorded)
    made = make_branch(plan, parent, prepared, inputs)
    say(f"commit: {made['branch']} in {made['repo']}: {made['commits'][0][:10]} (the pin, the proofs, the door entry; "
        f"{len(made['paths']['commit-1'])} paths) and {made['commits'][1][:10]} (the corpus re-pin), on "
        f"{parent[:10]}; both host records captured with the branch's real door")
    say(commit_next(plan, made))
    return 0


# ---------------------------------------------------------------------------
# verify (design steps 15 and 16)


def lineage_problems(lineage: dict, host: str, cohort: list[str], recreate, fixed_point: bool) -> list[str]:
    """Why a capture of the clone's seed for `host` is not a clean admission of the cohort."""
    problems = [str(error) for error in lineage.get("errors") or []]
    if lineage.get("status") not in ("validated", "validated-payloads"):
        problems.append(f"its status is {lineage.get('status')!r}")
    if lineage.get("admission_status") != "internal-admitted":
        problems.append(f"its admission is {lineage.get('admission_status')!r}, not internal-admitted")
    authority = ((lineage.get("authority") or {}).get("seed_ledger") or {}).get("host_records") or {}
    if sorted(authority.get("records") or {}) != sorted(cohort) or authority.get("selected_host") != host:
        problems.append(f"it captured the records of {sorted(authority.get('records') or {})}, not the cohort's "
                        f"{cohort}, for {host}")
    if fixed_point and (recreate._selected_host_record_schema(lineage) != recreate.FIXED_POINT_HOST_RECORD_SCHEMA
                        or not authority.get("fixed_point_validator_sha256")):
        problems.append("its selected record is not the fixed-point kind judged by seed_fixed_point.py")
    return problems


def view_problems(repo: Path, rev: str, archives: set[str]) -> list[str]:
    """Why the files verify's judges read in `repo` (VERIFY_VIEW, walked on disk) are
    not exactly `rev`'s: every tracked file there with its blob's bytes, and nothing
    else but the placed `archives` and Python's own __pycache__/*.pyc. Read from the
    disk and the commit, not from git's index or status, which skip-worktree,
    assume-unchanged, an untracked file or a stat-clean edit leave silent."""
    listed = git_text(repo, "ls-tree", "-r", "-z", "--full-tree", rev, "--", *VERIFY_VIEW,
                      what=f"the files of {rev[:10]} verify judges could not be listed")
    tracked: dict[str, str] = {}
    for entry in filter(None, listed.split("\0")):
        meta, _, path = entry.partition("\t")
        tracked[path] = meta.split()[2]
    found, links = set(), []
    for top in VERIFY_VIEW:
        base = repo / top
        if base.is_symlink():
            links.append(top)
        elif base.is_file():
            found.add(top)
        elif base.is_dir():
            for directory, dirnames, filenames in os.walk(base):
                for name in sorted(dirnames + filenames):
                    path = Path(directory) / name
                    relative = path.relative_to(repo).as_posix()
                    if path.is_symlink() or not (path.is_dir() or path.is_file()):
                        links.append(relative)
                    elif path.is_file():
                        found.add(relative)
    pycache = {path for path in found if "__pycache__" in path.split("/") and path.endswith(".pyc")}
    problems = []
    if links:
        problems.append(f"links or special files {sorted(links)[:3]}")
    other = sorted(found - set(tracked) - archives - pycache)
    if other:
        problems.append(f"files {rev[:10]} does not track {other[:3]} ({len(other)})")
    # A tracked link or submodule is never in `found` (a link on disk is in `links`, a submodule a
    # directory): it is missing, so only regular files are hashed.
    missing = sorted(set(tracked) - found)
    if missing:
        problems.append(f"files {rev[:10]} tracks that are not there {missing[:3]} ({len(missing)})")
    present = sorted(set(tracked) & found)
    hashed = git_text(repo, "hash-object", "--no-filters", "--stdin-paths", payload="\n".join(present).encode(),
                      what="the judged files could not be hashed").split() if present else []
    # A path git did not hash is a path whose bytes are not shown to be the commit's.
    differ = [path for index, path in enumerate(present) if index >= len(hashed) or hashed[index] != tracked[path]]
    if differ:
        problems.append(f"files whose bytes are not {rev[:10]}'s {differ[:3]} ({len(differ)})")
    return problems


def admission_problems(payload: bytes, pins: dict[str, str], commit: str) -> list[str]:
    """Why a branch's trust-stage0-admission.json is not prepare.py's internal admission
    of exactly the pinned archives, the pinned manifest and the commit."""
    try:
        admission = json.loads(payload)
    except ValueError as error:
        return [f"it is not JSON ({error})"]
    if not isinstance(admission, dict):
        return ["it is not a JSON object"]
    problems = [f"{key} is {admission.get(key)!r}, not {want!r}" for key, want in (
        ("schema", ADMISSION_SCHEMA), ("admission", "internal"), ("public_upload", False),
        ("promotion_decision", "admit-internal"), ("git_commit_hash", commit), ("date", pins.get("compiler_date")),
        ("manifest_hash", pins.get("compiler_channel_manifest_hash"))) if admission.get(key) != want]
    rows = admission.get("payloads") if isinstance(admission.get("payloads"), list) else []
    admitted = [(row.get("relative_path"), row.get("sha256")) for row in rows if isinstance(row, dict)]
    if len(admitted) != len(rows) or sorted(admitted, key=str) != sorted(pinned_rows(pins).items()):
        problems.append(f"its {len(rows)} payload rows are not the {len(pinned_rows(pins))} pinned archives with their "
                        "pins, each once")
    return problems


def release_problems(document: dict, pins: dict[str, str], commit: str) -> list[str]:
    """Why a branch's seed ledger does not name this pin's release (the tag every clone
    fetches and publish uploads to) and exactly its archives' checksums."""
    release = document.get("release") if isinstance(document.get("release"), dict) else {}
    repo, date = release.get("repo"), pins.get("compiler_date")
    tag = f"trust-stage0-{date}-{commit[:9]}"
    problems = []
    if not isinstance(repo, str) or not repo:
        problems.append(f"[release] repo is {repo!r}")
    if release.get("tag") != tag:
        problems.append(f"[release] tag is {release.get('tag')!r}, not {tag!r}")
    fetch = (f"gh release download {tag} --repo {repo} --dir {SEED_DIR}/dist/{date} --pattern '*.tar.xz' "
             "--clobber")
    if release.get("authenticated_fetch") != fetch:
        problems.append(f"[release] authenticated_fetch is {release.get('authenticated_fetch')!r}, not {fetch!r}")
    artifact = f"https://github.com/{repo}/releases/tag/{tag}"
    if (document.get("artifact_root") or {}).get("path") != artifact:
        problems.append(f"[artifact_root] path is {(document.get('artifact_root') or {}).get('path')!r}, not "
                        f"{artifact!r}")
    checksums = document.get("checksums")
    if not isinstance(checksums, list) or sorted(map(str, checksums)) != sorted(
            f"sha256:{digest}" for digest in pinned_rows(pins).values()):
        problems.append(f"checksums are not exactly the {len(pinned_rows(pins))} pinned archives' sha256, each once")
    return problems


def verify_branch(plan: Plan, repo: Path) -> dict:
    """design step 15: the branch's own judges over its tracked files and the 17 archives."""
    if not (repo / ".git").exists():
        raise Refusal(f"{repo} is not a clone (no .git). Nothing was read. Clone the add-host branch and name it with "
                      "--repo, or run the clone's own scripts/fixed_point_linux_seed.py")
    head = git_text(repo, "rev-parse", "--verify", "HEAD^{commit}", what="the clone's HEAD cannot be read")
    rev = git_text(repo, "rev-parse", "--verify", f"{plan.args.rev}^{{commit}}", what=f"--rev {plan.args.rev}")
    if rev != head:
        raise Refusal(f"--rev {plan.args.rev} is {rev[:10]} and the clone's HEAD is {head[:10]}: the capture reads the "
                      "checked-out files and the push rows read --rev, so they must be one commit. Check out --rev")
    stage0_bytes = git_blob(repo, rev, "src/stage0")
    if stage0_bytes is None:
        raise Refusal(f"{rev[:10]} has no src/stage0. Nothing was judged")
    pins = text_rows(stage0_bytes.decode("utf-8"), f"{rev[:10]}:src/stage0")
    for key in ("compiler_git_commit_hash", "rustfmt_git_commit_hash"):
        if pins.get(key) != plan.commit:
            raise Refusal(f"{repo}/src/stage0 pins {key} = {pins.get(key)!r}, not {plan.commit}. Nothing was judged")
    date, seed_root = pins.get("compiler_date", ""), repo / SEED_DIR
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", date):
        raise Refusal(f"{rev[:10]}:src/stage0 pins compiler_date = {date!r}. Nothing was judged")
    dated, rows = seed_root / "dist" / date, pinned_rows(pins)
    missing, wrong = [], []
    for key, digest in sorted(rows.items()):
        path = seed_root / key
        if path.is_symlink() or not path.is_file():
            missing.append(Path(key).name)
        elif sha256_file(path) != digest:
            wrong.append(Path(key).name)
    extra = sorted(entry.name for entry in dated.iterdir() if entry.name.endswith((".tar.xz", ".tar.gz", ".tar"))
                   and f"dist/{date}/{entry.name}" not in rows) if dated.is_dir() else []
    if missing or wrong or extra:
        raise Refusal(f"{dated} is not the {len(rows)} pinned archives: "
                      + "; ".join(filter(None, (f"missing {missing[:3]} ({len(missing)})" if missing else "",
                                               f"other bytes {wrong[:3]}" if wrong else "",
                                               f"not pinned {extra[:3]}" if extra else "")))
                      + f". Nothing was judged. Place exactly the pinned archives there (`agh release download "
                        f"<repo> <tag> --asset <name> --dir {dated}`, or copy them from the producing root)")
    # Before any judge is loaded from it: the files the judges read are the commit's.
    problems = view_problems(repo, rev, {f"{SEED_DIR}/{key}" for key in rows})
    if problems:
        raise Refusal(f"the files verify judges in {repo} ({', '.join(VERIFY_VIEW)}) are not {rev[:10]}'s: "
                      f"{'; '.join(problems)}. Nothing was judged: an untracked or flagged file would stand in for "
                      f"one the branch lacks or changes. Move what is not the commit's aside (only the "
                      f"{len(rows)} pinned archives are placed), or clone the branch again")
    dirty = git_text(repo, "status", "--porcelain", "--untracked-files=no", what="the clone's state cannot be read")
    if dirty:
        raise Refusal(f"the clone {repo} has changes to tracked files ({dirty.splitlines()[0]}): the tree judged must "
                      "be the commit's. Nothing was changed")
    # The rest of the tree, which leg 1 of --rebuild builds: no tracked file changed, and no index
    # entry that git status does not compare (skip-worktree, assume-unchanged) hiding a change.
    flagged = [entry for entry in git_text(repo, "ls-files", "-v", "-z", what="the clone's index cannot be read")
               .split("\0") if entry and not entry.startswith("H ")]
    if flagged:
        raise Refusal(f"the clone {repo} has {len(flagged)} index entries git status does not compare with {rev[:10]} "
                      f"(skip-worktree, assume-unchanged or unmerged; the first: {flagged[0]!r}): the tree judged must "
                      "be the commit's. Nothing was changed. Clear them (git update-index --no-skip-worktree "
                      "--no-assume-unchanged <path>) or clone the branch again")
    hosts = plan.repo_module(repo, "seed_host_ledger")
    try:
        payloads, cohort = hosts.host_payloads(pins, plan.host), hosts.pinned_hosts(pins)
    except ValueError as error:
        raise Refusal(f"{repo}/src/stage0 does not pin {plan.host}'s seed: {error}. Nothing was judged") from error
    receipt = seed_root / "host-proofs" / plan.host / validator().RECEIPT_NAME
    named = {"commit": plan.commit, "receipt_sha256": sha256_file(receipt) if receipt.is_file() else None}
    # The door names this host's receipt and nothing else (commit writes exactly that one entry).
    if hosts.FIXED_POINT_FIRST_HOSTS != {plan.host: named}:
        raise Refusal(f"the clone's real door ({DOOR_FILE} FIXED_POINT_FIRST_HOSTS) is "
                      f"{hosts.FIXED_POINT_FIRST_HOSTS!r}, and this branch adds exactly {{{plan.host!r}: {named!r}}}. "
                      "Nothing else was judged")
    problems = admission_problems((seed_root / "trust-stage0-admission.json").read_bytes()
                                  if (seed_root / "trust-stage0-admission.json").is_file() else b"", pins, plan.commit)
    if problems:
        raise Refusal(f"the branch's {ADMISSION_FILE} is not prepare.py's internal admission of exactly the pin: "
                      f"{'; '.join(problems[:4])}. Nothing else was judged")
    try:
        problems = release_problems(tomllib.loads((repo / LEDGER_FILE).read_text(encoding="utf-8")), pins, plan.commit)
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        problems = [f"it cannot be read as TOML ({error})"]
    if problems:
        raise Refusal(f"the branch's {LEDGER_FILE} does not name this pin's release and archives: "
                      f"{'; '.join(problems[:4])}. Nothing else was judged")
    recreate = plan.repo_module(repo, "recreate_bootstrap")
    statuses = {}
    for name in (plan.host, *(other for other in cohort if other != plan.host)):
        lineage = plan.seed_capture(recreate, repo, name)
        problems = lineage_problems(lineage, name, cohort, recreate, name == plan.host)
        if problems:
            raise Refusal(f"recreate_bootstrap's capture of the clone's seed for {name} refuses: "
                          f"{'; '.join(problems[:4])}. Nothing was changed")
        statuses[name] = lineage["status"]
    try:
        joined = hosts.fixed_point_module().check_archive_joins(seed_root, payloads, plan.host, hosts.read_proof,
                                                                archive_root=seed_root)
    except (ValueError, OSError) as error:
        raise Refusal(f"the full archive join refuses: {error}. Nothing was changed") from error
    for what, command in (("check_seed_freshness.py", plan.freshness(repo)),
                          (f"check_ledger_pins.py --rev {rev[:10]}", plan.ledger_pins(repo, rev)),
                          (f"check_corpus_membership.py --rev {rev[:10]}", plan.corpus(repo, "--rev", rev))):
        done = subprocess.run(command, cwd=repo, env=plan.verify_env(), capture_output=True, text=True,
                              errors="replace")
        if done.returncode:
            findings = [line for line in done.stdout.splitlines() if line.startswith("FINDING: ")]
            raise Refusal(f"{what} is red on the branch ({refresh.ended(done.returncode)}): "
                          f"{'; '.join(findings[:3]) or refresh.last_line(done.stdout + done.stderr)}. Nothing was "
                          "changed; a red the parent carries too is main's to fix before this lands")
    say(f"verify: {rev[:10]} in {repo}: the {len(rows)} pinned archives are in place and every file the judges read "
        f"is the commit's; the real door names this receipt alone; the admission and the ledger's release name "
        f"exactly the pin; the recreator captured {', '.join(f'{name} {status}' for name, status in statuses.items())}; "
        f"{joined} archive members joined; check_seed_freshness, check_ledger_pins and check_corpus_membership are "
        f"green. A build from this seed is graded {recreate.UNPINNED_ROOT_SEED_READY}")
    return {"head": head, "pins": pins, "payloads": payloads, "cohort": cohort, "hosts": hosts,
            "receipt_sha256": named["receipt_sha256"], "stage0_sha256": sha256_bytes(stage0_bytes)}


def leg_step(command: list[str], out: Path, doing: str, *, env: dict[str, str], cwd: Path,
             merge: bool = False) -> Path:
    """A command whose output file says it is done: run once, refused in words."""
    if out.is_file():
        return out
    errors = None if merge else out.with_name(out.name + ".stderr")
    if refresh.to_file(command, out, env=env, cwd=cwd, stderr=errors, merge=merge):
        printed = out.with_name(out.name + ".partial")
        reason = refresh.last_line(printed.read_text(errors="replace")) if merge else said(printed, errors)
        raise Refusal(f"{doing}: `{shlex.join(command)}` refused: {reason}. What it printed is {printed}; the same "
                      "command line runs this part again")
    return out


def bind(path: Path, binding: dict, leg: str, made: list[str]) -> None:
    """What --work holds of `leg` is for one head, receipt and pin (leg 2: and one produced
    root): `path` says which, written when the leg first starts. A run for others, or
    files of the leg with no such record (`made`), is refused: nothing there is reused."""
    if path.is_file():
        was = read_json(path, f"the record of what {leg} in {path.parent} is for")
        moved = sorted(key for key in set(was) | set(binding) if was.get(key) != binding.get(key))
        if moved:
            raise Refusal(f"{path.parent} holds {leg} of {brief({key: was.get(key) for key in moved})} ({path}), and "
                          f"this run is for {brief({key: binding.get(key) for key in moved})}. Nothing was started: a "
                          f"leg's records and files are reused only for what they were made for. Move {path.parent} "
                          "aside or name another --work")
        return
    if made:
        raise Refusal(f"{path.parent} holds {made[:3]} of {leg} and no {path.name} saying what they were made for. "
                      f"Nothing was started. Move {path.parent} aside or name another --work")
    write_json(path, binding)


def seed_leg(plan: Plan, repo: Path, work: Path, branch: dict) -> dict:
    """Leg 1: the clone's own source built in seed mode from the pinned archives."""
    bind(work / "seed-leg.binding.json", branch["binding"], "leg 1",
         sorted(entry.name for entry in work.iterdir() if entry.name not in ("verify.lock", "seed-leg.binding.json")))
    done = work / "seed-leg.json"
    if done.is_file():
        say(f"verify --rebuild: leg 1 already done ({done}); not repeated")
        return read_json(done, "leg 1's record")
    ledger_dir, tools, seed = work / "ledger", work / "tools", work / "seed"
    for directory in (work / "home", ledger_dir / "tmp", tools):
        directory.mkdir(parents=True, exist_ok=True)
    if not (tools / "ninja").is_file():
        shutil.copyfile(os.path.realpath(plan.args.ninja), tools / "ninja")
        (tools / "ninja").chmod(0o755)
    refresh.write_traps(ledger_dir)
    env, date = plan.leg_env(work), branch["pins"]["compiler_date"]
    if not seed.is_dir():
        leg_step(plan.seed_sysroot(repo / SEED_DIR / "dist" / date, repo / "src" / "stage0", seed),
                 work / "seed-sysroot.json", "the pinned archives could not be installed as a seed sysroot", env=env,
                 cwd=work)
    admission = leg_step(plan.admit_for(seed, repo, branch["head"]), work / "seed.admission.json",
                         "the seed sysroot was not admitted", env=env, cwd=work)
    leg_step(plan.seed_config_for(repo), work / "seed-config.json", "the clone's seed-mode config could not be written",
             env=env, cwd=work)
    leg_step(plan.closure_for(repo, seed, "prepare"), work / "closure-prepare.log",
             "the clone's dependency closure could not be fetched (the one fetch of the exit test)", env=env, cwd=repo,
             merge=True)
    leg_step(plan.closure_for(repo, seed, "check"), work / "closure-check.log",
             "the clone's dependency closure is not offline-complete", env=env, cwd=repo, merge=True)
    # Bootstrap, the build-tree manager the clone's x.py asks for, as every role constructs it.
    refresh.construct_bootstrap(types.SimpleNamespace(
        worktree=repo, bootstrap=lambda: repo / "build" / "bootstrap" / "debug" / "bootstrap",
        file=lambda label, suffix: work / f"{label}.{suffix}", construct=lambda: plan.construct_for(repo),
        construct_env=lambda label: {**env, "RUST_BOOTSTRAP_CONFIG": str(repo / "bootstrap.toml")}), SEED_LABEL)
    run_out = work / "seed.run.json"
    if not run_out.is_file():
        say(f"verify --rebuild: leg 1, x.py build --stage 2 of {branch['head'][:10]} in {repo} from the pinned seed")
        code, asked = run_recorded(plan.run_seed_mode(repo, ledger_dir, admission, plan.args.lean_library, tools,
                                                      plan.args.jobs), run_out, work / "seed.run.stderr", env=env,
                                   cwd=work)
        if code:
            raise Refusal(f"leg 1's seed-mode build of {branch['head'][:10]} did not end clean "
                          f"({refresh.ended(code)}{' after ' + ', '.join(asked) if asked else ''}); its record is "
                          f"{run_out}.partial. Main may no longer build from this seed for a reason of its own; the "
                          f"exit test is not passed. Move {work} aside to run leg 1 again")
    record = read_json(run_out, "leg 1's run record")
    # seed_staircase.py resolves the ledger it is given (--work may be reached through a link).
    arrangement = jobserver_arrangement(Path(os.path.realpath(ledger_dir)), plan.args.jobs)
    problems = refresh.rung_problems(record) + jobserver_problems(record, arrangement)
    if problems:
        raise Refusal(f"leg 1's run record is not clean: {'; '.join(problems[:3])}. The exit test is not passed")
    recreate = plan.repo_module(repo, "recreate_bootstrap")
    lineage = plan.seed_capture(recreate, repo, plan.host, build_root=repo / "build")
    if lineage.get("status") != "validated" or lineage.get("errors"):
        raise Refusal(f"after leg 1 the recreator's capture of the hydrated seed is {lineage.get('status')!r}, not "
                      f"validated: {'; '.join(map(str, lineage.get('errors') or []))[:300]}. The exit test is not passed")
    chained = leg_step(plan.lineage(admission, run_out, repo / "build" / plan.host / "stage2", repo),
                       work / "lineage.json", "the lineage from the pinned seed could not be made", env=env, cwd=work)
    root = read_json(chained, "the lineage record").get("root") or {}
    module = branch["hosts"].fixed_point_module()
    disclosure = module.root_disclosure(module.parse_receipt(
        (repo / SEED_DIR / "host-proofs" / plan.host / module.RECEIPT_NAME).read_bytes()).fields)
    pin = root.get("pin_admission") or {}
    if pin.get("kind") != module.KIND or pin.get("root_disclosure") != disclosure:
        raise Refusal(f"the lineage's root does not carry the fixed-point admission and its disclosure "
                      f"(root.pin_admission is {brief(pin)}). The exit test is not passed")
    made = {"head": branch["head"], "binding": branch["binding"], "run_sha256": sha256_file(run_out),
            "lineage_sha256": sha256_file(chained), "capture": lineage["status"], "pin_admission": pin}
    write_json(done, made)
    say(f"verify --rebuild: leg 1 passed: x.py built {branch['head'][:10]} from the pinned Linux seed, the capture is "
        "validated and the lineage's root names the fixed-point admission")
    return made


def produced_tree(produced: Path, host: str) -> Path:
    """Where the produced root's producer build tree is (its LLVM and lld)."""
    producer = read_json(produced / "kept" / "p.build.json", "the produced root's producer record")
    kept = produced / "kept" / f"{producer.get('label')}-tree" / host
    if kept.is_dir():
        return kept
    pointer = produced / "kept" / "current-tree.json"
    if pointer.is_file() and read_json(pointer, "the produced root's tree pointer").get("label") == producer.get("label"):
        return produced / "src" / "build" / host
    raise Refusal(f"the produced root {produced} holds no producer build tree (kept/{producer.get('label')}-tree or "
                  "src/build): leg 2 links its LLVM and lld. Nothing was built")


def produced_problems(inputs: dict, tracked: dict, fields: dict) -> list[str]:
    """Why a produced root's setup record (`inputs`) does not bind the cargo home, the
    Lean copy and ninja that the branch's evidence inputs.json (`tracked`) and receipt
    (`fields`) bind. (The job count and the linker are bound by rung_config_sha256.)"""
    cargo, lean, ninja = (inputs.get(key) if isinstance(inputs.get(key), dict) else {}
                          for key in ("cargo_home", "lean", "ninja"))
    bound_cargo, bound_lean, bound_ninja = (tracked.get(key) if isinstance(tracked.get(key), dict) else {}
                                            for key in ("cargo_home_inputs", "clean_lean_inputs", "ninja"))
    rows = (("the cargo-home input manifest sha256", cargo.get("manifest_sha256"),
             (bound_cargo.get("sha256"), fields.get("cargo_home_inputs_sha256"))),
            ("the cargo-home trees", cargo.get("trees"), (bound_cargo.get("trees"),)),
            ("the Lean input manifest sha256", lean.get("manifest_sha256"),
             (bound_lean.get("sha256"), fields.get("clean_lean_inputs_sha256"))),
            ("the Lean library", lean.get("library"), (bound_lean.get("library"),)),
            ("ninja's sha256", ninja.get("sha256"), (bound_ninja.get("sha256"),)))
    return [f"{what} is {brief(have, 80)} there, and the branch binds {brief(list(bound), 80)}"
            for what, have, bound in rows if have is None or any(value != have for value in bound)]


def replay_leg(plan: Plan, repo: Path, work: Path, branch: dict) -> dict:
    """Leg 2: the commit built again at the recorded root from the pinned archives as
    installed, with the produced native outputs, compared with the receipt's rows."""
    module = branch["hosts"].fixed_point_module()
    proofs = repo / SEED_DIR / "host-proofs" / plan.host
    receipt = (proofs / module.RECEIPT_NAME).read_bytes()
    fields, rows = module.parse_receipt(receipt).fields, module.member_rows(receipt)
    root, produced = Path(fields["build_root"]), plan.args.produced
    made_here, done = work / "replay-root.json", work / "replay-leg.json"
    if (root.exists() or root.is_symlink()) and not made_here.is_file():
        raise Refusal(f"the recorded root {root} is there, and this verify did not make it. Nothing was built. Move it "
                      f"aside (mv {root} {root}.produced) and give --produced {root}.produced")
    if produced is None or not (produced / "inputs" / "inputs.json").is_file() or produced == root:
        raise Refusal(f"--produced {produced} is not the produced root (no inputs/inputs.json there, or it is the "
                      f"recorded root itself). Nothing was built")
    bind(work / "replay-leg.binding.json", {**branch["binding"], "produced": str(produced),
                                            "produced_inputs_sha256": sha256_file(produced / "inputs" / "inputs.json")},
         "leg 2", [path.name for path in (made_here, done) if path.exists()])
    if done.is_file():
        say(f"verify --rebuild: leg 2 already done ({done}); not repeated")
        return read_json(done, "leg 2's record")
    inputs = read_json(produced / "inputs" / "inputs.json", "the produced root's setup record")
    # The inputs leg 2 copies from --produced are the ones the branch's receipt and evidence bind,
    # not merely the ones that root's own setup record names.
    tracked = read_json(proofs / module.EVIDENCE_DIR / "inputs.json", "the branch's evidence inputs.json")
    problems = produced_problems(inputs, tracked, fields)
    if problems:
        raise Refusal(f"the produced root {produced} did not bind the inputs the branch's receipt and evidence bind: "
                      f"{'; '.join(problems[:3])}. Nothing was built; it is not the root that recorded this receipt")
    replay = plan.replay_plan(root)
    replay.lean_library = Path(inputs["lean"]["library"])
    if root not in replay.lean_library.parents:
        raise Refusal(f"the produced root's Lean library {replay.lean_library} is not under {root}. Nothing was built")
    if not made_here.is_file():
        root.mkdir(parents=True)
        write_json(made_here, {"root": str(root), "made": time.strftime("%Y-%m-%dT%H:%M:%S%z")})
    for directory in (replay.home, replay.tools, replay.inputs, replay.ledger / "tmp", replay.kept):
        directory.mkdir(parents=True, exist_ok=True)
    if not replay.src.exists():
        say(f"verify --rebuild: leg 2, the root again at {root}")
        remove_own(root / "src.partial")
        plan.checkout_for(repo, plan.commit, root / "src.partial")
        (root / "src.partial").rename(replay.src)
    problems = refresh.worktree_problems(replay.src, plan.commit)
    if problems:
        raise Refusal(f"{replay.src} is not a clean checkout of {plan.commit[:10]}: {'; '.join(problems)}. Nothing "
                      "was built")
    config = replay.src / "bootstrap.toml"
    if not config.is_file():
        leg_step(replay.seed_config(), replay.inputs / "seed-config.json", "the base config could not be regenerated",
                 env=replay.env(), cwd=root)
    if sha256_file(config) != fields["base_config_sha256"]:
        raise Refusal(f"the regenerated base config {config} has sha256 {sha256_file(config)[:16]}, and the receipt's "
                      f"base_config_sha256 is {fields['base_config_sha256'][:16]}: the replay would not be the recorded "
                      "build. The exit test is not passed")
    for source, target in ((produced / "tools" / "ninja", replay.tools / "ninja"),):
        if not target.is_file():
            shutil.copyfile(source, target)
            target.chmod(0o755)
    if sha256_file(replay.tools / "ninja") != inputs["ninja"]["sha256"]:
        raise Refusal("the copied ninja is not the one the produced root bound. Nothing was built")
    lean_copy = replay.inputs / "lean"
    if not lean_copy.exists():
        refresh.copy_tree(produced / "inputs" / "lean", lean_copy)
    # setup's binding of that copy, which every run's Lean record is held to.
    lean_manifest = replay.inputs / "clean-lean-inputs.json"
    if not lean_manifest.is_file():
        shutil.copyfile(produced / "inputs" / "clean-lean-inputs.json", lean_manifest)
    if sha256_file(lean_manifest) != inputs["lean"]["manifest_sha256"]:
        raise Refusal("the produced root's Lean input manifest is not the one its setup bound. Nothing was built")
    for relative in support().CARGO_HOME_INPUT_TREES:
        source, target = produced / "ledger" / "cargo-home" / relative, replay.ledger / "cargo-home" / relative
        if source.is_dir() and not target.exists():
            target.parent.mkdir(parents=True, exist_ok=True)
            refresh.copy_tree(source, target)
    if cargo_home_trees(replay) != inputs["cargo_home"]["trees"]:
        raise Refusal("the copied cargo home is not the one the produced root bound. Nothing was built")
    steps: dict = {}
    version = captured(replay.version(), "the version of the commit could not be read", env=replay.env(),
                       cwd=root).strip()
    admitted = admit(replay, "admit-pinned", repo / SEED_DIR / "dist" / branch["pins"]["compiler_date"], version,
                     steps)
    install_seed(replay, admitted, version, steps)
    if not replay.stage0.exists():
        refresh.copy_tree(replay.seed, replay.stage0)
    draft = replay.file(REPLAY_LABEL, "bootstrap.toml.draft")
    draft.unlink(missing_ok=True)
    captured(replay.config(draft), "the rung config could not be regenerated", env=replay.env(), cwd=root)
    text = draft.read_text() + refresh.config_tail(inputs["jobs"], inputs["linker"] == "self-contained")
    draft.unlink()
    if sha256_bytes(text.encode("utf-8")) != fields["rung_config_sha256"]:
        raise Refusal(f"the regenerated rung config has sha256 {sha256_bytes(text.encode('utf-8'))[:16]}, and the "
                      f"receipt's rung_config_sha256 is {fields['rung_config_sha256'][:16]}. The exit test is not passed")
    replay.rung_config().write_text(text)
    host_dir = replay.build_dir() / plan.host
    host_dir.mkdir(parents=True, exist_ok=True)
    tree = produced_tree(produced, plan.host)
    for name in refresh.NATIVE_OUTPUTS:
        if (tree / name).is_dir() and not (host_dir / name).exists():
            refresh.copy_tree(tree / name, host_dir / name)
    native = native_table(host_dir)
    if native["sha256"] != fields["native_outputs_sha256"]:
        raise NotComparable(f"not comparable: the LLVM and lld at {host_dir} ({native['files']} files, "
                            f"{native['sha256'][:16]}) are not the record's native outputs "
                            f"({fields['native_outputs_sha256'][:16]}), so the replay's stage2 cannot be compared "
                            "with the receipt. This is not a pass")
    run_out = replay.file(REPLAY_LABEL, "run.json")
    if not run_out.is_file():
        admission = leg_step(replay.admit(), replay.file(REPLAY_LABEL, "admission.json"),
                             "the installed pinned archives were not admitted", env=replay.env(), cwd=root)
        refresh.write_traps(replay.ledger)
        leg_step(replay.closure(), replay.file(REPLAY_LABEL, "closure.log"), "the replay's dependency closure is not "
                 "offline-complete", env=replay.env(), cwd=replay.src, merge=True)
        if "--trust-build-tree-lock" in (replay.src / "x.py").read_text(errors="replace"):
            refresh.construct_bootstrap(replay, REPLAY_LABEL)
        say(f"verify --rebuild: leg 2, x.py build --stage 2 of {plan.commit[:10]} at {root} from the pinned archives")
        code, asked = run_label(replay, REPLAY_LABEL, BUILD_LINE, admission)
        if code:
            raise Refusal(f"leg 2's replay build did not end clean ({refresh.ended(code)}"
                          f"{' after ' + ', '.join(asked) if asked else ''}); its record is {run_out}.partial. The exit "
                          "test is not passed")
    problems = run_problems(replay, read_json(run_out, "the replay's run record"), REPLAY_LABEL, BUILD_LINE, inputs)
    if problems:
        raise Refusal(f"the replay's run record is not clean: {'; '.join(problems[:3])}. The exit test is not passed")
    after = native_table(host_dir)
    if after["sha256"] != fields["native_outputs_sha256"]:
        raise NotComparable(f"not comparable: the replay build changed the LLVM and lld it linked ({after['files']} "
                            f"files, {after['sha256'][:16]}). This is not a pass")
    manifest = replay.kept / "replay.stage2.json"
    if not manifest.is_file():
        partial = manifest.with_name(manifest.name + ".partial")
        partial.unlink(missing_ok=True)
        captured(replay.manifest(replay.stage2(), partial), "the replay's stage2 could not be measured",
                 env=replay.env(), cwd=root)
        partial.replace(manifest)
    built = {path: row.get("sha256") for path, row in manifest_rows(manifest).items() if row.get("kind") == "file"}
    excused = set(module.split_list(fields["not_reproduced"]))
    moved = sorted(path for path in set(built) | set(rows) if path not in excused and built.get(path) != rows.get(path))
    if moved:
        raise Refusal(f"the pinned archives did not rebuild their own source to the receipt's rows: {len(moved)} "
                      f"file(s) differ outside not_reproduced (the first: {', '.join(moved[:5])}; the manifest is "
                      f"{manifest}). The exit test is not passed")
    made = {"root": str(root), "binding": branch["binding"], "produced": str(produced), "rows": len(rows),
            "excused": sorted(excused), "manifest_sha256": sha256_file(manifest), "native_outputs_sha256": after["sha256"]}
    write_json(done, made)
    say(f"verify --rebuild: leg 2 passed: the pinned archives rebuilt {plan.commit[:10]} at {root} to the receipt's "
        f"{len(rows)} rows" + (f" outside {', '.join(sorted(excused))}" if excused else ""))
    return made


def verify_step(plan: Plan) -> int:
    repo = plan.args.repo
    branch = verify_branch(plan, repo)
    if not plan.args.rebuild:
        return 0
    work = plan.args.work
    for name, value in (("--produced", plan.args.produced), ("--work", work), ("--lean-library", plan.args.lean_library)):
        if value is None:
            raise Refusal(f"verify --rebuild needs {name} (see --help). The branch is verified; nothing was built")
    if work == repo or repo in work.parents:
        raise Refusal(f"--work {work} is inside the clone {repo}; the builds' records belong outside it")
    work.mkdir(parents=True, exist_ok=True)
    # What every file under --work is for: this head, its receipt and its pin.
    branch["binding"] = {"commit": plan.commit, "host": plan.host, "head": branch["head"],
                         "receipt_sha256": branch["receipt_sha256"], "stage0_sha256": branch["stage0_sha256"]}
    with open(work / "verify.lock", "a+") as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            raise Refusal(f"another verify --rebuild holds {work / 'verify.lock'}. Nothing was started") from None
        seed_leg(plan, repo, work, branch)
        replay = replay_leg(plan, repo, work, branch)
        # publish reads this: the archives it uploads are the ones this exit test passed with.
        write_json(work / "exit-test.json", {
            "schema": EXIT_TEST_SCHEMA, **branch["binding"],
            "archives": {Path(key).name: digest for key, digest in pinned_rows(branch["pins"]).items()},
            "produced": replay["produced"], "seed_leg_sha256": sha256_file(work / "seed-leg.json"),
            "replay_leg_sha256": sha256_file(work / "replay-leg.json"),
            "passed": time.strftime("%Y-%m-%dT%H:%M:%S%z")})
    say("verify --rebuild: the exit test passed (docs/PLAN.md PKG-S6): both records valid against the 17 archives, "
        "x.py builds the clone's source from the pinned Linux seed, and the pinned archives rebuild their own source "
        f"to the receipt's rows outside not_reproduced. Recorded in {work / 'exit-test.json'}")
    say(f"next (design step 17): move the replay root aside and the produced root back (mv {replay['root']} "
        f"{replay['root']}.replay && mv {replay['produced']} {replay['root']}), then fixed_point_linux_seed.py "
        f"publish --exit-test {work}")
    return 0


# ---------------------------------------------------------------------------
# publish (design step 17)


def release_assets(plan: Plan, slug: str, tag: str) -> dict[str, dict]:
    """The release's assets by name, as `agh release assets` lists them."""
    command = plan.agh("release", "assets", slug, tag, "--format", "json")
    try:
        done = subprocess.run(command, capture_output=True, text=True, errors="replace", env=plan.agh_env())
    except OSError as error:
        raise Refusal(f"agh could not be started ({command[0]}): {error.strerror or error}. Nothing was uploaded") \
            from error
    if done.returncode:
        raise Refusal(f"`{shlex.join(command)}` {refresh.ended(done.returncode)}: "
                      f"{refresh.last_line(done.stderr or done.stdout)}. Nothing was uploaded or deleted")
    try:
        value = json.loads(done.stdout)
    except ValueError as error:
        raise Refusal(f"`{shlex.join(command)}` printed no JSON ({error}). Nothing was uploaded") from error
    items = value if isinstance(value, list) else value.get("items", value.get("assets")) \
        if isinstance(value, dict) else None
    if not isinstance(items, list) or not all(isinstance(item, dict) and isinstance(item.get("name"), str)
                                              for item in items):
        raise Refusal(f"`{shlex.join(command)}` printed no list of named assets. Nothing was uploaded")
    names = [item["name"] for item in items]
    if len(set(names)) != len(names):
        raise Refusal(f"the release {tag} lists an asset name twice. Nothing was uploaded")
    return {item["name"]: item for item in items}


def held_bytes(asset: dict, digest: str) -> bool:
    """Whether an uploaded asset holds the pinned bytes, by the digest the release reports."""
    return asset.get("digest") == f"sha256:{digest}" and asset.get("state", "uploaded") == "uploaded"


def exit_test_passed(plan: Plan, made: dict, tip: str, pins: dict[str, str], stage0: bytes) -> dict:
    """The record a passed `verify --rebuild` wrote (--exit-test, its --work), of this
    branch tip, its receipt, its pin and these archives: publish is the one step that
    cannot be undone, and uploads only archives the exit test passed with."""
    given = plan.args.exit_test
    path = given / "exit-test.json" if given is not None else None
    if path is None or not path.is_file():
        raise Refusal(f"publish needs the exit test (design step 16) passed on this branch: "
                      f"{'no --exit-test was given' if path is None else f'{path} is not there'}. Nothing was "
                      f"uploaded. In a clone of {made['branch']}, run fixed_point_linux_seed.py verify --rebuild "
                      "--produced <root>.produced --work <W> ...; then publish --exit-test <W>")
    passed = read_json(path, "the exit test's record")
    want = {"schema": EXIT_TEST_SCHEMA, "commit": plan.commit, "host": plan.host, "head": tip,
            "receipt_sha256": made["receipt_sha256"], "stage0_sha256": sha256_bytes(stage0),
            "archives": {Path(key).name: digest for key, digest in pinned_rows(pins).items()}}
    moved = sorted(key for key, value in want.items() if passed.get(key) != value)
    if moved:
        raise Refusal(f"{path} is an exit test of another {', '.join(moved)} than the branch tip {tip[:10]} commit "
                      f"recorded (it names head {str(passed.get('head'))[:10]}). Nothing was uploaded: run verify "
                      "--rebuild on a clone of this tip")
    return {"path": str(path), "sha256": sha256_file(path)}


def publish_step(plan: Plan) -> int:
    require_setup(plan)
    done = plan.kept / "publish.json"
    if not commit_record(plan).is_file():
        raise Refusal(f"commit is not done ({commit_record(plan)} is not there): the archives published are the ones "
                      f"the add-host branch pins. Nothing was uploaded. Run: {shlex.join(command_line(plan, 'commit'))} "
                      "--parent ... --branch ... --identity ... --darwin-pack-state ...")
    made = read_json(commit_record(plan), "the commit step's record")
    repo, tip = Path(made["repo"]), made["commits"][-1]
    found = git_call(repo, "rev-parse", "--verify", "--quiet", f"refs/heads/{made['branch']}")
    if found.returncode or found.stdout.decode().strip() != tip:
        raise Refusal(f"{made['branch']} in {repo} is not the tip {tip[:10]} commit recorded. Nothing was uploaded")
    stage0 = git_text(repo, "show", f"{tip}:src/stage0", what="the branch's pin cannot be read")
    pins = text_rows(stage0, "src/stage0")
    passed = exit_test_passed(plan, made, tip, pins, git_blob(repo, tip, "src/stage0") or b"")
    release = tomllib.loads(git_text(repo, "show", f"{tip}:{LEDGER_FILE}", what="the branch's ledger cannot be read"))
    slug, tag = (release.get("release") or {}).get("repo"), (release.get("release") or {}).get("tag")
    date = pins.get("compiler_date", "")
    if tag != f"trust-stage0-{date}-{plan.commit[:9]}" or not isinstance(slug, str) or not slug:
        raise Refusal(f"the branch's ledger names the release {slug!r} {tag!r}, not this pin's "
                      f"trust-stage0-{date}-{plan.commit[:9]}. Nothing was uploaded")
    eight = {Path(key).name: digest for key, digest in ledger().host_payloads(pins, plan.host).items()
             if "/trust-src-" not in key}
    dated = plan.output_root() / "dist" / date
    wrong = [name for name, digest in sorted(eight.items())
             if not (dated / name).is_file() or (dated / name).is_symlink() or sha256_file(dated / name) != digest]
    if len(eight) != 8 or wrong:
        raise Refusal(f"{dated} does not hold this host's eight archives with the branch's pins ({wrong[:3]}). "
                      "Nothing was uploaded")
    if done.is_file():
        was = read_json(done, "the publish step's record")
        if was.get("tag") != tag or was.get("assets") != eight:
            raise Refusal(f"{done} records another release or other archives. Nothing was uploaded. Move it aside")
        # Done once, and the release is read again before the landing step is named: an asset
        # replaced since (another uploader's --clobber) is not what the branch pins.
        assets = release_assets(plan, slug, tag)
        differ = [name for name in sorted(eight) if name not in assets or not held_bytes(assets[name], eight[name])]
        if differ:
            raise Refusal(f"publish is done ({done}), and {slug} {tag} no longer reports {differ[:3]} with the pinned "
                          f"digests ({len(differ)} such asset(s)). Do not land. Nothing was uploaded or deleted: find "
                          "out what replaced them; the pin, not the release, is the authority")
        say(f"publish: already done ({done}): {len(eight)} archives on {slug} {tag}, read back in "
            f"{was.get('download')} and still reported with the pinned digests; not repeated")
        say(publish_next(plan, made))
        return 0
    assets = release_assets(plan, slug, tag)
    clash = [name for name in sorted(eight) if name in assets and not held_bytes(assets[name], eight[name])]
    if clash:
        asset = assets[clash[0]]
        raise Refusal(f"T13: {slug} {tag} already has {clash[0]} with digest {asset.get('digest')!r} (state "
                      f"{asset.get('state')!r}), not the pinned sha256:{eight[clash[0]][:16]}... "
                      f"({len(clash)} such asset(s)). An asset is never replaced (--clobber) or deleted here. Nothing "
                      "was uploaded. Find out what put it there; the pin, not the release, is the authority")
    upload = [str(dated / name) for name in sorted(eight) if name not in assets]
    if upload:
        command = plan.agh("release", "upload", slug, tag, *upload)
        say(f"publish: uploading {len(upload)} archive(s) to {slug} {tag} (no --clobber)")
        code = subprocess.run(command, env=plan.agh_env()).returncode
        if code:
            raise Refusal(f"`{shlex.join(command[:5])} ...` {refresh.ended(code)}. Whatever reached the release is "
                          "listed by the next run, which uploads only what is missing and refuses other bytes")
    else:
        say(f"publish: {slug} {tag} already holds the eight archives with their pinned bytes; nothing to upload")
    assets = release_assets(plan, slug, tag)
    absent = [name for name in sorted(eight) if name not in assets or not held_bytes(assets[name], eight[name])]
    if absent:
        raise Refusal(f"after the upload, {slug} {tag} does not report {absent[:3]} with the pinned digests. Nothing "
                      "was deleted; run publish again")
    download = free_name(plan.root / "publish" / "download")
    download.parent.mkdir(parents=True, exist_ok=True)
    download.mkdir()
    command = plan.agh("release", "download", slug, tag, *(word for name in sorted(eight) for word in ("--asset", name)),
                       "--dir", str(download))
    code = subprocess.run(command, env=plan.agh_env()).returncode
    if code:
        raise Refusal(f"the read-back `agh release download ... --dir {download}` {refresh.ended(code)}. The archives "
                      "are on the release; run publish again to read them back")
    got = sorted(entry.name for entry in download.iterdir())
    differ = [name for name in sorted(eight) if not (download / name).is_file() or (download / name).is_symlink()
              or sha256_file(download / name) != eight[name]]
    if got != sorted(eight) or differ:
        raise Refusal(f"the read-back in {download} is {got[:4]}..., and {differ[:3]} is not its pin: what the release "
                      "serves is not what the branch pins. Do not land; nothing was deleted")
    write_json(done, {"schema": PUBLISH_SCHEMA, "commit": plan.commit, "host": plan.host, "root": str(plan.root),
                      "repo": slug, "tag": tag, "assets": eight, "uploaded": sorted(Path(path).name for path in upload),
                      "download": str(download), "branch": made["branch"], "tip": tip, "exit_test": passed,
                      "finished": time.strftime("%Y-%m-%dT%H:%M:%S%z")})
    say(f"publish: {slug} {tag} serves this host's eight archives with the branch's pins, read back into {download}")
    say(publish_next(plan, made))
    return 0


def publish_next(plan: Plan, made: dict) -> str:
    return (f"next (design step 18): in a main checkout, git fetch {made['repo']} "
            f"refs/heads/{made['branch']}:refs/heads/{made['branch']}, merge it, add the STATUS and OPEN_ISSUES "
            "edits, run python3 scripts/land_gate.py plan and run, then git push origin HEAD:main")


# ---------------------------------------------------------------------------
# status: files only


def role_status(plan: Plan, stem: str) -> tuple[str, str]:
    """(state, words) of a role from the files it leaves: done, not-clean, unfinished or absent."""
    if plan.record(stem).is_file():
        record = read_json(plan.record(stem), "a build record")
        words = f"clean as {record.get('label')}, {(record.get('run') or {}).get('elapsed_s')} s"
        found = record.get("comparison")
        if found is not None:
            words += ("; the producer's tree, entry for entry" if found["identical"] else
                      f"; differs from the producer's in {len(found['differing'])} entr"
                      f"{'y' if len(found['differing']) == 1 else 'ies'}"
                      + (f", {len(found['outside_allowed'])} of them outside {' and '.join(UNREPRODUCED_ALLOWED)}: STOP"
                         if found["outside_allowed"] else f" ({', '.join(found['differing'])})"))
        return "done", words
    used = labels_used(plan, f"{stem}-build")
    if not used:
        return "absent", "not started"
    last = used[-1]
    if plan.not_clean(last).is_file():
        problems = read_json(plan.not_clean(last), "a not-clean record").get("problems") or []
        return "not-clean", f"{last} ended NOT clean ({'; '.join(problems)[:300]}); `--again` starts it anew"
    if plan.file(last, "run.json").is_file():
        return "unfinished", f"{last}: x.py ended and left its record; the same command resumes at the measurements"
    return "unfinished", f"{last} was started and has left no record yet (running, or interrupted)"


def status_lines(plan: Plan) -> list[str]:
    out = [f"root {plan.root}: {plan.commit[:10]} on {plan.host}"]
    if not plan.root.is_dir():
        return out + ["  setup        not started (the root does not exist)",
                      f"next: {shlex.join(command_line(plan, 'setup'))}"]
    if not plan.inputs_file().is_file():
        have = [name for name, path in (("checkout", plan.src), ("base config", plan.inputs / "seed-config.json"),
                                        ("ninja", plan.tools / "ninja"),
                                        ("Lean manifest", plan.inputs / "clean-lean-inputs.json"),
                                        ("cargo home", plan.ledger / "cargo-home")) if path.exists()]
        return out + [f"  setup        unfinished (there: {', '.join(have) or 'nothing'})",
                      f"next: {shlex.join(command_line(plan, 'setup'))}   # with the arguments of "
                      f"{plan.inputs / 'sources.json'}"]
    inputs = read_json(plan.inputs_file(), "the setup record")
    out.append(f"  setup        done: jobs {inputs.get('jobs')}, {inputs.get('linker')} linker, base config "
               f"{str((inputs.get('base_config') or {}).get('sha256'))[:16]}")
    if not isinstance(inputs.get("jobserver"), dict):
        out.append("  jobserver    none recorded: this root was set up before every x.py run was given a FIFO "
                   "jobserver, and no build or dist starts in it; set up a new --root")
    lines = trap_lines(plan.ledger)
    if lines:
        out.append(f"  trap log     {len(lines)} line(s): no build starts and no record can be written from this root")
    state = {stem: role_status(plan, stem) for stem in ("p", "f", "s")}
    out.append(f"  producer     {state['p'][1]}")
    if plan.dist_record().is_file():
        was = read_json(plan.dist_record(), "the dist record")
        dist_state = "done"
        out.append(f"  dist         done: {len(was.get('archives') or [])} files, "
                   f"{was.get('archive_bytes_total')} bytes")
    elif (plan.kept / "dist.not-clean.json").is_file():
        dist_state = "not-clean"
        problems = read_json(plan.kept / "dist.not-clean.json", "the dist record").get("problems") or []
        out.append(f"  dist         ran and is NOT usable ({'; '.join(problems)[:300]})")
    else:
        used = [label for base in DIST_LABELS for label in labels_used(plan, base)]
        dist_state = "unfinished" if used else "absent"
        out.append("  dist         " + (f"unfinished (x.py runs so far: {', '.join(used)})" if used else "not started"))
    seed = plan.prepare_record().is_file()
    if seed:
        prepared = read_json(plan.prepare_record(), "the prepare record")
        rows = (prepared.get("prepared") or {}).get("rows") or {}
        out.append(f"  prepare      done: the parent's {rows.get('kept')} rows kept, {len(rows.get('added') or [])} "
                   f"added; {(prepared.get('members') or {}).get('counts', {}).get('same')} archive files are the "
                   f"producer's rows ({plan.prepare_record()})")
        out.append(f"  seed         there ({plan.seed}, {prepared['seed']['tree']['entries']} entries, the pinned "
                   "archives as installed)")
    else:
        there = [name for name, path in (("admit-dist", plan.prepare_dir() / "admit-dist"),
                                         ("prepared", plan.prepared()),
                                         ("admit-pinned", plan.prepare_dir() / "admit-pinned"),
                                         ("seed", plan.prepare_dir() / "installed.json"),
                                         ("surface", plan.prepare_dir() / "seed-surface.json")) if path.exists()]
        out.append("  prepare      " + (f"unfinished (there: {', '.join(there)}); the same command resumes"
                                        if there or plan.prepare_dir().exists() else "not started"))
        out.append(f"  seed         absent ({plan.seed}); made by `prepare`"
                   + (" (a seed there without the prepare record is not used)" if plan.seed.exists() else ""))
    out.append(f"  fixed-point  {state['f'][1]}")
    out.append(f"  cross-check  {state['s'][1]}")
    following: list[str] = []
    control = None
    if state["p"][0] == "done" and state["f"][0] == "done":
        control = control_state(plan)
        if control["outside"]:
            out.append(f"  control      none can help: {len(control['outside'])} entr"
                       f"{'y' if len(control['outside']) == 1 else 'ies'} differ outside the two allowed files")
        elif control["absent"]:
            out.append(f"  control      none can help: {', '.join(control['absent'])} is missing from a build's tree")
        elif not control["decided"] and not control["undecided"]:
            out.append("  control      none needed: the fixed-point tree is the producer's")
        else:
            out.append(f"  control      {control['controls']} of at most {CONTROL_LIMIT} built; "
                       + "; ".join([f"{path}: {how}" for path, how in sorted(control["decided"].items())]
                                   + [f"{path}: undecided" for path in control["undecided"]]))
    else:
        out.append("  control      not known yet (it depends on the fixed-point build)")
    again = lambda key: ["--again"] if state[key][0] == "not-clean" else []  # noqa: E731
    if state["p"][0] != "done":
        following.append(shlex.join(command_line(plan, "build", "--role", "producer", *again("p"))))
    elif dist_state != "done":
        following.append(shlex.join(command_line(plan, "dist")))
    else:
        if state["f"][0] != "done":
            following.append(shlex.join(command_line(plan, "build", "--role", "fixed-point", *again("f"))) if seed
                             else shlex.join(command_line(plan, "prepare")))
        if state["s"][0] != "done":
            following.append(shlex.join(command_line(plan, "build", "--role", "cross-check", *again("s"))))
        if control is not None and control["undecided"] and not control["outside"] and not control["absent"] \
                and control["controls"] < CONTROL_LIMIT:
            following.append(shlex.join(command_line(plan, "build", "--role", "control")))
    if record_record(plan).is_file():
        was = read_json(record_record(plan), "the record step's record")
        out.append(f"  record       written: {host_proofs(plan)} (receipt sha256 "
                   f"{str(was.get('receipt_sha256'))[:16]}, {was.get('controls')} control(s), not reproduced "
                   f"{was.get('not_reproduced')})")
    elif (plan.root / "record" / "staging").exists():
        out.append("  record       refused by its validator; what it proposed is kept in "
                   f"{plan.root / 'record' / 'staging'}")
    else:
        out.append("  record       not written")
    made = read_json(commit_record(plan), "the commit step's record") if commit_record(plan).is_file() else None
    out.append(f"  commit       made: {made['branch']} in {made['repo']} at {made['commits'][-1][:10]} (nothing pushed)"
               if made else "  commit       not made")
    published = plan.kept / "publish.json"
    out.append(f"  publish      done: {read_json(published, 'the publish record').get('tag')}, read back"
               if published.is_file() else "  publish      not done")
    if not following:
        stopped = any("STOP" in state[stem][1] for stem in ("f", "s")) or bool(control and (
            control["outside"] or control["absent"]
            or (control["undecided"] and control["controls"] >= CONTROL_LIMIT)))
        if stopped:
            following.append("nothing: the stop rule holds, and no record is written from these builds")
        elif published.is_file() and made:
            following.append(publish_next(plan, made).removeprefix("next (design step 18): "))
        elif made:
            following.append(commit_next(plan, made).removeprefix("next (design step 15): ")
                             + "; then, in that clone, verify --rebuild --produced <this root, moved aside> --work <W> "
                             f"(design step 16); then {shlex.join(command_line(plan, 'publish'))} --exit-test <W>")
        elif record_record(plan).is_file():
            following.append(shlex.join(command_line(plan, "commit")) + " --parent <the parent, e.g. origin/main> "
                             f"--branch seed/linux-first-{plan.commit[:10]} --identity 'Name <email>' "
                             "--darwin-pack-state published|not-published")
        else:
            following.append(shlex.join(command_line(plan, "record")))
    return out + [f"next: {line}" for line in following]


# ---------------------------------------------------------------------------
# plan: every command, nothing run


def pinned_lean_directory(repo: Path, commit: str) -> str | None:
    """The Lean directory the commit's Clean pin names, read from the repository
    and its module store without a checkout; None when it cannot be read."""
    try:
        entry = refresh.git(repo, "ls-tree", commit, "first-party/clean").split()
        store = Path(refresh.git(repo, "rev-parse", "--absolute-git-dir")) / "modules" / "first-party" / "clean"
        pin = subprocess.run(["git", "--git-dir", str(store), "show", f"{entry[2]}:lean-toolchain"],
                             capture_output=True, text=True)
        return lean_directory(pin.stdout.strip()) if pin.returncode == 0 else None
    except (Refusal, IndexError):
        return None


def plan_lines(plan: Plan) -> list[str]:
    args, root, host = plan.args, plan.root, plan.host
    directory = pinned_lean_directory(args.repo, plan.commit)
    lean = plan.inputs / "lean" / (directory or "<the directory the Clean pin names>")
    plan.lean_library = lean / "lib" / "lean"
    lean_source = args.lean_toolchain or (default_lean(plan, directory) if directory
                                          else "<the installed Lean toolchain>")
    environment = " ".join(f"{key}={shlex.quote(value)}" for key, value in plan.env().items())
    tail = f"jobs = {args.jobs}" + (', [rust] bootstrap-override-lld = "self-contained"' if args.lld else "")

    def me(*words: str) -> str:
        return shlex.join(command_line(plan, *words))

    def role_lines(role: str, label: str, source: str, stem: str) -> list[str]:
        admission = plan.file(label, "admission.json")
        lines = [f"# == {role} ==   "
                 + me("build", "--role", role, *(("--stage0", source) if role in ("producer", "cross-check") else ()))]
        if role != "producer":
            lines.append(f"mv {plan.build_dir()} {plan.kept}/<the label of the tree in it>-tree")
        lines.append(f"cp -a {source} {plan.stage0}   # an earlier role's copy is first kept as {root}/stage0.<label>")
        if role != "producer":
            lines.append(f"mkdir -p {plan.build_dir() / host} && cp -a {plan.kept / 'p-build-tree' / host}/{{"
                         + ",".join(refresh.NATIVE_OUTPUTS) + f"}} {plan.build_dir() / host}/")
        lines += [
            f"$E {shlex.join(plan.admit())} > {admission}",
            f"$E {shlex.join(plan.config(plan.rung_config()))}   # then: {tail}; written once, and compared "
            "byte for byte by every later role",
            f"(cd {plan.src} && $E {shlex.join(plan.closure())}) > {plan.file(label, 'closure.log')} 2>&1",
            f"$E {shlex.join(plan.run(label, BUILD_LINE, admission))} > {plan.file(label, 'run.json')} "
            f"2> {plan.file(label, 'run.stderr')}",
            f"$E {shlex.join(plan.manifest(plan.stage2(), plan.manifest_path(stem)))}"]
        return lines

    out = [f"# The build half of a first Linux seed: {plan.commit[:10]} on {host}, in {root}",
           "# Every step runs with umask 022 and exactly this environment (the driver replaces its own):",
           "umask 022",
           f"E={shlex.quote('env -i ' + environment)}",
           "# Before every build the driver measures what the roles share and refuses a difference; after it,",
           f"# the native outputs, the trap log, the checkout and the cargo home again ({plan.kept}).",
           "#",
           f"# == setup ==   {me('setup')}",
           f"mkdir -p {plan.home} {plan.tools} {plan.inputs} {plan.ledger / 'tmp'} {plan.kept}",
           f"clone {args.repo} at {plan.commit[:10]} into {plan.src}, submodules from its module store",
           f"$E {shlex.join(plan.seed_config())} > {plan.inputs / 'seed-config.json'}",
           f"cp -L {args.ninja} {plan.tools / 'ninja'} && chmod 755 {plan.tools / 'ninja'}",
           f"cp -a {lean_source} {lean}",
           f"$E {shlex.join(plan.lean_inputs(plan.inputs / 'clean-lean-inputs.json'))}",
           "$E " + shlex.join(plan.cargo_home_inputs(args.cargo_home, plan.ledger / "cargo-home",
                                                     plan.inputs / "cargo-home-inputs.json")),
           f"write the trap shims into {plan.ledger / 'trap'}; record cc, c++, ld, cmake, make, python, the host "
           f"tools the base config names, jobs = {args.jobs}, the {'self-contained' if args.lld else 'system'} "
           f"linker and the FIFO jobserver every run is given (MAKEFLAGS={plan.jobserver(args.jobs)['makeflags']!r}, "
           f"and make through {plan.jobserver(args.jobs)['make_adapter']}) in {plan.inputs_file()}",
           "#"]
    out += role_lines("producer", "p-build", str(args.producer_stage0), "p")
    words = dist_words(["$COMPONENTS"])
    packaged = plan.build_dir() / "dist"
    out += ["#", f"# == dist ==   {me('dist')}   (in the producer's tree, by the producer's stage0)",
            f"COMPONENTS=$($E {shlex.join(plan.dist_components())})"]
    for label in DIST_LABELS:
        # The component list is the shell's word here, not one quoted argument.
        run = shlex.join(plan.run(label, words[label], plan.file("p-build", "admission.json")))
        out.append(f"$E {run.replace(shlex.quote('$COMPONENTS'), '$COMPONENTS')}"
                   f" > {plan.file(label, 'run.json')} 2> {plan.file(label, 'run.stderr')}")
    out += [f"TOOL=$($E {shlex.join(plan.manifest_tool())})",
            f"$E \"$TOOL\" {packaged} {packaged} $(git -C {plan.src} log -1 --date=short --pretty=format:%cd) "
            f"{DIST_SERVER} {CHANNEL} > {plan.ledger / 'p-channel-manifest.log'} 2>&1",
            f"$E {shlex.join(plan.stage2_unchanged())}",
            f"cp -a {packaged} {plan.dist}   # refused before this when an archive is over "
            f"{args.asset_limit_bytes} bytes",
            "#", f"# == prepare ==   {me('prepare')}"]
    work, output = plan.prepare_dir(), plan.output_root()
    out += [f"git -C {HERE.parent} show <--parent, default HEAD>:src/stage0   # it must pin {plan.commit[:10]} and "
            f"not {host}; and its channel manifest, by the hash it pins",
            f"sha256 every archive the parent pins, in {COHORT_DIR} (read as data, never unpacked)",
            f"$E {shlex.join(plan.stage_artifacts(plan.dist, work / 'admit-dist', '<version>'))}",
            f"$E {shlex.join(plan.handoff(work / 'admit-dist' / 'seed-inputs.json', work / 'admit-dist', output))}",
            f"copy the parent's channel manifest and pinned archives into {output}/dist",
            f"$E {shlex.join(plan.prepare_py(plan.dist, output, plan.prepared() / 'src-stage0', '<date>', '<server>'))}",
            f"check the candidate (the parent's src/stage0 head + {plan.prepared()}/src-stage0): every parent row "
            f"unchanged, {host}'s eight rows added, one new manifest hash, nothing else in {output}",
            f"$E {shlex.join(plan.stage_artifacts(output / 'dist' / '<date>', work / 'admit-pinned', '<version>'))}",
            f"<each of the five admitted pinned archives>/install.sh --prefix={plan.seed} --disable-ldconfig",
            f"$E {shlex.join(plan.validate_seed('<version>', work / 'seed-surface.json'))}",
            f"$E {shlex.join(plan.carried())}",
            f"write {work / 'archive-members.json'} (each pinned {host} archive's installed bin/, lib/, libexec/ "
            f"files joined to {plan.manifest_path('p')}), check every file of {plan.seed} against the pinned "
            f"members, then {plan.prepare_record()}", "#"]
    out += role_lines("fixed-point", "f-build", str(plan.seed), "f")
    out.append("#")
    out += role_lines("cross-check", "s-build", str(args.cross_check_stage0), "s")
    out += ["#", f"# == control ==   {me('build', '--role', 'control')}",
            f"# Only when f-build differs from p-build in {' or '.join(UNREPRODUCED_ALLOWED)} and nowhere else; at "
            f"most {CONTROL_LIMIT} (c1-build .. c{CONTROL_LIMIT}-build), each the fixed-point commands under its "
            "own label.",
            "#", "# linker: " + ("rust.bootstrap-override-lld = \"self-contained\" for every role (--lld)" if args.lld
                                 else "the system linker for every role (the rung config has no lld key)")]
    for role, source in (("producer", args.producer_stage0), ("cross-check", args.cross_check_stage0),
                         ("fixed-point", plan.seed)):
        ships = all(path.is_file() for path in refresh.self_contained_lld(Path(source), host))
        there = (Path(source) / "bin" / "trustc").is_file()
        out.append(f"#   {role} stage0 {source}: " + ("not there yet" if not there else
                   "ships its own rust-lld" if ships else "ships no rust-lld, so it cannot build with --lld"))
    cargo_home = plan.ledger / "cargo-home"
    out.append(f"# clean fact store: {fact_store_words(fact_store_state(cargo_home), cargo_home)}")
    named = names_account(str(root), plan.account)
    if named:
        out.append(f"# NOTE: the root, {root}, names the invoking account ({named}); `build` and `dist` refuse that "
                   "before they start (every record names the root)")
    named = names_account(str(plan.driver), plan.account)
    if named:
        out.append(f"# NOTE: this script's directory, {plan.driver}, names the invoking account ({named}); the run "
                   "records name it (`tool.path`), and every build record lists where the account is named")
    if root.exists():
        out.append(f"# NOTE: {root} exists; `status` says what is done in it")
    return out


# ---------------------------------------------------------------------------
# the command line


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--root", type=Path,
                        help=f"the neutral root; nothing is written outside it (default {ROOT_PARENT}/<commit, "
                             "ten digits>)")
    common.add_argument("--commit", default=COMMIT, help="the commit to build, all 40 digits (default: the "
                                                         "compiler commit of the 2026-11-07 pin)")
    common.add_argument("--host", help=argparse.SUPPRESS)
    sources = argparse.ArgumentParser(add_help=False)
    sources.add_argument("--repo", type=Path,
                         help="the checkout to clone from; its module store supplies the submodules (default: "
                              "the main worktree of this script's checkout)")
    sources.add_argument("--cargo-home", type=Path, default=Path(CARGO_HOME_SOURCE),
                         help="a cargo home a build of this commit filled; its registry/index, registry/cache "
                              f"and git/db are copied (default {CARGO_HOME_SOURCE})")
    sources.add_argument("--ninja", type=Path, default=Path(NINJA_SOURCE),
                         help=f"the ninja to copy into the tool directory (default {NINJA_SOURCE})")
    sources.add_argument("--lean-toolchain", type=Path,
                         help="the installed Lean toolchain the commit's Clean pin names (default: "
                              "${ELAN_HOME:-~/.elan}/toolchains/<the pin's directory>)")
    sources.add_argument("--jobs", type=int, default=os.cpu_count() or 1,
                         help="the job count of every build (default: this host's CPUs)")
    sources.add_argument("--lld", action="store_true",
                         help="link every role's Rust code with its stage0's own rust-lld instead of the system "
                              "linker; a role whose stage0 ships none is then refused")
    limit = argparse.ArgumentParser(add_help=False)
    limit.add_argument("--asset-limit-bytes", type=int, default=ASSET_LIMIT_BYTES,
                       help="dist stops when an archive is larger (default 2 GiB, a release's per-asset limit)")
    again = argparse.ArgumentParser(add_help=False)
    again.add_argument("--again", action="store_true",
                       help="start anew, under the next label, a build that ended and was not clean")
    sub = result.add_subparsers(dest="command", required=True,
                                metavar="{plan,setup,build,dist,prepare,record,commit,verify,publish,status}")
    planned = sub.add_parser("plan", parents=[common, sources, limit],
                             help="print every command of setup, the builds and dist; run nothing")
    planned.add_argument("--producer-stage0", type=Path, default=Path(PRODUCER_STAGE0))
    planned.add_argument("--cross-check-stage0", type=Path, default=None)
    sub.add_parser("setup", parents=[common, sources], help="make the root and bind every non-Rust input")
    built = sub.add_parser("build", parents=[common, again], help="one build of the commit")
    built.add_argument("--role", choices=ROLES, required=True)
    built.add_argument("--stage0", type=Path,
                       help=f"the compiler to copy to <root>/stage0 (producer: default {PRODUCER_STAGE0}; "
                            f"cross-check: default {CROSS_CHECK_STAGE0}; the other roles build from <root>/seed)")
    sub.add_parser("dist", parents=[common, limit, again],
                   help="the dist archives and channel manifest from the producer's tree")
    prepared = sub.add_parser("prepare", parents=[common],
                              help="join this host's archives to the parent's pin and install them into <root>/seed")
    prepared.add_argument("--parent", default="HEAD",
                          help="the commit of this script's checkout whose src/stage0 the seed joins (default HEAD)")
    prepared.add_argument("--cohort", type=Path, default=COHORT_DIR,
                          help=f"where the parent's pinned archives are, each checked by its pin (default {COHORT_DIR})")
    prepared.add_argument("--archive-jobs", type=int, default=ARCHIVE_JOBS,
                          help=f"archives prepare.py repacks at once (default {ARCHIVE_JOBS})")
    recorded = sub.add_parser("record", parents=[common],
                              help="write the host record and its evidence under prepared/, and validate it")
    recorded.add_argument("--chain", type=Path, default=Path(CHAIN_RECORD),
                          help=f"the host chain's unpinned-root record (default {CHAIN_RECORD})")
    recorded.add_argument("--origin-provenance", type=Path, action="append", default=None,
                          help="a PROVENANCE whose build stamps say how the chain's root and its builder were built; "
                               f"repeatable (default: {' and '.join(ORIGIN_PROVENANCE)})")
    recorded.add_argument("--origin-config", type=Path, default=Path(ORIGIN_CONFIG),
                          help=f"the config whose line names the root's builder (default {ORIGIN_CONFIG})")
    committed = sub.add_parser("commit", parents=[common],
                               help="build the add-host branch in a new clone under the root; push nothing")
    committed.add_argument("--parent", required=True,
                           help="the commit of this script's checkout the branch starts from: the one prepare "
                                "joined, or a descendant with the same src/stage0 and bootstrap/trust-stage0")
    committed.add_argument("--branch", required=True, help="the branch to create (create-only)")
    committed.add_argument("--identity", required=True, help="the author and committer, 'Name <email>'")
    committed.add_argument("--darwin-pack-state", required=True, choices=DARWIN_PACK_STATES,
                           help="whether the Darwin pack of the commit is published (the message states the "
                                "consequence)")
    verified = sub.add_parser("verify", parents=[common],
                              help="judge a clone of the add-host branch with its 17 archives placed")
    verified.add_argument("--repo", type=Path,
                          help="the clone of the branch (default: this script's checkout)")
    verified.add_argument("--rev", default="HEAD", help="the commit judged; it must be the clone's HEAD")
    verified.add_argument("--rebuild", action="store_true",
                          help="the exit test: leg 1 builds the clone's source from the pinned seed, leg 2 rebuilds "
                               "the commit at the recorded root and compares it with the receipt (hours)")
    verified.add_argument("--produced", type=Path,
                          help="the produced root, moved aside from the recorded build_root (--rebuild)")
    verified.add_argument("--work", type=Path, help="where --rebuild keeps leg 1's ledger and both legs' records")
    verified.add_argument("--lean-library", type=Path,
                          help="the Lean library the clone's Clean pin names, for leg 1 (--rebuild)")
    verified.add_argument("--ninja", type=Path, default=Path(NINJA_SOURCE),
                          help=f"the ninja leg 1's LLVM build runs (default {NINJA_SOURCE})")
    verified.add_argument("--jobs", type=int, default=SEED_BUILD_JOBS,
                          help=f"leg 1's job count (default {SEED_BUILD_JOBS})")
    published = sub.add_parser("publish", parents=[common],
                               help="upload this host's eight archives to the pin's release and read them back")
    published.add_argument("--agh", type=Path, help="the agh executable (default: agh on the invoker's PATH)")
    published.add_argument("--exit-test", type=Path,
                           help="the --work of the `verify --rebuild` that passed on a clone of the branch tip; "
                                "publish uploads only the archives that exit test passed with")
    sub.add_parser("status", parents=[common], help="what is done and what is next, from the files under the root")
    # EXTENSION POINT (see the top of this file): scout is added here when it exists.
    # It is not stubbed.
    return result


def default_repo() -> Path:
    """The main worktree of this script's checkout: a linked worktree has no module
    store of its own, and the clone takes every submodule from one."""
    done = subprocess.run(["git", "-C", str(HERE), "rev-parse", "--path-format=absolute", "--git-common-dir"],
                          capture_output=True, text=True)
    common = Path(done.stdout.strip()) if done.returncode == 0 and done.stdout.strip() else None
    return common.parent if common is not None and common.name == ".git" else HERE.parent


def absolute(path: Path) -> Path:
    return Path(os.path.abspath(os.path.expanduser(str(path))))


def resolve(args: argparse.Namespace, host: str) -> None:
    """Defaults and `~`, from the invoker's environment, before it is replaced."""
    if not re.fullmatch(r"[0-9a-f]{40}", args.commit):
        raise Refusal(f"--commit {args.commit} is not a commit id of 40 hexadecimal digits")
    args.root = absolute(args.root) if args.root else ROOT_PARENT / args.commit[:10]
    real = Path(os.path.realpath(args.root))
    if real != args.root:
        raise Refusal(f"--root {args.root} is reached through a symbolic link: it is {real}. The staircase records "
                      "resolved paths and they are compared with the root as given, so every build under it would "
                      f"end not clean. Nothing was written. Give --root {real}")
    if args.command in ("plan", "setup") and jobs_problem(args.jobs):
        raise Refusal(jobs_problem(args.jobs))
    if getattr(args, "repo", None) is None and args.command in ("plan", "setup"):
        args.repo = default_repo()
    if args.command in ("plan", "setup"):
        args.elan_home = Path(os.environ.get("ELAN_HOME") or "~/.elan")
    if args.command == "prepare" and args.archive_jobs < 1:
        raise Refusal(f"--archive-jobs is {args.archive_jobs}, and prepare.py repacks at least one archive at a time. "
                      f"Nothing was started. Give --archive-jobs {ARCHIVE_JOBS} or another count of at least 1")
    if args.command == "record" and args.origin_provenance is None:
        args.origin_provenance = [Path(path) for path in ORIGIN_PROVENANCE]
    if args.command == "verify" and args.repo is None:
        args.repo = HERE.parent
    if args.command == "verify" and args.jobs < 1:
        raise Refusal(f"--jobs is {args.jobs}; leg 1 builds with at least 1")
    if args.command == "publish":
        # agh holds the release credential: it is found on, and run with, the invoker's PATH.
        found = args.agh or shutil.which("agh")
        if found is None or not (os.path.isfile(found) and os.access(found, os.X_OK)):
            raise Refusal(f"no agh executable ({found or 'none on PATH'}): publish uploads through agh. Nothing was "
                          "uploaded. Name it with --agh")
        args.agh = Path(found)
    for name in ("repo", "cargo_home", "ninja", "lean_toolchain", "elan_home", "producer_stage0", "stage0", "cohort",
                 "chain", "origin_config", "work", "produced", "lean_library", "agh", "exit_test"):
        if getattr(args, name, None) is not None:
            setattr(args, name, absolute(getattr(args, name)))
    if getattr(args, "origin_provenance", None) is not None:
        args.origin_provenance = [absolute(path) for path in args.origin_provenance]
    if args.command == "plan":
        args.cross_check_stage0 = absolute(args.cross_check_stage0 or Path(CROSS_CHECK_STAGE0.format(host=host)))
    if args.command == "build" and args.stage0 is None and args.role in ("producer", "cross-check"):
        args.stage0 = absolute(Path((PRODUCER_STAGE0 if args.role == "producer" else CROSS_CHECK_STAGE0)
                                    .format(host=host)))
    for checkout in filter(None, (HERE.parent, getattr(args, "repo", None))):
        if args.root == checkout or checkout in args.root.parents:
            raise Refusal(f"--root {args.root} is inside the checkout {checkout}. The root holds a clone, a "
                          "cargo home and builds, and belongs outside every checkout. Nothing was written")


def main(argv: list[str] | None = None) -> int:
    # Before anything is written, the root itself included (`adopt` sets it again).
    os.umask(0o022)
    args = parser().parse_args(argv)
    try:
        host = args.host or refresh.host_triple()
        resolve(args, host)
        plan = Plan(args, host, args.commit)
        if args.command == "plan":
            print("\n".join(plan_lines(plan)))
            return 0
        if args.command == "status":
            print("\n".join(status_lines(plan)))
            return 0
        if args.command == "verify":
            # The clone is judged, not the root: no root, no lock there, and nothing of the
            # invoker's environment but HOME (verify_env).
            os.environ.clear()
            os.environ.update(plan.verify_env())
            os.umask(0o022)
            return verify_step(plan)
        if args.command == "setup":
            plan.root.mkdir(parents=True, exist_ok=True)
        elif not plan.root.is_dir():
            require_setup(plan)
        adopt(plan)
        with locked(plan):
            if args.command == "setup":
                return setup(plan)
            if args.command == "build":
                return build(plan, args.role)
            if args.command == "prepare":
                return prepare_seed(plan)
            if args.command == "record":
                return record_step(plan)
            if args.command == "commit":
                return commit_step(plan)
            if args.command == "publish":
                return publish_step(plan)
            return dist(plan)
    except NotComparable as refusal:
        print(f"fixed-point-linux-seed: {refusal}", file=sys.stderr)
        return 3
    except Refusal as refusal:
        print(f"fixed-point-linux-seed: refused: {refusal}", file=sys.stderr)
        return 2
    except OSError as error:
        print(f"fixed-point-linux-seed: refused: the operating system refused a step: {error.strerror or error}"
              + (f": {error.filename}" if error.filename else "")
              + (f" -> {error.filename2}" if error.filename2 else "")
              + ". What was already written is kept; the same command line runs the step again once the "
              "cause is removed", file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print("fixed-point-linux-seed: interrupted. A step that was running left its files as they were; the "
              "same command line runs it again, and `status` says where things stand", file=sys.stderr)
        return 130


if __name__ == "__main__":
    sys.exit(main())
