#!/usr/bin/env python3
"""Trust: RUN the `crates/` tests that exist only under a non-default feature.

WHY THIS EXISTS. A test file that opens with `#![cfg(feature = "...")]`
compiles, in every lane that does not enable that feature, to a test binary
with NO tests in it. libtest prints `running 0 tests` and `test result: ok.`,
cargo exits 0, and the lane is green having run nothing. Counted 2026-10-09:
35 of trust-cg-bridge's 54 integration-test files are gated on a feature that
way (20 on `ay-proofs`, 10 on `test-hooks`, 3 on `kernel-recheck`, 2 on both
`ay-proofs` and `test-hooks`; a 36th is `#![cfg(target_arch = "aarch64")]`),
and 8 of trust-router's 22 are `#![cfg(feature = "ay-backend")]`. No lane
enabled those features for those files. Measured by this lane on 2026-10-09
(each file counted in the run where it runs the most), the 35 hold 350 tests
(352 with the aarch64 file) and trust-router's 8 hold 20 that check something,
plus the measurement driver `adjudicate_undischarged_vcs`, which is `#[ignore]`d
(it asserts nothing; ZERO_TEST_ALLOWED names its binary).
They ran only when somebody typed the command. The libs gate test modules the
same way. trust-cg-bridge's lib runs 766 tests with `kernel-recheck,test-hooks`
and 632 with `test-hooks`, and no other lane runs its gated modules.
trust-router's gated lib modules ALSO run in the scoped crates lane's two `--lib`
tails (scripts/check_crates_tests_scoped.py FEATURE_RUNS: `ay-backend`, and
`ay-certify,trust-build,trust-cg-backend,carcara-crosscheck`), but only for a
change that touches trust-router (or, in scripts/land_gate.py's crates-tests
leg, reaches it). That lane is not a push lane: since 39b35cb9f7 (2026-11-02)
the push profile has no crates lane, so no push runs a crates/ test. Neither
tail enables `trust-cg-output-gate`.
This lane's runs do not enable `carcara-crosscheck` (it links GMP through
`rug`), so that tail is still the only lane for trust-router's
`carcara-crosscheck` test modules.
(`slow.trust-cg-cer-gate` runs six trust-cg-bridge files with
`kernel-recheck,test-hooks`; this lane overlaps it on purpose and leaves it be.)
Outside those two crates two gated test targets had no lane until
2026-10-27: trust-vcgen's `tests/infoflow_leak.rs`
(`#![cfg(feature = "prototype-infoflow")]`, 4 tests; its run is narrowed,
below) and trust-spec-temporal's `model_prelude_patched` (a `[[test]]` with
`required-features = ["test-support"]`; that crate is its own workspace root,
so its run names the crate's own manifest, and it builds `--tests`, which also
reaches the item-level `test-support` tests in model_prelude_kernel.rs and
model_theorems.rs). Most of trust-spec-temporal's feature tests are
`#[cfg_attr(debug_assertions, ignore)]` (release-only, B1A-D42), and this lane
builds debug, so it runs only their debug subset (FGT-LANE-4).
trust-bmc's `tests/raw_postcondition_dispatch.rs` (`#![cfg(feature =
"trust-mc-native-trust-ir-bundle")]`) had no lane until 2026-11-06 (BMC-LANE-1).
Its lib's bundle-gated modules ALSO run in trust-bmc's `trust-build --lib` tail
(`trust-build` enables the same features). No push runs that tail: the pre-push
hook runs only the push profile, which has had no crates lane since 39b35cb9f7.
The tail runs in scripts/land_gate.py's crates-tests leg for any change that
reaches trust-bmc (a first-party pin move and a trust-ir-bridge change among
them), in the fast profile's `scoped.crates-tests` row when origin/main...HEAD
touches trust-bmc's own files, and by hand. Neither builds the integration file,
which only this lane runs.
trust-build-tree's `tests/fixed_run_public.rs` and `tests/fixed_test_graph_public.rs`
(`#![cfg(all(target_os = "macos", target_arch = "aarch64", feature =
"native-cli-tests", feature = "native-exec"))]`, added 2026-11-08) had no lane
until 2026-11-10 (FGT-LANE-5). They, and the lib's `native-cli-tests` tests,
execute this checkout's newly built Targo, Bootstrap and stage-1 compiler, so
that run takes them from build/ (BUILT INPUTS, below).

NARROWED RUNS. A run builds `--tests` unless its `targets` name fewer, which is
allowed only when the feature set changes nothing but the targets named:
trust-vcgen's `prototype-infoflow` adds only the lib's
`#[cfg(any(test, feature = "prototype-infoflow"))] pub mod infoflow`, which the
lib's own test build compiles anyway, and only `infoflow_leak` imports it, so
`--tests` would rebuild and re-run the default build's 200-odd binaries (the
scoped crates lane's) for nothing. The selftest holds the claim to the source,
failing closed (`narrowed_run_problems`): the run's features may reach no other
crate's feature or optional dependency, the crate may have no build script, its
src/ may `#[path]`-load only test-only helpers already scanned under tests/
and use no `include!`; no cfg
in src/ may flip under the features in the lib's unit-test build (`cfg(test)`
on) unless the run selects `--lib` (`--bins` for a bin's), nor in the lib the
other targets link (`cfg(test)` off) unless it gates a top-level `mod` that
nothing outside it names and whose code holds no impl block, static, extern,
macro_rules, asm, out-of-line nested mod, attribute, derive or macro outside
the short inert lists (`exempt_module_problems`); and no tests/ file a selected
target does not own (a shared helper module included) may name the features.

GATED-FILE COVERAGE. The selftest also reads each crates/*/ crate's test
targets as cargo picks them (tests/<name>.rs and tests/<name>/main.rs unless
`autotests = false`, each `[[test]]`, and each bin that holds a `#[test]`) and
fails while any target gated on a feature, by a leading `#![cfg(...)]` that
names one (comments skipped as rustc skips them, nested ones too) or by
`required-features`, compiles to its tests in no lane: it must hold under its
crate's default features (the scoped crates lane's `--tests`) or under a RUN here
that selects it, features expanded through the crate's [features] table. cfg
atoms other than `feature` are valued as on MEASURED_HOST (HOST_CFG_NAMES,
HOST_CFG_VALUES); one outside those tables fails closed. It also fails when a
RUN names a manifest other than the one its crate builds from (its own for a
crate that is its own workspace root), and when a crate with a RUN has no
`slow.feature-gated-tests-<crate>` harness row (its last_green field is free).
A gate on one function or module inside a file is not counted
(docs/VALIDATION_LADDER.md says why).

WHY NOT A PUSH LANE. Each wide run links 24-55 fresh test executables, and on
the macOS hosts this repo is pushed from syspolicyd assesses every new
executable on its first exec, one at a time and host-wide, before it may run. A
push cannot pay that (nor the narrowed trust-vcgen run's feature build of the
whole crate and its dependencies, in a target dir of its own), so this is a
SLOW lane (harness rows `slow.feature-gated-tests-*`). Its `--selftest`, which
builds nothing, is the row `fast.feature-gated-tests-selftest`, in the fast and
release profiles; 39b35cb9f7 (2026-11-02) took it out of the push profile, so no
push runs it either.

WHAT IT RUNS. For every configured RUN (crate, feature set) in RUNS:

  1. BUILD.  targo --unverified test --manifest-path Cargo.toml --locked
                   -p <crate> --features <set> --tests --no-run
                   --target-dir <this lane's target dir>
     (a NARROWED run passes its own targets in place of `--tests`, and a crate
     that is its own workspace root its own manifest)
                   --message-format=json-render-diagnostics
     Cargo's `compiler-artifact` messages name every test executable the run
     builds (`profile.test`, with an `executable`): that list, not a source
     scan, is the selection. `--tests` is the lib's unit tests, every bin's
     unit tests and every `tests/*.rs`; it is the right unit because the libs
     gate test MODULES on the same features (trust-cg-bridge's
     `object_replay` StrictProvenOnly fixtures are `kernel-recheck`-only,
     trust-router's `in_process_ay_backend` tests are `ay-backend`-only), and
     it costs one more link per run. Doctests are not run.
  2. RUN.    the same command with `--no-fail-fast` instead of `--no-run`, and
     cargo's own `target.<cfg>.runner` hook pointed at RUNNER (below). Cargo
     still decides HOW each binary runs (argv, working directory, environment:
     DYLD_FALLBACK_LIBRARY_PATH, CARGO, CARGO_MANIFEST_DIR, ...); RUNNER runs it
     with that, writes its output to a log of its own and records its exit
     status. So what each binary REPORTED is read from that binary's own log:
     no `Running ...` line is matched against interleaved output, and nothing
     depends on cargo's output order.
  3. JUDGE.  Each binary must have been built AND run exactly once, end with
     libtest's `test result:` line, agree with its exit status (0 = ok,
     101 = FAILED; anything else is a crash or a kill), and report at least
     one test RUN (passed + failed > 0). A binary that reports zero fails the
     lane unless ZERO_TEST_ALLOWED names it WITH A REASON; an allowlisted
     binary that does run a test fails it too ("delete the row"), and so do
     an allowlist row that names no binary the run built and one whose
     `covered_by` run (the same crate, other features) ran no test of that
     target in the same invocation. A test NO_OP_TESTS names (one that passes
     while checking nothing on this lane, with the reason) is run and shown
     but not counted: a binary whose every passing test is such a no-op is
     NO-OP, not PASS, and a row whose test the binary no longer runs fails
     ("delete or update the row"). The run fails when
     the build fails, when it selects no executable, when cargo exits non-zero
     with no failing binary to show for it, and when it builds fewer test
     binaries or runs fewer tests than its measured floor (RUNS: a target
     merged away, or a test module cfg'd out of a binary that still has other
     tests, which the zero-test rule cannot see). The floors are per RUN, not
     per binary, and equal the counts measured that day: deleting a test of
     either crate on purpose means lowering its run's floor here, in the same
     commit, and a module lost from one binary while tests are added to
     another of the same run is not seen.

Each binary runs under a wall limit (--binary-limit, default
DEFAULT_BINARY_LIMIT_S); a binary past it is killed with its process group and
fails. Output: a per-binary table per run, the failures' libtest `failures:`
sections, and one final verdict line beginning PASS:, FAIL: or NOT JUDGED:.

ONE HOST. The floors, ZERO_TEST_ALLOWED and NO_OP_TESTS were measured on
MEASURED_HOST (aarch64-apple-darwin). Other hosts compile a different test set:
trust-cg-bridge's `lean_isa_machine_sem_differential` is
`#![cfg(target_arch = "aarch64")]`, its lib and `emit_object_macho` have
Apple-aarch64-only tests, and several of its files return early with "SKIP
native execution" off aarch64-apple-darwin. On another host the lane still
builds, runs and judges every binary, and a failure or crash is still red, but
a broken floor or a zero-test binary is NOT JUDGED (exit 2, never green): no
floor was measured there. Measure that host's and key them by host before
relying on the rows there.

ITS OWN TARGET DIR. Builds default to crates/target-feature-gated-build.noindex
(TARGET_DIR_REL; git-ignored; `.noindex` keeps Spotlight out). `--target-dir`
selects another dedicated target and passes that choice unchanged to the native
owner, including its refusals. Either way cargo gets it as `--target-dir`, and
the ambient target variables are removed from its environment (BUILT INPUTS):
they neither replace this lane's isolation nor reach a test binary. A target overlapping the log directory is rejected before
either directory is created. Not
crates/target, not a shared cache: another lane building at the same time
never waits on this lane's cargo lock or has its artifacts relinked under it,
and a cold first run here costs this lane alone. Builds are non-incremental
(CARGO_INCREMENTAL=0): with incremental caches the four runs' target dir
measured 71G, 30G of it caches. So the native incremental reclaimer, whose
`crates/target*` glob covers this dir, finds nothing to reclaim here, and
nothing else reclaims it: measured 43G after a cold run of all four runs on
2026-10-09, kept per checkout. `rm -rf crates/target-feature-gated-build.noindex`
from the checkout root reclaims all of it; the next run then builds cold (about
7-8 minutes of builds per crate on that day). Like crates/target.noindex, it
sits under crates/, so a source walker that prunes only a directory named
exactly `target` walks it (trust-bmc's verifier_api root-source test,
trust-cg-bridge's compiler_consumer_census,
scripts/check_audited_trust_spec_sources.py). trust-bmc's walker panics on a
directory that vanishes mid-walk, which a build here, or in
crates/target.noindex, can cause if it runs at the same time.

Logs live separately in crates/target-feature-gated-logs.noindex. Writing or
pruning them never creates the compiler target: its native registrar must be
the first creator. Old crates/target-feature-gated.noindex output is left
untouched, never adopted or moved; an explicitly selected unmanaged target
still refuses before a build.

THE NATIVE BUILD LOCK (`targo trust repo lock`). It guards `build/`, which no
crates/ build writes (docs/VALIDATION_LADDER.md audits the crates lane's build
phase: build/ - nothing), and no crates-test row takes it. So the BUILD phase
takes no lock. The RUN phase of trust-router does read `build/`: its
real-solver tests (`tests/nonlinear_relaxation.rs`, `incremental_ay`'s unit
tests) take their `ay` from this checkout's `build/host/stage2` (else stage1)
`trustc` (trust_router::ay_discovery), which an `x.py build` deletes at its
start. That is a MEASUREMENT of the build tree in the lock's own terms, so a
RUN whose `reads_build_tree` is set holds `acquire --kind measurement` while
its binaries run (waiting up to --lock-wait seconds for a build to finish)
and releases it after; refused, the lane exits 2, NOT JUDGED. trust-cg-bridge's
tests read nothing under build/ and run unlocked. While it is held, an x.py
build in the same checkout (a push's scoped.compiler-check too) is refused or
waits: the choice and its cost are FGT-LANE-1 in docs/DECISION_QUEUE.md, and
what the lane may exempt (ZERO_TEST_ALLOWED, NO_OP_TESTS, ONE HOST) is
FGT-LANE-2.

BUILT INPUTS (FGT-LANE-5). A RUN may name built executables its tests
execute (`inputs`). trust-build-tree's `native-cli-tests` qualification runs
this checkout's own newly built Targo (its `resource fixed` and `trust repo
lock` front doors), its Bootstrap, and a stage-1 compiler for the crates the
tests make; no build of the crate itself provides those, and its tests fail,
rather than skip, without them. The lane takes each from this checkout's
build tree, never from PATH or the caller's environment (an ambient value is
replaced), and only once it holds the build lock, so no x.py build can replace
one between the hash and the last test: a run with inputs reads build/ and
sets reads_build_tree. The path passed is the file's real path (a held image
refuses a symlink), and with `sha256_env` set its SHA-256 goes with it, which
a test that holds the image checks. An input that is not an executable file
is NOT JUDGED (exit 2): the RUN phase never starts, so nothing is skipped and
nothing is green. Each `scratch` variable names a fresh directory OUTSIDE the
checkout, because cargo reads every `.cargo/config.toml` above a crate's
directory and this checkout's sets `[build] target-dir = "crates/target"`: a
crate a test made inside the checkout would build into the shared developer
cache. The directories are kept (those tests keep their worlds as evidence),
and the lane prints where. The lane's own target dir is an argument
(`--target-dir`), and cargo gets no CARGO_TARGET_DIR or TARGO_TARGET_DIR, the
caller's included: every test binary inherits cargo's environment, and those
tests refuse a target variable they did not set, which would redirect the
build they qualify.

Usage:
  feature_gated_tests.py [--crate NAME]... [--target-dir PATH] [--binary-limit S] [--lock-wait S]
  feature_gated_tests.py --list [--crate NAME]...   # the runs; build nothing
  feature_gated_tests.py --selftest                 # canned outputs; build nothing

Exit codes:
  0  every selected run built, every binary ran tests (or is allowlisted with
     a reason, or runs only NO_OP_TESTS) and passed, and every floor held
  1  a red: a test failed or crashed, a build failed, a zero-test binary
     outside the allowlist, a stale allowlist or no-op row, a floor broken, an
     empty selection (a red outranks a NOT JUDGED finding in another run)
  2  NOT JUDGED: no real targo, the build lock refused, a record cargo's
     runner could not make faithfully, a floor or zero-test finding on a host
     other than MEASURED_HOST, or a usage error
  128+N  interrupted by signal N (forwarded to the cargo and test processes)

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Dict, List, NamedTuple, Optional, Sequence, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
CRATES_MANIFEST = "Cargo.toml"
TARGET_DIR_REL = "crates/target-feature-gated-build.noindex"
LOG_DIR_REL = "crates/target-feature-gated-logs.noindex"
DEFAULT_BINARY_LIMIT_S = 3600
DEFAULT_LOCK_WAIT_S = 3600
KEEP_LOG_RUNS = 5
# The host the floors, ZERO_TEST_ALLOWED and NO_OP_TESTS were measured on (ONE HOST).
MEASURED_HOST = "aarch64-apple-darwin"
# What rustc_mir_transform links trust-router with (compiler/rustc_mir_transform/Cargo.toml).
SHIPPED_ROUTER = "ay-backend,ay-certify,trust-build,trust-cg-output-gate,trust-vc-native"
# The variables that select a target dir. The lane passes its own as `--target-dir`
# and gives cargo none of these, so a test binary inherits no target choice
# (BUILT INPUTS in the header).
TARGET_DIR_VARS = ("CARGO_TARGET_DIR", "TARGO_TARGET_DIR")


class Input(NamedTuple):
    """A built executable a RUN's tests execute, taken from this checkout's build
    tree (BUILT INPUTS in the header). `path` is relative to the checkout, with
    `{host}` this host's triple; `env` is the variable the tests read it from.
    With `sha256_env` set the lane also passes the file's SHA-256 there, which a
    test that holds the image compares with what it opened."""

    env: str
    path: str
    sha256_env: Optional[str] = None


class Run(NamedTuple):
    """One (crate, feature set) the lane builds and runs with `--tests` (or the
    narrower `targets`, NARROWED RUNS)."""

    crate: str
    features: str
    # Floors MEASURED on this host (see the dated note at each row). A run that
    # builds fewer test binaries, or runs fewer tests, fails: lower a floor only
    # in the commit that removes the targets or tests, saying why.
    min_binaries: int
    min_tests: int
    # True when the run's TESTS read build/ (see THE BUILD LOCK above).
    reads_build_tree: bool
    why: str
    # Cargo's target selection. `--tests` (lib, bins, tests/*.rs) unless the
    # feature set changes nothing but the targets named here (NARROWED RUNS
    # above; the selftest holds that claim to the crate's source).
    targets: Tuple[str, ...] = ("--tests",)
    # The manifest cargo builds the crate from: Cargo.toml, or the
    # crate's own when it is its own workspace root (trust-spec-temporal); the
    # selftest holds each run to the right one.
    manifest: str = CRATES_MANIFEST
    # Built executables the run's tests execute (BUILT INPUTS): read under the
    # build lock, so a run with inputs sets reads_build_tree.
    inputs: Tuple[Input, ...] = ()
    # Variables the run's tests read as a directory to keep what they make in:
    # each gets a fresh one outside the checkout (BUILT INPUTS says why outside).
    scratch: Tuple[str, ...] = ()

    @property
    def label(self) -> str:
        return f"{self.crate}[{self.features}]"


RUNS: List[Run] = [
    Run(
        crate="trust-cg-bridge",
        features="kernel-recheck,test-hooks",
        # 2026-10-09 at be000c64a5: 55 binaries (lib + 54 tests/*.rs), 1285 tests run.
        # 1282 since 2026-10-09: emit_determinism_child_emitter (emit_determinism.rs)
        # and multisym_emit_child_emitter and multisym_hazard_child_emitter
        # (emit_determinism_multisym.rs), subprocess children that returned at once
        # unless their parent re-executed them, are `#[ignore]`d (the parents select
        # them with `--ignored --exact`). Neither file is cfg-gated, so both runs lose
        # 3: measured that day under each feature set, the two binaries report 3 + 5
        # passed and 1 + 2 ignored (4 + 7 passed before).
        min_binaries=55,
        min_tests=1282,
        reads_build_tree=False,
        why=(
            "the shipped configuration (rustc_codegen_trust_cg links ay-proofs + "
            "kernel-recheck) plus the mutation hooks: every gated file compiles, and "
            "only kernel-recheck awards [PROVED] (the object_replay StrictProvenOnly "
            "lib tests and call_event_gate / f1_compile / variadic_split_attacks / "
            "pointer_slots)"
        ),
    ),
    Run(
        crate="trust-cg-bridge",
        features="test-hooks",
        # 2026-10-09 at be000c64a5: 55 binaries, 1083 tests run (3 kernel-only binaries
        # report zero; see ZERO_TEST_ALLOWED). 1080 since 2026-10-09: the same three
        # `#[ignore]`d subprocess children as the run above.
        min_binaries=55,
        min_tests=1080,
        reads_build_tree=False,
        why=(
            "ay-proofs + test-hooks WITHOUT the kernel: the ay-only grading path, and "
            "the tests that exist only there (`#[cfg(not(feature = \"kernel-recheck\"))]`, "
            "e.g. wide_mul_citation_grade's pipeline test, which the kernel run "
            "discharges before the citation path is consulted)"
        ),
    ),
    Run(
        crate="trust-router",
        features="ay-backend",
        # 2026-10-09 at be000c64a5: 24 binaries (lib, the trustd bin, 22 tests/*.rs), 1202
        # tests run, one of them the no-op adjudicate_undischarged_vcs, which no floor
        # counted: 1201. That driver is now `#[ignore]`d, so 1201 run (ZERO_TEST_ALLOWED).
        # Lowered the same day by determinism batch 1 (T4.2, d970f53a730, and T1a),
        # measured on its merge with main 953d84b3824: 1143 run, 1142 counted, so 1142
        # with the driver ignored. T4.2 deleted the session solver cache and the parallel
        # router with their tests (solver_cache.rs 49; router.rs, router_tests.rs,
        # in_process_ay_backend.rs, incremental_ay.rs and tests/cross_crate_pipeline.rs
        # 12), and T1a added 2.
        # Binaries re-measured 2026-11-06 at b304639207 on m22 (ROUTER-WP-FLEET-1): 22
        # (the lib and 21 tests/*.rs), 1204 tests run, all passed. e33307c530 (2026-10-26)
        # moved the `trustd` bin and tests/trustd_process.rs to crates/trust-coordinator,
        # where they need no feature: `targo --unverified test -p trust-coordinator` ran
        # its lib (160), the trustd bin (9) and trustd_process (9, 1 ignored), all passed,
        # the same day. The test floor is unchanged.
        min_binaries=22,
        min_tests=1142,
        reads_build_tree=True,
        why=(
            "the 8 `#![cfg(feature = \"ay-backend\")]` test files, which no other lane "
            "runs (no test file needs another feature), and the ay-backend lib modules, "
            "which the scoped crates lane's `ay-backend --lib` tail also runs for a change "
            "that touches trust-router (no push runs it since 39b35cb9f7); ay-backend is on in the shipped trustc "
            "(rustc_mir_transform)"
        ),
    ),
    Run(
        crate="trust-router",
        features=SHIPPED_ROUTER,
        # 2026-10-09 at be000c64a5: 24 binaries, 1271 tests run (the lib 1161 of them), one
        # of them the no-op adjudicate_undischarged_vcs: 1270 counted. That driver is now
        # `#[ignore]`d, so 1270 run (ZERO_TEST_ALLOWED). Lowered the same day by
        # determinism batch 1, measured as above: 1212 run, 1211 counted (the same 59
        # tests), so 1211 with the driver ignored.
        # Binaries re-measured 2026-11-06 at b304639207 on m22 (ROUTER-WP-FLEET-1):
        # 22 (the lib and 21 tests/*.rs), 1293 tests run, all passed. The two targets e33307c530 moved to trust-coordinator, as above.
        min_binaries=22,
        min_tests=1211,
        reads_build_tree=True,
        why=(
            "exactly the set rustc_mir_transform links, so every test file runs in the "
            "shipped configuration. Only this run reaches the lib tests behind "
            "trust-cg-output-gate: two trust_cg_backend.rs tests exist only under it, and "
            "the ones that call verify_codegen take its byte-level output-preservation "
            "path instead of the round-trip-only one. Its trust-build / trust-vc-native / "
            "trust-cg-backend lib coverage overlaps the scoped crates lane's second "
            "`--lib` tail, which runs only for a change that touches trust-router. It does "
            "not replace the ay-backend run: ay-certify compiles out the "
            "`not(feature = \"ay-certify\")` tests. Neither run enables "
            "carcara-crosscheck; only that crates tail runs its test modules"
        ),
    ),
    Run(
        crate="trust-vcgen",
        features="prototype-infoflow",
        # 2026-10-27 at b2b85b18e3 (crates/ as origin/main 723f9ec299), cold: the
        # feature still builds (522s, 1-minute load average 56 then 49), 1 binary
        # (tests/infoflow_leak.rs), 4 tests run, all passed. NARROWED (FGT-LANE-3);
        # `--tests` under the same features builds 211 (the lib + 210 tests/*.rs).
        min_binaries=1,
        min_tests=4,
        reads_build_tree=False,
        why=(
            "tests/infoflow_leak.rs is `#![cfg(feature = \"prototype-infoflow\")]`, the one "
            "crate-level gated test file outside trust-cg-bridge and trust-router, and no other "
            "lane enables the feature. NARROWED to that one target: the feature only adds "
            "`#[cfg(any(test, feature = \"prototype-infoflow\"))] pub mod infoflow` (no trait "
            "impls) to the lib, which its test build already compiles, and only "
            "infoflow_leak imports it, so the other 200-odd binaries `--tests` would build "
            "are the default build's, already the scoped crates lane's (FGT-LANE-3)"
        ),
        targets=("--test", "infoflow_leak"),
    ),
    Run(
        crate="trust-spec-temporal",
        features="test-support",
        # 2026-10-27 on a9ec715ade plus this change (crates/ and first-party/ as
        # origin/main 723f9ec299; 66addcea2d moves only trust-router), warm (the same day's cold build: 6m16s), 1-minute
        # load average 37 at the start, 88 midway, 43 at the end: 4 binaries (the
        # lib, model_prelude_kernel, model_prelude_patched, model_theorems), 161
        # tests run (151 + 2 + 1 + 7), 0 failed, 23 ignored (release-only), 521s.
        min_binaries=4,
        min_tests=161,
        reads_build_tree=False,
        why=(
            "tests/model_prelude_patched.rs is a `[[test]]` with `required-features = "
            "[\"test-support\"]`, and model_prelude_kernel.rs and model_theorems.rs gate tests "
            "on the feature item by item; no other lane passes it (the scoped crates lane runs "
            "this crate's own workspace featureless). Not narrowed: the feature adds lib items "
            "under a plain `cfg(feature)`, so the lib's own test build differs too. Its own "
            "workspace root, so its own manifest (FGT-LANE-4)"
        ),
        manifest="crates/trust-spec-temporal/Cargo.toml",
    ),
    Run(
        crate="trust-certify",
        features="calculus-row-test-support",
        # 2026-10-30 on the VF5 review-fixes branch merged onto origin/main 532ea0ac73d,
        # cold (its own target dir), 665s wall: 36 binaries (the lib + 35 tests/*.rs),
        # 1103 tests run, 0 failed, 1 no-op not counted (vf5_calculus_rows, NO_OP_TESTS).
        min_binaries=36,
        min_tests=1103,
        reads_build_tree=False,
        why=(
            "tests/vf5_calculus_rows.rs is a `[[test]]` with `required-features = "
            "[\"calculus-row-test-support\"]` (VF5's CalculusRowProved over the real family: it "
            "reaches `calculus_row::test_support`, which production never links), and no other "
            "lane enables the feature. Not narrowed: the feature adds the lib's "
            "`test_support` module, which the other targets link, so this runs `--tests`; its "
            "one test is a NO_OP_TESTS row on this lane, which has no copy of the family"
        ),
    ),
    Run(
        crate="trust-verifier-api",
        features="native-trust-ir-claims",
        # 2026-11-06 on m22 (18 cores) at 4cb1d0f40a (origin/main, the landed
        # merge): 3 binaries (the lib + artifact_length_boundaries +
        # native_contract_claim), 97 tests run (83 + 2 + 12), 0 failed, 1 ignored.
        min_binaries=3,
        min_tests=97,
        reads_build_tree=False,
        why=(
            "tests/native_contract_claim.rs is `#![cfg(feature = \"native-trust-ir-claims\")]` "
            "(737295cf48, 2026-11-03), and no lane ran this crate's tests with the feature "
            "(trust-router's and trust-vc-bridge's `trust-build` enable it only as a "
            "dependency), so its 12 tests never ran. Not narrowed: the feature adds the lib's `#[cfg(feature = "
            "\"native-trust-ir-claims\")]` module and its trust-ir dependency, so the lib's own "
            "test build differs too (CG-BRIDGE-LANES-1)"
        ),
    ),
    Run(
        crate="trust-bmc",
        features="trust-mc-native-trust-ir-bundle",
        # 2026-11-06 on m22 (18 cores), on this change's merge of origin/main 787a98d09b
        # (7942b2bafe) with first-party/trust-mc at 5d05b457a, which the next commit
        # (1ca3b18386) pinned: 2 binaries (the lib + raw_postcondition_dispatch), 229 tests
        # run (221 + 8), 0 failed. Not re-run after the later merges of 9dcdc04d50 and
        # 09ecbd2359; neither changes a crate this run's build compiled.
        min_binaries=2,
        min_tests=229,
        reads_build_tree=False,
        why=(
            "tests/raw_postcondition_dispatch.rs is `#![cfg(feature = "
            "\"trust-mc-native-trust-ir-bundle\")]` and the feature adds the lib's native "
            "trust-mc CHC lane (lib.rs, verifier_api.rs: unknown_offset_soundness, "
            "direct_shadow_differential and the native dispatch tests). The integration file "
            "ran in no lane. The lib modules run in trust-bmc's `trust-build --lib` tail, which "
            "no push runs (the push profile has had no crates lane since 39b35cb9f7, "
            "2026-11-02); land_gate's crates-tests leg runs it for any change that reaches "
            "trust-bmc, the fast profile's `scoped.crates-tests` when origin/main...HEAD "
            "touches trust-bmc, and anyone by hand. 4 lib tests in that tail were red on main "
            "(measured at 6821832b6e; the trust-mc guard they failed on came in with the pin "
            "move 8862c94337), and no push ran them (docs/DECISION_QUEUE.md BMC-LANE-1). "
            "The feature is part of `trust-build`, the production lane. Not narrowed: it "
            "changes the lib's own test build"
        ),
    ),
    Run(
        crate="trust-build-tree",
        features="native-cli-tests,native-exec",
        # 2026-11-10 on m22 (18 cores) at e66b24d03d plus this change, its inputs built
        # there (x.py stage 1: targo 0.13.0+g2b529da32), 1-minute load average 50: 4
        # binaries (the lib, the bin, fixed_run_public, fixed_test_graph_public), 296 tests
        # run (294 + 0 + 1 + 1), 5 ignored, 84s wall. The two fixed files FAILED there, as
        # they must on a Mac whose aterm resource service has not initialized the native
        # host CPU pool (`targo resource fixed`: "canonical native host pool must exist
        # before legacy retirement"; trust-build-cpu's README: that service owns the
        # pool); the lane does not create it (FGT-LANE-5).
        min_binaries=4,
        min_tests=296,
        reads_build_tree=True,
        why=(
            "tests/fixed_run_public.rs and tests/fixed_test_graph_public.rs are "
            "`#![cfg(all(target_os = \"macos\", target_arch = \"aarch64\", feature = "
            "\"native-cli-tests\", feature = \"native-exec\"))]` (2026-11-08) and no lane "
            "enabled the features, so neither ran. They qualify this checkout's own newly "
            "built Targo: `resource fixed -- run|test` keeps the caller's GNU jobserver pool "
            "below its CPU ceiling and never hands a fixture its target or wrappers. The lib's "
            "`native-cli-tests` tests drive the same Targo's `trust repo lock` front door and "
            "the built Bootstrap's `--trust-build-tree-lock` protocol. Each test fails, not "
            "skips, without its executable, so the run takes them from build/ (BUILT INPUTS). "
            "Only the default `cap2` case of each file runs here; `TRUST_FIXED_RUN_CASE` and "
            "`TRUST_FIXED_TEST_CASE` select the others by hand. Not narrowed: native-exec "
            "enables optional dependencies. Its own workspace root, so its own manifest "
            "(FGT-LANE-5)"
        ),
        manifest="crates/trust-build-tree/Cargo.toml",
        inputs=(
            Input("TRUST_BUILD_TREE_TARGO", "build/{host}/stage1-tools-bin/{host}/targo",
                  sha256_env="TRUST_BUILD_TREE_TARGO_SHA256"),
            Input("TRUST_BUILD_TREE_BOOTSTRAP", "build/bootstrap/debug/bootstrap"),
            Input("TRUST_FIXED_RUN_COMPILER", "build/{host}/stage1/bin/rustc"),
            Input("TRUST_FIXED_TEST_COMPILER", "build/{host}/stage1/bin/rustc"),
        ),
        scratch=("TRUST_FIXED_RUN_ARTIFACT_ROOT", "TRUST_FIXED_TEST_ARTIFACT_ROOT"),
    ),
]

class Allow(NamedTuple):
    """Why a binary may report zero tests run, and (optionally) the feature set
    of the SAME crate whose run does run it. With `covered_by` set, the lane
    also checks that claim: that run must have run the target with at least one
    test, in this same invocation."""

    reason: str
    covered_by: Optional[str]


# Test binaries a run builds that legitimately report ZERO tests run, keyed by
# (crate, features, "<target kind>:<target name>"), each with its reason. An
# entry that stops being true fails the lane: a binary listed here that runs a
# test ("delete the row"), a row that names no binary its run built, and a
# `covered_by` run that did not run the target.
_KERNEL_ONLY = Allow(
    'the file is `#![cfg(feature = "kernel-recheck")]` (it judges [PROVED], which only the '
    "Clean kernel re-check awards); the kernel-recheck,test-hooks run runs it",
    "kernel-recheck,test-hooks",
)
_ADJUDICATE_DRIVER = Allow(
    "its one test, adjudicate_undischarged_vcs, is an `#[ignore]`d measurement driver, not a "
    "check: it asserts nothing (it prints how many undischarged obligations ay decides each "
    "way) and needs TRUST_ADJUDICATE_VC_LOG, a trust-clean census log no lane provides; "
    "without one it panics with the recipe. No run of this lane runs it",
    None,
)
ZERO_TEST_ALLOWED: Dict[Tuple[str, str, str], Allow] = {
    # Measured 2026-10-09: each reports `running 0 tests` under `test-hooks` alone.
    ("trust-cg-bridge", "test-hooks", "test:call_event_gate"): _KERNEL_ONLY,
    ("trust-cg-bridge", "test-hooks", "test:f1_compile"): _KERNEL_ONLY,
    ("trust-cg-bridge", "test-hooks", "test:variadic_split_attacks"): _KERNEL_ONLY,
    # Added 2026-10-14 with the file (PTR.0, the gate's evidence for pointer slots): it is
    # `#![cfg(feature = "kernel-recheck")]` like the three above. Measured that day under
    # `test-hooks` alone: `running 0 tests`.
    ("trust-cg-bridge", "test-hooks", "test:pointer_slots"): _KERNEL_ONLY,
    # Added 2026-11-06 (CG-BRIDGE-LANES-1): five CER test files added 11-04/11-05 are
    # `#![cfg(all(feature = "kernel-recheck", ...))]` like the rows above; measured that
    # day under `test-hooks` alone: `running 0 tests`, and under the kernel run each runs.
    ("trust-cg-bridge", "test-hooks", "test:cer_branch26_operands"): _KERNEL_ONLY,
    ("trust-cg-bridge", "test-hooks", "test:cer_memory_caller_frontier"): _KERNEL_ONLY,
    ("trust-cg-bridge", "test-hooks", "test:cer_object_addresses"): _KERNEL_ONLY,
    ("trust-cg-bridge", "test-hooks", "test:source_c_u8_abi"): _KERNEL_ONLY,
    ("trust-cg-bridge", "test-hooks", "test:vot_object_addresses"): _KERNEL_ONLY,
    # Added 2026-11-14 (DECISION_QUEUE CANCEL-1 review): strength_reduced_gate is
    # `#![cfg(feature = "kernel-recheck")]`, branch_split_gate and additive_cancel_gate
    # `#![cfg(all(feature = "kernel-recheck", feature = "test-hooks"))]`, so under `test-hooks`
    # alone each builds empty. Not measured under `test-hooks` alone (that build was not run):
    # empty by the file's own `cfg`. The kernel run runs each (measured 2026-11-14: 10, 7 and 5).
    ("trust-cg-bridge", "test-hooks", "test:strength_reduced_gate"): _KERNEL_ONLY,
    ("trust-cg-bridge", "test-hooks", "test:branch_split_gate"): _KERNEL_ONLY,
    ("trust-cg-bridge", "test-hooks", "test:additive_cancel_gate"): _KERNEL_ONLY,
    # Added 2026-11-15 with the file (DECISION_QUEUE DIV-SPLIT-1): div_split_gate is
    # `#![cfg(all(feature = "kernel-recheck", feature = "test-hooks"))]` like branch_split_gate,
    # so under `test-hooks` alone it builds empty by its own `cfg` (that build was not run).
    ("trust-cg-bridge", "test-hooks", "test:div_split_gate"): _KERNEL_ONLY,
    # The converse (CG-BRIDGE-LANES-1): this file checks what the build WITHOUT the kernel
    # refuses, so the kernel run builds it empty; measured 2026-11-06.
    ("trust-cg-bridge", "kernel-recheck,test-hooks", "test:m5_instance_feature_absence"): Allow(
        'the file is `#![cfg(all(feature = "ay-proofs", not(feature = "kernel-recheck")))]`: '
        "it checks the kernel-less build's refusals, which the kernel build does not have; "
        "the test-hooks run runs it",
        "test-hooks",
    ),
    # Until 2026-10-09 this test was a plain `#[test]` that returned at once, and
    # NO_OP_TESTS showed it uncounted; now it is `#[ignore]`d, so the binary runs
    # no test: `running 1 test` (libtest counts an ignored test there), then
    # `0 passed; 0 failed; 1 ignored`, and the lane judges passed + failed.
    ("trust-router", "ay-backend", "test:adjudicate_undischarged_vcs"): _ADJUDICATE_DRIVER,
    ("trust-router", SHIPPED_ROUTER, "test:adjudicate_undischarged_vcs"): _ADJUDICATE_DRIVER,
    # Added 2026-11-10 with the run (FGT-LANE-5); measured that day: `running 0 tests`.
    ("trust-build-tree", "native-cli-tests,native-exec", "bin:trust-build-tree"): Allow(
        "src/main.rs is the 18-line `trust-build-tree` entry point and holds no `#[test]` "
        "under any feature; `--tests` builds its unit-test harness all the same (a bin is "
        "`test = true` by default), which runs nothing",
        None,
    ),
}


class NoOp(NamedTuple):
    """Tests a binary runs and libtest counts as passed, though on this lane
    they check nothing, and why. They are shown but not counted: a binary whose
    every passing test is listed is NO-OP, not PASS, and no floor counts them."""

    tests: Tuple[str, ...]
    reason: str


# Keyed like ZERO_TEST_ALLOWED. An entry that stops being true fails the lane: a
# listed test the binary did not run and pass ("delete or update the row"), and a
# row that names no binary its run built. Empty since 2026-10-09: its one row,
# trust-router's adjudicate_undischarged_vcs (found that day by a review of the
# 8 ay-backend files: the only test in them that judged nothing here), is now an
# `#[ignore]`d measurement driver, so its binary is a ZERO_TEST_ALLOWED row
# instead. A test that passes while checking nothing belongs `#[ignore]`d at its
# source; this table is for one that cannot be.
NO_OP_TESTS: Dict[Tuple[str, str, str], NoOp] = {
    # 2026-10-30 (VF5 review fixes): the real VF5 family is not in the pinned
    # first-party/clean, so the test reads it from outside the tree
    # (TRUST_VF5_FAMILY_OLEANS, TRUST_VF5_ROWS) and without both prints why and
    # passes, checking nothing. It is not `#[ignore]`d because with the family
    # named it is the check (the DQ entry's runs). Delete this row when the pinned
    # Clean carries the family and the test reads it from the tree.
    ("trust-certify", "calculus-row-test-support", "test:vf5_calculus_rows"): NoOp(
        tests=("compiled_calculus_rows_are_certified_through_the_reference_entry",),
        reason=("a named skip without TRUST_VF5_FAMILY_OLEANS and TRUST_VF5_ROWS, which this "
                "lane cannot supply: the pinned first-party/clean has no VF5 family"),
    ),
}


# Cargo's test runner in the RUN phase. Cargo starts it as
#   <python> -S -c RUNNER <record dir> <wall limit s> <test executable> <args...>
# once per test binary, one at a time, with the argv, working directory and
# environment it would have given the binary. It runs the binary in a session
# of its own, output to its own log, under the wall limit; records argv, cwd,
# exit status, time and whether cargo's DYLD_FALLBACK_LIBRARY_PATH reached it;
# and exits with the binary's status so cargo's --no-fail-fast bookkeeping is
# unchanged. The record is written BEFORE the binary starts (rc null) and
# replaced when it ends, so a runner that died mid-binary leaves a record that
# says so. `sys.executable`, never a `#!/usr/bin/env` script: macOS strips DYLD_*
# from a SIP-protected executable's environment. `-S`: no `site` import per
# binary.
RUNNER = r"""
import json, os, signal, subprocess, sys, time
d, limit, argv = sys.argv[1], float(sys.argv[2]), sys.argv[3:]
n = 0
while True:
    path = os.path.join(d, '%06d.json' % n)
    try:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
        break
    except FileExistsError:
        n += 1
log = os.path.join(d, '%06d.log' % n)
rec = {'argv': argv, 'exe': os.path.realpath(argv[0]), 'cwd': os.getcwd(), 'log': log,
       'rc': None, 'timed_out': False,
       'interrupted': None, 'seconds': None,
       'dyld': 'DYLD_FALLBACK_LIBRARY_PATH' in os.environ}
def save():
    tmp = path + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as fh:
        json.dump(rec, fh)
    os.replace(tmp, path)
with os.fdopen(fd, 'w', encoding='utf-8') as fh:
    json.dump(rec, fh)
start = time.time()
out = open(log, 'wb')
try:
    p = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=out, stderr=subprocess.STDOUT,
                         start_new_session=True)
except OSError as exc:
    out.write(('runner: could not start %r: %s\n' % (argv[0], exc)).encode())
    out.close()
    rec['rc'] = 127
    rec['seconds'] = time.time() - start
    save()
    sys.exit(127)
def killgroup(sig):
    try:
        os.killpg(p.pid, sig)
    except OSError:
        pass
def stop(signum, _frame):
    killgroup(signal.SIGKILL)
    rec['interrupted'] = signum
    rec['seconds'] = time.time() - start
    save()
    os._exit(128 + signum)
for s in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
    signal.signal(s, stop)
try:
    rc = p.wait(timeout=limit)
except subprocess.TimeoutExpired:
    rec['timed_out'] = True
    killgroup(signal.SIGTERM)
    try:
        rc = p.wait(timeout=10)
    except subprocess.TimeoutExpired:
        killgroup(signal.SIGKILL)
        rc = p.wait()
out.close()
rec['rc'] = rc
rec['seconds'] = time.time() - start
save()
sys.stderr.write('  ran %s: exit %s in %.1fs%s\n' % (os.path.basename(argv[0]), rc,
                 rec['seconds'], ' (WALL LIMIT)' if rec['timed_out'] else ''))
sys.stderr.flush()
sys.exit(124 if rec['timed_out'] else (rc if rc >= 0 else 128 - rc))
"""

_RESULT = re.compile(
    r"^test result: (ok|FAILED)\. (\d+) passed; (\d+) failed; (\d+) ignored; "
    r"(\d+) measured; (\d+) filtered out",
    re.M,
)
_FAILED_TEST = re.compile(r"^test (\S.*?) \.\.\. FAILED$", re.M)
_OK_TEST = re.compile(r"^test (\S.*?) \.\.\. ok$", re.M)


class Artifact(NamedTuple):
    """A test executable cargo reported building (`compiler-artifact`)."""

    exe: str
    kind: str
    name: str
    src: str

    @property
    def target(self) -> str:
        return f"{self.kind}:{self.name}"


class Build(NamedTuple):
    rc: int
    artifacts: List[Artifact]
    errors: List[str]  # cargo's rendered `error` lines, for the report
    seconds: float


class Record(NamedTuple):
    """What RUNNER recorded for one binary, plus that binary's log text."""

    exe: str
    rc: Optional[int]
    timed_out: bool
    interrupted: Optional[int]
    seconds: float
    dyld: bool
    log: str
    text: str


class Outcome(NamedTuple):
    """The verdict on one binary."""

    target: str
    exe: str
    status: str  # PASS NO-OP ALLOWED-ZERO HOST-ZERO, or a red: FAIL ZERO STALE-ALLOW ...
    passed: int
    failed: int
    ignored: int
    filtered: int
    seconds: float
    problem: Optional[str]
    failed_tests: List[str]
    log: str
    noop: int = 0  # of `passed`, the NO_OP_TESTS ones, which no count includes


# The outcomes that are not a red. HOST-ZERO is not green either: it adds a NOT
# JUDGED finding (ONE HOST in the docstring).
NOT_RED = ("PASS", "NO-OP", "ALLOWED-ZERO", "HOST-ZERO")


class Verdict(NamedTuple):
    run: Run
    outcomes: List[Outcome]
    problems: List[str]  # run-level reds
    unjudged: List[str]  # run-level NOT JUDGED
    binaries: int
    tests_run: int  # passed + failed over every binary, less the NO_OP_TESTS ones
    noop_tests: int = 0


# ---------------------------------------------------------------------------
# Parsing and judging: pure functions over cargo's messages and the records.
# The selftest drives exactly these.
# ---------------------------------------------------------------------------


def parse_build_messages(lines: Sequence[str]) -> List[Artifact]:
    """Every test executable in cargo's JSON stream, once, in cargo's order."""
    seen: Dict[str, Artifact] = {}
    for line in lines:
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            msg = json.loads(line)
        except ValueError:
            continue
        if msg.get("reason") != "compiler-artifact" or not msg.get("executable"):
            continue
        if not (msg.get("profile") or {}).get("test"):
            continue
        target = msg.get("target") or {}
        kinds = target.get("kind") or ["?"]
        exe = os.path.realpath(msg["executable"])
        seen.setdefault(
            exe, Artifact(exe, kinds[0], target.get("name") or "?", target.get("src_path") or "")
        )
    return list(seen.values())


def parse_libtest(text: str) -> Optional[Tuple[str, int, int, int, int, int]]:
    """libtest's LAST `test result:` line: (ok|FAILED, passed, failed, ignored,
    measured, filtered out), or None. The last one, because a failing test's
    captured stdout is printed above the summary and may itself say anything."""
    found = _RESULT.findall(text)
    if not found:
        return None
    last = found[-1]
    return (last[0],) + tuple(int(x) for x in last[1:])  # type: ignore[return-value]


def judge_binary(art: Artifact, rec: Record, allow: Optional[Allow],
                 noop: Optional[NoOp] = None) -> Outcome:
    """The verdict on one built-and-run binary (see JUDGE in the docstring)."""

    def out(status: str, problem: Optional[str], counts=(0, 0, 0, 0), failed_tests=(),
            n_noop: int = 0) -> Outcome:
        p, f, i, x = counts
        return Outcome(art.target, art.exe, status, p, f, i, x, rec.seconds, problem,
                       list(failed_tests), rec.log, n_noop)

    if rec.interrupted is not None:
        return out("INTERRUPTED", f"interrupted by signal {rec.interrupted} mid-run")
    if rec.rc is None:
        return out("NO-RESULT", "the runner recorded a start and no end: it died mid-binary")
    if rec.timed_out:
        return out("TIMEOUT", f"killed at the wall limit after {rec.seconds:.0f}s")
    summary = parse_libtest(rec.text)
    if summary is None:
        return out(
            "NO-RESULT",
            f"exit {rec.rc} without libtest's closing `test result:` line: it crashed, "
            "was killed, or is not a libtest harness",
        )
    word, passed, failed, ignored, _measured, filtered = summary
    counts = (passed, failed, ignored, filtered)
    failed_tests = _FAILED_TEST.findall(rec.text)
    want = {0: "ok", 101: "FAILED"}.get(rec.rc)
    if want is None:
        return out("FAIL", f"exit {rec.rc} is not libtest's 0 or 101: crashed or killed",
                   counts, failed_tests)
    if word != want:
        return out("FAIL", f"exit {rec.rc} disagrees with libtest's `test result: {word}.`",
                   counts, failed_tests)
    if failed or word == "FAILED":
        named = len(failed_tests)
        note = "" if named >= failed else f" ({failed - named} not named by a `test ... FAILED` line)"
        return out("FAIL", f"{failed} test(s) failed{note}", counts, failed_tests)
    # The binary passed. Its NO_OP_TESTS must each have run and passed by name (a
    # `test <name> ... ok` line; libtest's default format, which cargo uses).
    listed = noop.tests if noop is not None else ()
    passed_names = set(_OK_TEST.findall(rec.text))
    gone = [t for t in listed if t not in passed_names]
    if gone:
        return out(
            "STALE-NOOP",
            f"NO_OP_TESTS lists {', '.join(gone)} for this binary, which did not run and "
            "pass it: delete or update the row",
            counts,
        )
    n_noop = len(listed)
    ran = passed + failed - n_noop
    if ran <= 0:
        if allow is not None:
            return out("ALLOWED-ZERO", None, counts, n_noop=n_noop)
        if n_noop:
            return out("NO-OP", None, counts, n_noop=n_noop)
        return out(
            "ZERO",
            f"ran no test ({ignored} ignored, {filtered} filtered out): a cfg'd-away "
            "binary passes vacuously; enable what it needs or allowlist it WITH A REASON",
            counts,
        )
    if allow is not None:
        return out(
            "STALE-ALLOW",
            f"allowlisted as running no test, but ran {ran}: delete its ZERO_TEST_ALLOWED row",
            counts,
            n_noop=n_noop,
        )
    return out("PASS", None, counts, n_noop=n_noop)


def judge_run(
    run: Run,
    build: Build,
    records: Sequence[Record],
    cargo_rc: Optional[int],
    allowed: Dict[Tuple[str, str, str], Allow],
    darwin: bool,
    noops: Optional[Dict[Tuple[str, str, str], NoOp]] = None,
    host: str = MEASURED_HOST,
) -> Verdict:
    """Judge one run from its build result, its runner records and cargo's exit
    status (None when the RUN phase never started). `host` is the host the run
    ran on: off MEASURED_HOST, a floor or zero-test finding is NOT JUDGED."""
    problems: List[str] = []
    unjudged: List[str] = []
    outcomes: List[Outcome] = []
    mine = {k[2]: v for k, v in allowed.items() if k[0] == run.crate and k[1] == run.features}
    my_noops = {k[2]: v for k, v in (noops or {}).items()
                if k[0] == run.crate and k[1] == run.features}
    foreign = host != MEASURED_HOST
    unmeasured = (f"the floors and the zero-test allowlist were measured on {MEASURED_HOST}, "
                  f"and this host is {host}: measure its own before judging it")

    if build.rc != 0:
        problems.append(f"BUILD FAILED (targo exit {build.rc}); no test ran")
        return Verdict(run, outcomes, problems, unjudged, len(build.artifacts), 0)
    if not build.artifacts:
        problems.append(
            "EMPTY SELECTION: the build reported no test executable, so this run would "
            "judge nothing"
        )
        return Verdict(run, outcomes, problems, unjudged, 0, 0)

    by_exe: Dict[str, List[Record]] = {}
    for rec in records:
        by_exe.setdefault(os.path.realpath(rec.exe), []).append(rec)
    built = {a.exe for a in build.artifacts}
    for exe in sorted(set(by_exe) - built):
        problems.append(f"UNEXPECTED: cargo ran {exe}, which the build did not list")
    for art in build.artifacts:
        recs = by_exe.get(art.exe, [])
        allow = mine.get(art.target)
        if not recs:
            outcomes.append(Outcome(art.target, art.exe, "NOT-RUN", 0, 0, 0, 0, 0.0,
                                    "built but never handed to the runner", [], ""))
            continue
        if len(recs) > 1:
            problems.append(f"{art.target}: run {len(recs)} times; expected once")
        if darwin and not recs[-1].dyld:
            unjudged.append(
                f"{art.target}: cargo's DYLD_FALLBACK_LIBRARY_PATH did not reach the runner "
                "(a SIP-protected interpreter strips DYLD_*), so it did not run as cargo runs it"
            )
        outcome = judge_binary(art, recs[-1], allow, my_noops.get(art.target))
        if foreign and outcome.status == "ZERO":
            outcome = outcome._replace(status="HOST-ZERO", problem=None)
            unjudged.append(f"{art.target}: ran no test; {unmeasured}")
        outcomes.append(outcome)
    targets = {a.target for a in build.artifacts}
    for target in sorted(set(mine) - targets):
        problems.append(
            f"STALE ALLOWLIST ROW: ZERO_TEST_ALLOWED names {run.crate} [{run.features}] "
            f"{target}, which this run did not build: delete the row"
        )
    for target in sorted(set(my_noops) - targets):
        problems.append(
            f"STALE NO-OP ROW: NO_OP_TESTS names {run.crate} [{run.features}] {target}, "
            "which this run did not build: delete or update the row"
        )

    reds = [o for o in outcomes if o.status not in NOT_RED]
    noop_tests = sum(o.noop for o in outcomes)
    tests_run = sum(o.passed + o.failed for o in outcomes) - noop_tests
    if cargo_rc not in (None, 0) and not reds:
        problems.append(f"cargo exited {cargo_rc} and no binary failed: something else broke")
    if cargo_rc == 0 and any(r.rc != 0 for r in records):
        problems.append("cargo exited 0 although a binary exited non-zero: the runner lost a status")
    floors: List[str] = []
    if len(build.artifacts) < run.min_binaries:
        floors.append(
            f"FLOOR: {len(build.artifacts)} test binaries, below the measured floor of "
            f"{run.min_binaries} (a target merged away or cfg'd out?)"
        )
    if tests_run < run.min_tests:
        floors.append(
            f"FLOOR: {tests_run} tests run, below the measured floor of {run.min_tests} "
            "(a test module cfg'd out of a binary that still runs others?)"
        )
    if foreign:
        unjudged += [f"{f}; {unmeasured}" for f in floors]
    else:
        problems += floors
    return Verdict(run, outcomes, problems, unjudged, len(build.artifacts), tests_run,
                   noop_tests)


def coverage_problems(verdicts: Sequence[Verdict],
                      allowed: Dict[Tuple[str, str, str], Allow]) -> List[str]:
    """Hold each `covered_by` claim of an allowlist row whose run executed to
    what the covering run REPORTED for that target in this invocation."""
    ran = {(v.run.crate, v.run.features): v for v in verdicts}
    problems: List[str] = []
    for (crate, features, target), allow in sorted(allowed.items()):
        if allow.covered_by is None or (crate, features) not in ran:
            continue
        here = ran[(crate, features)]
        if not any(o.target == target and o.status == "ALLOWED-ZERO" for o in here.outcomes):
            continue  # not exempted in this run (stale or red there already)
        cover = ran.get((crate, allow.covered_by))
        if cover is None:
            problems.append(f"{crate} [{features}] {target}: allowlisted as covered by "
                            f"[{allow.covered_by}], which did not run in this invocation")
            continue
        if cover.problems and not cover.outcomes:
            problems.append(f"{crate} [{features}] {target}: its covering run "
                            f"[{allow.covered_by}] judged nothing")
            continue
        got = [o for o in cover.outcomes if o.target == target]
        if not got or got[0].passed + got[0].failed - got[0].noop <= 0:
            problems.append(f"{crate} [{features}] {target}: allowlisted as covered by "
                            f"[{allow.covered_by}], which ran no test of it: the exemption "
                            "covers nothing")
    return problems


def failures_excerpt(text: str, limit: int = 120) -> List[str]:
    """libtest's `failures:` section (panic messages and the failed names)."""
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if line.strip() == "failures:":
            return lines[i:i + limit]
    return lines[-40:]


def report(verdict: Verdict, allowed: Dict[Tuple[str, str, str], Allow],
           noops: Dict[Tuple[str, str, str], NoOp], show_failures: bool = True) -> None:
    """The run's per-binary table and findings. `allowed` and `noops` are the
    tables judge_run judged with, so a reason printed is the one applied."""
    run = verdict.run
    noop_note = f", {verdict.noop_tests} no-op not counted" if verdict.noop_tests else ""
    print(f"\n=== {run.label}: {verdict.binaries} test binaries, {verdict.tests_run} tests run"
          f"{noop_note} (floors: {run.min_binaries} binaries, {run.min_tests} tests)")
    if verdict.outcomes:
        print(f"  {'VERDICT':<13}{'PASSED':>7}{'FAILED':>7}{'IGNORED':>8}{'FILTERED':>9}"
              f"{'NO-OP':>6}{'SECS':>8}  TARGET")
        for o in sorted(verdict.outcomes, key=lambda o: o.target):
            print(f"  {o.status:<13}{o.passed:>7}{o.failed:>7}{o.ignored:>8}{o.filtered:>9}"
                  f"{o.noop:>6}{o.seconds:>8.1f}  {o.target}")

    def mine(table):
        return {k[2]: v for k, v in table.items() if k[0] == run.crate and k[1] == run.features}

    my_allowed, my_noops = mine(allowed), mine(noops)
    for o in sorted(verdict.outcomes, key=lambda o: o.target):
        if o.status == "ALLOWED-ZERO":
            allow = my_allowed.get(o.target)
            print(f"  allowlisted zero-test {o.target}: {allow.reason if allow else '?'}")
        if o.noop:
            noop = my_noops.get(o.target)
            names = ", ".join(noop.tests) if noop else "?"
            print(f"  no-op test(s) {o.target}::{names} (shown, not counted): "
                  f"{noop.reason if noop else '?'}")
    for o in verdict.outcomes:
        if o.problem:
            print(f"  {o.status}: {o.target}: {o.problem}  (log {o.log or '-'})")
            for name in o.failed_tests:
                print(f"      failed: {name}")
    for p in verdict.problems:
        print(f"  RED: {p}")
    for p in verdict.unjudged:
        print(f"  NOT JUDGED: {p}")
    if show_failures:
        for o in verdict.outcomes:
            if o.status in ("FAIL", "NO-RESULT", "TIMEOUT") and o.log and os.path.exists(o.log):
                with open(o.log, encoding="utf-8", errors="replace") as fh:
                    excerpt = failures_excerpt(fh.read())
                print(f"  --- {o.target}: {o.log}")
                for line in excerpt:
                    print(f"  | {line}")


def verdict_reds(v: Verdict) -> int:
    return len(v.problems) + sum(1 for o in v.outcomes if o.status not in NOT_RED)


def final_grade(verdicts: Sequence[Verdict], covered: Sequence[str],
                wall: float) -> Tuple[int, str]:
    """The invocation's exit status and its one verdict line, from every run's
    verdict and the allowlist's `covered_by` findings. A red anywhere is FAIL
    (1), and outranks a NOT JUDGED finding (2); no run judged is a FAIL."""
    if not verdicts:
        return 1, "FAIL: feature-gated tests: no run was judged"
    binaries = sum(v.binaries for v in verdicts)
    tests = sum(v.tests_run for v in verdicts)
    noop_tests = sum(v.noop_tests for v in verdicts)
    failed = sum(o.failed for v in verdicts for o in v.outcomes)
    reds = sum(verdict_reds(v) for v in verdicts) + len(covered)
    zeros = sum(1 for v in verdicts for o in v.outcomes if o.status == "ALLOWED-ZERO")
    unjudged = sum(len(v.unjudged) for v in verdicts)
    summary = (f"feature-gated tests: {len(verdicts)} run(s), {binaries} test binaries, "
               f"{tests} tests run ({failed} failed; {noop_tests} no-op not counted), "
               f"{zeros} allowlisted zero-test binaries, {reds} red finding(s), "
               f"{wall:.0f}s wall")
    if reds:
        tail = f"; {unjudged} NOT JUDGED finding(s)" if unjudged else ""
        return 1, f"FAIL: {summary}{tail}"
    if unjudged:
        return 2, f"NOT JUDGED: {summary}; {unjudged} NOT JUDGED finding(s)"
    return 0, f"PASS: {summary}"


# ---------------------------------------------------------------------------
# Building and running.
# ---------------------------------------------------------------------------


def this_host() -> str:
    """This host as a target triple, for the ONE HOST rule."""
    machine = platform.machine().lower()
    arch = {"arm64": "aarch64", "amd64": "x86_64"}.get(machine, machine)
    if sys.platform == "darwin":
        return f"{arch}-apple-darwin"
    if sys.platform.startswith("linux"):
        return f"{arch}-unknown-linux-gnu"
    return f"{arch}-{sys.platform}"


def targo_problem() -> Optional[str]:
    """CLAUDE.md's one discriminator: cargo-in-disguise rejects `--unverified`."""
    try:
        proc = subprocess.run(["targo", "--unverified", "--version"], stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, universal_newlines=True, check=False)
    except OSError as exc:
        return f"no `targo` on PATH ({exc})"
    if proc.returncode != 0:
        return ("`targo --unverified --version` failed: this `targo` is not Targo "
                f"(cargo under the name?): {(proc.stderr or proc.stdout).strip()[:200]}")
    return None


def base_command(run: Run) -> List[str]:
    return ["targo", "--unverified", "test", "--manifest-path", run.manifest, "--locked",
            "-p", run.crate, "--features", run.features] + list(run.targets)


def cargo_command(run: Run, target_dir: str) -> List[str]:
    """base_command with the lane's target dir as an argument, never a variable
    the test binaries would inherit (BUILT INPUTS)."""
    return base_command(run) + ["--target-dir", target_dir]


def cargo_env(environ: Dict[str, str]) -> Dict[str, str]:
    """The environment cargo, and through it every test binary, gets: the
    caller's, less any target-dir choice (the lane's own is `--target-dir`)."""
    env = {k: v for k, v in environ.items() if k not in TARGET_DIR_VARS}
    env.update(CARGO_TERM_COLOR="never", CARGO_INCREMENTAL="0")
    return env


def resolve_inputs(run: Run, root: Path, host: str) -> Tuple[Dict[str, str], List[str]]:
    """The variables naming a run's built inputs in the checkout at `root`, and
    why any cannot be had: an input that is not an executable file there is
    NOT JUDGED, never skipped (BUILT INPUTS)."""
    env: Dict[str, str] = {}
    missing: List[str] = []
    for item in run.inputs:
        path = root / item.path.format(host=host)
        if not (path.is_file() and os.access(path, os.X_OK)):
            missing.append(f"{item.env}: {path} is not a built executable; build it in this "
                           f"checkout (x.py) before this run")
            continue
        # The real path: a test that holds the image opens it without following
        # a symlink, and the hash below is of that file.
        path = Path(os.path.realpath(path))
        env[item.env] = str(path)
        if item.sha256_env:
            digest = hashlib.sha256()
            with open(path, "rb") as fh:
                for block in iter(lambda: fh.read(1 << 20), b""):
                    digest.update(block)
            env[item.sha256_env] = digest.hexdigest()
    return env, missing


def make_scratch(run: Run, parent: Optional[str] = None) -> Dict[str, str]:
    """A fresh, empty directory per `scratch` variable, outside the checkout
    (BUILT INPUTS), kept after the run for its evidence."""
    if not run.scratch:
        return {}
    base = Path(tempfile.mkdtemp(prefix=f"trust-feature-gated-{run.crate}-", dir=parent))
    env: Dict[str, str] = {}
    for name in run.scratch:
        path = base / name.lower()
        path.mkdir()
        env[name] = str(path)
    return env


def runner_config(record_dir: str, limit: float) -> str:
    """`cfg(all())` matches every target, so no triple is spelled; a TOML array,
    so a path with spaces stays one argument."""
    return "target.'cfg(all())'.runner=" + json.dumps(
        [sys.executable, "-S", "-c", RUNNER, record_dir, str(limit)])


_CHILDREN: List[subprocess.Popen] = []


def _on_signal(signum: int, _frame: object) -> None:
    for proc in list(_CHILDREN):
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except OSError:
            pass
    raise SystemExit(128 + signum)


def spawn(cmd: List[str], env: Dict[str, str], **kwargs) -> subprocess.Popen:
    """Start `cmd` in a session of its own (a deadline or signal reaches the
    whole group: cargo, the runner, rustc) and track it for _on_signal."""
    proc = subprocess.Popen(cmd, cwd=str(REPO_ROOT), env=env, start_new_session=True, **kwargs)
    _CHILDREN.append(proc)
    return proc


def finish(proc: subprocess.Popen) -> int:
    rc = proc.wait()
    _CHILDREN.remove(proc)
    return rc


def do_build(run: Run, env: Dict[str, str], target_dir: str, logdir: Path) -> Build:
    cmd = cargo_command(run, target_dir) + ["--no-run", "--message-format=json-render-diagnostics"]
    print(f"--- build {run.label}: {' '.join(cmd)}", flush=True)
    out_path, err_path = logdir / "build.jsonl", logdir / "build.log"
    start = time.time()
    with open(out_path, "w", encoding="utf-8") as out, open(err_path, "w", encoding="utf-8") as err:
        rc = finish(spawn(cmd, env, stdout=out, stderr=err, stdin=subprocess.DEVNULL))
    with open(out_path, encoding="utf-8", errors="replace") as fh:
        artifacts = parse_build_messages(fh.read().splitlines())
    with open(err_path, encoding="utf-8", errors="replace") as fh:
        err_lines = fh.read().splitlines()
    errors = [l for l in err_lines if l.startswith("error")]
    seconds = time.time() - start
    print(f"    exit {rc} in {seconds:.0f}s: {len(artifacts)} test executables (log {err_path})",
          flush=True)
    if rc != 0:
        for line in (errors[:40] or err_lines[-40:]):
            print(f"    | {line}")
    return Build(rc, artifacts, errors, seconds)


def load_records(record_dir: Path) -> Tuple[List[Record], List[str]]:
    records: List[Record] = []
    bad: List[str] = []
    for name in sorted(os.listdir(record_dir)):
        if not name.endswith(".json"):
            continue
        try:
            with open(record_dir / name, encoding="utf-8") as fh:
                raw = json.load(fh)
        except (OSError, ValueError) as exc:
            bad.append(f"runner record {name} unreadable: {exc}")
            continue
        text = ""
        try:
            with open(raw["log"], encoding="utf-8", errors="replace") as fh:
                text = fh.read()
        except OSError:
            pass
        records.append(Record(raw.get("exe") or raw["argv"][0], raw.get("rc"),
                              bool(raw.get("timed_out")), raw.get("interrupted"),
                              float(raw.get("seconds") or 0.0), bool(raw.get("dyld")),
                              raw["log"], text))
    return records, bad


class Lock:
    """Native Targo measurement ownership, held by this process."""

    def __init__(self, purpose: str, wait_s: int) -> None:
        self.purpose, self.wait_s, self.token, self.nested = purpose, wait_s, "", False

    def acquire(self) -> Optional[str]:
        cmd = ["targo", "trust", "repo", "lock", "acquire", "--repo-root", str(REPO_ROOT), "--kind", "measurement",
               "--purpose", self.purpose, "--pid", str(os.getpid()), "--wait", str(self.wait_s),
               "--contract", "test binaries read build/host/stage{1,2}: do not run x.py "
               "while this is held"]
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              universal_newlines=True, check=False, cwd=str(REPO_ROOT))
        token = (proc.stdout.strip().splitlines() or [""])[-1].strip()
        if proc.returncode != 0 or not token:
            return (f"the build lock refused (exit {proc.returncode}) after waiting up to "
                    f"{self.wait_s}s: {proc.stderr.strip()[-600:]}")
        self.token = token
        self.nested = os.environ.get("TRUST_BUILD_LOCK_TOKEN") == token
        return None

    def release(self) -> None:
        if self.token and not self.nested:
            subprocess.run(["targo", "trust", "repo", "lock", "release", self.token,
                            "--repo-root", str(REPO_ROOT)],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           check=False, cwd=str(REPO_ROOT))
        self.token = ""


def do_run(run: Run, env: Dict[str, str], target_dir: str, logdir: Path, limit: float,
           lock_wait: int) -> Tuple[Optional[int], List[Record], List[str]]:
    """The RUN phase: (cargo's exit status or None, records, NOT JUDGED reasons).
    None with reasons: the phase never started (the lock refused, or a built
    input is missing), so nothing ran."""
    record_dir = logdir / "records"
    record_dir.mkdir()
    cmd = cargo_command(run, target_dir) + ["--no-fail-fast", "--config",
                                            runner_config(str(record_dir), limit)]
    lock = Lock(f"feature-gated tests {run.label}", lock_wait) if run.reads_build_tree else None
    if lock is not None:
        print(f"--- {run.label} reads build/: taking the build lock (measurement)", flush=True)
        refused = lock.acquire()
        if refused:
            return None, [], [refused]
    try:
        # Under the lock: the inputs are read (and hashed) where no x.py build
        # can replace them before or while the tests execute them.
        inputs, missing = resolve_inputs(run, REPO_ROOT, this_host())
        if missing:
            return None, [], [f"built input missing, so no test ran: {m}" for m in missing]
        scratch = make_scratch(run)
        for name, value in sorted({**inputs, **scratch}.items()):
            print(f"    {name}={value}", flush=True)
        env = dict(env, **inputs, **scratch)
        print(f"--- run {run.label}: {' '.join(cargo_command(run, target_dir))} --no-fail-fast "
              f"(runner: per-binary logs in {record_dir})", flush=True)
        with open(logdir / "run.log", "w", encoding="utf-8") as cargo_log:
            proc = spawn(cmd, env, stdout=cargo_log, stderr=subprocess.PIPE,
                         stdin=subprocess.DEVNULL, universal_newlines=True)
            assert proc.stderr is not None
            for line in proc.stderr:  # cargo's status lines and the runner's one-liners
                cargo_log.write(line)
                if line.lstrip().startswith(("Running", "Compiling", "ran ", "error")) or \
                        "test failed" in line:
                    sys.stdout.write("    " + line.strip() + "\n")
                    sys.stdout.flush()
            rc = finish(proc)
    finally:
        if lock is not None:
            lock.release()
    records, bad = load_records(record_dir)
    return rc, records, bad


def _pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:  # alive, another user's
        return True
    except OSError:
        return False
    return True


def prune_logs(root: Path, keep: int = KEEP_LOG_RUNS) -> List[Path]:
    """Delete all but the `keep` newest invocations' log dirs (the stamp sorts
    by start time), never one whose invocation, the pid after its stamp, is
    still running: a long run's logs outlive later, shorter invocations."""
    runs = sorted(p for p in root.iterdir() if p.is_dir())
    removed: List[Path] = []
    for old in runs[:max(len(runs) - keep, 0)]:
        m = re.search(r"-(\d+)$", old.name)
        if m and _pid_alive(int(m.group(1))):
            continue
        shutil.rmtree(old, ignore_errors=True)
        removed.append(old)
    return removed


# ---------------------------------------------------------------------------
# GATED-FILE COVERAGE: which lane runs each feature-gated test target. The
# selftest holds the tree to it (`gated_coverage_problems`), building nothing.
# ---------------------------------------------------------------------------

# The cfg atoms other than `feature` that a gate may use, valued as on
# MEASURED_HOST in a test build. Anything else fails closed: the selftest says
# it cannot read the gate (teach this table, never guess).
HOST_CFG_NAMES = {"unix": True, "windows": False, "test": True, "debug_assertions": True,
                  "miri": False}
HOST_CFG_VALUES = {"target_arch": "aarch64", "target_os": "macos", "target_vendor": "apple",
                   "target_family": "unix", "target_pointer_width": "64",
                   "target_endian": "little", "target_env": ""}
_CFG_TOKEN = re.compile(r'\s*(?:([A-Za-z_][A-Za-z0-9_]*)|("(?:[^"\\]|\\.)*")|([(),=]))')
HARNESS_REL = "tests/run_trust_comprehensive_harness.sh"
# What a module a narrowed run's features add (and nothing else names) may hold
# and still change no other target (`exempt_module_problems`): these
# attributes, these derives, these macros. Anything else fails closed.
_INERT_ATTRS = {"doc", "allow", "warn", "deny", "forbid", "expect", "must_use", "inline",
                "cold", "track_caller", "test", "ignore", "should_panic", "non_exhaustive",
                "cfg", "derive"}
_STD_DERIVES = {"Debug", "Clone", "Copy", "PartialEq", "Eq", "PartialOrd", "Ord", "Hash",
                "Default"}
_STD_MACROS = {"matches", "vec", "format", "format_args", "write", "writeln", "print",
               "println", "eprint", "eprintln", "assert", "assert_eq", "assert_ne",
               "debug_assert", "debug_assert_eq", "debug_assert_ne", "panic", "unreachable",
               "todo", "unimplemented", "concat", "stringify"}
_RISKY_TOKENS = re.compile(r"\b(?<!')(static|extern|macro_rules|global_asm|asm)\b")


class CfgUnknown(ValueError):
    """A cfg predicate this module cannot read or value."""


class Target(NamedTuple):
    """One test target cargo builds for a crate: `kind` "test" (tests/) or
    "bin" (a bin's unit tests), its source, and its `required-features`."""

    kind: str
    name: str
    path: Path
    required: Tuple[str, ...]

    @property
    def key(self) -> str:
        return self.name if self.kind == "test" else f"bin:{self.name}"


def parse_cfg(text: str):
    """`cfg(...)`'s predicate, as nested tuples: ("all"|"any", [..]),
    ("not", p), ("kv", key, value) or ("name", ident)."""
    toks: List[str] = []
    pos = 0
    while pos < len(text):
        m = _CFG_TOKEN.match(text, pos)
        if not m or m.end() == pos:
            if text[pos:].strip():
                raise CfgUnknown(f"cannot tokenize cfg predicate {text!r}")
            break
        toks.append(m.group(1) or m.group(2) or m.group(3))
        pos = m.end()

    def pred(i: int):
        if i >= len(toks) or not re.match(r"[A-Za-z_]", toks[i]):
            raise CfgUnknown(f"cfg predicate {text!r}: expected a name at token {i}")
        name = toks[i]
        if name in ("all", "any", "not") and i + 1 < len(toks) and toks[i + 1] == "(":
            i += 2
            items = []
            while toks[i] != ")":
                node, i = pred(i)
                items.append(node)
                if toks[i] == ",":
                    i += 1
                elif toks[i] != ")":
                    raise CfgUnknown(f"cfg predicate {text!r}: expected `,` or `)`")
            if name == "not":
                if len(items) != 1:
                    raise CfgUnknown(f"cfg predicate {text!r}: not() takes one predicate")
                return ("not", items[0]), i + 1
            return (name, items), i + 1
        if i + 2 < len(toks) and toks[i + 1] == "=" and toks[i + 2].startswith('"'):
            return ("kv", name, toks[i + 2][1:-1]), i + 3
        return ("name", name), i + 1

    try:
        node, end = pred(0)
    except IndexError:
        raise CfgUnknown(f"cfg predicate {text!r} ends early") from None
    if end != len(toks):
        raise CfgUnknown(f"cfg predicate {text!r}: trailing tokens")
    return node


def cfg_features(node) -> List[str]:
    """Every `feature = "..."` the predicate names."""
    kind = node[0]
    if kind in ("all", "any"):
        return [f for n in node[1] for f in cfg_features(n)]
    if kind == "not":
        return cfg_features(node[1])
    return [node[2]] if kind == "kv" and node[1] == "feature" else []


def eval_cfg(node, features: frozenset, test: bool = True) -> bool:
    kind = node[0]
    if kind == "all":
        return all(eval_cfg(n, features, test) for n in node[1])
    if kind == "any":
        return any(eval_cfg(n, features, test) for n in node[1])
    if kind == "not":
        return not eval_cfg(node[1], features, test)
    if kind == "kv":
        if node[1] == "feature":
            return node[2] in features
        if node[1] in HOST_CFG_VALUES:
            return HOST_CFG_VALUES[node[1]] == node[2]
        raise CfgUnknown(f"cfg `{node[1]} = \"{node[2]}\"` is not in HOST_CFG_VALUES")
    if node[1] == "test":
        return test
    if node[1] in HOST_CFG_NAMES:
        return HOST_CFG_NAMES[node[1]]
    raise CfgUnknown(f"cfg `{node[1]}` is not in HOST_CFG_NAMES")


def strip_comments(text: str, blank_strings: bool = False) -> str:
    """The Rust source with every comment (`//`, nested `/* */`, doc comments)
    turned into spaces, newlines and offsets kept. Literals are kept, or with
    `blank_strings` their contents blanked, so a token scan reads code only."""
    out: List[str] = []
    i, n = 0, len(text)

    def blank(seg: str) -> str:
        return "".join(c if c == "\n" else " " for c in seg)

    while i < n:
        c = text[i]
        prev_ident = i > 0 and (text[i - 1].isalnum() or text[i - 1] == "_")
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(blank(text[i:j]))
            i = j
        elif text.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(blank(text[i:j]))
            i = j
        elif not prev_ident and re.match(r'[bc]?r#*"', text[i:i + 260]):
            m = re.match(r'([bc]?r)(#*)"', text[i:])
            close = '"' + m.group(2)
            j = text.find(close, i + m.end())
            j = n if j < 0 else j + len(close)
            body_start, body_end = i + m.end(), max(i + m.end(), j - len(close))
            out.append(text[i:body_start])
            seg = text[body_start:body_end]
            out.append(blank(seg) if blank_strings else seg)
            out.append(text[body_end:j])
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            seg = text[i + 1:j]
            out.append('"' + (blank(seg) if blank_strings else seg) + '"')
            i = j + 1
        elif c == "'" and i + 2 < n and (text[i + 1] == "\\" or text[i + 2] == "'"):
            j = i + 3 if text[i + 1] == "\\" else i + 2
            while j < n and text[j] != "'":
                j += 1
            seg = text[i + 1:j]
            out.append("'" + (blank(seg) if blank_strings else seg) + "'")
            i = j + 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def _balanced(text: str, i: int, open_: str, close: str) -> int:
    """The index just past the `close` matching text[i] == open_ (strings
    skipped; run it on strip_comments output)."""
    depth, j = 0, i
    while j < len(text):
        c = text[j]
        if c == '"':
            j += 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
        elif c == open_:
            depth += 1
        elif c == close:
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    raise CfgUnknown(f"unbalanced `{open_}` at offset {i}")


def crate_level_cfgs(text: str) -> List[str]:
    """The predicates of the file's leading `#![cfg(...)]` attributes (all
    must hold for the file to compile to anything)."""
    code = strip_comments(text)
    preds: List[str] = []
    i = len(code) - len(code.lstrip())
    while code.startswith("#![", i):
        end = _balanced(code, i + 2, "[", "]")
        inner = code[i + 3:end - 1].strip()
        m = re.match(r"cfg\s*\(", inner)
        if m:
            preds.append(inner[m.end():inner.rindex(")")])
        rest = code[end:]
        i = end + len(rest) - len(rest.lstrip())
    return preds


def _manifest_sections(text: str) -> List[Tuple[str, str]]:
    """(header, body) for each table of a Cargo.toml, `#` comments dropped
    (read without a TOML library: the harness may run /usr/bin/python3 3.9,
    which has no tomllib); an array-of-tables header keeps its `[[...]]`."""
    sections: List[Tuple[str, str]] = [("", "")]
    for raw in text.splitlines():
        line = raw.split("#", 1)[0]
        m = re.match(r"^\s*(\[\[?[^\[\]]+\]\]?)\s*$", line)
        if m:
            sections.append((re.sub(r"\s+", "", m.group(1)), ""))
        else:
            head, body = sections[-1]
            sections[-1] = (head, body + line + "\n")
    return sections


def _toml_value(body: str, key: str):
    """A string, bool or string-array value of `key` in a table body (None
    when absent)."""
    m = re.search(rf'^\s*"?{re.escape(key)}"?\s*=\s*(\[.*?\]|"[^"]*"|true|false)',
                  body, re.M | re.S)
    if not m:
        return None
    v = m.group(1)
    if v.startswith("["):
        return re.findall(r'"([^"]*)"', v)
    if v.startswith('"'):
        return v[1:-1]
    return v == "true"


def manifest_features(text: str) -> Dict[str, List[str]]:
    """A Cargo.toml's [features] table (name -> its items)."""
    out: Dict[str, List[str]] = {}
    for head, body in _manifest_sections(text):
        if head == "[features]":
            out.update({name: re.findall(r'"([^"]*)"', items) for name, items in
                        re.findall(r'^\s*"?([A-Za-z0-9_.-]+)"?\s*=\s*\[(.*?)\]', body,
                                   re.M | re.S)})
    return out


def feature_closure(table: Dict[str, List[str]], requested: Sequence[str]):
    """What `--features <requested>` turns on, defaults included (no run
    passes --no-default-features): (the crate's own features, the items that
    reach outside its table: `dep:x`, `x/feat`, `x?/feat`, or a name the table
    lacks, which can only be an optional dependency's implicit feature)."""
    own, foreign, todo = set(), set(), ["default"] + [f for f in requested if f]
    while todo:
        f = todo.pop()
        if f in own or f in foreign:
            continue
        if "/" in f or f.startswith("dep:") or (f not in table and f != "default"):
            foreign.add(f)
            continue
        own.add(f)
        todo += table.get(f, [])
    return frozenset(own), frozenset(foreign)


def enabled_features(table: Dict[str, List[str]], requested: Sequence[str]) -> frozenset:
    """The crate's own features `--features <requested>` enables, defaults
    included (another crate's are not followed: a gate valued without one is
    false, so a test that needs one reads as UNRUN, never as covered)."""
    return feature_closure(table, requested)[0]


def test_targets(crate_dir: Path, manifest: str) -> Dict[str, Target]:
    """The test targets cargo builds for the crate, as cargo picks them:
    tests/<name>.rs and tests/<name>/main.rs unless `autotests = false`, every
    `[[test]]` (its `path`, else tests/<name>.rs or tests/<name>/main.rs,
    replacing a discovered target of the same name or path), and every bin
    whose source holds a `#[test]` (src/main.rs, src/bin/ unless `autobins =
    false`, and each `[[bin]]` without `test = false`), each with the
    `required-features` its table declares."""
    sections = _manifest_sections(manifest)
    package = next((b for h, b in sections if h == "[package]"), "")
    pkg_name = _toml_value(package, "name") or crate_dir.name
    found: Dict[str, Target] = {}

    def discover(kind: str, auto, base: Path, single: Optional[Path]) -> None:
        if auto is False:
            return
        if single is not None and single.is_file():
            found[f"{kind}:{pkg_name}"] = Target(kind, pkg_name, single, ())
        if base.is_dir():
            for p in sorted(base.iterdir()):
                if p.suffix == ".rs" and p.is_file():
                    found[f"{kind}:{p.stem}"] = Target(kind, p.stem, p, ())
                elif p.is_dir() and (p / "main.rs").is_file():
                    found[f"{kind}:{p.name}"] = Target(kind, p.name, p / "main.rs", ())

    discover("test", _toml_value(package, "autotests"), crate_dir / "tests", None)
    discover("bin", _toml_value(package, "autobins"), crate_dir / "src" / "bin",
             crate_dir / "src" / "main.rs")
    for head, body in sections:
        kind = {"[[test]]": "test", "[[bin]]": "bin"}.get(head)
        if not kind:
            continue
        name = _toml_value(body, "name")
        if not isinstance(name, str):
            raise CfgUnknown(f"{crate_dir.name}/Cargo.toml: a {head} without a name")
        rel = _toml_value(body, "path")
        if isinstance(rel, str):
            path = crate_dir / rel
        else:
            base = crate_dir / ("tests" if kind == "test" else "src/bin")
            path = base / f"{name}.rs"
            if not path.is_file() and (base / name / "main.rs").is_file():
                path = base / name / "main.rs"
            if kind == "bin" and name == pkg_name and (crate_dir / "src/main.rs").is_file() \
                    and not path.is_file():
                path = crate_dir / "src/main.rs"
        for k in [k for k, t in found.items() if t.kind == kind and t.path == path]:
            del found[k]
        if _toml_value(body, "test") is False:
            found.pop(f"{kind}:{name}", None)
            continue
        found[f"{kind}:{name}"] = Target(kind, name, path,
                                         tuple(_toml_value(body, "required-features") or ()))
    out: Dict[str, Target] = {}
    for t in found.values():
        if t.kind == "bin":
            try:
                code = strip_comments(t.path.read_text(encoding="utf-8"), blank_strings=True)
            except OSError:
                continue
            if not re.search(r"#\s*\[\s*test\s*\]", code):
                continue
        out[t.key] = t
    return out


def run_selects(run: Run, target: Target) -> bool:
    t = list(run.targets)
    pairs = list(zip(t, t[1:]))
    if target.kind == "bin":
        return "--tests" in t or "--bins" in t or ("--bin", target.name) in pairs
    return "--tests" in t or ("--test", target.name) in pairs


def _src_cfgs(code: str):
    """(line, kind, predicate, start, end) for every `cfg(...)`, `cfg!(...)`
    and `cfg_attr(pred, ..)` in comment-stripped source; `kind` is "attr" for
    an outer `#[cfg(...)]` (start..end spans the attribute), else "other"."""
    for m in re.finditer(r"\b(cfg_attr|cfg)\s*!?\s*\(", code):
        end = _balanced(code, m.end() - 1, "(", ")")
        inner = code[m.end():end - 1]
        if m.group(1) == "cfg_attr":
            depth = 0
            for k, c in enumerate(inner):
                depth += c == "("
                depth -= c == ")"
                if c == "," and depth == 0:
                    inner = inner[:k]
                    break
        kind, start, stop = "other", m.start(), end
        attr = re.search(r"#\s*\[\s*$", code[max(0, m.start() - 40):m.start()])
        if m.group(1) == "cfg" and attr and code[m.start():end].count("!") == 0:
            close = re.match(r"\s*\]", code[end:])
            if close:
                kind = "attr"
                start = max(0, m.start() - 40) + attr.start()
                stop = end + close.end()
        yield code.count("\n", 0, m.start()) + 1, kind, inner, start, stop


def _gated_module(code: str, path: Path, start: int, stop: int):
    """When the outer cfg attribute at code[start:stop] gates a top-level
    `mod NAME`, return (NAME, the module's files' comment-and-string-blanked
    code (one file, or the inline body), the span of the declaration); else
    None. Fails closed (None) on a `#[path]`, a nested module or an
    out-of-line module that resolves to no single file."""
    if code[:start].count("{") - code[:start].count("}") != 0:
        return None
    i = stop
    while True:
        rest = code[i:]
        i += len(rest) - len(rest.lstrip())
        if not code.startswith("#", i) or code.startswith("#!", i):
            break
        bracket = code.find("[", i)
        if bracket < 0:
            return None
        attr_end = _balanced(code, bracket, "[", "]")
        if re.match(r"\[\s*path\b", code[bracket:attr_end]):
            return None
        i = attr_end
    m = re.match(r"(?:pub(?:\s*\([^)]*\))?\s+)?mod\s+([A-Za-z_][A-Za-z0-9_]*)\s*([;{])", code[i:])
    if not m:
        return None
    name = m.group(1)
    if m.group(2) == "{":
        body_start = i + m.end() - 1
        body_end = _balanced(code, body_start, "{", "}")
        return name, code[body_start:body_end], (start, body_end), None
    here = path.parent if path.name in ("lib.rs", "main.rs", "mod.rs") else path.parent / path.stem
    files = [p for p in (here / f"{name}.rs", here / name / "mod.rs") if p.is_file()]
    if len(files) != 1:
        return None
    body = strip_comments(files[0].read_text(encoding="utf-8"), blank_strings=True)
    return name, body, (start, i + m.end()), files[0]


def exempt_module_problems(body: str) -> List[str]:
    """Why a gated module's code could change something outside it (empty:
    it cannot). It may hold no impl block (an inherent method shadows a trait method
    for every caller; a trait impl is behaviour every caller of the type can
    reach), static, extern block or fn, macro_rules, asm, nested out-of-line
    module, attribute outside _INERT_ATTRS, derive outside _STD_DERIVES, or
    macro call outside _STD_MACROS."""
    problems = sorted({f"`{t}`" for t in _RISKY_TOKENS.findall(body)})
    for m in re.finditer(r"\bimpl\b", body):
        # An impl BLOCK sits where an item starts (after `;`, `{`, `}`, an
        # attribute's `]`, or the file's start, maybe behind `unsafe` or
        # `default`); `impl Trait` in a type (`x: impl Iterator`, `-> impl Fn`)
        # follows a `:`, `->`, `(`, `<`, `,`, `&` or `=` and adds no impl.
        before = re.sub(r"(\b(unsafe|default)\s*)+$", "", body[:m.start()].rstrip()).rstrip()
        if not before or before[-1] in ";{}]":
            problems.append("an `impl` block")
            break
    if re.search(r"\bmod\s+[A-Za-z_][A-Za-z0-9_]*\s*;", body):
        problems.append("an out-of-line nested `mod`")
    for m in re.finditer(r"#\s*!?\s*\[", body):
        end = _balanced(body, m.end() - 1, "[", "]")
        inner = body[m.end():end - 1].strip()
        head = re.match(r"([A-Za-z_][A-Za-z0-9_:]*)", inner)
        name = head.group(1) if head else inner
        if name not in _INERT_ATTRS:
            problems.append(f"attribute `#[{inner[:40]}]`")
        elif name == "derive":
            for d in re.findall(r"[A-Za-z_][A-Za-z0-9_:]*", inner[len("derive"):]):
                if d not in _STD_DERIVES:
                    problems.append(f"derive `{d}`")
    for m in re.finditer(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*!\s*[(\[{]", body):
        if m.group(1) not in _STD_MACROS:
            problems.append(f"macro `{m.group(1)}!`")
    return problems


def _manifest_text(crate_dir: Path) -> str:
    return (crate_dir / "Cargo.toml").read_text(encoding="utf-8")


def narrowed_run_problems(root: Path, crate_dir: Path, r: Run,
                          targets: Dict[str, Target]) -> List[str]:
    """A narrowed RUN (no `--tests`) must leave every target it does not run
    as the default build compiles it (NARROWED RUNS in the header)."""
    problems: List[str] = []
    manifest = _manifest_text(crate_dir)
    table = manifest_features(manifest)
    defaults, base_foreign = feature_closure(table, [])
    own, foreign = feature_closure(table, r.features.split(","))
    added = own - defaults
    for item in sorted(foreign - base_foreign):
        problems.append(
            f"NARROWED RUN {r.label}: its features reach `{item}` (another crate's feature or "
            "an optional dependency), which every target of the crate links: widen to `--tests`")
    package = next((b for h, b in _manifest_sections(manifest) if h == "[package]"), "")
    if (crate_dir / "build.rs").is_file() or isinstance(_toml_value(package, "build"), str):
        problems.append(
            f"NARROWED RUN {r.label}: the crate has a build script, which can read the run's "
            "features (CARGO_FEATURE_*) and set cfgs this check cannot see: widen to `--tests`")
    selected = {k for k, t in targets.items() if run_selects(r, t)}
    src = crate_dir / "src"
    src_files = sorted(src.rglob("*.rs")) if src.is_dir() else []
    blanked = {p: strip_comments(p.read_text(encoding="utf-8", errors="replace"),
                                 blank_strings=True) for p in src_files}
    tests_dir = crate_dir / "tests"
    # Every tests/ file a target the run does not select may compile (its own
    # file, or a helper module any target can `mod`-load), read as code.
    unselected = {}
    for p in (sorted(tests_dir.rglob("*.rs")) if tests_dir.is_dir() else []):
        if not any(t.kind == "test" and k in selected and
                   (p == t.path or (t.path.name == "main.rs" and t.path.parent in p.parents))
                   for k, t in targets.items()):
            unselected[p] = strip_comments(p.read_text(encoding="utf-8", errors="replace"))
    unselected_test_code = [strip_comments(c, blank_strings=True) for c in unselected.values()]
    for path in src_files:
        rel = path.relative_to(root)
        is_bin = path == src / "main.rs" or (src / "bin") in path.parents
        unit_ok = ("--bins" in r.targets) if is_bin else ("--lib" in r.targets)
        text = path.read_text(encoding="utf-8", errors="replace")
        code = strip_comments(text)
        for m in re.finditer(r'#\s*\[\s*path\s*=\s*"([^"]*)"', code):
            target_path = (path.parent / m.group(1)).resolve()
            if src.resolve() not in target_path.parents:
                # A test-only helper under tests/ is already scanned below for
                # feature-dependent behavior. It cannot affect the production
                # library linked by other integration targets.
                test_only = re.search(r"#\s*\[\s*cfg\s*\(\s*test\s*\)\s*\]\s*$", code[:m.start()])
                if test_only and tests_dir.resolve() in target_path.parents and any(target_path == p.resolve() for p in unselected):
                    continue
                problems.append(f"NARROWED RUN {r.label}: {rel} loads `{m.group(1)}` from "
                                "outside src/, which this check does not read: widen to `--tests`")
        if re.search(r"\binclude\s*!\s*\(", code):
            problems.append(f"NARROWED RUN {r.label}: {rel} uses include!, whose file this "
                            "check does not read: widen to `--tests`")
        if not any(f'"{f}"' in code for f in added):
            continue
        for line, kind, inner, start, stop in _src_cfgs(code):
            try:
                node = parse_cfg(inner)
                if not set(cfg_features(node)) & added:
                    continue
                unit_flip = eval_cfg(node, defaults, True) != eval_cfg(node, own, True)
                link_flip = eval_cfg(node, defaults, False) != eval_cfg(node, own, False)
            except CfgUnknown as exc:
                if not any(f'"{f}"' in inner for f in added):
                    continue
                unit_flip = link_flip = True
                inner = f"{inner} ({exc})"
            where = f"{rel}:{line} `cfg({inner.strip()})`"
            if unit_flip and not unit_ok:
                problems.append(
                    f"NARROWED RUN {r.label}: {where} compiles the {'bin' if is_bin else 'lib'}'s "
                    f"unit-test build differently under the run's features, which its targets "
                    f"do not run: add `{'--bins' if is_bin else '--lib'}`")
            if not link_flip or is_bin:
                continue
            gated = _gated_module(blanked[path], path, start, stop) if kind == "attr" else None
            why: List[str] = []
            if gated is None:
                why = ["it gates something other than a top-level `mod` this check can read"]
            else:
                name, body, (d0, d1), module_file = gated
                why = exempt_module_problems(body)
                ident = re.compile(rf"\b{re.escape(name)}\b")
                for other, other_code in blanked.items():
                    if other == module_file:
                        continue
                    scan = other_code[:d0] + other_code[d1:] if other == path else other_code
                    if ident.search(scan):
                        why.append(f"{other.relative_to(root)} names `{name}`")
                if any(ident.search(c) for c in unselected_test_code):
                    why.append(f"a tests/ file the run does not select names `{name}`")
            if why:
                problems.append(
                    f"NARROWED RUN {r.label}: {where} changes the lib that the targets the run "
                    f"does not select link ({'; '.join(why)}): widen to `--tests`")
    for p, code in unselected.items():
        named = sorted(f for f in added if re.search(rf'feature\s*=\s*"{re.escape(f)}"', code))
        if named:
            problems.append(
                f"NARROWED RUN {r.label}: {p.relative_to(root)} names feature(s) "
                f"{', '.join(named)} but the run does not select the target that compiles it")
    return problems


def gated_coverage_problems(root: Path, runs: Sequence[Run]) -> List[str]:
    """Every crates/ test target gated on a feature (a leading `#![cfg(...)]`
    that names one, or `required-features`) must compile to its tests in SOME
    lane: under its crate's default features (the scoped crates lane's
    `--tests`), or under a RUN here that selects it. A RUN's manifest must be
    the one cargo can build its crate with, and a narrowed RUN must leave the
    rest of its crate as the default build compiles it."""
    problems: List[str] = []
    crates_dir = root / "crates"
    for crate_dir in sorted(p for p in crates_dir.iterdir() if (p / "Cargo.toml").is_file()):
        crate = crate_dir.name
        manifest = _manifest_text(crate_dir)
        table = manifest_features(manifest)
        defaults = enabled_features(table, [])
        mine = [r for r in runs if r.crate == crate]
        own_root = any(h == "[workspace]" for h, _ in _manifest_sections(manifest))
        want_manifest = f"crates/{crate}/Cargo.toml" if own_root else CRATES_MANIFEST
        for r in mine:
            if r.manifest != want_manifest:
                problems.append(f"RUN {r.label}: manifest {r.manifest}, but {crate} builds "
                                f"from {want_manifest}")
        try:
            targets = test_targets(crate_dir, manifest)
        except CfgUnknown as exc:
            problems.append(f"crates/{crate}: cannot read its test targets: {exc}")
            continue
        for target in targets.values():
            rel = target.path.relative_to(root) if root in target.path.parents else target.path
            try:
                preds = [parse_cfg(p) for p in
                         crate_level_cfgs(target.path.read_text(encoding="utf-8"))]
            except (CfgUnknown, OSError, UnicodeDecodeError) as exc:
                problems.append(f"{rel}: cannot read its crate-level cfg: {exc}")
                continue
            if not target.required and not any(cfg_features(p) for p in preds):
                continue
            if any("/" in f or f.startswith("dep:") for f in target.required):
                problems.append(f"{rel}: cannot value its required-features "
                                f"{list(target.required)}")
                continue

            def holds(features: frozenset) -> bool:
                return set(target.required) <= features and \
                    all(eval_cfg(p, features) for p in preds)

            try:
                if holds(defaults):
                    continue
                if any(run_selects(r, target) and
                       holds(enabled_features(table, r.features.split(","))) for r in mine):
                    continue
            except CfgUnknown as exc:
                problems.append(f"{rel}: cannot value its crate-level cfg: {exc}")
                continue
            gate = (f"required-features {list(target.required)}" if target.required
                    else "crate-level cfg")
            problems.append(
                f"UNRUN GATED FILE {rel}: its {gate} holds under no RUN of {crate} that selects "
                f"{target.kind}:{target.name}, nor under its default features, so no lane "
                "compiles its tests: add a RUN (floors measured) and its harness row")
        for r in mine:
            if "--tests" not in r.targets:
                problems += narrowed_run_problems(root, crate_dir, r, targets)
    return problems


def harness_row_problems(root: Path, runs: Sequence[Run]) -> List[str]:
    """Each crate with a RUN has its own slow harness row (ONE ROW PER CRATE):
    `slow.feature-gated-tests-<crate>|<profiles with slow>|<category>|<required>|
    <last_green>|python3 scripts/feature_gated_tests.py --crate <crate>`. The
    last_green field is free: `--record-last-green` rewrites it."""
    try:
        text = (root / HARNESS_REL).read_text(encoding="utf-8")
    except OSError as exc:
        return [f"{HARNESS_REL} unreadable: {exc}"]
    problems = []
    for crate in sorted({r.crate for r in runs}):
        gate = f"slow.feature-gated-tests-{crate}"
        command = f"python3 scripts/feature_gated_tests.py --crate {crate}"
        found = False
        for line in text.splitlines():
            fields = line.split("|")
            if len(fields) == 6 and fields[0] == gate and fields[5] == command and \
                    "slow" in fields[1].split(","):
                found = True
        if not found:
            problems.append(f"RUNS has {crate} but {HARNESS_REL} has no row "
                            f"`{gate}|slow,...|...|...|<last_green>|{command}`")
    return problems


# ---------------------------------------------------------------------------
# Selftest: every red the lane promises, on canned output, building nothing.
# ---------------------------------------------------------------------------

_SELFTEST_RUN = Run("demo-crate", "feat-a", min_binaries=2, min_tests=2,
                    reads_build_tree=False, why="selftest")


def _art(name: str, kind: str = "test") -> Artifact:
    return Artifact(f"/t/debug/deps/{name}-0123", kind, name, f"tests/{name}.rs")


def _libtest(passed: int, failed: int = 0, ignored: int = 0, filtered: int = 0,
             failing: Sequence[str] = (), noise: str = "") -> str:
    lines = [f"\nrunning {passed + failed + ignored} tests"]
    lines += [f"test ok_{i} ... ok" for i in range(passed)]
    lines += [f"test {name} ... FAILED" for name in failing]
    lines += [f"test ign_{i} ... ignored" for i in range(ignored)]
    if failed:
        lines += ["", "failures:", ""]
        for name in failing:
            lines += [f"---- {name} stdout ----", noise or f"thread '{name}' panicked", ""]
        lines += ["", "failures:"] + [f"    {n}" for n in failing]
    word = "FAILED" if failed else "ok"
    lines += ["", f"test result: {word}. {passed} passed; {failed} failed; {ignored} ignored; "
                  f"0 measured; {filtered} filtered out; finished in 0.01s", ""]
    return "\n".join(lines)


def _rec(art: Artifact, text: str, rc: Optional[int] = 0, timed_out: bool = False,
         dyld: bool = True) -> Record:
    return Record(art.exe, rc, timed_out, None, 0.5, dyld, f"/logs/{art.name}.log", text)


def _selftest_cases():
    a, b, c = _art("alpha"), _art("beta"), _art("gamma")
    lib = _art("demo_crate", "lib")
    green = Build(0, [lib, a, b], [], 1.0)
    ok = [_rec(lib, _libtest(5)), _rec(a, _libtest(3, ignored=1)), _rec(b, _libtest(2))]
    key = ("demo-crate", "feat-a", "test:beta")
    yield ("all green", green, ok, 0, {}, "PASS", [])
    yield ("zero-test binary (`running 0 tests`, exit 0) is a red", green,
           ok[:2] + [_rec(b, _libtest(0))], 0, {}, "FAIL", ["ZERO"])
    yield ("an ignored-only binary ran no test either", green,
           ok[:2] + [_rec(b, _libtest(0, ignored=4))], 0, {}, "FAIL", ["ZERO"])
    yield ("filtered-out-only binary ran no test", green,
           ok[:2] + [_rec(b, _libtest(0, filtered=7))], 0, {}, "FAIL", ["ZERO"])
    yield ("allowlisted zero-test binary passes, with its reason", green,
           ok[:2] + [_rec(b, _libtest(0))], 0, {key: Allow("cfg(feature = x) only", None)}, "PASS",
           ["ALLOWED-ZERO"])
    yield ("stale allowlist: the allowlisted binary ran tests", green, ok, 0,
           {key: Allow("cfg(feature = x) only", None)}, "FAIL", ["STALE-ALLOW"])
    yield ("stale allowlist: the row names a target the run did not build", green, ok, 0,
           {("demo-crate", "feat-a", "test:gone"): Allow("renamed", None)}, "FAIL", ["STALE ALLOWLIST ROW"])
    yield ("an allowlist row for ANOTHER feature set is not consulted", green,
           ok[:2] + [_rec(b, _libtest(0))], 0, {("demo-crate", "feat-b", "test:beta"): Allow("x", None)},
           "FAIL", ["ZERO"])
    yield ("failing binary names its failed tests", green,
           ok[:2] + [_rec(b, _libtest(1, 2, failing=["m::t1", "m::t2"]), rc=101)], 101, {},
           "FAIL", ["FAIL", "m::t1", "m::t2"])
    yield ("a fake `test result: ok` in captured stdout does not hide the real one", green,
           ok[:2] + [_rec(b, _libtest(1, 1, failing=["m::liar"],
                                      noise="test result: ok. 9 passed; 0 failed; 0 ignored; "
                                            "0 measured; 0 filtered out"), rc=101)],
           101, {}, "FAIL", ["m::liar", "1 test(s) failed"])
    yield ("crash: no `test result:` line (SIGSEGV)", green,
           ok[:2] + [_rec(b, "\nrunning 2 tests\ntest ok_0 ... ok\n", rc=-11)], 101, {},
           "FAIL", ["NO-RESULT"])
    yield ("exit 0 with a FAILED summary is inconsistent", green,
           ok[:2] + [_rec(b, _libtest(1, 1, failing=["m::x"]), rc=0)], 0, {}, "FAIL",
           ["disagrees"])
    yield ("cargo exit 0 over a binary that exited 101: the runner lost a status", green,
           ok[:2] + [_rec(b, _libtest(1, 1, failing=["m::x"]), rc=101)], 0, {}, "FAIL",
           ["runner lost a status"])
    yield ("exit 3 is not libtest's", green,
           ok[:2] + [_rec(b, _libtest(2), rc=3)], 101, {}, "FAIL", ["not libtest's"])
    yield ("wall limit", green, ok[:2] + [_rec(b, "", rc=-15, timed_out=True)], 124, {},
           "FAIL", ["TIMEOUT"])
    yield ("runner died mid-binary", green, ok[:2] + [_rec(b, "", rc=None)], 101, {}, "FAIL",
           ["NO-RESULT", "died mid-binary"])
    yield ("built but never run", green, ok[:2], 0, {}, "FAIL", ["NOT-RUN"])
    yield ("ran a binary the build did not list", green, ok + [_rec(c, _libtest(1))], 0, {},
           "FAIL", ["UNEXPECTED"])
    yield ("run twice", green, ok + [_rec(b, _libtest(2))], 0, {}, "FAIL", ["2 times"])
    yield ("build failure", Build(101, [], ["error[E0425]: cannot find value"], 1.0), [], None,
           {}, "FAIL", ["BUILD FAILED"])
    yield ("empty selection", Build(0, [], [], 1.0), [], None, {}, "FAIL", ["EMPTY SELECTION"])
    yield ("below the binary floor", Build(0, [a], [], 1.0), [_rec(a, _libtest(9))], 0, {},
           "FAIL", ["FLOOR: 1 test binaries"])
    yield ("below the tests floor", Build(0, [a, b], [], 1.0),
           [_rec(a, _libtest(1, ignored=5)), _rec(b, _libtest(0, ignored=5))], 0,
           {key: Allow("x", None)}, "FAIL", ["FLOOR: 1 tests run"])
    yield ("cargo failed and no binary did", green, ok, 101, {}, "FAIL", ["something else broke"])
    yield ("DYLD_FALLBACK_LIBRARY_PATH lost on Darwin is NOT JUDGED", green,
           ok[:2] + [_rec(b, _libtest(2), dyld=False)], 0, {}, "UNJUDGED", ["DYLD"])


def _selftest_cases_noop_host():
    """NO_OP_TESTS and ONE HOST: (name, build, records, cargo_rc, allowed, noops,
    host, want, needles). _libtest names its passing tests ok_0, ok_1, ..."""
    a, b = _art("alpha"), _art("beta")
    lib = _art("demo_crate", "lib")
    green = Build(0, [lib, a, b], [], 1.0)
    ok2 = [_rec(lib, _libtest(5)), _rec(a, _libtest(3, ignored=1))]
    key = ("demo-crate", "feat-a", "test:beta")
    one = {key: NoOp(("ok_0",), "an instrument")}
    linux = "x86_64-unknown-linux-gnu"
    yield ("a binary whose only test is a listed no-op is NO-OP, not counted", green,
           ok2 + [_rec(b, _libtest(1))], 0, {}, one, MEASURED_HOST, "PASS",
           ["NO-OP test:beta", "tests_run=8 noop=1"])
    yield ("a listed no-op among real tests: PASS, the no-op not counted", green,
           ok2 + [_rec(b, _libtest(3))], 0, {}, one, MEASURED_HOST, "PASS",
           ["PASS test:beta", "tests_run=10 noop=1"])
    yield ("a no-op row whose test the binary did not run is stale", green,
           ok2 + [_rec(b, _libtest(2))], 0, {}, {key: NoOp(("gone",), "x")}, MEASURED_HOST,
           "FAIL", ["STALE-NOOP", "gone"])
    yield ("a no-op test that was only ignored did not run", green,
           ok2 + [_rec(b, _libtest(1, ignored=1))], 0, {}, {key: NoOp(("ign_0",), "x")},
           MEASURED_HOST, "FAIL", ["STALE-NOOP"])
    yield ("a no-op row naming a target the run did not build is stale", green,
           ok2 + [_rec(b, _libtest(2))], 0, {},
           {("demo-crate", "feat-a", "test:gone"): NoOp(("t",), "x")}, MEASURED_HOST, "FAIL",
           ["STALE NO-OP ROW"])
    yield ("a no-op row for ANOTHER feature set is not consulted", green,
           ok2 + [_rec(b, _libtest(1))], 0, {},
           {("demo-crate", "feat-b", "test:beta"): NoOp(("ok_0",), "x")}, MEASURED_HOST,
           "PASS", ["PASS test:beta", "tests_run=9 noop=0"])
    yield ("a failing binary is FAIL although its no-op test passed", green,
           ok2 + [_rec(b, _libtest(1, 1, failing=["m::x"]), rc=101)], 101, {}, one,
           MEASURED_HOST, "FAIL", ["FAIL test:beta", "m::x"])
    yield ("no-op tests count toward no floor", Build(0, [a, b], [], 1.0),
           [_rec(a, _libtest(1)), _rec(b, _libtest(1))], 0, {},
           {key: NoOp(("ok_0",), "x"), ("demo-crate", "feat-a", "test:alpha"): NoOp(("ok_0",), "x")},
           MEASURED_HOST, "FAIL", ["FLOOR: 0 tests run"])
    yield ("an allowlisted binary that runs only its no-op stays ALLOWED-ZERO", green,
           ok2 + [_rec(b, _libtest(1))], 0, {key: Allow("x", None)}, one, MEASURED_HOST,
           "PASS", ["ALLOWED-ZERO test:beta"])
    yield ("another host: a zero-test binary is NOT JUDGED, not green", green,
           ok2 + [_rec(b, _libtest(0))], 0, {}, {}, linux, "UNJUDGED",
           ["HOST-ZERO test:beta", f"measured on {MEASURED_HOST}", linux])
    yield ("another host: a broken floor is NOT JUDGED, not green", Build(0, [a], [], 1.0),
           [_rec(a, _libtest(9))], 0, {}, {}, linux, "UNJUDGED", ["FLOOR: 1 test binaries", linux])
    yield ("another host: a failing test is still red", green,
           ok2 + [_rec(b, _libtest(1, 1, failing=["m::x"]), rc=101)], 101, {}, {}, linux,
           "FAIL", ["m::x"])
    yield ("another host: a red outranks its NOT JUDGED findings", Build(0, [lib, a, b], [], 1.0),
           [_rec(lib, _libtest(0)), _rec(a, _libtest(1, 1, failing=["m::y"]), rc=101),
            _rec(b, _libtest(0))], 101, {}, {}, linux, "FAIL", ["m::y", "HOST-ZERO"])
    yield ("another host: everything held, PASS", green, ok2 + [_rec(b, _libtest(2))], 0, {},
           {}, linux, "PASS", ["PASS test:beta"])


def _grade(v: Verdict) -> str:
    """final_grade's order on one run: a red outranks NOT JUDGED."""
    if verdict_reds(v):
        return "FAIL"
    return "UNJUDGED" if v.unjudged else "PASS"


def _verdict_text(v: Verdict) -> str:
    parts = [f"{o.status} {o.target} {o.problem or ''} {' '.join(o.failed_tests)}"
             for o in v.outcomes]
    counts = f"tests_run={v.tests_run} noop={v.noop_tests}"
    return "\n".join(parts + v.problems + v.unjudged + [counts])


def _selftest_final_grade() -> List[str]:
    """main()'s verdict line and exit status, from canned verdicts."""
    errors: List[str] = []
    a, b, lib = _art("alpha"), _art("beta"), _art("demo_crate", "lib")
    build = Build(0, [lib, a, b], [], 1.0)
    ok = [_rec(lib, _libtest(5)), _rec(a, _libtest(3)), _rec(b, _libtest(2))]
    green = judge_run(_SELFTEST_RUN, build, ok, 0, {}, darwin=True)
    unjudged = judge_run(_SELFTEST_RUN, build, ok[:2] + [_rec(b, _libtest(2), dyld=False)], 0,
                         {}, darwin=True)
    red = judge_run(_SELFTEST_RUN, build, ok[:2] + [_rec(b, _libtest(0))], 0, {}, darwin=True)
    noop = judge_run(_SELFTEST_RUN, build, ok[:2] + [_rec(b, _libtest(1))], 0, {}, darwin=True,
                     noops={("demo-crate", "feat-a", "test:beta"): NoOp(("ok_0",), "x")})
    cases = [
        ("every run green", [green, green], [], 0, ["PASS: ", "2 run(s), 6 test binaries",
                                                    "20 tests run (0 failed; 0 no-op"]),
        ("a covered_by finding alone is a red", [green], ["cover"], 1, ["FAIL: ", "1 red"]),
        ("a NOT JUDGED finding alone exits 2", [green, unjudged], [], 2,
         ["NOT JUDGED: ", "1 NOT JUDGED finding"]),
        ("a red outranks a NOT JUDGED finding in another run", [red, unjudged], [], 1,
         ["FAIL: ", "1 red finding", "1 NOT JUDGED finding"]),
        ("no run judged is a FAIL", [], [], 1, ["FAIL: ", "no run was judged"]),
        ("the line counts tests without the no-ops", [noop], [], 0,
         ["PASS: ", "8 tests run (0 failed; 1 no-op not counted)"]),
    ]
    for name, verdicts, covered, want_rc, needles in cases:
        rc, line = final_grade(verdicts, covered, 1.0)
        missing = [n for n in needles if n not in line]
        if rc != want_rc or missing:
            errors.append(f"final_grade: {name}: exit {rc} (want {want_rc}); missing {missing}: "
                          f"{line}")
    return errors


def _selftest_prune() -> List[str]:
    """prune_logs keeps the newest and never a live invocation's dir."""
    errors: List[str] = []
    dead = subprocess.Popen([sys.executable, "-S", "-c", "pass"])
    dead.wait()
    with tempfile.TemporaryDirectory(prefix="feature-gated-prune.") as tmp:
        root = Path(tmp)
        live = root / f"20260101T000000Z-{os.getpid()}"
        stamped = root / "20260101T000001Z"
        newer = [root / f"20260101T00001{i}Z-{dead.pid}" for i in range(5)]
        for d in [live, stamped] + newer:
            d.mkdir()
        removed = prune_logs(root, keep=5)
        if removed != [stamped] or not live.is_dir() or not all(d.is_dir() for d in newer):
            errors.append(f"prune_logs removed {[p.name for p in removed]}; want only "
                          f"{stamped.name}, and the live {live.name} kept")
    return errors


def _selftest_cache_placement() -> List[str]:
    """Run main's real setup and first-build boundary without compiling Rust."""
    import contextlib
    import io
    from unittest import mock

    errors: List[str] = []
    a, b = _art("alpha"), _art("beta")
    cases = [
        ("fresh default", [], False, False, False),
        ("legacy output preserved", [], True, False, False),
        ("explicit fresh target", ["--target-dir", "chosen cache"], False, False, False),
        ("explicit unmanaged target", ["--target-dir", "existing cache"], False, True, False),
        ("log target overlap", ["--target-dir", LOG_DIR_REL], False, False, True),
        ("log target case alias", ["--target-dir", LOG_DIR_REL.upper()], False, False, True),
        ("log target ancestor", ["--target-dir", "crates"], False, False, True),
        ("log target descendant", ["--target-dir", LOG_DIR_REL + "/nested"], False, False, True),
    ]
    for label, argv, legacy, unmanaged, overlap in cases:
        with tempfile.TemporaryDirectory(prefix="feature-gated-layout.") as tmp:
            root = Path(tmp)
            old = root / "crates" / "target-feature-gated.noindex"
            if legacy:
                old.mkdir(parents=True)
                (old / "old-output").write_text("preserved")
            selected = argv[-1] if argv else str(root / TARGET_DIR_REL)
            target = Path(selected)
            if not target.is_absolute():
                target = root / target
            if unmanaged:
                target.mkdir(parents=True)
                (target / "unmanaged-output").write_text("untouched")
            seen: List[str] = []

            def build_probe(run: Run, env: Dict[str, str], target_dir: str,
                            logdir: Path) -> Build:
                seen.append(target_dir)
                if target_dir != selected:
                    errors.append(f"{label}: the selected target changed")
                # The target is an argument; no variable the test binaries
                # inherit names one, the ambient ones included.
                leaked = [k for k in TARGET_DIR_VARS if k in env]
                if leaked:
                    errors.append(f"{label}: cargo's environment names a target dir: {leaked}")
                cmd = cargo_command(run, target_dir)
                at = cmd.index("--target-dir") if "--target-dir" in cmd else len(cmd)
                if cmd[at + 1:at + 2] != [selected]:
                    errors.append(f"{label}: the build command does not name the target: {cmd}")
                if logdir == target or target in logdir.parents:
                    errors.append(f"{label}: logs are inside the compiler target")
                if not unmanaged and target.exists():
                    errors.append(f"{label}: logging created the target before the producer")
                (logdir / "build.log").write_text("refused" if unmanaged else "build started")
                if unmanaged:
                    return Build(75, [], ["native ownership refused"], 0.0)
                return Build(0, [a, b], [], 0.0)

            handlers = {sig: signal.getsignal(sig) for sig in
                        (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)}
            try:
                with mock.patch.dict(os.environ, {
                    "CARGO_TARGET_DIR": "ambient cargo target",
                    "TARGO_TARGET_DIR": "ambient targo target",
                }), mock.patch.dict(globals(), {
                    "REPO_ROOT": root,
                    "RUNS": [_SELFTEST_RUN],
                    "ZERO_TEST_ALLOWED": {},
                    "NO_OP_TESTS": {},
                    "targo_problem": lambda: None,
                    "this_host": lambda: MEASURED_HOST,
                    "do_build": build_probe,
                    "do_run": lambda *args: (0, [_rec(a, _libtest(1)),
                                                  _rec(b, _libtest(1))], []),
                }), contextlib.redirect_stdout(io.StringIO()), \
                        contextlib.redirect_stderr(io.StringIO()):
                    try:
                        rc = main(argv)
                    except SystemExit as exc:
                        rc = exc.code
            finally:
                for sig, handler in handlers.items():
                    signal.signal(sig, handler)
            if rc != (2 if overlap else 1 if unmanaged else 0) or seen != ([] if overlap else [selected]):
                errors.append(f"{label}: exit {rc}, selected targets {seen}")
            logs = list(root.rglob("build.log"))
            if overlap:
                if target.exists() or (root / LOG_DIR_REL).exists() or logs:
                    errors.append(f"{label}: overlap refusal created output")
            elif len(logs) != 1 or logs[0].read_text() != ("refused" if unmanaged else "build started"):
                errors.append(f"{label}: build/refusal log was not retained")
            if legacy and (old / "old-output").read_text() != "preserved":
                errors.append(f"{label}: old output changed")
            if unmanaged and (target / "unmanaged-output").read_text() != "untouched":
                errors.append(f"{label}: unmanaged output changed")
    return errors


def _selftest_built_inputs() -> List[str]:
    """BUILT INPUTS: resolve_inputs, make_scratch and do_run's use of them, with
    the lock and cargo replaced by recorders (nothing is built or run)."""
    import contextlib
    import io
    from unittest import mock

    errors: List[str] = []
    with tempfile.TemporaryDirectory(prefix="feature-gated-inputs.") as tmp:
        root = Path(tmp)
        exe = root / "build" / MEASURED_HOST / "stage1" / "bin" / "tool"
        exe.parent.mkdir(parents=True)
        exe.write_bytes(b"#!/bin/sh\nexit 0\n")
        exe.chmod(0o755)
        plain = root / "build" / "plain"
        plain.write_bytes(b"not executable")
        run = _SELFTEST_RUN._replace(
            reads_build_tree=True,
            inputs=(Input("DEMO_TOOL", "build/{host}/stage1/bin/tool", "DEMO_TOOL_SHA256"),),
            scratch=("DEMO_SCRATCH_A", "DEMO_SCRATCH_B"))
        env, missing = resolve_inputs(run, root, MEASURED_HOST)
        want_sha = hashlib.sha256(exe.read_bytes()).hexdigest()
        real = os.path.realpath(exe)
        if missing or env != {"DEMO_TOOL": real, "DEMO_TOOL_SHA256": want_sha}:
            errors.append(f"inputs: a built executable resolved to {env}, {missing}")
        link = root / "build" / "link"
        link.symlink_to(exe)
        env, missing = resolve_inputs(run._replace(inputs=(Input("DEMO_TOOL", "build/link"),)),
                                      root, MEASURED_HOST)
        if missing or env != {"DEMO_TOOL": real}:
            errors.append(f"inputs: a symlinked input is not passed as its real path: {env}")
        for label, path in (("absent", "build/{host}/absent"), ("not executable", "build/plain"),
                            ("a directory", "build/{host}")):
            gone = run._replace(inputs=(Input("DEMO_TOOL", path, "DEMO_TOOL_SHA256"),))
            try:
                env, missing = resolve_inputs(gone, root, MEASURED_HOST)
            except OSError as exc:  # it went on to read what it should have refused
                env, missing = {"raised": str(exc)}, []
            if env or len(missing) != 1 or "DEMO_TOOL" not in missing[0]:
                errors.append(f"inputs: an input that is {label} was not refused: {env}, {missing}")
        scratch = make_scratch(run, parent=tmp)
        dirs = [Path(scratch.get(n, "")) for n in run.scratch]
        if sorted(scratch) != sorted(run.scratch) or len(set(dirs)) != 2 or \
                any(not d.is_dir() or any(d.iterdir()) for d in dirs):
            errors.append(f"scratch: not one fresh empty directory per variable: {scratch}")
        default = make_scratch(run._replace(scratch=("DEMO_SCRATCH_A",)))
        made = Path(default["DEMO_SCRATCH_A"]).resolve()
        if REPO_ROOT.resolve() in made.parents:
            errors.append(f"scratch: {made} is inside the checkout, whose cargo config "
                          "would reach a crate the tests make there")
        shutil.rmtree(made.parent, ignore_errors=True)

        # do_run: missing inputs stop the phase before cargo starts (NOT JUDGED,
        # never a pass), with the lock released; present ones reach cargo's
        # environment beside the target-dir argument.
        calls: List[Tuple[List[str], Dict[str, str]]] = []
        held: List[str] = []

        class FakeLock:
            def __init__(self, purpose: str, wait_s: int) -> None:
                pass

            def acquire(self) -> Optional[str]:
                held.append("acquire")
                return None

            def release(self) -> None:
                held.append("release")

        class FakeProc:
            stderr: List[str] = []

        def fake_spawn(cmd: List[str], env: Dict[str, str], **_kw) -> FakeProc:
            calls.append((cmd, env))
            return FakeProc()

        for label, chosen in (("missing", run._replace(inputs=(Input("DEMO_TOOL", "build/x"),))),
                              ("present", run)):
            calls.clear()
            held.clear()
            logdir = root / f"logs-{label}"
            logdir.mkdir()
            with mock.patch.dict(globals(), {"REPO_ROOT": root, "Lock": FakeLock,
                                             "spawn": fake_spawn, "finish": lambda p: 0,
                                             "this_host": lambda: MEASURED_HOST}), \
                    contextlib.redirect_stdout(io.StringIO()):
                # An ambient value for an input is the caller's, never the build tree's.
                rc, records, why = do_run(chosen, {"PATH": "/bin", "DEMO_TOOL": "/ambient/tool"},
                                          "the target", logdir, 60.0, 0)
            if held != ["acquire", "release"]:
                errors.append(f"do_run {label}: the lock was {held}, want taken and released")
            if label == "missing":
                if rc is not None or records or calls or \
                        not any("built input missing" in w and "DEMO_TOOL" in w for w in why):
                    errors.append(f"do_run with a missing input: rc {rc}, cargo calls "
                                  f"{len(calls)}, reasons {why}")
                continue
            if rc != 0 or why or len(calls) != 1:
                errors.append(f"do_run with its inputs: rc {rc}, reasons {why}, calls {len(calls)}")
                continue
            cmd, env = calls[0]
            made_dirs = {Path(env[n]).parent for n in run.scratch if n in env}
            if env.get("DEMO_TOOL") != real or env.get("DEMO_TOOL_SHA256") != want_sha or \
                    not all(Path(env.get(n, "")).is_dir() for n in run.scratch) or \
                    env.get("PATH") != "/bin" or any(k in env for k in TARGET_DIR_VARS):
                errors.append(f"do_run with its inputs: cargo's environment {env}")
            at = cmd.index("--target-dir") if "--target-dir" in cmd else len(cmd)
            if cmd[at + 1:at + 2] != ["the target"]:
                errors.append(f"do_run: the RUN command does not name the target: {cmd}")
            for made_dir in made_dirs:
                shutil.rmtree(made_dir, ignore_errors=True)
    env = cargo_env({"CARGO_TARGET_DIR": "a", "TARGO_TARGET_DIR": "b", "KEEP": "c"})
    if env != {"KEEP": "c", "CARGO_TERM_COLOR": "never", "CARGO_INCREMENTAL": "0"}:
        errors.append(f"cargo_env passes a target-dir variable or drops the caller's: {env}")
    for r in RUNS:
        names = [i.env for i in r.inputs] + [i.sha256_env for i in r.inputs if i.sha256_env] \
            + list(r.scratch)
        if len(names) != len(set(names)):
            errors.append(f"RUNS {r.label}: an input or scratch variable is named twice: {names}")
        if r.inputs and not r.reads_build_tree:
            errors.append(f"RUNS {r.label}: it executes built inputs, so it reads build/ and "
                          "must take the build lock (reads_build_tree)")
        for item in r.inputs:
            if not item.path.startswith("build/"):
                errors.append(f"RUNS {r.label}: input {item.env} at {item.path} is not under "
                              "build/, which the build lock guards")
    return errors


def _selftest_coverage() -> List[str]:
    """An allowlist row's `covered_by` claim is held to the covering run."""
    errors: List[str] = []
    a, b, lib = _art("alpha"), _art("beta"), _art("demo_crate", "lib")
    build = Build(0, [lib, a, b], [], 1.0)
    covering = Run("demo-crate", "feat-full", 2, 2, False, "selftest")
    key = ("demo-crate", "feat-a", "test:beta")
    allowed = {key: Allow("only under feat-full", "feat-full")}
    zero_b = [_rec(lib, _libtest(5)), _rec(a, _libtest(3)), _rec(b, _libtest(0))]
    here = judge_run(_SELFTEST_RUN, build, zero_b, 0, allowed, darwin=True)
    good = judge_run(covering, build, [_rec(lib, _libtest(5)), _rec(a, _libtest(3)),
                                       _rec(b, _libtest(4))], 0, allowed, darwin=True)
    bad = judge_run(covering, build, zero_b, 0, allowed, darwin=True)
    if coverage_problems([here, good], allowed):
        errors.append("coverage: a target the covering run ran was reported uncovered")
    if not any("covers nothing" in p for p in coverage_problems([here, bad], allowed)):
        errors.append("coverage: a covering run that ran no test of the target was accepted")
    if not any("did not run" in p for p in coverage_problems([here], allowed)):
        errors.append("coverage: a covering run that never ran was accepted")
    noop_only = judge_run(covering, build, [_rec(lib, _libtest(5)), _rec(a, _libtest(3)),
                                            _rec(b, _libtest(1))], 0, allowed, darwin=True,
                          noops={("demo-crate", "feat-full", "test:beta"): NoOp(("ok_0",), "x")})
    if not any("covers nothing" in p for p in coverage_problems([here, noop_only], allowed)):
        errors.append("coverage: a covering run whose only test of the target is a no-op "
                      "was accepted")
    return errors


def _selftest_gated_coverage() -> List[str]:
    """gated_coverage_problems over small canned trees, then its cfg reader,
    the harness-row reader and base_command's target selection."""
    errors: List[str] = []
    manifest = ('[package]\nname = "demo"\n\n[features]\n# a comment\ndefault = ["std"]\n'
                'std = []\nfeat-a = []\nfeat-b = [\n    "feat-a", # implies a\n    "dep:x",\n]\n'
                'proto = []\nproto2 = [] # not "feat-a"\nproto-dep = ["other/x"]\n'
                'proto-opt = ["dep:y"]\n\n[dependencies]\n')
    gated = '// header\n#![cfg(feature = "feat-a")]\n//! doc\nuse demo::*;\n'
    narrow = ("--test", "p")
    inert = ("pub fn leak(x: &'static str, y: impl IntoIterator<Item = u8>) -> bool "
             "{ matches!(x, \"a\") }\n")
    p_file = {"tests/p.rs": '#![cfg(feature = "proto")]\n'}

    def nrun(features: str = "proto", targets: Tuple[str, ...] = narrow) -> List[Run]:
        return [Run("demo", features, 1, 1, False, "t", targets)]

    cases = [
        ("a gated file no run selects is UNRUN", {"tests/g.rs": gated}, [], ["UNRUN GATED FILE"]),
        ("a run that selects it covers it", {"tests/g.rs": gated},
         [Run("demo", "feat-a", 1, 1, False, "t")], []),
        ("a feature the table implies counts (feat-b enables feat-a)", {"tests/g.rs": gated},
         [Run("demo", "feat-b", 1, 1, False, "t")], []),
        ("a quoted name in a manifest comment implies nothing", {"tests/g.rs": gated},
         [Run("demo", "proto2", 1, 1, False, "t")], ["UNRUN GATED FILE"]),
        ("a run of another crate does not count", {"tests/g.rs": gated},
         [Run("other", "feat-a", 1, 1, False, "t")], ["UNRUN GATED FILE"]),
        ("a run with the feature that does not select the file does not count",
         {"tests/g.rs": gated}, [Run("demo", "feat-a", 1, 1, False, "t", ("--test", "h"))],
         ["UNRUN GATED FILE"]),
        ("a default feature's gate is the crates lane's", {"tests/s.rs": '#![cfg(feature = "std")]\n'},
         [], []),
        ("not(default feature) holds under no run: UNRUN",
         {"tests/s.rs": '#![cfg(not(feature = "std"))]\n'}, [], ["UNRUN GATED FILE"]),
        ("a gate without a feature is not this lane's", {"tests/u.rs": "#![cfg(unix)]\n"}, [], []),
        ("a nested block comment before the gate is skipped as rustc skips it",
         {"tests/g.rs": '/* a /* b */ c */\n#![cfg(feature = "feat-a")]\n'}, [],
         ["UNRUN GATED FILE"]),
        ("every leading cfg must hold (tests/<name>/main.rs)",
         {"tests/m/main.rs": '#![allow(dead_code)]\n#![cfg(feature = "feat-a")]\n'
                             '#![cfg(target_os = "linux")]\n'},
         [Run("demo", "feat-a", 1, 1, False, "t")], ["UNRUN GATED FILE", "tests/m/main.rs"]),
        ("an atom the host table lacks fails closed", {"tests/k.rs": '#![cfg(all(kani, feature = "feat-a"))]\n'},
         [Run("demo", "feat-a", 1, 1, False, "t")], ["cannot value", "kani"]),
        ("a key = value atom the host table lacks fails closed",
         {"tests/k.rs": '#![cfg(all(target_abi = "x", feature = "feat-a"))]\n'},
         [Run("demo", "feat-a", 1, 1, False, "t")], ["cannot value", "target_abi"]),
        ("[[test]] required-features is a gate: UNRUN without a run",
         {"tests/r.rs": "#[test]\nfn t() {}\n",
          "Cargo.toml": manifest + '\n[[test]]\nname = "r"\nrequired-features = ["feat-a"]\n'},
         [], ["UNRUN GATED FILE", "required-features"]),
        ("[[test]] required-features: a run that selects it covers it",
         {"tests/r.rs": "#[test]\nfn t() {}\n",
          "Cargo.toml": manifest + '\n[[test]]\nname = "r"\nrequired-features = ["feat-a"]\n'},
         [Run("demo", "feat-a", 1, 1, False, "t", ("--test", "r"))], []),
        ("autotests = false: an undeclared file is no target, a declared one is",
         {"tests/g.rs": gated, "tests/d.rs": '#![cfg(feature = "proto")]\n',
          "Cargo.toml": manifest.replace('name = "demo"\n', 'name = "demo"\nautotests = false\n')
          + '\n[[test]]\nname = "d"\n'}, [], ["UNRUN GATED FILE crates/demo/tests/d.rs", "!tests/g.rs"]),
        ("a [[bin]] with required-features and a unit test is a gated target",
         {"src/bin/b.rs": "fn main() {}\n#[test]\nfn t() {}\n",
          "Cargo.toml": manifest + '\n[[bin]]\nname = "b"\nrequired-features = ["feat-a"]\n'},
         [], ["UNRUN GATED FILE", "bin:b"]),
        ("a [[bin]] with required-features and no unit test is no test target",
         {"src/bin/b.rs": "fn main() {}\n",
          "Cargo.toml": manifest + '\n[[bin]]\nname = "b"\nrequired-features = ["feat-a"]\n'},
         [], []),
        ("an own-workspace crate's run must name its own manifest",
         {"tests/g.rs": gated, "Cargo.toml": manifest + "\n[workspace]\n"},
         [Run("demo", "feat-a", 1, 1, False, "t")], ["manifest Cargo.toml"]),
        ("an own-workspace crate's run with its own manifest is clean",
         {"tests/g.rs": gated, "Cargo.toml": manifest + "\n[workspace]\n"},
         [Run("demo", "feat-a", 1, 1, False, "t", manifest="crates/demo/Cargo.toml")], []),
        ("a narrowed run: an inert module only it names, gated any(test, feature), is clean",
         dict(p_file, **{"src/lib.rs": '#[cfg(any(test, feature = "proto"))]\npub mod p;\n',
                         "src/p.rs": inert}), nrun(), []),
        ("a narrowed run: the same module holding an impl is a red (test=false build)",
         dict(p_file, **{"src/lib.rs": '#[cfg(any(test, feature = "proto"))]\npub mod p;\n',
                         "src/p.rs": inert + "impl crate::S { pub fn f(&self) {} }\n"}),
         nrun(), ["NARROWED RUN", "src/lib.rs:1", "`impl` block", "widen to `--tests`"]),
        ("a narrowed run: the same module named elsewhere in src is a red",
         dict(p_file, **{"src/lib.rs": '#[cfg(any(test, feature = "proto"))]\npub mod p;\n'
                                       'pub fn g() { let p = 1; }\n',
                         "src/p.rs": inert}), nrun(), ["NARROWED RUN", "names `p`"]),
        ("a narrowed run: the same module with an unknown macro is a red",
         dict(p_file, **{"src/lib.rs": '#[cfg(any(test, feature = "proto"))]\npub mod p;\n',
                         "src/p.rs": inert + "inventory::submit! { 1 }\n"}),
         nrun(), ["NARROWED RUN", "macro `submit!`"]),
        ("a narrowed run: an any(test, feature) impl is a red",
         dict(p_file, **{"src/lib.rs": 'pub struct S;\n#[cfg(any(test, feature = "proto"))]\n'
                                       'impl Default for S { fn default() -> S { S } }\n'}),
         nrun(), ["NARROWED RUN", "src/lib.rs:2", "widen to `--tests`"]),
        ("a narrowed run: cfg!(any(test, feature)) is a red",
         dict(p_file, **{"src/lib.rs": 'pub fn f() -> bool { cfg!(any(test, feature = "proto")) }\n'}),
         nrun(), ["NARROWED RUN", "src/lib.rs:1", "widen to `--tests`"]),
        ("a narrowed run whose feature flips a lib test module is a red",
         dict(p_file, **{"src/lib.rs": '// cfg(feature = "proto") in a comment is not read\n'
                                       '#[cfg(all(test, feature = "proto"))]\nmod t;\n'}),
         nrun(), ["NARROWED RUN", "src/lib.rs:2", "add `--lib`"]),
        ("a narrowed run that selects --lib covers a lib-test flip",
         dict(p_file, **{"src/lib.rs": '#[cfg(all(test, feature = "proto"))]\nmod t;\n'}),
         nrun(targets=("--lib",) + narrow), []),
        ("a narrowed run: a cfg only in comments (nested too) is not read",
         dict(p_file, **{"src/lib.rs": '// #[cfg(feature = "proto")] mod a;\n'
                                       '/* #[cfg(feature = "proto")] /* nested */ mod b; */\n'}),
         nrun(), []),
        ("a narrowed run: a `//` inside a string does not hide a cfg after it",
         dict(p_file, **{"src/lib.rs": 'pub const U: &str = "http://x"; '
                                       '#[cfg(feature = "proto")] pub fn h() {}\n'}),
         nrun(), ["NARROWED RUN", "src/lib.rs:1"]),
        ("a narrowed run: cfg_attr's predicate is read, its attributes are not",
         dict(p_file, **{"src/lib.rs": '#[cfg_attr(feature = "proto", derive(Debug))]\npub struct S;\n'}),
         nrun(), ["NARROWED RUN", "src/lib.rs:1"]),
        ("a narrowed run: a cfg_attr whose predicate never flips is clean",
         dict(p_file, **{"src/lib.rs": '#[cfg_attr(all(feature = "proto", not(feature = "proto")), '
                                       'allow(dead_code))]\npub struct S;\n'}),
         nrun(), []),
        ("a narrowed run: an unreadable cfg naming its feature fails closed",
         dict(p_file, **{"src/lib.rs": '#[cfg(feature = "proto",,)]\npub fn h() {}\n'}),
         nrun(), ["NARROWED RUN", "src/lib.rs:1"]),
        ("a narrowed run: another test file naming its feature is a red",
         dict(p_file, **{"tests/q.rs": '#[cfg(feature = "proto")]\n#[test]\nfn t() {}\n'}),
         nrun(), ["NARROWED RUN", "tests/q.rs"]),
        ("a narrowed run: a shared tests/ helper naming its feature is a red",
         dict(p_file, **{"tests/common/mod.rs": '#[cfg(feature = "proto")]\npub fn h() {}\n'}),
         nrun(), ["NARROWED RUN", "tests/common/mod.rs"]),
        ("a narrowed run whose feature turns on another crate's is a red",
         {"tests/p.rs": '#![cfg(feature = "proto-dep")]\n'}, nrun("proto-dep"),
         ["NARROWED RUN", "other/x"]),
        ("a narrowed run whose feature turns on an optional dependency is a red",
         {"tests/p.rs": '#![cfg(feature = "proto-opt")]\n'}, nrun("proto-opt"),
         ["NARROWED RUN", "dep:y"]),
        ("a narrowed run of a crate with a build script is a red",
         dict(p_file, **{"build.rs": "fn main() {}\n"}), nrun(), ["NARROWED RUN", "build script"]),
        ("a narrowed run: a test-only helper already scanned under tests is unchanged",
         dict(p_file, **{"src/lib.rs": '#[cfg(test)]\n#[path = "../tests/support.rs"]\nmod support;\n',
                         "tests/support.rs": 'pub fn helper() {}\n'}), nrun(), []),
        ("a narrowed run: a test-only helper changing under the feature is red",
         dict(p_file, **{"src/lib.rs": '#[cfg(test)]\n#[path = "../tests/support.rs"]\nmod support;\n',
                         "tests/support.rs": '#[cfg(feature = "proto")]\npub fn helper() {}\n'}),
         nrun(), ["NARROWED RUN", "tests/support.rs"]),
        ("a narrowed run: a production feature path cannot use the test-only exemption",
         dict(p_file, **{"src/lib.rs": '#[cfg(any(test, feature = "proto"))]\n#[path = "../tests/support.rs"]\nmod support;\n',
                         "tests/support.rs": 'pub fn helper() {}\n'}), nrun(), ["NARROWED RUN", "outside src/"]),
        ("a narrowed run: a #[path] out of src/ is a red",
         dict(p_file, **{"src/lib.rs": '#[path = "../extra/x.rs"]\nmod x;\n'}), nrun(),
         ["NARROWED RUN", "outside src/"]),
    ]
    for name, files, runs, needles in cases:
        with tempfile.TemporaryDirectory(prefix="feature-gated-coverage.") as tmp:
            crate = Path(tmp) / "crates" / "demo"
            (crate / "src").mkdir(parents=True)
            (crate / "Cargo.toml").write_text(manifest)
            for rel, text in files.items():
                (crate / rel).parent.mkdir(parents=True, exist_ok=True)
                (crate / rel).write_text(text)
            try:
                got = gated_coverage_problems(Path(tmp), runs)
            except Exception as exc:  # a crash is a selftest failure, never a pass
                got = [f"CRASH {type(exc).__name__}: {exc}"]
                needles = needles or ["(no crash)"]
        text = "\n".join(got)
        want = [n for n in needles if not n.startswith("!")]
        absent = [n[1:] for n in needles if n.startswith("!")]
        if (not want and got) or (want and any(n not in text for n in want)) or \
                any(a in text for a in absent):
            errors.append(f"gated coverage: {name}: got {got or 'no problem'}; want {needles or 'none'}")
    demo_run = [Run("demo", "feat-a", 1, 1, False, "t")]
    row = ("slow.feature-gated-tests-demo|slow,release|soundness|true|never|python3 "
           "scripts/feature_gated_tests.py --crate demo\n")
    for name, harness, want in (("a crate with a RUN and no harness row", "# no rows\n", 1),
                                ("its row present", "# rows\n" + row, 0),
                                ("its row with a recorded last_green", row.replace("|never|", "|2026-10-28|"), 0),
                                ("a commented-out row is not its row", "# " + row, 1),
                                ("a row outside the slow profile is not its row",
                                 row.replace("slow,release", "release"), 1),
                                ("a row for another command is not its row",
                                 row.replace("--crate demo", "--crate other"), 1)):
        with tempfile.TemporaryDirectory(prefix="feature-gated-rows.") as tmp:
            (Path(tmp) / HARNESS_REL).parent.mkdir(parents=True)
            (Path(tmp) / HARNESS_REL).write_text(harness)
            got = harness_row_problems(Path(tmp), demo_run)
        if len(got) != want:
            errors.append(f"harness rows: {name}: got {got}; want {want} problem(s)")
    reads = [("all(feature = \"a\", any(unix, windows))", True), ("not(feature = \"a\")", False),
             ("any()", False), ("all()", True), ("target_pointer_width = \"32\"", False)]
    for text, want in reads:
        try:
            got_v = eval_cfg(parse_cfg(text), frozenset({"a"}))
        except CfgUnknown as exc:
            got_v = exc
        if got_v is not want:
            errors.append(f"cfg reader: {text!r} valued {got_v!r}, want {want}")
    for bad in ("all(feature = \"a\"", "feature = ", "not(a, b)", "a b"):
        try:
            parse_cfg(bad)
            errors.append(f"cfg reader: {bad!r} parsed; want a CfgUnknown")
        except CfgUnknown:
            pass
    stripped = strip_comments("a /* x /* y */ z */ b // c\n'\\'' \"//\" r#\"/*\"# d")
    if stripped.split() != ["a", "b", "'\\''", '"//"', 'r#"/*"#', "d"]:
        errors.append(f"strip_comments: got {stripped!r}")
    # base_command: the run's own targets and manifest, in place of `--tests`.
    probe = Run("demo", "proto", 1, 1, False, "t", ("--test", "p"), "crates/demo/Cargo.toml")
    cmd = base_command(probe)
    if cmd[-2:] != ["--test", "p"] or "--tests" in cmd or \
            cmd[cmd.index("--manifest-path") + 1] != "crates/demo/Cargo.toml":
        errors.append(f"base_command ignores the run's targets or manifest: {cmd}")
    for r in RUNS:
        cmd = base_command(r)
        if cmd[-len(r.targets):] != list(r.targets) or \
                cmd[cmd.index("--manifest-path") + 1] != r.manifest:
            errors.append(f"base_command({r.label}) is not the run's selection: {cmd}")
        if "--tests" not in r.targets and "--tests" in cmd:
            errors.append(f"base_command({r.label}) widens a narrowed run: {cmd}")
    return errors


def _selftest_runner() -> List[str]:
    """Drive the real RUNNER (as cargo would) over two fake executables: a
    passing one and one that hangs past the wall limit."""
    errors: List[str] = []
    with tempfile.TemporaryDirectory(prefix="feature-gated-selftest.") as tmp:
        root = Path(tmp)
        good, hang, records = root / "good", root / "hang", root / "records"
        records.mkdir()
        good.write_text("#!/bin/sh\nprintf '%s\\n' \"$(pwd -P)\" 'running 1 test' 'test a ... ok' ''"
                        " 'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; "
                        "0 filtered out; finished in 0.00s'\nexit 0\n")
        hang.write_text("#!/bin/sh\nexec sleep 30\n")
        for exe in (good, hang):
            exe.chmod(0o755)
        # The passing binary's limit is a one-minute hang detector, never a
        # latency budget: under host load a 30 s limit was seen to kill it.
        for exe, limit in ((good, "60"), (hang, "0.5")):
            proc = subprocess.run([sys.executable, "-S", "-c", RUNNER, str(records), limit,
                                   str(exe)], cwd=tmp, stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, check=False,
                                  env=dict(os.environ, DYLD_FALLBACK_LIBRARY_PATH="/x"))
            want = 0 if exe is good else 124
            if proc.returncode != want:
                errors.append(f"runner over {exe.name}: exit {proc.returncode}, want {want}")
        recs, bad = load_records(records)
        errors += bad
        if len(recs) != 2:
            return errors + [f"runner wrote {len(recs)} records, want 2"]
        g, h = recs
        art_g = Artifact(str(good), "test", "good", "")
        art_h = Artifact(str(hang), "test", "hang", "")
        if judge_binary(art_g, g, None).status != "PASS" or not g.dyld:
            errors.append(f"runner record of a passing binary judged wrong: {g}")
        if os.path.realpath((g.text.splitlines() or [""])[0]) != os.path.realpath(tmp):
            errors.append("the runner did not run the binary in cargo's working directory")
        if judge_binary(art_h, h, None).status != "TIMEOUT" or h.seconds > 15:
            errors.append(f"runner did not enforce the wall limit: {h}")
    return errors


def selftest() -> int:
    failures: List[str] = []
    n = 0
    cases = [c[:5] + ({}, MEASURED_HOST) + c[5:] for c in _selftest_cases()]
    cases += list(_selftest_cases_noop_host())
    for name, build, records, cargo_rc, allowed, noops, host, want, needles in cases:
        n += 1
        v = judge_run(_SELFTEST_RUN, build, records, cargo_rc, allowed, darwin=True,
                      noops=noops, host=host)
        got, text = _grade(v), _verdict_text(v)
        missing = [s for s in needles if s not in text]
        if got != want or missing:
            failures.append(f"{name}: got {got}, want {want}; missing {missing}\n{text}")
    canned = n
    n += 1
    msgs = [
        '{"reason":"compiler-artifact","target":{"kind":["lib"],"name":"x","src_path":"s"},'
        '"profile":{"test":true},"executable":"/t/x-1"}',
        '{"reason":"compiler-artifact","target":{"kind":["lib"],"name":"x","src_path":"s"},'
        '"profile":{"test":false},"executable":null}',
        '{"reason":"compiler-artifact","target":{"kind":["bin"],"name":"d","src_path":"s"},'
        '"profile":{"test":false},"executable":"/t/d"}',
        '{"reason":"compiler-artifact","target":{"kind":["test"],"name":"t","src_path":"s"},'
        '"profile":{"test":true},"executable":"/t/t-2"}',
        "warning: not json",
        '{"reason":"build-finished","success":true}',
    ]
    arts = parse_build_messages(msgs)
    if [a.target for a in arts] != ["lib:x", "test:t"]:
        failures.append(f"parse_build_messages: got {[a.target for a in arts]}, "
                        "want the two test-profile executables only")
    n += 1
    failures += _selftest_coverage()
    n += 1
    failures += _selftest_gated_coverage()
    n += 1
    failures += [f"runner: {e}" for e in _selftest_runner()]
    n += 1
    failures += _selftest_final_grade()
    n += 1
    failures += _selftest_prune()
    n += 1
    failures += _selftest_cache_placement()
    n += 1
    failures += [f"built inputs: {e}" for e in _selftest_built_inputs()]
    n += 1
    for run in RUNS:
        if run.min_binaries <= 0 or run.min_tests <= 0:
            failures.append(f"RUNS {run.label}: a floor of {run.min_binaries} binaries / "
                            f"{run.min_tests} tests disables that guard; floors are > 0")
        manifest = REPO_ROOT / "crates" / run.crate / "Cargo.toml"
        try:
            text = manifest.read_text(encoding="utf-8")
        except OSError as exc:
            failures.append(f"RUNS names {run.crate}, whose manifest is unreadable: {exc}")
            continue
        for feature in run.features.split(","):
            if not re.search(rf"^{re.escape(feature)}\s*=", text, re.M):
                failures.append(f"RUNS names feature {feature!r}, which {manifest} does not "
                                "declare (renamed? the run would fail to build, loudly)")
    for (crate, features, target), allow in ZERO_TEST_ALLOWED.items():
        if not allow.reason.strip():
            failures.append(f"ZERO_TEST_ALLOWED {crate} [{features}] {target} has no reason")
        if not any(r.crate == crate and r.features == features for r in RUNS):
            failures.append(f"ZERO_TEST_ALLOWED {crate} [{features}] {target} names no run")
        if allow.covered_by is not None and not any(
                r.crate == crate and r.features == allow.covered_by for r in RUNS):
            failures.append(f"ZERO_TEST_ALLOWED {crate} [{features}] {target}: covered_by "
                            f"[{allow.covered_by}] is not a configured run of {crate}")
    for (crate, features, target), noop in NO_OP_TESTS.items():
        if not noop.reason.strip() or not noop.tests or not all(t.strip() for t in noop.tests):
            failures.append(f"NO_OP_TESTS {crate} [{features}] {target}: no reason or no test")
        if not any(r.crate == crate and r.features == features for r in RUNS):
            failures.append(f"NO_OP_TESTS {crate} [{features}] {target} names no run")
    # The tree itself: every crate-level feature-gated test file has a lane, and
    # every crate with a RUN has its harness row.
    n += 1
    failures += gated_coverage_problems(REPO_ROOT, RUNS)
    n += 1
    failures += harness_row_problems(REPO_ROOT, RUNS)
    for f in failures:
        print(f"SELFTEST FAIL: {f}")
    if failures:
        print(f"FAIL: feature_gated_tests selftest: {len(failures)} of {n} checks failed")
        return 1
    print(f"PASS: feature_gated_tests selftest: {n} checks (the judge's {canned} canned "
          "runs, the build-message parser, the allowlist's covered_by check, the real "
          "runner, the final verdict line, log pruning and target ownership, the RUNS/allowlist/no-op tables, "
          "the built inputs and scratch directories (FGT-LANE-5), the gated-file coverage "
          "reader and this tree's coverage and harness rows)")
    return 0


# ---------------------------------------------------------------------------


def run_all(runs: Sequence[Run], env: Dict[str, str], target_dir: str, log_dir: Path,
            args: argparse.Namespace) -> List[Verdict]:
    """Build, run, judge and report each run in turn."""
    verdicts: List[Verdict] = []
    for run in runs:
        logdir = log_dir / re.sub(r"[^A-Za-z0-9_.-]", "_", run.label)
        logdir.mkdir(parents=True)
        build = do_build(run, env, target_dir, logdir)
        cargo_rc: Optional[int] = None
        records: List[Record] = []
        unjudged: List[str] = []
        if build.rc == 0 and build.artifacts:
            cargo_rc, records, unjudged = do_run(run, env, target_dir, logdir,
                                                 args.binary_limit, args.lock_wait)
        if cargo_rc is None and unjudged:
            # The RUN phase never started (the build lock refused, or a built input
            # is missing): nothing ran, so nothing is judged — not a NOT-RUN red
            # per binary.
            v = Verdict(run, [], [], unjudged, len(build.artifacts), 0)
        else:
            v = judge_run(run, build, records, cargo_rc, ZERO_TEST_ALLOWED,
                          darwin=sys.platform == "darwin", noops=NO_OP_TESTS,
                          host=this_host())
            v = v._replace(unjudged=v.unjudged + unjudged)
        report(v, ZERO_TEST_ALLOWED, NO_OP_TESTS)
        verdicts.append(v)
    return verdicts


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--crate", action="append", default=[],
                    help="run only this crate's runs (repeatable); default: every run")
    ap.add_argument("--list", action="store_true", help="print the runs; build nothing")
    ap.add_argument("--selftest", action="store_true", help="canned outputs; build nothing")
    ap.add_argument("--target-dir", help="dedicated compiler target; native ownership checks still apply")
    ap.add_argument("--binary-limit", type=float, default=DEFAULT_BINARY_LIMIT_S,
                    help=f"wall limit per test binary, seconds (default {DEFAULT_BINARY_LIMIT_S})")
    ap.add_argument("--lock-wait", type=int, default=DEFAULT_LOCK_WAIT_S,
                    help="seconds to wait for the build lock (default "
                         f"{DEFAULT_LOCK_WAIT_S})")
    args = ap.parse_args(argv)
    if args.selftest:
        return selftest()

    known = sorted({r.crate for r in RUNS})
    for crate in args.crate:
        if crate not in known:
            print(f"FAIL: --crate {crate}: no run configured (known: {', '.join(known)})",
                  file=sys.stderr)
            return 2
    runs = [r for r in RUNS if not args.crate or r.crate in args.crate]
    if args.list:
        for r in runs:
            print(f"{r.label}: {' '.join(base_command(r))}\n    floors {r.min_binaries} "
                  f"binaries / {r.min_tests} tests; build lock: "
                  f"{'measurement, RUN phase' if r.reads_build_tree else 'none'}\n    {r.why}")
            for item in r.inputs:
                sha = f" (SHA-256 in {item.sha256_env})" if item.sha256_env else ""
                print(f"    built input: {item.env}={item.path.format(host=this_host())}{sha}")
            for name in r.scratch:
                print(f"    scratch dir: {name} (fresh, outside the checkout, kept)")
            for (c, f, t), allow in sorted(ZERO_TEST_ALLOWED.items()):
                if c == r.crate and f == r.features:
                    print(f"    zero-test allowed: {t}: {allow.reason}")
            for (c, f, t), noop in sorted(NO_OP_TESTS.items()):
                if c == r.crate and f == r.features:
                    print(f"    no-op: {t}::{', '.join(noop.tests)}: {noop.reason}")
        print(f"floors, allowlist and no-op rows measured on {MEASURED_HOST}; "
              f"this host: {this_host()}")
        return 0

    problem = targo_problem()
    if problem:
        print(f"NOT JUDGED: {problem}", file=sys.stderr)
        return 2
    for s in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        signal.signal(s, _on_signal)

    target_dir = args.target_dir if args.target_dir is not None else str(REPO_ROOT / TARGET_DIR_REL)
    # The pid keeps two invocations started in the same second (the two rows run
    # by hand side by side) out of each other's log directories.
    stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()) + f"-{os.getpid()}"
    # A compiler target must first be created by its native owner, not by a
    # logger. Keep evidence separate even when an explicit target is refused.
    log_root = REPO_ROOT / LOG_DIR_REL
    # Resolve actual symlinks, then conservatively reject case-only aliases
    # even before either path exists on a case-insensitive filesystem.
    target_parts = tuple(p.casefold() for p in (REPO_ROOT / target_dir).resolve().parts)
    log_parts = tuple(p.casefold() for p in log_root.resolve().parts)
    if target_parts[:len(log_parts)] == log_parts or log_parts[:len(target_parts)] == target_parts:
        print(f"NOT JUDGED: target {target_dir!r} overlaps log directory {log_root}", file=sys.stderr)
        return 2
    log_root.mkdir(parents=True, exist_ok=True)
    prune_logs(log_root)
    # CARGO_INCREMENTAL=0 (cargo_env): measured 2026-10-09, the four runs'
    # incremental caches were 30G of a 71G target dir, for a lane that runs rarely
    # and whose path crates have mostly moved between two runs anyway.
    env = cargo_env(dict(os.environ))
    print(f"feature-gated tests: {len(runs)} run(s) on {this_host()} (floors measured on "
          f"{MEASURED_HOST}); target dir {target_dir}; logs {log_root / stamp}; wall limit "
          f"{args.binary_limit:.0f}s per binary")

    started = time.time()
    try:
        verdicts = run_all(runs, env, target_dir, log_root / stamp, args)
    except SystemExit as stop:  # _on_signal: the children are already signalled
        print(f"\nNOT JUDGED: feature-gated tests interrupted (exit {stop.code}) after "
              f"{time.time() - started:.0f}s; nothing after the interrupt was judged",
              flush=True)
        raise
    covered = coverage_problems(verdicts, ZERO_TEST_ALLOWED)
    for p in covered:
        print(f"RED: {p}")
    rc, line = final_grade(verdicts, covered, time.time() - started)
    print(f"\n{line}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
