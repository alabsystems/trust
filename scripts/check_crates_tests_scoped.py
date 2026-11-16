#!/usr/bin/env python3
"""Trust: run the `crates/` tests of the crates a push touches.

WHY THIS EXISTS (TRUST-16). Until this lane, NO push-profile row ran a single
`crates/` test. `scoped.compiler-check` type-checks them (`x.py check --stage 1`
compiles test targets), but a test that compiles and FAILS is green there, and
every other push row is a drift or pin check that compiles nothing. The measured
cost of that hole: trust-router's `native_lane_logic_tests::
no_feature_set_loses_a_verdict_to_the_parser` (TRUST-13) went red on `main` and
stayed red, because it lives in a module compiled only under
`--features ay-backend` — `trust-router` has `default = []`, so the ladder's own
per-crate spelling `targo test -p trust-router` compiles none of the ay-backend
modules and reports green.

WHAT IT RUNS. The subject is the diff being PUSHED, and a `SUBJECT (...)` line
names which reading ran:
  * `--push-context` reads TRUST_PUSHED_REFS (scripts/hooks/pre-push exports
    one "<local-ref> <local-sha> <remote-ref> <remote-sha>" line per update):
    the union over every update of the TREE diff `<remote-sha>..<local-sha>`,
    each new branch's `origin/main...<local-sha>`, and nothing for a deletion;
  * `--range A..B` (or `A...B`): `A...B`, the changes since the merge base;
  * otherwise, or when TRUST_PUSHED_REFS names no update: `origin/main...HEAD`.
See resolve_ranges for why an update is two-dot and a new branch three-dot.
Every changed path under `crates/` is attributed to the `crates/`-workspace
member that owns it (from `targo metadata --no-deps`, not from directory
names), and then:

  1. ONE invocation for all touched members, default features:
       targo --unverified test -Zfeature-unification
             --config 'resolver.feature-unification="selected"'
             --manifest-path Cargo.toml --locked --no-fail-fast -p A -p B ... --tests
     The words after the verb (MEMBER_FEATURE_SCOPE, on every Targo
     build and test here) keep the features to the ones the selected members
     ask for, as Cargo's default does, whatever a wrapper or config says.
     `--tests` = lib unit tests + bins + `tests/*.rs`. Doctests, examples and
     benches are NOT run.
  2. For each touched member listed in FEATURE_RUNS, its extra feature lane(s),
     because `--all-targets`/`--tests` select TARGETS, never FEATURES
     (docs/VALIDATION_LADDER.md rung 1). Today: trust-router's ay-backend lib
     tests, the TRUST-16 trap, its ay-certify,trust-build,trust-cg-backend,
     carcara-crosscheck lib tests, and its ay-backend setter_assert_refute_lane
     integration target in a separate target directory; and one `--lib` tail
     each for trust-lift (ay-verify), trust-vc-bridge (trust-build),
     trust-strengthen (trust-wp),
     trust-types (ay-bridge-solve,trust-wp-bridge), trust-bmc
     (trust-build, the shipped set, since 2026-10-09), trust-decompile
     (trust-cg) and trust-wp (trust-build): lib tests no push lane ran before
     2026-10-01 (trust-decompile's trust-cg code was already compiled, as a
     dependency of the targo-trust prebuild, but its tests were not).
  3. A touched crate that is its own `[workspace]` root under `crates/` (today
     `trust-process-isolation`, `trust-spec-temporal` and `trust-worker-linux`,
     the last Linux-only: its test targets do not compile on macOS) runs
     against its own manifest.
  4. Each CROSS_CRATE_INSTRUMENTS entry whose subject the push moves, unless the
     push touches its host member (then run 1 tests the host; a host only
     --also-members adds keeps its instrument run, and its instrument rules,
     2026-11-02): an instrument test that lives in one
     member and measures another's output (2026-09-30; the missing-obligation
     ratchet, which went red on `main` from a trust-vcgen-only change;
     2026-10-09, trust-model-prelude's
     source digest, `tests::digest::`, which hashes the Clean files under
     `crates/trust-spec-temporal/clean/Trust/`, B1A-D35; and, 2026-10-09,
     trust-integration-tests' clean_proof_obligations, which reads two Clean
     proof files under proofs/ and trust-cg-bridge's verify_output.rs and
     judges with trust-certify's clean_island); and binary_to_trust_ir_e2e when
     its checked-in tests/fixtures/binary_decomp/ inputs move. An instrument run
     must REPORT at least one test, and each test INSTRUMENT_REQUIRED_PASSES
     names for its host must print `test <name> ... ok` (2026-10-09, B1A-14a):
     a filter that matched nothing exits 0 having judged nothing.
  5. Each CORPUS_INSTRUMENTS entry whose subject the push moves, on the same
     terms: a gate whose subject is every checked-in document of one format,
     wherever it lives (2026-10-08; trust-json's acceptance gate for any
     `*.json`, trust-toml's corpus differentials for any `*.toml`, outside
     `first-party/` and `vendor/`). Such a push runs this lane even when it
     changes nothing under `crates/`; so does one that moves only a
     CROSS_CRATE_INSTRUMENTS subject outside `crates/`
     (`proofs/codegen-equivalence/`, `proofs/trust-soundness/`).

Before any of them, when a member in TARGO_TRUST_CONSUMERS is touched, or a
TARGO_TRUST_INSTRUMENTS target is selected (today
trust-integration-tests, whose binary_to_trust_ir_e2e and scale_fixture_crate
tests run targo-trust, read its path from TRUST_TARGO_TRUST_BIN, and fail
without it), the lane builds targo-trust from the tree under test:
       targo --unverified build --manifest-path targo-trust/Cargo.toml
             --bin targo-trust --locked --message-format json-render-diagnostics
takes the path from cargo's compiler-artifact message for that bin, copies the
file into a private temporary directory (an APFS clone on macOS, `cp -c`: no new
disk for a ~200 MB binary), and exports TRUST_TARGO_TRUST_BIN=<the copy> to the
record pass, so cargo hands it to every recorded test binary. The copy, not the
target dir's file, is what runs: a sibling build relinking the shared target
dir's targo-trust mid-run cannot swap the binary under test. A failed build
fails the lane; it never skips the tests. Its output (cargo's text, and any
stdout line that is not cargo's JSON) is shown only when it fails. Untouched, nothing is built; a push that changes targo-trust/ and no
consumer prints a NOT RUN line naming the tests this lane did not run.
Targo and the developer libraries share the root workspace. The pre-push hook
defaults direct builds to the pushing worktree's crates/target, matching the landing gate;
either explicit CARGO_TARGET_DIR or native TARGO_TARGET_DIR is preserved.
A direct invocation without a target override still uses targo-trust/target
by default. Every build comes out of the one budget below.
It is part of the BUILD phase: it runs before the record pass, so before the
barrier below, and it runs no test and no verifier (`--unverified`). Like
every process the lane starts it is spawned in a session of its own and
tracked (_spawn), so an interrupt reaches it, and its private directory is
removed on every exit, an interrupt's included.

WHAT IT DOES NOT SEE — printed on every run, never summarised away:
  * reverse dependencies: `-p X` tests X, never X's callers, except the
    instruments CROSS_CRATE_INSTRUMENTS and CORPUS_INSTRUMENTS name;
  * the three rustc_private crates outside developer default-members (trust-mir-extract,
    trust-thir-lower, trust-witness): root-workspace members, type-checked by
    `scoped.compiler-check`, tested only by `x.py test --stage 1 crates/<name>`;
  * a `Cargo.toml`/`Cargo.lock` change or a `first-party/` pin
    move, which can move every member's graph: this lane tests only members
    whose own files changed;
  * non-default feature lanes not in FEATURE_RUNS.

TEST BINARIES RUN IN PARALLEL (2026-09-29). Cargo runs one invocation's test
binaries one after another, so the lane's wall time was the SUM of every
binary's (measured on the 2026-09-29 landing pushes: 1008s for trust-certify +
trust-clean + trust-router, of which trust-clean's lib alone was 322s). Each
planned command is now run once as a BUILD-AND-RECORD pass: the same `targo
--unverified test ...` with cargo's own `target.<cfg>.runner` hook pointed at
RECORDER, which saves the argv, working directory and environment cargo hands
each test binary and runs nothing. Then every recorded
binary, from every command, runs in one pool of TRUST_CRATES_TESTS_JOBS
processes (default_jobs(): sized from cores and memory, at most 4). In a
build-slot job, the admitted CARGO_BUILD_JOBS share is divided across this
configured pool before Cargo records any binary: RUST_TEST_THREADS is at most
share // pool size, preserving a smaller inherited value. A pool override
larger than the share, invalid managed inputs, or a record that loses this
choice refuses. RUN_ALONE retains this conservative recorded allowance too;
replay never rewrites a binary's environment. This bounds configured libtest
workers, not arbitrary threads a test starts or total OS CPU. Unmanaged runs
keep their existing environment. Every binary still runs with
exactly the argv, directory and environment cargo would have used — recorded,
not re-derived, so DYLD_FALLBACK_LIBRARY_PATH, CARGO_PKG_*, CARGO_MANIFEST_DIR
and whatever Targo adds are cargo's own. Nothing about what runs changes: the
same binaries, `--no-fail-fast`, the same per-command known-red judgement over
the same `Running (...)`/`test ... ok|FAILED` text, one budget. A binary named
in RUN_ALONE runs after the pool drains, with nothing beside it; one executable
recorded by two commands never runs twice at once. TRUST_CRATES_TESTS_JOBS=1
runs the binaries one at a time.

What the pool adds is each binary's own exit code, and binary_problem() holds
every binary to libtest's contract, which cargo's single exit code could not:
a binary that exits other than 0/101, or without libtest's closing `test
result:` line, or counts more failures there than the lane could read, died
mid-run or hid a failure, and fails the lane even when a known-red failure in
its output (or another binary's) would have excused cargo's exit 101. So does a
non-zero exit from the build-and-record pass, which runs no test.

BOUNDED TIME (CRATES-TIME-1, 2026-10-28: scripts/lib/crates_tests_time.py, the
one rule for the hook and the land gate alike). The lane has two bounds, both
from that module, over the crates it is asked to test (TimeBound): it stops when
nothing it runs has progressed for TRUST_CRATES_TESTS_STALL_S (default 1800 s;
progress is a line of output from a test binary while it runs, a binary
ending, an executable carried through macOS's first-exec check; a build, which
can be silent for long on a loaded host or behind cargo's lock, is bounded by the
ceiling alone, and the stall clock starts again when it ends), and in any case
after its ceiling, max(14400, 900 s x crates), which TRUST_CRATES_TESTS_BUDGET_S
replaces. Until 2026-10-28 it had a flat 1200 s, which three pushes of one
3-member change ran out of on a loaded host while the same tree's land gate leg
(its own 240 s x 36 members) passed: a fixed total is a latency budget, since most
of a binary's wall time here is outside libtest's clock (below). When either bound
runs out every running cargo or test binary is killed and the lane exits 3, NOT
JUDGED, naming which bound and what it did not run. A hung binary still ends the
lane that way, the stall bound after the last progress (a line printed by a
process the lane is still waiting for, not by one a finished binary left behind). It never
turns an unrun test into a pass. The lane waits for each process, never for EOF
on its output, so a daemon a test leaves holding that output open costs
OUTPUT_GRACE_S, not the budget, and cannot hold the lane past either bound by more
than a kill's grace. A docs-only push pays nothing.

ONE AT A TIME THROUGH MACOS'S FIRST-EXEC CHECK (2026-10-09). macOS holds a
newly linked executable at its first exec until syspolicyd clears it (unless
the process's responsible app is listed under Privacy & Security > Developer
Tools; aterm is not). The hold is in the kernel, before dyld or any of the
program runs (the process sits at 32 KB resident, no CPU), outside libtest's
`finished in` clock, and the whole host shares one serial queue. What one
clearance costs depends on the binary's size (a fresh 320 MB test binary
4.0-4.4s through a hard link from a two-entry directory; a 1.7 MB one
0.2-0.3s from an empty directory) and on the DIRECTORY it is exec'd from (the
1.7 MB one ~5s from a directory of 600k entries; measured 2026-10-09 on an
idle host). crates/target/debug/deps held 1.16M entries, and during the
2026-10-09 landing push's pool the queue released one binary every 39s,
whatever its size, with all four workers often parked in it at once
(observed live; syspolicyd's I/O wait and the host's load were seen, not
recorded). On four 2026-10-08/09 landing pushes 88-95% of the pool's binary
wall time was outside libtest's clock (r2-3: 38358s of binary wall time
against 4343s of libtest time, a ~146s median for binaries whose tests took
under 2s; the lane 157-197 min). That gap also holds process start and image
load; the live observation puts most of it in the first-exec hold.

So a worker starts a binary only once Admission has carried its executable
through the check: one at a time, in the pool's order, on a thread of its
own, ahead of the workers (admit_one). The probe execs a HARD LINK to the
executable made in a private directory of two entries (the same file, so the
clearance is the file's, and the binary at its own path then starts at once,
measured 0.01s; the link is removed after), with DYLD_INSERT_LIBRARIES naming
a FIFO nobody writes. dyld starts only after the check, prints
(DYLD_PRINT_SEARCHING) that it is about to open that library, and blocks on
the FIFO before it runs any initializer; the line is the proof, and the probe
is SIGKILLed (no crash report) with none of the program run. admissible()
lets only a thin Mach-O executable, not setuid, without __RESTRICT, with one
CodeDirectory that is ad hoc or linker-signed and nothing more, and not a
platform binary, be probed, so dyld cannot ignore the variables and run it.
A probe that prints anything but dyld's lines, ends on its own, has not
parked ADMIT_PROBE_MAX_S after it started or ADMIT_DYLD_MAX_S after dyld's
first line, or is not reaped after its SIGKILL, stops all admission, and
every binary after it pays the check itself, as before; so does an error in
admission itself. What runs, and how it is judged, is unchanged: the same
binaries at the same paths, with the same argv, directory and environment,
the same pool of TRUST_CRATES_TESTS_JOBS, the same budget, barrier and
verdict rules. A binary's wait for admission is lane time under the one
budget, no longer counted in its `--- exit 0 in Ns`.
TRUST_CRATES_TESTS_ADMIT=0 turns it off (only "0"); off macOS it does nothing.
The residual risk is the guard itself: should dyld ever ignore DYLD_* for a
binary admissible() passes, the probe would run that program once, with the
probe's argv, the scratch directory and a DYLD_*-only environment, until its
first output line; a `harness = false` target (trust-platform's) ignores the
`--list --exact` argv that makes a libtest one run nothing. The probe is then
killed, admission stops, and the gate log says the binary may have run.

A BARRIER BETWEEN BUILDING AND RUNNING (2026-09-30). With
TRUST_CRATES_TESTS_RUN_AFTER=<path> set, the lane builds and records as above,
then WAITS, before it starts any test binary, until <path> exists, and runs the
binaries only if the file says `run`; any other content is a stop, which exits
3, NOT JUDGED, with no binary run. scripts/hooks/pre-push sets it when it
overlaps this lane's build with the scoped lanes before it (the hook's header,
"CRATES-TESTS' BUILD OVERLAPS THE LANES BEFORE IT"): some of these tests run
build/<host>/stage1, which `scoped.compiler-check` rebuilds, so no binary may
start before that lane has finished. The wait is printed with its length and is
NOT charged to the budget: the deadline moves by exactly the time waited. A
barrier that never comes cannot hold the lane forever: with
TRUST_CRATES_TESTS_RUN_AFTER_OWNER=<pid> (the hook's), the lane stops, NOT
JUDGED, once that process is gone, and in any case after
TRUST_CRATES_TESTS_RUN_AFTER_MAX_S (default DEFAULT_RUN_AFTER_MAX_S). Unset,
nothing waits: the lane is exactly what it was.

INTERRUPTS REACH WHAT IT STARTED. cargo (the targo-trust build's and the
record passes'), the `cp -c` that copies targo-trust on macOS, and every test
binary run in sessions of their own (so a deadline can kill each whole), which a terminal's or a
hook's group-directed signal does not reach. So an INT, TERM or HUP to the lane
is forwarded to each of those groups (KILL after KILL_GRACE_S), the lane's
scratch directories (the records, the targo-trust copy) are removed once
they are gone, and the lane exits 128+signal, NOT JUDGED. A signal the lane
inherited as ignored stays ignored. Starting a process and recording it is one
step a signal cannot split (_spawn), so a process forked just as the signal
came is reached too; so is making a scratch directory and recording it
(_scratch_dir).

KNOWN RED (a ratchet, not a mask). A touched crate can carry failures that
are already red on `main`; failing every push on them would make this lane
unusable, and a whole-lane quarantine would hide NEW failures. So each run's
output is parsed per test binary (`<binary>::<test path>`), and:
  * a failure listed in tests/known-red/crates-tests.txt is reported, not failed;
  * a failure NOT listed fails the lane;
  * a listed test that RAN AND PASSED fails the lane too, until its row is
    deleted (rows tagged `[flaky]` are exempt: load-sensitive tests that may do
    either);
  * a non-zero exit with no parsed test failure (a compile error, a crash) fails,
    and so does a binary that broke libtest's contract (binary_problem): no
    known-red row excuses a run that stopped before it reported every test.
Each row carries its reason and owner, so the file is the to-do list.

ZERO TESTS IS NOT A PASS (2026-10-09). libtest exits 0 on `running 0 tests`,
so a touched crate whose tests a feature compiles out printed PASS here while
judging nothing: trust-ny-bridge (all 28 tests behind `ny`) did on every push
that touched it. After every run is judged, the lane adds up what each touched
crate's binaries REPORTED (passed + failed on libtest's closing line; a
`harness = false` binary is one test, its exit code the verdict), over all its
runs: a member's binaries in the default run and in its FEATURE_RUNS tails,
an own-workspace crate's in its own run. A crate whose total is 0 makes an
otherwise green lane exit 3, NOT JUDGED, naming it. The rule is per crate,
never per binary: bin targets and helper files report `running 0 tests` as a
matter of course. It cannot tell a crate with no test code from one whose test
code is compiled out (libtest prints the same line for both) and fires on
both: neither was judged (docs/DECISION_QUEUE.md, 2026-10-09).

Usage:
  check_crates_tests_scoped.py [--push-context | --range A..B] [--plan]

Exit codes:
  0  every planned run passed and every touched crate reported a test, or
     nothing under crates/ is in scope
  1  a planned run failed (a test, or a compile error, targo-trust's included)
  2  could not judge: a range git cannot diff (never read as "no changes"),
     an --also-members dir that is no member of this lane (scripts/land_gate.py
     would otherwise store a PASS for a crate nothing ran),
     no real targo, metadata failure, a targo-trust build that names no binary,
     a targo-trust that cannot be copied, a recorded consumer test binary whose
     environment lacks the copy's TRUST_TARGO_TRUST_BIN
  3  out of time (a stall or the budget, BOUNDED TIME; targo-trust's build
     included), the barrier stopped
     the lane or never came, or a touched crate's runs reported no test
     (ZERO TESTS IS NOT A PASS): NOT JUDGED
  128+N  interrupted by signal N (forwarded to everything it started): NOT JUDGED

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import contextlib
import json
import math
import os
import signal
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple, Union

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
import crates_tests_time  # noqa: E402  (the one time-bound rule, shared with scripts/land_gate.py)
import crates_lane_members  # noqa: E402  (the one own-workspace rule, shared with scripts/lib/land_select.py)

CRATES_MANIFEST = "Cargo.toml"
KNOWN_RED_REL = "tests/known-red/crates-tests.txt"

# The words every Targo build or test this lane runs carries right after its
# verb, so `-p X` builds X with the features the selected packages ask for,
# as Cargo's default does, whatever the environment says
# (TARGO-MEMBER-FEATURE-SCOPE-1). Cargo reads `resolver.feature-unification`
# only under `-Zfeature-unification`, and a wrapper or a config file can set
# it: aterm's atpkg `targo` shim, since aterm a1679bf032 (2026-11-06), puts
# `--config resolver.feature-unification="workspace"` before the verb of every
# `--unverified` test, bench and dev build it starts under $HOME, unless the
# target directory is under a `.noindex` path or the call names
# `-Zfeature-unification` itself. Over the root workspace that is the
# compiler's features too: rustc_mir_transform's `trust-ir-bridge/
# compiler-context` pulls 38 compiler units (rustc_macros first, whose build
# script refuses to run outside bootstrap) into `-p trust-vcgen --tests`, 757
# units in all where Cargo's selection has 538. The flag must follow the verb
# (a `-Z` before it is replaced by any after it, such as `--unit-graph`'s
# `-Zunstable-options`), and the `--config` follows it, so it is read after
# any one put before the verb (the later value wins).
MEMBER_FEATURE_SCOPE = ["-Zfeature-unification", "--config", 'resolver.feature-unification="selected"']

# Feature lanes a default-feature `--tests` run cannot reach, per member. Each
# entry is the argument tail after `-p <member>`. The regression test
# (scripts/tests/check_crates_tests_scoped_test.py) checks every feature named
# here still exists in that member's Cargo.toml, so a rename fails loudly
# instead of quietly running the default lane twice.
FEATURE_RUNS: Dict[str, List[List[str]]] = {
    # TRUST-16: every ay-backend module (in_process_ay_backend.rs, the
    # smt2_self_consistency_tests at lib.rs) is `#[cfg(feature = "ay-backend")]`.
    # router_tests.rs also has `#[cfg(not(feature = "ay-backend"))]` tests, so the
    # default run in step 1 is not redundant with this one.
    #
    # The second trust-router tail's features are a superset of the first's
    # (ay-certify implies ay-backend; trust-build implies trust-vc-native), and
    # it still does not replace the first. Only the first compiles the
    # ay-backend code behind `not(feature = "carcara-crosscheck")` (the default
    # expectation arms inside tests, which expect Proved) and behind
    # `not(feature = "ay-certify")` (whole items in in_process_ay_backend.rs,
    # the test recognized_lia_stays_smtbacked_without_clean_payload_transport
    # among them). It adds ay_certify.rs, carcara_cross_check.rs and its gate,
    # trust_cg_backend.rs and the trust-vc-native full_verification paths:
    # 1104 tests on 2026-09-30 (1130 at 59ed95327d), once five carcara expectation arms
    # (docs/issues/2026-10-01-ay-alethe-hole-rule-blocks-carcara-for-datatype-and-skolem-refl.md)
    # and a timing bug in one full_verification test were fixed.
    "trust-router": [
        ["--features", "ay-backend", "--lib"],
        ["--features", "ay-certify,trust-build,trust-cg-backend,carcara-crosscheck", "--lib"],
        # The default run compiles this file's ay-backend tests out. Cargo also
        # builds trustd for an integration target: isolate its output so this
        # feature build cannot replace the default run's CARGO_BIN_EXE_trustd
        # before the recorded trustd_process tests execute.
        ["--features", "ay-backend", "--test", "setter_assert_refute_lane", "--target-dir",
         "crates/target-scoped-feature-tests.noindex/trust-router-ay-backend"],
    ],
    # The rest were dormant: no push lane compiled them (measured green
    # 2026-09-30, with the lib test counts given).
    # validation.rs, translation validation of lifted code through ay: 241 tests.
    "trust-lift": [["--features", "ay-verify", "--lib"]],
    # the native trust-vc engine paths and trust_ir_adapter_request.rs: 105.
    "trust-vc-bridge": [["--features", "trust-build", "--lib"]],
    # trust_wp_oracle.rs, the trust-wp/trust-vcgen strengthening oracle: 930.
    "trust-strengthen": [["--features", "trust-wp", "--lib"]],
    # ay_bridge.rs with its solving tests (ay-bridge-solve implies ay-bridge)
    # and trust_wp_bridge.rs: 1781.
    "trust-types": [["--features", "ay-bridge-solve,trust-wp-bridge", "--lib"]],
    # verifier_api.rs and replay_oracle.rs, the trust-mc CHC/PDR solver path,
    # in the configuration the compiler ships: `trust-build` is
    # trust-mc-core-types plus trust-mc-native-trust-ir-bundle, which implies
    # trust-mc-native-solver, and both rustc_mir_transform (via trust-router's
    # trust-build) and targo-trust (trust-mc-in-process) turn the bundle on.
    # Until 2026-10-09 this tail stopped at
    # trust-mc-core-types,trust-mc-native-solver (156 tests) and compiled out
    # the 52 tests gated on the bundle: the receipt and claim-binding refusals,
    # the unknown-offset soundness falsifier, and the refutation-scope
    # regression for d7e6d7cc1d. No trust-bmc test is gated on not(bundle), so
    # this set is a superset of that one (each of the 156 still runs). Measured
    # 2026-10-09 at load average 10-30: 208 tests in 38s of test time (2.7s
    # before), and 10s of build on a target dir that had built the old tail.
    "trust-bmc": [["--features", "trust-build", "--lib"]],
    # the trust-cg-bridge conversion paths; targo-trust ships this build: 148.
    "trust-decompile": [["--features", "trust-cg", "--lib"]],
    # native.rs's trust_build_tests and the native verifier_api paths, measured
    # 2026-10-01: 108 tests, once cli.rs's two timeout tests stopped failing
    # under load (their bound) and began to test the kill (their script).
    "trust-wp": [["--features", "trust-build", "--lib"]],
}
# A tail sharing the default target directory builds `--lib` only. An explicit
# feature integration target uses its own target directory; the regression test
# holds both shapes. All record passes build before any binary runs, so a later
# feature build must not replace a default-feature CARGO_BIN_EXE_<bin> executable.

# Instruments whose SUBJECT is another crate's output. `-p X` never runs the
# tests of X's callers, and that is how the missing-obligation ratchet stayed red
# on `main` (found 2026-09-30): it lives in trust-ir-bridge, it compares the
# spine against trust-vcgen's VCs over the trust-clean fixture corpus, and
# `1f3b181649` changed trust-vcgen ALONE, so the run its push planned was
# `-p trust-vcgen` and nothing reached the ratchet. Each entry is (path prefixes
# that move the instrument's subject, the member hosting it, the argument tail
# after `-p <member>`). An instrument tail builds `--lib` only and
# selects the instrument by test-path prefix; the regression test checks the
# prefix still names a module holding at least one `#[test]`, because a filter
# that matches nothing runs zero tests and reads `ok`. A host member the push
# also touches is already in run 1, whose `--tests` covers the instrument, so it
# is not run twice. A host only --also-members adds still runs it (plan_for).
# These instruments run a targo-trust consumer target. Keep selection and its
# private-binary prebuild dependency together; library-only instruments hosted
# by the same crate do not need the CLI.
TARGO_TRUST_INSTRUMENTS: List[Tuple[Tuple[str, ...], str, List[str]]] = [
    (
        ("tests/fixtures/binary_decomp/",),
        "trust-integration-tests",
        ["--test", "binary_to_trust_ir_e2e"],
    ),
]

CROSS_CRATE_INSTRUMENTS: List[Tuple[Tuple[str, ...], str, List[str]]] = [
    *TARGO_TRUST_INSTRUMENTS,
    (
        ("crates/trust-vcgen/", "crates/trust-types/", "crates/trust-clean/fixtures/"),
        "trust-ir-bridge",
        ["--lib", "--", "flip::missing_obligation_ratchet::"],
    ),
    # trust-model-prelude's source digest (2026-10-09, Beyond-TLA B1a, B1A-D35):
    # the crate `include_str!`s the Trust/*.lean files trust-spec-temporal
    # kernel-checks and exports PRELUDE_DIGEST over their bytes, so its subject is
    # another crate's files. A push that edits Temporal.lean or FiniteModel.lean
    # alone plans only trust-spec-temporal's own workspace, and nothing would
    # notice the digest go stale. `tests::digest::source_digest_matches` is a
    # debug-cheap SHA-256 over the sources; the fix is one re-bless command,
    # `--ignored --exact tests::digest::print_source_digest`.
    (
        ("crates/trust-spec-temporal/clean/Trust/",),
        "trust-model-prelude",
        ["--lib", "--", "tests::digest::"],
    ),
    # trust-integration-tests' Clean proof obligations (2026-10-09): the
    # in-process check that proofs/codegen-equivalence/g16_multiplier_equivalence.lean
    # and proofs/trust-soundness/i128_mul_corner_bounds.lean still prove the
    # theorems their `clean`-binary gates name (the load-bearing ones with their
    # statements pinned), and that trust-cg-bridge's
    # MAX_RECHECKABLE_MUL_WIDTH (src/verify_output.rs, read as text) stays 8 while
    # G16Mul.ay_blast_agrees is unproved. Before it, only binary gates asserted
    # those, and they passed with a NOTICE when no binary was found; a push
    # touching only a proof (outside crates/) planned nothing, and one touching
    # only the cap ran only trust-cg-bridge's tests, none of which checks it.
    # `crates/trust-certify/src/clean_island` (clean_island.rs,
    # clean_island_batch.rs, clean_island/) is the checker the tests judge with:
    # its strict island policy and `audit_cited_theorem`, whose refusals the red
    # controls pin. Cost, measured 2026-10-09: a push that needs it builds this
    # lib test binary and its normal dependencies (trust-router, trust-lift,
    # trust-symex, ...): 4m19s from an empty target dir at load ~8 (9m41s at
    # load ~17 in a review), ~13s of it tests, most of those the G16 file's
    # kernel check; 14s when nothing needs rebuilding.
    (
        (
            "proofs/codegen-equivalence/",
            "proofs/trust-soundness/",
            "crates/trust-cg-bridge/src/",
            "crates/trust-certify/src/clean_island",
        ),
        "trust-integration-tests",
        ["--lib", "--", "clean_proof_obligations::tests::"],
    ),
]

# What an instrument run must show it judged (2026-10-09, Beyond-TLA B1a, B1A-14a,
# the M0 review's finding 7). libtest exits 0 on `running 0 tests`, and the
# zero-test rule (tests_reported) credits no member for an instrument run, so a
# tail whose filter matched nothing (a renamed module, one a cfg compiles out, an
# #[ignore]d test) passed having checked nothing. Every instrument run must report
# at least one test (instrument_problem), and the tests named here for its host
# must each print `test <name> ... ok`: the source digest is the D35 seam's only
# push-time check, so its own test must have run and passed.
INSTRUMENT_REQUIRED_PASSES: Dict[str, Tuple[str, ...]] = {
    "trust-model-prelude": ("tests::digest::source_digest_matches",),
}

# Instruments whose SUBJECT is every checked-in document of one format, wherever
# it lives (2026-10-08). trust-json's acceptance gate and trust-toml's corpus
# differentials parse each tracked `*.json` / `*.toml` outside `first-party/` and
# `vendor/`, pinned by path in their tests/corpus_manifest.txt, and fail when the
# tree and the pin differ in either direction. Those documents belong to every
# member and to none (fixtures, reports, every Cargo.toml), so no prefix names
# the subject, and until this table a push that added one planned neither gate:
# main went red on unpinned documents four times (trust-json 40 at 14ea013bfe,
# 13 and trust-toml 4 at f99836cc18, trust-json 27 at c9e3451867, trust-json 563
# at the 2026-10-08 re-pin), each found by someone else. Each entry is (the path
# suffix, the prefixes the manifest's own rule excludes, the member hosting the
# gate, the argument tail after `-p <member>`). The tail names, by `--test`,
# every test target of the host that reads tests/corpus_manifest.txt, and the
# regression test holds it to that set; a `--test` tail builds the lib and those
# targets, and the hosts have no bin target an integration-test build would
# rebuild. A host the push also touches is already in run 1.
CORPUS_INSTRUMENTS: List[Tuple[str, Tuple[str, ...], str, List[str]]] = [
    (".json", ("first-party/", "vendor/"), "trust-json", ["--test", "acceptance_gate"]),
    (
        ".toml", ("first-party/", "vendor/"), "trust-toml",
        ["--test", "differential_corpus", "--test", "serialize_differential"],
    ),
]

# Test binaries that must not share the machine with the pool, keyed as
# parse_results keys a binary (its file name without cargo's hash). They run
# one at a time after the pool drains. The regression test checks each still
# names a test target under crates/. Declare a binary here rather than mask its
# test: a [flaky] known-red row excuses every failure of that test.
RUN_ALONE: Dict[str, str] = {
    # trust-clean: test_clean_kernel_rejects_wrong_proof_for_vc asserts the
    # kernel rejects a wrong proof AND does so in under 5000 ms; at 8 jobs on
    # 2026-09-29 the second half missed. 3-4s alone.
    "clean_pipeline_integration": "a wall-clock assertion that missed under the pool's load",
}

# Members whose tests run the targo-trust binary TRUST_TARGO_TRUST_BIN names and
# fail without it. Until 2026-09-30 they searched the target dirs instead, and a
# search that found nothing returned early, which libtest counts as a pass; one
# that found something ran whatever tree had built it (docs/issues/
# 2026-09-29-binary-to-trust-ir-e2e-golden-stale-and-passes-without-its-binary.md,
# defect 2). The regression test checks that every crates/ file naming the
# variable belongs to a member listed here, so a new consumer cannot go unbuilt.
TARGO_TRUST_CONSUMERS = ("trust-integration-tests",)
TARGO_TRUST_VAR = "TRUST_TARGO_TRUST_BIN"
# --locked: Cargo.lock is used as it is, never updated. (The lane builds the
# working tree, uncommitted edits included, as it does every test it runs.) The
# JSON messages go to stdout and the human text to stderr, so the lane reads the
# path cargo itself reports, and holds the text until a failure needs it.
TARGO_TRUST_BUILD = [
    "targo", "--unverified", "build", *MEMBER_FEATURE_SCOPE, "--manifest-path", "targo-trust/Cargo.toml",
    "--bin", "targo-trust", "--locked", "--message-format", "json-render-diagnostics",
]

# Compiler-private members outside developer default-members, with
# the lane that DOES reach them. Kept literal so the disclosure names a command.
EXCLUDED_ELSEWHERE: Dict[str, str] = {
    "trust-mir-extract": "x.py test --stage 1 crates/trust-mir-extract",
    "trust-thir-lower": "x.py test --stage 1 crates/trust-thir-lower",
    "trust-witness": "x.py test --stage 1 crates/trust-witness",
}


def git(*args: str) -> str:
    # UTF-8 with surrogateescape, not the locale: a path is bytes to git, and a
    # hook environment's C locale must not turn a non-ASCII path into an error
    # or into different text than the `crates/<member>/` prefix test expects.
    proc = subprocess.run(
        ["git", *args], cwd=REPO_ROOT, capture_output=True, check=False,
        text=True, encoding="utf-8", errors="surrogateescape",
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or f"git {' '.join(args)} failed")
    return proc.stdout


def resolve_ranges(
    push_context: bool, explicit: Optional[str], pushed_refs: str
) -> Tuple[List[str], str]:
    """The git-diff ranges whose union is this run's subject, and which reading
    produced them (printed on the SUBJECT line).

    TWO DOTS FOR AN UPDATE, three for a new branch — the reading
    scripts/check_compiler_targets_build.sh and
    scripts/check_completion_gate_tests.sh took in b882c0a672, for the same
    reasons. Until 2026-09-27 this lane diffed every update
    `<remote-sha>...<local-sha>`, the changes since the MERGE BASE. For a
    fast-forward that equals the tree diff; for a force push it does not: a
    push that DROPS the remote's crates/ commits and adds one docs commit was
    judged on the docs commit and SKIPPED, although the tree it installs
    differs from the remote's in crates/. A rewind (local an ancestor of
    remote) read as no change at all. `<remote-sha>..<local-sha>` is, for
    `git diff`, `git diff remote local`: the remote tree against the pushed
    tree, so it lists what a push removes too.

    A new branch (all-zero remote-sha) has no remote tree, so it keeps
    `origin/main...<local-sha>`, what the branch adds since its fork. The
    two-dot diff against origin/main is not strictly safer there: a change the
    branch shares with main by cherry-pick drops out of it, and it would charge
    a docs branch cut from an older main with every crates/ change main landed
    since, none of which this push carries.

    `--range A..B` keeps its meaning, `A...B`; with no push context, or
    TRUST_PUSHED_REFS naming only deletions or lines that are not four fields,
    the subject is `origin/main...HEAD` and the reading SAYS so."""
    if explicit:
        if ".." not in explicit:
            raise ValueError(f"--range must be A..B, got {explicit!r}")
        base, head = explicit.replace("...", "..").split("..", 1)
        return [f"{base or 'origin/main'}...{head or 'HEAD'}"], "explicit --range"
    if push_context:
        out = []
        for line in pushed_refs.splitlines():
            parts = line.split()
            if len(parts) < 4:
                continue
            _local_ref, local_sha, _remote_ref, remote_sha = parts[:4]
            if local_sha.strip("0") == "":
                continue  # a deletion pushes nothing
            if remote_sha.strip("0"):
                out.append(f"{remote_sha}..{local_sha}")  # an update: remote tree vs pushed tree
            else:
                out.append(f"origin/main...{local_sha}")  # a new branch: what it adds since its fork
        if out:
            return out, (
                f"pushed refs, TRUST_PUSHED_REFS, {len(out)} update(s); an update is the tree "
                "diff <remote>..<local>, a new branch origin/main...<local>"
            )
        if pushed_refs.strip():
            return ["origin/main...HEAD"], (
                "standing origin/main...HEAD; TRUST_PUSHED_REFS names no update to diff, "
                "only deletions or malformed lines"
            )
    return ["origin/main...HEAD"], "standing origin/main...HEAD; no push in flight"


# How every range is diffed. --no-renames (and diff.renames=false, against a
# config that says otherwise): with git's default rename detection a file moved
# OUT of crates/<member>/ is listed only under its new path, so its member was
# never tested (a move to docs/ skipped the lane). Without it the old path is
# listed as a deletion and attributes to its old member. -z: without it git
# C-quotes a path holding non-ASCII bytes, `"` or `\` ("crates/x/\303\251.rs",
# leading quote included), which then fails every `crates/` prefix test.
# --ignore-submodules=none: no gitlink sits under crates/ today, but one that
# did would be its member's change, and the plan's disclosure counts moved
# first-party/ pins; diff.ignoreSubmodules or a .gitmodules `ignore = all` (read
# from the worktree even for a commit-to-commit diff) would hide either. The
# same spelling as the two shell scoped lanes, where each was fixed first.
DIFF_ARGS = (
    "-c", "diff.renames=false", "diff", "--no-renames", "--ignore-submodules=none",
    "--name-only", "-z",
)


def changed_paths(ranges: Sequence[str]) -> List[str]:
    """The union of the paths each range changes. A range git cannot diff (an
    object this clone lacks, as after a force push over a remote tip never
    fetched here; no merge base; no origin/main) raises RuntimeError, and main()
    turns that into exit 2, red: it is never read as "no changes"."""
    paths = set()
    for rng in ranges:
        # The trailing `--` makes an unknown sha an unknown REVISION, never a path.
        text = git(*DIFF_ARGS, rng, "--")
        paths.update(p for p in text.split("\0") if p)
    return sorted(paths)


def developer_member_ids(metadata: dict) -> set:
    """Cargo owns the default developer product inventory; missing data is an error."""
    members = metadata.get("workspace_default_members")
    if not isinstance(members, list) or not members:
        raise RuntimeError("Targo metadata has no developer default-member inventory")
    if not set(members).issubset(metadata.get("workspace_members", [])):
        raise RuntimeError("Targo metadata defaults include non-members")
    return set(members)


def workspace_members(metadata: dict) -> Dict[str, str]:
    """Map `crates/<dir>` (repo-relative) -> package name, for workspace members."""
    member_ids = developer_member_ids(metadata)
    root = str(REPO_ROOT.resolve())
    members: Dict[str, str] = {}
    for pkg in metadata.get("packages", []):
        if pkg.get("id") not in member_ids:
            continue
        manifest = str(Path(pkg["manifest_path"]).resolve())
        if not manifest.startswith(root + os.sep):
            continue
        rel_dir = Path(manifest[len(root) + 1 :]).parent.as_posix()
        members[rel_dir] = pkg["name"]
    return members


def package_specs(metadata: dict, lock_text: str) -> Dict[str, str]:
    """Member name -> the `-p` spec that names it unambiguously. A member whose
    name another package of the lockfile also carries (crates/trust-sha2-compat,
    deleted 2026-11-10, was `sha2`, beside the registry's and ty's) must be named by its package ID:
    `-p sha2` is refused ("specification `sha2` is ambiguous") and takes the whole
    run with it (measured 2026-10-14: the landing gate's run of every member,
    0 test binaries recorded). Unambiguous names stay plain."""
    counts: Dict[str, int] = {}
    for name in re.findall(r'^name = "([^"]+)"$', lock_text, re.M):
        counts[name] = counts.get(name, 0) + 1
    member_ids = developer_member_ids(metadata)
    specs: Dict[str, str] = {}
    for pkg in metadata.get("packages", []):
        if pkg.get("id") in member_ids and counts.get(pkg.get("name", ""), 0) > 1:
            specs[pkg["name"]] = pkg["id"]
    return specs


HOST_OS = {"darwin": "macos", "linux": "linux", "win32": "windows"}.get(sys.platform, sys.platform)
CRATE_OS_CFG = re.compile(r'^#!\[cfg\(target_os\s*=\s*"([a-z]+)"\)\]', re.M)


def apply_host_limits(plan: "Plan", tree: Path, members: Dict[str, str], host_os: str = HOST_OS) -> None:
    """Take out of the plan every crate whose library is compiled only for
    another OS (a crate-level `#![cfg(target_os = "linux")]` in src/lib.rs, as
    crates/trust-worker-linux has: its test targets cannot build here, so on this
    host the run could only fail, and that failure would say nothing about the
    change). Each is named NOT RUN on this host; it is never counted as tested."""
    by_name = {name: d for d, name in members.items()}
    candidates = [(d, "root") for d in plan.own_workspaces] + \
                 [(by_name[p], "member") for p in plan.packages if p in by_name]
    for d, kind in candidates:
        try:
            text = (tree / d / "src" / "lib.rs").read_text(encoding="utf-8")
        except OSError:
            continue
        m = CRATE_OS_CFG.search(text)
        if m and m.group(1) != host_os:
            plan.host_limited.append((d, f"its library is `#![cfg(target_os = \"{m.group(1)}\")]`; "
                                         f"this host is {host_os}"))
            if kind == "root":
                plan.own_workspaces = [r for r in plan.own_workspaces if r != d]
            else:
                plan.packages = [p for p in plan.packages if p != members[d]]
                plan.feature_runs = [(p, t) for p, t in plan.feature_runs if p != members[d]]


def own_workspace_roots(tree: Path) -> List[str]:
    """`crates/<dir>` whose Cargo.toml declares its own `[workspace]`, by the
    one rule scripts/lib/crates_lane_members.py states. The land gate's
    selector reads the same rule, so every member it hands this lane is one the
    lane can attribute (LAND-GATE-HOOKLESS-1 round 5, D1). A `[workspace]`
    nested deeper is no crate of this lane."""
    roots = []
    for manifest in sorted((tree / "crates").glob("*/Cargo.toml")):
        try:
            text = manifest.read_text(encoding="utf-8")
        except OSError:
            continue
        root = crates_lane_members.own_workspace_root(manifest.relative_to(tree).as_posix(), text)
        if root is not None:
            roots.append(root)
    return roots


def path_owner(path: str, members: Dict[str, str], own_roots: Sequence[str]) -> Optional[str]:
    """The crate directory this lane tests for a changed `crates/` path, or
    None: the member whose directory is the path's longest prefix (a nested
    member never loses a path to its parent), else the first own-workspace root
    that holds it. plan_for attributes every path this way, and so does
    scripts/land_gate.py's hook_lane_members when it asks what the hook's lane
    tests on a push. A second implementation there could disagree with this one
    (round 5, D1)."""
    owner = next((d for d in sorted(members, key=len, reverse=True) if path.startswith(d + "/")), None)
    if owner is not None:
        return owner
    return next((r for r in own_roots if path.startswith(r + "/")), None)


# Plan.attributed_commands' mark for a run whose binaries count, under the
# zero-test rule, for the member cargo ran each one for (CARGO_PKG_NAME in its
# record). Not a path: an own-workspace run is marked with its `crates/<dir>`.
MEMBERS = "<the member of each binary>"


class Plan:
    def __init__(self) -> None:
        self.packages: List[str] = []
        self.feature_runs: List[Tuple[str, List[str]]] = []
        self.instrument_runs: List[Tuple[str, List[str]]] = []
        self.own_workspaces: List[str] = []
        self.excluded: List[Tuple[str, str]] = []
        self.workspace_files: List[str] = []
        self.first_party: List[str] = []
        self.unattributed: List[str] = []
        # --also-members dirs that are no member and no own-workspace root here.
        self.unknown_members: List[str] = []
        self.specs: Dict[str, str] = {}  # package_specs: a name `-p` cannot take alone
        self.host_limited: List[Tuple[str, str]] = []  # (crate dir, why): not built on this host

    def empty(self) -> bool:
        return not (
            self.packages or self.feature_runs or self.instrument_runs or self.own_workspaces
        )

    def crates(self) -> int:
        """How many crates this plan tests, for the time bound's ceiling
        (scripts/lib/crates_tests_time.py budget_s): each member, each
        own-workspace crate, and each instrument host the plan does not already
        test as a member. A land-gate run (--also-members, no diff) counts
        exactly the members it was handed."""
        return len(set(self.packages) | set(self.own_workspaces)
                   | {host for host, _ in self.instrument_runs})

    def targo_trust_consumers(self) -> List[str]:
        """Planned members and instruments that require the private CLI copy."""
        return sorted(
            {pkg for pkg in self.packages if pkg in TARGO_TRUST_CONSUMERS}
            | {host for _, host, tail in TARGO_TRUST_INSTRUMENTS
               if (host, tail) in self.instrument_runs}
        )

    def needs_targo_trust(self) -> bool:
        return bool(self.targo_trust_consumers())

    def commands(self) -> List[List[str]]:
        return [cmd for cmd, _ in self.attributed_commands()]

    def attributed_commands(self) -> List[Tuple[List[str], Optional[str]]]:
        """commands(), each with whom its tests count for under the zero-test
        rule (tests_reported): MEMBERS for the default run and each feature
        tail, whose binaries count for the member cargo ran each one for; the
        crate's directory for an own-workspace run; None for an instrument,
        whose subject is another member's output and whose host the push did
        not touch."""
        base = ["targo", "--unverified", "test", *MEMBER_FEATURE_SCOPE]
        cmds: List[Tuple[List[str], Optional[str]]] = []
        if self.packages:
            cmd = base + ["--manifest-path", CRATES_MANIFEST, "--locked", "--no-fail-fast"]
            for pkg in self.packages:
                cmd += ["-p", self.specs.get(pkg, pkg)]
            cmds.append((cmd + ["--tests"], MEMBERS))
        runs = [(pkg, tail, MEMBERS) for pkg, tail in self.feature_runs]
        runs += [(pkg, tail, None) for pkg, tail in self.instrument_runs]
        for pkg, tail, credit in runs:
            cmds.append((
                base
                + ["--manifest-path", CRATES_MANIFEST, "--locked", "--no-fail-fast", "-p", pkg]
                + tail,
                credit,
            ))
        for root in self.own_workspaces:
            cmds.append((
                base + ["--manifest-path", f"{root}/Cargo.toml", "--locked", "--no-fail-fast", "--tests"],
                root,
            ))
        return cmds


def feature_target_directory_problem(plan: Plan, metadata: dict, root: Path) -> Optional[str]:
    """Keep feature-built package binaries out of the default run's target dir.

    The record passes all build before any tests execute. A feature integration
    target can therefore replace a binary whose path a default test embeds.
    Cargo metadata, rather than an environment/config guess, names that default
    directory. Resolving paths only reads the filesystem; absent target dirs
    need not be created for this check.
    """
    targets: List[Tuple[str, str]] = []
    for pkg, tail in plan.feature_runs:
        cargo_args = tail[:tail.index("--")] if "--" in tail else tail
        for index, arg in enumerate(cargo_args):
            if arg == "--target-dir":
                if index + 1 == len(cargo_args):
                    return f"feature target directory is missing for {pkg}"
                targets.append((pkg, cargo_args[index + 1]))
            elif arg.startswith("--target-dir="):
                targets.append((pkg, arg.split("=", 1)[1]))
    if not targets:
        return None

    default = metadata.get("target_directory")
    if not isinstance(default, str) or not default or "\0" in default or not Path(default).is_absolute():
        return "metadata target_directory must be a nonempty absolute path for explicit feature target directories"
    try:
        default_path = Path(default).resolve()
        for pkg, target in targets:
            if not target or "\0" in target:
                return f"feature target directory is invalid for {pkg}"
            target_path = Path(target)
            if not target_path.is_absolute():
                target_path = root / target_path
            target_path = target_path.resolve()
            # Refuse case-only aliases even before either directory exists.
            # Conservatively also refuse them on case-sensitive filesystems.
            same = str(target_path).casefold() == str(default_path).casefold()
            if not same:
                try:
                    # Also catch other existing filesystem aliases.
                    same = target_path.samefile(default_path)
                except FileNotFoundError:
                    pass
            if same:
                return (f"feature target directory collides with metadata target_directory for {pkg}: "
                        f"{target_path}")
    except (OSError, RuntimeError, ValueError) as exc:
        return f"cannot resolve feature/metadata target_directory: {exc}"
    return None


def plan_for(
    paths: Sequence[str],
    members: Dict[str, str],
    own_roots: Sequence[str],
    feature_runs: Dict[str, List[List[str]]] = FEATURE_RUNS,
    excluded: Dict[str, str] = EXCLUDED_ELSEWHERE,
    instruments: Sequence[Tuple[Tuple[str, ...], str, List[str]]] = CROSS_CRATE_INSTRUMENTS,
    corpus_instruments: Sequence[Tuple[str, Tuple[str, ...], str, List[str]]] = CORPUS_INSTRUMENTS,
    also_dirs: Sequence[str] = (),
) -> Plan:
    plan = Plan()
    packages = set()
    touched = set()  # the members a path in the range belongs to (not --also-members)
    roots = set()
    # --also-members (scripts/land_gate.py): members the change REACHES through
    # the dependency graph, added to the ones it touches. Only adds.
    for d in also_dirs:
        if d in members:
            packages.add(members[d])
        elif d in own_roots:
            roots.add(d)
        else:
            plan.unattributed.append(d)
            # The caller asked for it to be tested and nothing here can test
            # it: main() refuses the run (round 5, D1), so no caller stores a
            # PASS for a crate this lane never ran.
            plan.unknown_members.append(d)
    for path in paths:
        if path.startswith("first-party/"):
            plan.first_party.append(path)
            continue
        if path in ("Cargo.toml", "Cargo.lock"):
            plan.workspace_files.append(path)
            continue
        if not path.startswith("crates/"):
            continue
        owner = path_owner(path, members, own_roots)
        if owner in members:
            packages.add(members[owner])
            touched.add(members[owner])
            continue
        if owner is not None:
            roots.add(owner)
            continue
        parts = path.split("/")
        if len(parts) > 2 and parts[1] in excluded:
            entry = (parts[1], excluded[parts[1]])
            if entry not in plan.excluded:
                plan.excluded.append(entry)
            continue
        plan.unattributed.append(path)
    plan.packages = sorted(packages)
    plan.feature_runs = [(pkg, tail) for pkg in plan.packages for tail in feature_runs.get(pkg, [])]
    # An instrument whose host the range TOUCHES is left to the host's default
    # run (the hook's rule since TRUST-16). A host only --also-members adds
    # (scripts/land_gate.py's hookless leg, which hands this lane the landing
    # range) keeps its instrument run: a member run is judged by the zero-test
    # rule, which an #[ignore]d INSTRUMENT_REQUIRED_PASSES test passes, and the
    # instrument run by instrument_problem (LAND-GATE-HOOKLESS-1 round 2, D3).
    plan.instrument_runs = [
        (host, tail)
        for host, tail in moved_instruments(paths, instruments, corpus_instruments)
        if host not in touched
    ]
    plan.own_workspaces = sorted(roots)
    return plan


def corpus_document(path: str, suffix: str, outside: Tuple[str, ...]) -> bool:
    """Whether `path` is a document of a CORPUS_INSTRUMENTS subject: the
    manifests' rule, less the size cap (a document crossing trust-json's 1 MiB
    cap changes the membership too, so every size counts)."""
    return path.endswith(suffix) and not path.startswith(outside)


def moved_instruments(
    paths: Sequence[str],
    instruments: Sequence[Tuple[Tuple[str, ...], str, List[str]]] = CROSS_CRATE_INSTRUMENTS,
    corpus_instruments: Sequence[Tuple[str, Tuple[str, ...], str, List[str]]] = CORPUS_INSTRUMENTS,
) -> List[Tuple[str, List[str]]]:
    """(host, tail) of every instrument whose subject one of `paths` moves, in
    table order. It needs no metadata, so _main asks it before deciding that a
    push with no `crates/` path has nothing to run."""
    return [
        (host, tail)
        for prefixes, host, tail in instruments
        if any(path.startswith(prefix) for path in paths for prefix in prefixes)
    ] + [
        (host, tail)
        for suffix, outside, host, tail in corpus_instruments
        if any(corpus_document(path, suffix, outside) for path in paths)
    ]


def print_plan(plan: Plan) -> None:
    if plan.packages:
        print(f"in scope: {len(plan.packages)} crates/ member(s): {', '.join(plan.packages)}")
    for root in plan.own_workspaces:
        print(f"in scope: own-workspace crate {root}")
    for pkg, tail in plan.feature_runs:
        print(f"feature lane: {pkg} {' '.join(tail)}")
    if plan.needs_targo_trust():
        print(f"prebuild: targo-trust, whose copy the tests of "
              f"{', '.join(plan.targo_trust_consumers())} get as {TARGO_TRUST_VAR}")
    for pkg, tail in plan.instrument_runs:
        print(f"cross-crate instrument: {pkg} {' '.join(tail)} (its subject changed)")
    print("NOT COVERED by this lane (named, not summarised away):")
    print(
        "  - reverse dependencies of the crates above (-p X never tests X's callers), "
        "except the instruments CROSS_CRATE_INSTRUMENTS and CORPUS_INSTRUMENTS name "
        "and the members --also-members adds (scripts/land_gate.py passes every member the "
        "change reaches through the dependency graph and the files its tests read)"
    )
    print("  - doctests, examples and benches (the runs use --tests)")
    print("  - non-default feature lanes other than the feature lanes listed above")
    for name, lane in plan.excluded:
        print(f"  - {name}: excluded from crates/ (rustc_private); tests run only by `{lane}`")
    if plan.workspace_files:
        print(
            f"  - {', '.join(plan.workspace_files)} changed: every member's graph may move, "
            "but only the members whose own files changed are tested here"
        )
    if plan.first_party:
        print(
            f"  - {len(plan.first_party)} first-party/ path(s) changed (pin moves): crates that "
            "depend on them are not re-tested unless their own files changed"
        )
    if plan.unattributed:
        print(f"  - {len(plan.unattributed)} crates/ path(s) owned by no member: {', '.join(plan.unattributed[:5])}")
    for d, why in plan.host_limited:
        print(f"  - {d}: NOT RUN on this host ({why})")


def targo_is_targo() -> Optional[str]:
    """CLAUDE.md's one discriminator: cargo-in-disguise rejects `--unverified`."""
    try:
        proc = subprocess.run(
            ["targo", "--unverified", "--version"], capture_output=True, text=True, check=False
        )
    except OSError as exc:
        return f"no `targo` on PATH ({exc})"
    if proc.returncode != 0:
        return (
            "`targo --unverified --version` failed — this `targo` is not Targo "
            f"(cargo under the name?): {(proc.stderr or proc.stdout).strip()[:200]}"
        )
    return None


class TimeBound:
    """The lane's time bound (the header's BOUNDED TIME; the rule is
    scripts/lib/crates_tests_time.py's): out of time when nothing has
    progressed (progress()) for `stall_s` seconds, or `ceiling_s` seconds after
    it was made, the ceiling moved on by every extend(). Thread-safe: the pool's
    workers, their output readers and the admission thread all report progress."""

    def __init__(self, ceiling_s: float, stall_s: float, started: Optional[float] = None) -> None:
        """`started` (a time.monotonic() instant, default now) is when the ceiling
        starts counting; the stall clock starts now."""
        now = time.monotonic()
        self.ceiling_s = ceiling_s
        self.stall_s = stall_s
        self._lock = threading.Lock()
        self._ceiling_at = (now if started is None else started) + ceiling_s
        self._last = now
        self._building = 0

    def progress(self) -> None:
        with self._lock:
            self._last = time.monotonic()

    @contextlib.contextmanager
    def building(self):
        """While a build runs (cargo building the tests, targo-trust's build),
        the stall bound does not apply and the ceiling alone bounds it: one
        rustc can be silent for long on a loaded host, and cargo is silent while
        it waits on another build's lock, which is latency, not a hang. When the
        build ends the stall clock starts again (CRATES-TIME-1)."""
        with self._lock:
            self._building += 1
        try:
            yield
        finally:
            with self._lock:
                self._building -= 1
                self._last = time.monotonic()

    def _stall_at(self) -> float:
        return math.inf if self._building else self._last + self.stall_s

    def extend(self, seconds: float) -> None:
        """Refund `seconds` the lane spent waiting on someone else (the barrier):
        the ceiling moves by exactly that, and the stall clock starts again."""
        with self._lock:
            self._ceiling_at += seconds
            self._last = time.monotonic()

    def left(self) -> float:
        with self._lock:
            return min(self._ceiling_at, self._stall_at()) - time.monotonic()

    def why(self) -> str:
        """Which bound ran out, for a NOT JUDGED line (call it once left() <= 0)."""
        with self._lock:
            stalled = self._stall_at() < self._ceiling_at
        if stalled:
            return (f"the lane STALLED: nothing it ran printed, ended or was admitted "
                    f"for {self.stall_s:.0f}s (TRUST_CRATES_TESTS_STALL_S)")
        return f"the {self.ceiling_s:.0f}s budget ran out"


# A deadline is a TimeBound (the lane's own) or a plain time.monotonic() instant
# (a fixed bound, which nothing moves).
Deadline = Union[float, TimeBound]
# The longest one wait sleeps before it looks at a TimeBound again: progress
# elsewhere can move the bound while a wait is under way.
BOUND_POLL_S = 1.0


def _left(deadline: Deadline) -> float:
    if isinstance(deadline, TimeBound):
        return deadline.left()
    return deadline - time.monotonic()


def _progress(deadline: Deadline) -> None:
    if isinstance(deadline, TimeBound):
        deadline.progress()


def _building(deadline: Deadline):
    """TimeBound.building() for the lane's bound; nothing for a fixed one."""
    return deadline.building() if isinstance(deadline, TimeBound) else contextlib.nullcontext()


def _why(deadline: Deadline) -> str:
    return deadline.why() if isinstance(deadline, TimeBound) else "the budget ran out"


def _wait_until(proc: subprocess.Popen, deadline: Deadline) -> Optional[int]:
    """proc's exit code, or None when the deadline came first (proc still runs)."""
    while True:
        left = _left(deadline)
        if left <= 0:
            return None
        try:
            return _wait(proc, timeout=min(left, BOUND_POLL_S))
        except subprocess.TimeoutExpired:
            continue


def _event_until(event: threading.Event, deadline: Deadline) -> bool:
    """event.wait() until the deadline: True once it is set, False at the deadline."""
    while True:
        left = _left(deadline)
        if left <= 0:
            return event.is_set()
        if event.wait(timeout=min(left, BOUND_POLL_S)):
            return True


def run_with_deadline(
    cmd: List[str], deadline: Deadline, env: Optional[Dict[str, str]] = None,
    messages: Optional[List[str]] = None,
) -> Tuple[Optional[int], str]:
    """Run `cmd`, streaming its output; (exit code or None when the deadline killed it, output).
    `env` replaces the lane's own environment. With `messages`, nothing is shown:
    stdout (cargo's --message-format JSON) is collected there, and the output is
    stderr (cargo's rendered text), for the caller to show when the build fails.
    It runs only builds (the record pass, targo-trust's), which the stall bound
    does not judge (TimeBound.building()): the ceiling alone bounds them, and
    the stall clock starts again when one ends. Nothing it prints is progress,
    so a process it left holding its output open cannot defer the stall bound
    for the binaries that run after it."""
    with _building(deadline):
        return _run_with_deadline(cmd, deadline, env, messages)


def _run_with_deadline(
    cmd: List[str], deadline: Deadline, env: Optional[Dict[str, str]],
    messages: Optional[List[str]],
) -> Tuple[Optional[int], str]:
    if _left(deadline) <= 0:
        return None, ""
    proc = _spawn(
        cmd, cwd=REPO_ROOT, env=env, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT if messages is None else subprocess.PIPE, text=True, errors="replace",
    )
    if proc is None:  # the lane is being interrupted: nothing started
        return None, ""
    lines: List[str] = []

    def pump(stream, sink: List[str], show: bool) -> None:
        for line in stream:
            sink.append(line)
            if show:
                sys.stdout.write(line)
        sys.stdout.flush()

    if messages is None:
        readers = [threading.Thread(target=pump, args=(proc.stdout, lines, True), daemon=True)]
    else:
        readers = [threading.Thread(target=pump, args=(proc.stdout, messages, False), daemon=True),
                   threading.Thread(target=pump, args=(proc.stderr, lines, False), daemon=True)]
    for reader in readers:
        reader.start()
    rc = _wait_until(proc, deadline)
    if rc is None:
        _kill_group(proc)
    _untrack(proc)
    for reader in readers:
        reader.join(timeout=30)
    return rc, "".join(lines)


# Every process group the lane has started and not yet reaped: cargo's record
# passes and the test binaries, each the leader of a session of its own
# (start_new_session), which a signal aimed at the lane's own group misses.
_LIVE: set = set()
_STOPPING = threading.Event()
# How long a forwarded signal is given before the group is KILLed.
KILL_GRACE_S = 10
# Starting, signaling and reaping share one lifecycle lock. A worker removes
# its child from _LIVE in the same critical section that reaps it; cancellation
# claims _STOPPING before taking its snapshot, so workers cannot release any
# of the selected leader PID pins before the handler finishes group signals.
# Starting a process and adding it to _LIVE is ONE step an interrupt cannot
# split (_spawn): a process forked but not yet in _LIVE when the handler took
# its snapshot would outlive the lane. A pool thread holds _SPAWN_LOCK across
# both, and the handler takes it (after setting _STOPPING) before its snapshot,
# so a spawn is either in the snapshot or sees _STOPPING and starts nothing.
# The handler runs in the main thread, so it cannot wait for a lock the main
# thread itself holds: when it lands inside the main thread's own spawn it
# records the signal (_PENDING_SIGNAL) and returns, and _spawn forwards it
# once the process is in _LIVE.
_SPAWN_LOCK = threading.Lock()
_MAIN_SPAWNING = False
_PENDING_SIGNAL: Optional[int] = None
_FORWARDING = False
# Every scratch directory the lane has made and not yet removed (_scratch_dir):
# the record pass's, and the private one holding the targo-trust copy. The
# handler's os._exit runs no `finally` and no context manager's exit, so it
# removes them itself, once every process that could write there is gone.
_SCRATCH: List[str] = []


@contextlib.contextmanager
def _process_state():
    """Serialize child custody; defer a main-thread signal until unlock.

    The handler must not recursively acquire a lock held by its own interrupted
    thread. Workers only hold this lock for nonblocking observation/reap, never
    while waiting for a live child to terminate.
    """
    global _MAIN_SPAWNING
    in_main = threading.current_thread() is threading.main_thread()
    previous = _MAIN_SPAWNING
    if in_main:
        _MAIN_SPAWNING = True
    try:
        with _SPAWN_LOCK:
            yield
    finally:
        if in_main:
            _MAIN_SPAWNING = previous
            if not previous and _PENDING_SIGNAL is not None and not _FORWARDING:
                _forward_and_exit(_PENDING_SIGNAL, None)


def _spawn(cmd: List[str], **kwargs) -> Optional[subprocess.Popen]:
    """Start a new-session child and register it atomically with cancellation."""
    # Without WNOWAIT or with an automatic/external SIGCHLD reaper, a child PID
    # cannot reserve group identity until the last signal. Refuse before fork.
    if not all(hasattr(os, name) for name in ("waitid", "P_PID", "WEXITED", "WNOWAIT", "WNOHANG")):
        raise OSError("crates-tests child custody requires POSIX waitid WNOWAIT")
    if signal.getsignal(signal.SIGCHLD) != signal.SIG_DFL:
        raise OSError("crates-tests child custody requires the default SIGCHLD handler")
    with _process_state():
        if _STOPPING.is_set() or _PENDING_SIGNAL is not None:
            return None
        proc = subprocess.Popen(cmd, start_new_session=True, **kwargs)
        _LIVE.add(proc)
        return proc


def _untrack(proc: subprocess.Popen) -> None:
    with _process_state():
        _LIVE.discard(proc)


def _exited_locked(proc: subprocess.Popen) -> bool:
    # Observe without wait()/poll(): the unreaped direct child reserves its PID
    # even after exit, preventing group-ID reuse until the final group signal.
    return proc.returncode is not None or os.waitid(
        os.P_PID, proc.pid, os.WEXITED | os.WNOWAIT | os.WNOHANG,
    ) is not None


def _exited(proc: subprocess.Popen) -> bool:
    with _process_state():
        return _exited_locked(proc)


def _wait(proc: subprocess.Popen, timeout: float, *, cleanup: bool = False) -> int:
    """Reap and retire atomically, or leave the pin to cancellation's owner."""
    deadline = time.monotonic() + max(timeout, 0)
    while True:
        with _process_state():
            if proc.returncode is not None:
                return proc.returncode
            if (cleanup or not _STOPPING.is_set()) and _exited_locked(proc):
                rc = proc.wait(timeout=0)
                _LIVE.discard(proc)
                return rc
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise subprocess.TimeoutExpired(proc.args, timeout)
        time.sleep(min(.02, remaining))


def _wait_for_exit(proc: subprocess.Popen, timeout: float) -> None:
    """Wait for termination without releasing the leader pin."""
    deadline = time.monotonic() + max(timeout, 0)
    while not _exited(proc):
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise subprocess.TimeoutExpired(proc.args, timeout)
        time.sleep(min(.02, remaining))


@contextlib.contextmanager
def _scratch_dir(prefix: str):
    """tempfile.TemporaryDirectory for the lane: removed on every exit, an
    interrupt's included (_forward_and_exit removes what _SCRATCH holds). Making
    it and recording it is one step, as for _spawn: a signal that lands in
    between is deferred until the directory is recorded, then forwarded."""
    global _MAIN_SPAWNING
    in_main = threading.current_thread() is threading.main_thread()
    if in_main:
        _MAIN_SPAWNING = True
    try:
        path = tempfile.mkdtemp(prefix=prefix)
        _SCRATCH.append(path)
    finally:
        if in_main:
            _MAIN_SPAWNING = False
            if _PENDING_SIGNAL is not None:
                _forward_and_exit(_PENDING_SIGNAL, None)
    try:
        yield path
    finally:
        shutil.rmtree(path, ignore_errors=True)
        with contextlib.suppress(ValueError):
            _SCRATCH.remove(path)


def _signal_group(proc: subprocess.Popen, sig: int) -> None:
    with _process_state():
        # A cancellation snapshot may race with normal retirement. Never signal
        # a captured process after its worker has released the child PID pin.
        if proc not in _LIVE or proc.returncode is not None:
            return
        terminal = _exited_locked(proc)  # raises if an outside waiter stole custody
        if not terminal:
            try:
                if os.getpgid(proc.pid) != proc.pid:
                    raise RuntimeError("owned child lost its new-session group identity")
            except ProcessLookupError:
                if not _exited_locked(proc):
                    raise
        try:
            os.killpg(proc.pid, sig)
        except (ProcessLookupError, PermissionError):
            pass  # already gone (PermissionError: macOS, for a zombie leader)


def _forward_and_exit(signum: int, _frame: object) -> None:
    """INT/TERM/HUP handler: pass the signal on to every group the lane
    started, KILL what outlives KILL_GRACE_S, remove the lane's scratch
    directories (_SCRATCH: the record pass's, and the targo-trust copy's) once
    nothing it started can write there, and exit 128+signum, NOT JUDGED.
    The signal the lane got is the one forwarded: cargo, like a terminal's
    Ctrl-C, gets a SIGINT when the lane did."""
    global _PENDING_SIGNAL, _FORWARDING
    if _FORWARDING:  # first signal owns cleanup; a second cannot interrupt its pins
        return
    if _PENDING_SIGNAL is None:
        _PENDING_SIGNAL = signum
    signum = _PENDING_SIGNAL
    if _MAIN_SPAWNING:  # finish the main thread's child-custody critical section
        return
    _FORWARDING = True
    _STOPPING.set()
    with _process_state():  # every spawn is now tracked, or will start nothing
        procs = list(_LIVE)
    for proc in procs:
        _signal_group(proc, signum)
    deadline = time.monotonic() + KILL_GRACE_S
    for proc in procs:
        try:
            _wait_for_exit(proc, timeout=max(deadline - time.monotonic(), 0))
        except subprocess.TimeoutExpired:
            pass
        _signal_group(proc, signal.SIGKILL)
    for proc in procs:
        with contextlib.suppress(subprocess.TimeoutExpired):
            _wait(proc, timeout=5, cleanup=True)
    for path in list(_SCRATCH):
        shutil.rmtree(path, ignore_errors=True)
    try:
        name = signal.Signals(signum).name
    except ValueError:
        name = str(signum)
    # The handler can run while the main thread is inside a `print` on the same
    # BufferedWriter; touching that writer here then raises "reentrant call inside
    # <_io.BufferedWriter name='<stdout>'>" and the lane exits 1 instead of
    # 128+signum (measured: the InheritedIgnoredInterruptTest barrier case, a push
    # gate RED on 2026-10-14). Flush what is already buffered only when the writer
    # is free, then write the notice straight to fd 1, which needs no buffer.
    with contextlib.suppress(RuntimeError, OSError, ValueError):
        sys.stdout.flush()
    with contextlib.suppress(OSError):
        os.write(
            1,
            (
                f"\ncrates-tests: interrupted ({name}); passed it to {len(procs)} running process "
                "group(s) and waited for them. NOT JUDGED.\n"
            ).encode(),
        )
    os._exit(128 + signum)


@contextlib.contextmanager
def forwarding_signals():
    """_forward_and_exit on INT, TERM and HUP for the duration, then the
    previous handlers back (main() runs inside tests too). A signal inherited
    as ignored (nohup's HUP, a background job's INT) stays ignored."""
    saved = {}
    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        previous = signal.getsignal(sig)
        if previous is signal.SIG_IGN:
            continue
        saved[sig] = previous
        signal.signal(sig, _forward_and_exit)
    try:
        yield
    finally:
        for sig, previous in saved.items():
            signal.signal(sig, previous)


RUN_AFTER_ENV = "TRUST_CRATES_TESTS_RUN_AFTER"
RUN_AFTER_OWNER_ENV = "TRUST_CRATES_TESTS_RUN_AFTER_OWNER"
RUN_AFTER_MAX_ENV = "TRUST_CRATES_TESTS_RUN_AFTER_MAX_S"
# The longest a barrier is waited for when nothing says sooner. A cold
# `x.py check --stage 1` has taken over an hour; four is far past any warm one.
DEFAULT_RUN_AFTER_MAX_S = 4 * 3600
BARRIER_POLL_S = 0.2


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True  # it exists; it is not ours
    return True


def wait_for_barrier(path: str, owner: Optional[int], max_wait: float) -> Tuple[bool, float, str]:
    """Wait until `path` exists: (run?, seconds waited, what released it).

    `run` only when the file's content is exactly `run` (the hook writes it
    whole, by rename, so a half-written file is never read); any other content
    is a stop. No `run` also when `owner` (the process that promised to write
    it) is gone without writing it, or after `max_wait` seconds: a barrier that
    never comes costs at most that, never a hang."""
    t0 = time.monotonic()
    while True:
        try:
            with open(path, encoding="utf-8", errors="replace") as fh:
                text = fh.read().strip()
        except FileNotFoundError:
            text = None
        waited = time.monotonic() - t0
        if text is not None:
            return text == "run", waited, f"it says {text!r}"
        if owner is not None and not _alive(owner):
            if os.path.exists(path):
                continue  # written just before its writer exited: read it
            return False, waited, f"pid {owner}, which was to release it, is gone and never did"
        if waited >= max_wait:
            return False, waited, f"it did not appear within {RUN_AFTER_MAX_ENV}={max_wait:.0f}s"
        time.sleep(BARRIER_POLL_S)


def _cargo_message(line: str) -> Optional[dict]:
    """One line of cargo's --message-format JSON as a dict, or None for any
    other line (a wrapper's own text on stdout, say)."""
    try:
        msg = json.loads(line)
    except ValueError:
        return None
    return msg if isinstance(msg, dict) else None


def targo_trust_executable(messages: Iterable[str]) -> Optional[str]:
    """The `executable` of cargo's compiler-artifact message for the targo-trust
    bin, or None. Cargo's own answer, never a path derived from CARGO_TARGET_DIR
    and a profile name: a config, a profile or a build target moves the file."""
    found = None
    for line in messages:
        msg = _cargo_message(line)
        if msg is None:
            continue
        target = msg.get("target")
        if (msg.get("reason") == "compiler-artifact" and isinstance(target, dict)
                and target.get("name") == "targo-trust" and "bin" in target.get("kind", [])
                and msg.get("executable")):
            found = msg["executable"]
    return found


def targo_trust_change_not_run(paths: Sequence[str], packages: Sequence[str]) -> Optional[str]:
    """A line for a push that changes targo-trust/ but touches no consumer: the
    consumers' tests run targo-trust, so the change reaches them, and the lane,
    which plans from crates/ paths, does not run them. Named, not skipped silently."""
    if not any(p.startswith("targo-trust/") for p in paths):
        return None
    if any(pkg in TARGO_TRUST_CONSUMERS for pkg in packages):
        return None
    return (f"NOT RUN: the tests of {', '.join(TARGO_TRUST_CONSUMERS)} run targo-trust, which this "
            f"push changes; this lane plans from crates/ paths and does not run them "
            f"(`scripts/dev-test.sh {' '.join(TARGO_TRUST_CONSUMERS)}` does)")


def clone_or_copy(src: str, dst: str, deadline: Deadline) -> bool:
    """Copy `src` to `dst` as it is now; False when the deadline stopped it. On
    macOS `cp -c` clones it (APFS clonefile: copy-on-write, no new disk; cp falls
    back to a copy where it cannot clone), started like every process the lane
    runs (_spawn), so an interrupt reaches it and the budget bounds it.
    shutil.copy2 would write all ~200 MB of targo-trust to $TMPDIR on every run,
    on a disk that has been full."""
    if sys.platform == "darwin":
        # A file captures stderr without communicate()'s implicit, uncoordinated
        # wait(). cp has no useful stdout; all reaping goes through _wait.
        with tempfile.TemporaryFile(mode="w+t", errors="replace") as errors:
            proc = _spawn(["cp", "-c", "-p", src, dst], stdin=subprocess.DEVNULL,
                          stdout=subprocess.DEVNULL, stderr=errors, text=True, errors="replace")
            if proc is None:
                return False
            try:
                if _wait_until(proc, deadline) is None:
                    _kill_group(proc)
                    return False
            finally:
                _untrack(proc)
            if proc.returncode != 0:
                errors.seek(0)
                raise OSError(f"cp -c exited {proc.returncode}: {errors.read().strip()}")
            return True
    shutil.copy2(src, dst)
    return True


def prebuild_targo_trust(deadline: Deadline, private_dir: str) -> Tuple[int, str]:
    """Build targo-trust and copy it into `private_dir`: (0, the copy's path), or
    (main()'s exit code, why). The copy is taken the moment cargo exits, and the
    tests run it, not the target dir's file, which any build sharing that
    target dir may relink while they run. The build is one of the lane's
    processes (run_with_deadline: _spawn, _LIVE): its time comes out of the
    budget, and an interrupt reaches it."""
    spelled = " ".join(TARGO_TRUST_BUILD)
    print(f"\nbuilding targo-trust for {', '.join(TARGO_TRUST_CONSUMERS)}: {spelled}", flush=True)
    t0 = time.monotonic()
    messages: List[str] = []
    rc, held = run_with_deadline(TARGO_TRUST_BUILD, deadline, messages=messages)
    built = targo_trust_executable(messages) if rc == 0 else None
    if not built:
        # Held while it can only be noise: every run replayed targo-trust's
        # cached dependency warnings, 3786 lines on 2026-09-30, about as many
        # as the record pass's whole output (3563). On a failure all of it is
        # shown: cargo's text (stderr), then whatever stdout carried that is
        # not one of cargo's JSON messages.
        sys.stdout.write(held)
        sys.stdout.write("".join(line for line in messages if _cargo_message(line) is None))
        sys.stdout.flush()
    if rc is None:
        return 3, f"{_why(deadline)} building targo-trust ({time.monotonic() - t0:.0f}s in)"
    if rc != 0:
        return 1, (f"targo-trust FAILED TO BUILD (exit {rc}): the tests that run it cannot "
                   f"run, and are never skipped: `{spelled}`")
    if not built:
        return 2, f"`{spelled}` exited 0 but no compiler-artifact message named the targo-trust bin"
    copy = os.path.join(private_dir, Path(built).name)
    try:
        copied = clone_or_copy(built, copy, deadline)
    except OSError as exc:
        return 2, f"cannot copy {built} into {private_dir}: {exc}"
    if not copied:
        return 3, f"{_why(deadline)} copying targo-trust ({time.monotonic() - t0:.0f}s in)"
    print(f"--- targo-trust: built {built} (exit 0, {time.monotonic() - t0:.0f}s; its "
          f"{held.count(chr(10))} lines of build output are shown only on a failure); "
          f"the tests get the copy {TARGO_TRUST_VAR}={copy}", flush=True)
    return 0, copy


_RUNNING = re.compile(r"^\s*Running (?:unittests )?\S+ \((?P<path>[^)]+)\)\s*$")
# libtest spells a #[should_panic] test `test <name> - should panic ... <outcome>`.
_RESULT = re.compile(r"^test (?P<name>\S+)(?: - should panic)? \.\.\. (?P<outcome>ok|FAILED)\s*$")


def binary_name(path: str) -> str:
    """A test binary's name as the known-red keys spell it: cargo's hash dropped."""
    return re.sub(r"-[0-9a-f]{8,}$", "", Path(path.strip()).name)


def parse_results(text: str) -> Tuple[set, set]:
    """(failed, passed) test keys `<binary>::<test path>` from cargo test output."""
    failed: set = set()
    passed: set = set()
    binary = "?"
    for line in text.splitlines():
        m = _RUNNING.match(line)
        if m:
            binary = binary_name(m.group("path"))
            continue
        m = _RESULT.match(line)
        if m:
            key = f"{binary}::{m.group('name')}"
            (failed if m.group("outcome") == "FAILED" else passed).add(key)
    return failed, passed


def load_known_red(path: Path) -> Dict[str, bool]:
    """Known-red rows: key -> True when tagged `[flaky]` (may pass or fail)."""
    rows: Dict[str, bool] = {}
    if not path.exists():
        return rows
    for raw in path.read_text().splitlines():
        body, _, comment = raw.partition("#")
        key = body.strip()
        if key:
            rows[key] = "[flaky]" in comment
    return rows


def judge(rc: int, text: str, known: Dict[str, bool]) -> Tuple[bool, List[str]]:
    """(ok, report lines) for one run under the known-red ratchet."""
    failed, passed = parse_results(text)
    report: List[str] = []
    ok = True
    if rc != 0 and not failed:
        report.append("FAILED WITHOUT A TEST FAILURE (a compile error or a crash): nothing is excused")
        ok = False
    unexpected = sorted(k for k in failed if k not in known)
    excused = sorted(k for k in failed if k in known)
    stale = sorted(k for k in passed if k in known and not known[k])
    for key in excused:
        report.append(f"known red (listed in {KNOWN_RED_REL}): {key}")
    for key in unexpected:
        report.append(f"NEW FAILURE: {key}")
        ok = False
    for key in stale:
        report.append(f"STALE KNOWN-RED ROW, the test now passes: delete it from {KNOWN_RED_REL}: {key}")
        ok = False
    return ok, report


# Cargo's test runner during the record pass: save how cargo would run this
# binary (argv, working directory, environment) and run nothing. Cargo runs
# binaries one at a time, so the file's sequence number is cargo's order, and
# "x" makes two runners at once (cargo never does that) collide and fail the
# record pass rather than lose a binary. Inline and `-S`: it starts once per
# binary, and importing this module and `site` doubled that cost.
RECORDER = (
    "import json, os, sys\n"
    "d = sys.argv[1]\n"
    "with open(os.path.join(d, '%06d.json' % len(os.listdir(d))), 'x', encoding='utf-8') as fh:\n"
    "    json.dump({'argv': sys.argv[2:], 'cwd': os.getcwd(), 'env': dict(os.environ)}, fh)\n"
)


def runner_config(record_dir: str) -> str:
    """The `--config` that makes cargo hand every test binary to RECORDER.

    `cfg(all())` matches every target, so no triple is spelled; a TOML array,
    so a path with spaces stays one argument. sys.executable, never a
    `#!/usr/bin/env` script: macOS strips DYLD_* from the environment of a
    SIP-protected executable, and cargo's DYLD_FALLBACK_LIBRARY_PATH must reach
    the record intact (load_invocations refuses a Darwin record without it)."""
    return "target.'cfg(all())'.runner=" + json.dumps([sys.executable, "-S", "-c", RECORDER, record_dir])


def with_runner_config(cmd: List[str], record_dir: str) -> List[str]:
    """`cmd` with runner_config's `--config` among cargo's own arguments: before
    a `--`, if the command has one. Appended after it (as before 2026-10-01),
    cargo hands `--config` to the test binary as a filter, runs none through
    RECORDER, and load_invocations refuses the record ("cargo announced 1 test
    binaries but handed 0 to the runner") for every CROSS_CRATE_INSTRUMENTS
    command, whose tail ends in `-- <filter>`."""
    config = ["--config", runner_config(record_dir)]
    if "--" in cmd:
        at = cmd.index("--")
        return cmd[:at] + config + cmd[at:]
    return cmd + config


class Binary:
    """One recorded test binary: how cargo would run it, and how it ran."""

    def __init__(self, record: dict, display: str) -> None:
        self.argv: List[str] = record["argv"]
        self.cwd: str = record["cwd"]
        self.env: Dict[str, str] = record["env"]
        self.display = display
        self.rc: Optional[int] = None
        self.output = ""
        self.seconds = 0.0

    def text(self) -> str:
        """This binary's part of the output judge() reads, as cargo prints it,
        ending in a newline so the next binary's `Running` line starts a line."""
        tail = "" if self.output.endswith("\n") or not self.output else "\n"
        return f"{self.display}\n{self.output}{tail}"


def load_invocations(record_dir: str, output: str) -> List[Binary]:
    """The record pass's binaries in cargo's order, each with the `Running ...`
    line cargo printed for it (matched by file name), which is what
    parse_results keys every test by. Every binary cargo announced must have
    been recorded: one it ran itself, bypassing the runner, would be judged on
    nothing, so a mismatch refuses."""
    shown = {}
    announced = 0
    for line in output.splitlines():
        m = _RUNNING.match(line)
        if m:
            announced += 1
            shown[Path(m.group("path").strip()).name] = line.rstrip()
    names = sorted(os.listdir(record_dir))
    if announced != len(names):
        raise RuntimeError(
            f"cargo announced {announced} test binaries but handed {len(names)} to the runner, "
            "so it ran some itself"
        )
    binaries = []
    for name in names:
        with open(os.path.join(record_dir, name), encoding="utf-8") as fh:
            record = json.load(fh)
        exe = record["argv"][0]
        if sys.platform == "darwin" and "DYLD_FALLBACK_LIBRARY_PATH" not in record["env"]:
            raise RuntimeError(
                f"the record of {exe} has no DYLD_FALLBACK_LIBRARY_PATH, which cargo always sets on "
                f"macOS: {sys.executable} stripped it (SIP), so a replay would not be cargo's run"
            )
        display = shown.get(Path(exe).name, f"     Running {exe} ({exe})")
        binaries.append(Binary(record, display))
    return binaries


MAX_DEFAULT_JOBS = 4


def default_jobs() -> int:
    """How many test binaries run at once: a quarter of the cores (an unmanaged
    libtest binary can already use every core; managed workers are divided
    across this pool before recording), the memory plan of
    scripts/lib/host_budget.py for one `crates-test` child (16 GiB wanted per
    binary, read against the memory AVAILABLE NOW less a reserve, not the
    host's total: 2026-10-14), and never more than MAX_DEFAULT_JOBS, the most
    measured without a new red: on 2026-09-29, 8 jobs bought 5% over 4 and
    turned a wall-clock assertion red. Raise the cap only with a measurement at
    the new value. A host the helper cannot measure, or one where not even one
    binary's floor fits, gets 1 (the lane's own budget and the governor are the
    backstop; the binaries then run one at a time)."""
    cores = os.cpu_count() or 1
    mem_jobs = 1
    try:
        sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
        import host_budget  # noqa: E402  (scripts/lib/host_budget.py, Python 3.9 compatible)
        host = host_budget.measure()
        plan = host_budget.plan(host, "crates-test")
        print(host_budget.describe_plan(host, plan), file=sys.stderr)
        mem_jobs = plan.jobs if plan.admitted else 1
    except Exception as exc:  # noqa: BLE001 - any failure to measure sizes down, never up
        print(f"crates-tests: host budget unavailable ({exc}); one binary at a time", file=sys.stderr)
    return max(1, min(MAX_DEFAULT_JOBS, cores // 4, mem_jobs))


def managed_test_threads(jobs: int) -> Optional[int]:
    """Choose libtest's per-binary allowance BEFORE Cargo records its env.

    One managed share belongs to the whole configured binary pool. Floor
    division can leave capacity unused, including in RUN_ALONE; changing a
    recorded binary's allowance later would violate exact Cargo replay.
    Unmanaged callers keep Cargo's original environment and behavior.
    """
    if os.environ.get("BUILD_SLOT_HELD") != "1":
        return None

    def positive(name: str) -> int:
        raw = os.environ.get(name, "")
        if not re.fullmatch(r"[0-9]+", raw):
            raise ValueError(f"{name} must be a positive integer in a build-slot job")
        try:
            value = int(raw)
        except ValueError:
            raise ValueError(f"{name} is too large to parse") from None
        if value < 1:
            raise ValueError(f"{name} must be a positive integer in a build-slot job")
        return value

    share = positive("CARGO_BUILD_JOBS")
    if "TRUST_CRATES_TESTS_JOBS" in os.environ:
        positive("TRUST_CRATES_TESTS_JOBS")
    if jobs > share:
        raise ValueError(f"TRUST_CRATES_TESTS_JOBS={jobs} exceeds admitted CARGO_BUILD_JOBS={share}")
    threads = share // jobs
    if "RUST_TEST_THREADS" in os.environ:
        threads = min(threads, positive("RUST_TEST_THREADS"))
    return threads


def _file_size(path: str) -> int:
    try:
        return os.path.getsize(path)
    except OSError:
        return 0


def _kill_group(proc: subprocess.Popen) -> None:
    """TERM, then KILL, with the same reserved-identity rule as cancellation."""
    _signal_group(proc, signal.SIGTERM)
    with contextlib.suppress(subprocess.TimeoutExpired):
        _wait_for_exit(proc, timeout=10)
    # Even a terminated leader can leave TERM-ignoring group descendants.
    # Finish group signals while its waitable PID still reserves that PGID.
    _signal_group(proc, signal.SIGKILL)
    with contextlib.suppress(subprocess.TimeoutExpired):
        _wait(proc, timeout=10)


# How long a binary's output is still read after the binary itself has ended.
OUTPUT_GRACE_S = 10


def run_one(binary: Binary, deadline: Deadline) -> None:
    """Run one binary with cargo's argv, directory and environment, and wait for
    the PROCESS, as cargo does — not for EOF on its output, which a process it
    started (a solver, a trustd) can hold open long after it exits. The output
    is read for OUTPUT_GRACE_S more, then judged as it stands, saying so. At the
    deadline the binary's process group is killed and its rc stays None. Each
    line it prints while it runs, and its end, are progress (TimeBound); its
    start is not, as it always follows another binary's end or an admission at
    once; nor is a line read after its end, which can only come from a process
    it left holding its output open, and which must not keep a hang in another
    binary from stalling the lane (that leftover could otherwise defer the
    stall bound to the ceiling)."""
    t0 = time.monotonic()
    try:
        proc = _spawn(
            binary.argv, cwd=binary.cwd, env=binary.env,
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, errors="replace",
        )
    except OSError as exc:  # a failed binary, never a skipped one
        binary.rc, binary.output = 127, f"cannot start {binary.argv[0]}: {exc}\n"
        return
    if proc is None:  # the lane is being interrupted: not started, not judged
        binary.output = "[crates-tests: not started: the lane was interrupted]\n"
        return
    lines: List[str] = []
    ended = threading.Event()

    def pump() -> None:
        assert proc.stdout is not None
        with proc.stdout:
            for line in proc.stdout:
                lines.append(line)
                if not ended.is_set():
                    _progress(deadline)

    reader = threading.Thread(target=pump, daemon=True)
    reader.start()
    binary.rc = _wait_until(proc, deadline)
    ended.set()
    if binary.rc is None:
        _kill_group(proc)
    else:
        _progress(deadline)
    _untrack(proc)
    reader.join(timeout=OUTPUT_GRACE_S)
    binary.output = "".join(list(lines))
    if reader.is_alive():
        binary.output += (
            f"[crates-tests: a process this binary started still held its output open "
            f"{OUTPUT_GRACE_S}s after it ended; judged on the output above]\n"
        )
    binary.seconds = time.monotonic() - t0


# MACOS FIRST-EXEC ADMISSION (2026-10-09; the header's "ONE AT A TIME THROUGH
# MACOS'S FIRST-EXEC CHECK"). The variable that turns it off, for an A/B
# measurement or a host where it misbehaves; anything but "0" leaves it on.
ADMIT_ENV = "TRUST_CRATES_TESTS_ADMIT"
# The one platform with the check (the regression test points it at its own).
ADMIT_PLATFORM = "darwin"
# The argv a probe carries, should dyld ever not stop it: libtest then lists
# the tests named exactly this, which is none, and runs nothing.
ADMIT_NO_TEST = "trust-crates-tests-admission-probe-names-no-test"
# Mach-O, read only as far as admissible() needs.
_MH_MAGIC_64 = 0xFEEDFACF
_MH_EXECUTE = 2
_LC_SEGMENT_64 = 0x19
_LC_CODE_SIGNATURE = 0x1D
_CSMAGIC_EMBEDDED_SIGNATURE = 0xFADE0CC0
_CSMAGIC_CODEDIRECTORY = 0xFADE0C02
# A probe is made only of an ad hoc signed executable (CS_ADHOC, with
# CS_LINKER_SIGNED at most: what the linker gives every cargo test binary on
# Apple silicon) that is not a platform binary. Any other flag (CS_RUNTIME,
# CS_RESTRICT, ...), an Apple signature (the SIP-protected /bin, /usr/bin
# tools), or no signature at all, and dyld may ignore DYLD_* variables: a
# probe whose DYLD_INSERT_LIBRARIES is ignored would run the program.
_CS_ADHOC = 0x2
_CS_ALLOWED_FLAGS = _CS_ADHOC | 0x20000
# The SuperBlob slots that hold a CodeDirectory: the primary, and the
# alternates (CSSLOT_ALTERNATE_CODEDIRECTORIES) a multi-digest signature adds,
# whose strongest-hash one the kernel enforces. Only a signature with exactly
# one, in the primary slot, is read as what dyld will honour.
_CD_SLOTS = (0,) + tuple(range(0x1000, 0x1005))
# A probe's own ceilings, inside the lane's budget, so that one probe that
# never parks can never hold every worker until the deadline. From its start:
# generous against the measured clearances (0.2-5s idle; one every 39s, and an
# 85s wait, in a loaded landing push's shared queue). From dyld's first line:
# the check is over once dyld runs, and its FIFO line follows within
# milliseconds. Either one passed is a misbehaviour: admission stops and every
# binary after it pays the check itself, as before admission existed.
ADMIT_PROBE_MAX_S = 300.0
ADMIT_DYLD_MAX_S = 10.0
# How long a SIGKILLed probe is waited for. One killed in the kernel's hold was
# reaped in 0.32s (measured); past this it is left to die on its own, and
# admission stops rather than hold the lane past its budget.
ADMIT_REAP_S = 10.0


def admissible(path: str) -> Optional[str]:
    """None when a probe (admit_one) stops `path` inside dyld for certain:
    a thin 64-bit Mach-O executable, not setuid/setgid, without a __RESTRICT
    segment, with an ad hoc code signature (linker-signed at most) that is not
    a platform binary's. Otherwise why not; such a binary is not probed and
    pays macOS's check itself, as every binary did before admission existed."""
    import stat as stat_mod
    import struct

    try:
        st = os.stat(path)
        if st.st_mode & (stat_mod.S_ISUID | stat_mod.S_ISGID):
            return "setuid/setgid"
        with open(path, "rb") as fh:
            head = fh.read(32)
            if len(head) < 32 or struct.unpack_from("<I", head)[0] != _MH_MAGIC_64:
                return "not a thin 64-bit Mach-O"
            _, _, _, filetype, ncmds, sizeofcmds, _, _ = struct.unpack_from("<IiiIIIII", head)
            if filetype != _MH_EXECUTE:
                return "not a Mach-O executable"
            cmds = fh.read(sizeofcmds)
            signature = None
            at = 0
            for _ in range(ncmds):
                cmd, size = struct.unpack_from("<II", cmds, at)
                if size < 8:
                    return "malformed load commands"
                if cmd == _LC_SEGMENT_64 and cmds[at + 8:at + 24].rstrip(b"\0") == b"__RESTRICT":
                    return "has a __RESTRICT segment"
                if cmd == _LC_CODE_SIGNATURE:
                    signature = struct.unpack_from("<II", cmds, at + 8)
                at += size
            if signature is None:
                return "not code-signed"
            fh.seek(signature[0])
            blob = fh.read(signature[1])
        magic, _, count = struct.unpack_from(">III", blob)
        if magic != _CSMAGIC_EMBEDDED_SIGNATURE:
            return "unreadable code signature"
        directories = []
        for i in range(count):
            slot, offset = struct.unpack_from(">II", blob, 12 + 8 * i)
            if slot in _CD_SLOTS:
                directories.append((slot, offset))
        if not directories:
            return "no code directory"
        if len(directories) != 1 or directories[0][0] != 0:
            # The kernel enforces the strongest-hash CodeDirectory's flags,
            # which need not be the primary's: read none of them as certain.
            return f"{len(directories)} code directories (a multi-digest signature)"
        offset = directories[0][1]
        cd_magic, _, _, flags = struct.unpack_from(">IIII", blob, offset)
        platform = blob[offset + 38]
        if cd_magic != _CSMAGIC_CODEDIRECTORY:
            return "unreadable code directory"
        if not flags & _CS_ADHOC or flags & ~_CS_ALLOWED_FLAGS:
            return f"not an ad hoc signature (code signature flags {flags:#x})"
        if platform:
            return "a platform binary"
        return None
    except (OSError, struct.error, IndexError) as exc:
        return f"unreadable: {exc}"


def admit_one(exe: str, env: Dict[str, str], directory: str, deadline: Deadline) -> Tuple[str, str]:
    """Carry `exe` through macOS's first-exec check without running any of it.

    The probe is `exe` itself (through a hard link in `directory`, see below),
    started with DYLD_INSERT_LIBRARIES naming a FIFO
    nobody ever writes. The kernel holds a newly linked executable at its first
    exec until the check clears it; then dyld starts, and with
    DYLD_PRINT_SEARCHING it says `find path "<fifo>"` just before it opens the
    FIFO, where it blocks: dyld loads inserted libraries before it runs any
    initializer, so neither the program nor any library initializer has run.
    That line is the proof the check is done; the probe is then killed (SIGKILL:
    no crash report, which dyld's own failure, a missing library or a FIFO
    with a writer, would leave).

    Returns (outcome, detail): "admitted"; "skipped" (admissible() refused it,
    or the probe could not start: it pays the check itself); "deadline" (the
    budget ran out first, or the lane is being interrupted); or "misbehaved"
    (the probe printed something other than dyld's lines, ended on its own or
    was killed by someone else, passed ADMIT_PROBE_MAX_S or ADMIT_DYLD_MAX_S,
    or was not reaped ADMIT_REAP_S after its SIGKILL: dyld may not have
    stopped it, or admission costs more than it saves, and the caller probes
    nothing more). The probe's stdout and stderr are one pipe, read line by
    line: any line that is not dyld's is a misbehaviour."""
    why = admissible(exe)
    if why:
        return "skipped", why
    fifo = os.path.join(directory, "never-written.dylib")
    if not os.path.exists(fifo):
        os.mkfifo(fifo)
    # The probe execs a hard link in `directory`: the same file (the check's
    # verdict is the file's, so the binary at its own path then starts at
    # once), but named from a directory of two entries. The check's cost
    # grows with the directory an executable is exec'd from (measured: a
    # 1.7 MB binary 0.2-0.3s from an empty directory, ~5s from one of 600k
    # entries; crates/target/debug/deps held 1.16M). Where no link can be made
    # (another volume), the probe execs `exe` itself.
    link = os.path.join(directory, "admit-" + Path(exe).name)
    try:
        with contextlib.suppress(FileNotFoundError):
            os.unlink(link)
        # Under _SPAWN_LOCK, as a spawn is: the interrupt handler sets
        # _STOPPING and takes this lock before it removes the scratch
        # directories, so a link is either made before that removal (and
        # removed with the directory) or never made.
        with _process_state():
            if _STOPPING.is_set():
                return "deadline", "the lane is being interrupted"
            os.link(exe, link)
        target = link
    except OSError:
        target = exe
    try:
        return _probe(target, env, directory, fifo, deadline)
    finally:
        if target == link:
            with contextlib.suppress(OSError):
                os.unlink(link)


def _probe(target: str, env: Dict[str, str], directory: str, fifo: str, deadline: Deadline) -> Tuple[str, str]:
    """admit_one's probe of `target`, an admissible executable or a hard link to one."""
    probe_env = {k: v for k, v in env.items() if k.startswith("DYLD_")}
    probe_env.update(DYLD_INSERT_LIBRARIES=fifo, DYLD_PRINT_SEARCHING="1")
    try:
        proc = _spawn(
            [target, "--list", "--exact", ADMIT_NO_TEST], cwd=directory, env=probe_env,
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
    except OSError as exc:
        return "skipped", f"cannot start: {exc}"
    if proc is None:
        return "deadline", "the lane is being interrupted"
    started = time.monotonic()
    parked = threading.Event()
    stray: List[str] = []
    dyld_since: List[float] = []  # when dyld's first line came: the check is over
    expect = f'dyld[{proc.pid}]: find path "{fifo}"'

    def watch() -> None:
        assert proc.stdout is not None
        for raw in proc.stdout:
            line = raw.decode("utf-8", "replace").rstrip("\n")
            if line == expect:
                parked.set()
                return
            if not line.startswith(f"dyld[{proc.pid}]: "):
                stray.append(line)
                return
            if not dyld_since:
                dyld_since.append(time.monotonic())

    reader = threading.Thread(target=watch, daemon=True)
    reader.start()
    stopped = ""  # why the wait ended without the probe parking, printing or exiting
    while not parked.is_set() and not stray:
        if _exited(proc):
            stopped = "exited"
            break
        now = time.monotonic()
        left = _left(deadline)
        if left <= 0:
            stopped = "deadline"
            break
        if now - started >= ADMIT_PROBE_MAX_S:
            stopped = f"neither through macOS's check nor stopped in dyld after {ADMIT_PROBE_MAX_S:.0f}s"
            break
        if dyld_since and now - dyld_since[0] >= ADMIT_DYLD_MAX_S:
            stopped = (f"dyld ran but did not reach the FIFO in {ADMIT_DYLD_MAX_S:.0f}s "
                       "(its DYLD_PRINT_SEARCHING line was not the one expected)")
            break
        parked.wait(timeout=min(0.5, left))
    _signal_group(proc, signal.SIGKILL)
    try:
        _wait(proc, timeout=ADMIT_REAP_S)
    except subprocess.TimeoutExpired:
        # SIGKILLed; it is reaped whenever the kernel lets it go. Not waited
        # for: the lane's budget is the bound, not the host's queue.
        _untrack(proc)
        if stopped == "deadline":
            return "deadline", "the budget ran out during macOS's first-exec check"
        return "misbehaved", f"the SIGKILLed probe was not reaped in {ADMIT_REAP_S:.0f}s"
    _untrack(proc)
    reader.join(timeout=OUTPUT_GRACE_S)
    if proc.stdout is not None and not reader.is_alive():
        with contextlib.suppress(OSError):
            proc.stdout.close()
    if parked.is_set() and not stray:
        return "admitted", ""
    if stray:
        return "misbehaved", f"the probe was not stopped in dyld ({stray[0][:120]!r})"
    if stopped == "exited":
        # Ended before the lane killed it: on its own (dyld did not stop it),
        # or killed by someone else (jetsam, a user). Either way not admitted,
        # and no reason to trust the next probe.
        return "misbehaved", f"the probe ended before it was stopped in dyld (exit {proc.returncode})"
    if stopped == "deadline":
        return "deadline", "the budget ran out during macOS's first-exec check"
    return "misbehaved", stopped


class Admission:
    """Admits each executable, one at a time and in the pool's order (admit_one),
    on a thread of its own, so a worker finds its next binary already through
    macOS's check. Off macOS, or with ADMIT_ENV=0, it admits nothing and holds
    no worker back."""

    def __init__(self, runs: List[List[Binary]], deadline: Deadline) -> None:
        self.order = [(os.path.realpath(r[0].argv[0]), r[0].env) for r in runs]
        self.ready = {exe: threading.Event() for exe, _ in self.order}
        self.deadline = deadline
        self.enabled = sys.platform == ADMIT_PLATFORM and os.environ.get(ADMIT_ENV, "1") != "0"
        self.counts: Dict[str, int] = {}
        self.notes: List[str] = []
        self.seconds = 0.0
        self.thread: Optional[threading.Thread] = None

    def start(self, directory: str) -> None:
        if not self.enabled:
            for event in self.ready.values():
                event.set()
            return
        self.thread = threading.Thread(target=self._run, args=(directory,), daemon=True)
        self.thread.start()

    def _run(self, directory: str) -> None:
        t0 = time.monotonic()
        try:
            for exe, env in self.order:
                if _STOPPING.is_set() or _left(self.deadline) <= 0:
                    break
                try:
                    outcome, detail = admit_one(exe, env, directory, self.deadline)
                except Exception as exc:  # pylint: disable=broad-except
                    # mkfifo/link/spawn failing in a way admit_one does not
                    # expect (EACCES, ENOSPC, a TMPDIR without FIFOs): stop
                    # admitting, say so, and let every binary run as before.
                    outcome, detail = "failed", f"{type(exc).__name__}: {exc}"
                self.counts[outcome] = self.counts.get(outcome, 0) + 1
                if outcome == "skipped":
                    self.notes.append(f"not admitted ahead, pays the check itself: {Path(exe).name}: {detail}")
                if outcome in ("misbehaved", "failed"):
                    self.notes.append(f"admission STOPPED at {Path(exe).name}: {detail}; every binary "
                                      "after it pays macOS's check itself")
                    self.ready[exe].set()
                    break
                if outcome == "admitted":
                    _progress(self.deadline)
                self.ready[exe].set()
        finally:
            self.seconds = time.monotonic() - t0
            for event in self.ready.values():
                event.set()

    def wait(self, exe: str) -> bool:
        """Until `exe` is admitted (or admission gave up on it); False at the deadline."""
        return _event_until(self.ready[os.path.realpath(exe)], self.deadline)

    def summary(self) -> Optional[str]:
        if not self.enabled:
            return None
        made = ", ".join(f"{n} {k}" for k, n in sorted(self.counts.items())) or "none"
        if self.counts.get("misbehaved"):
            # A misbehaving probe may be one dyld did NOT stop: that binary
            # may have run once already, with the probe's argv (`--list
            # --exact <no test>`), the scratch directory and a DYLD_*-only
            # environment, before its judged run.
            ran = ("a probe that misbehaved may have run its binary's code once, with the probe's argv, "
                   "directory and environment, before that binary's judged run")
        else:
            ran = "no probe ran any code of the binary"
        return (f"--- macOS first-exec admission, one at a time ahead of the pool ({ADMIT_ENV}=0 turns "
                f"it off): {made} of {len(self.order)} executables in {self.seconds:.0f}s; {ran}")


def run_binaries(binaries: List[Binary], jobs: int, deadline: Deadline) -> bool:
    """Run every binary, `jobs` at a time (run_one). Each block is printed as its
    binary ends. False when the deadline killed or never started one (its rc
    stays None).

    Biggest file first: a crate's lib unittest binary carries its whole suite
    and is the long pole (trust-clean's ran 322-367s on 2026-09-29), and started
    in cargo's order behind the small ones it would leave the pool idle at the
    end. The order a binary starts in changes nothing it reports.

    One executable never runs twice at once. Two commands can record the same
    one (feature unification can make them build the same unit), and cargo
    would have run it twice, one after the other; beside itself its fixed temp
    paths would collide. So a worker takes all runs of one executable, in order.

    On macOS each executable is first carried through the OS's first-exec
    check by Admission, one at a time and in this same order, and a worker
    starts a binary only once it is through (the header's "ONE AT A TIME
    THROUGH MACOS'S FIRST-EXEC CHECK"). A worker that reaches the deadline
    still waiting starts nothing, and the binary is not judged, as a binary
    the deadline never let start always was."""
    by_exe: Dict[str, List[Binary]] = {}
    for binary in binaries:
        by_exe.setdefault(os.path.realpath(binary.argv[0]), []).append(binary)
    pending = sorted(by_exe.values(), key=lambda runs: -_file_size(runs[0].argv[0]))
    admission = Admission(list(pending), deadline)
    lock = threading.Lock()
    expired = threading.Event()
    finished = [0]

    def worker() -> None:
        while True:
            with lock:
                if expired.is_set() or not pending:
                    return
                runs = pending.pop(0)
            for binary in runs:
                if expired.is_set() or not admission.wait(binary.argv[0]) or _left(deadline) <= 0:
                    expired.set()
                    return
                with lock:
                    sys.stdout.write(f"--- started: {Path(binary.argv[0]).name}\n")
                    sys.stdout.flush()
                run_one(binary, deadline)
                if binary.rc is None:
                    expired.set()
                with lock:
                    finished[0] += 1
                    status = "KILLED at the deadline" if binary.rc is None else f"exit {binary.rc}"
                    tail = "" if binary.output.endswith("\n") or not binary.output else "\n"
                    sys.stdout.write(
                        f"{binary.display}\n{binary.output}{tail}"
                        f"--- {status} in {binary.seconds:.0f}s ({finished[0]}/{len(binaries)})\n"
                    )
                    sys.stdout.flush()

    with _scratch_dir("crates-tests-admit.") as directory:
        admission.start(directory)
        threads = [threading.Thread(target=worker, daemon=True) for _ in range(min(jobs, len(pending)))]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join()
        if admission.thread is not None:  # a probe is never left behind in the directory
            admission.thread.join()
    summary = admission.summary()
    if summary:
        print(summary, flush=True)
        for note in admission.notes:
            print(f"  {note}", flush=True)
    return all(b.rc is not None for b in binaries)


# libtest's contract: `running N tests` first; last, `test result: ok.` and
# exit 0, or `test result: FAILED.` and exit 101, counting its failures.
_LIBTEST_START = re.compile(r"^running \d+ tests?$", re.M)
_LIBTEST_END = re.compile(r"^test result: (ok|FAILED)\. \d+ passed; (\d+) failed;", re.M)
# The same closing line, read for how many tests it says were judged.
_LIBTEST_COUNTS = re.compile(r"^test result: (?:ok|FAILED)\. (\d+) passed; (\d+) failed;", re.M)


def binary_problem(binary: Binary) -> Optional[str]:
    """Why this binary's run fails the lane whatever its test lines say, or None.

    judge() excuses a non-zero exit once a known-red failure is among the parsed
    ones. That is right for a binary libtest ran to the end and wrong for one
    that died mid-run: every test it had not reported yet went unjudged, and a
    known-red line printed before a SIGKILL (jetsam, the OOM killer) or a
    `process::exit` would pass the lot. So each binary is held to libtest's
    contract, and the failures libtest counts must all have been read. A binary
    that never started libtest (a `harness = false` target, one that died before
    `main`, one that could not start) passes only on exit 0."""
    rc, out = binary.rc, binary.output
    if not _LIBTEST_START.search(out):
        return None if rc == 0 else f"exit {rc} with no libtest run (a crash before main, or it could not start)"
    want = {0: "ok", 101: "FAILED"}.get(rc)
    if want is None:
        return f"exit {rc} is not libtest's 0 or 101: killed, crashed or aborted mid-run"
    summary = _LIBTEST_END.findall(out)
    if not summary or summary[-1][0] != want:
        return f"exit {rc} without libtest's closing `test result: {want}.`: it ended mid-run"
    failed = parse_results(binary.text())[0]
    if rc != 0 and not failed:
        return f"exit {rc} with no test failure the lane could read"
    if len(failed) < int(summary[-1][1]):
        return f"libtest counted {summary[-1][1]} failure(s), the lane read {len(failed)} `test ... FAILED` line(s)"
    return None


def reported_tests(binary: Binary) -> int:
    """How many tests this binary REPORTED judging: passed + failed on libtest's
    closing `test result:` line (ignored and filtered-out tests judge nothing).
    A binary that never started libtest (a `harness = false` target) counts as
    one test whose verdict is its exit code, which binary_problem holds to 0.
    That trusts the target to check something when it exits 0: a target with no
    `main` does not build, but one whose `main` a cfg empties (or a `#![no_main]`
    one whose extern `main` does nothing) exits 0 having checked nothing, and
    this rule cannot see it. Today's only such target, trust-platform's
    `conformance_darwin` (`#![no_main]`, its extern "C" `main` not cfg-gated),
    sits beside its crate's lib tests. A libtest run that never closed reports
    nothing (and binary_problem fails it)."""
    if not _LIBTEST_START.search(binary.output):
        return 1
    summary = _LIBTEST_COUNTS.findall(binary.output)
    if not summary:
        return 0
    passed, failed = summary[-1]
    return int(passed) + int(failed)


def tests_reported(plan: Plan, records: Sequence[Tuple[str, int, List[Binary], Optional[str]]]) -> Dict[str, int]:
    """Tests REPORTED (reported_tests) per crate the push touches, summed over
    every run that tests it: a member's binaries in the shared default run and
    in its FEATURE_RUNS tails, each credited to the package cargo ran it for
    (CARGO_PKG_NAME in its record; a record without one credits nobody, so its
    member stays at 0), and an own-workspace crate's in its own run. An
    instrument run credits nobody (Plan.attributed_commands).

    THE ZERO-TEST RULE (2026-10-09). A touched crate whose total is 0 was not
    judged, whatever its runs' exit codes say: libtest exits 0 on `running 0
    tests`, and a crate whose tests all sit behind a feature no run enables (as
    trust-ny-bridge's 28 sat behind `ny`) printed PASS on this lane while
    judging nothing. The rule is per crate, over ALL its runs, never per
    binary: a member's bin targets and helper files report `running 0 tests`
    as a matter of course. It does not see a crate that reports SOME tests
    while a feature compiles out others (trust-bmc's tail ran 156 and compiled
    out 52 until 2026-10-09): only a tail in the shipped set does."""
    counts: Dict[str, int] = {pkg: 0 for pkg in plan.packages}
    counts.update({root: 0 for root in plan.own_workspaces})
    for _, _, binaries, credit in records:
        if credit is None:
            continue
        for binary in binaries:
            owner = binary.env.get("CARGO_PKG_NAME") if credit == MEMBERS else credit
            if owner in counts:
                counts[owner] += reported_tests(binary)
    return counts


def instrument_problem(spelled: str, binaries: Sequence[Binary]) -> Optional[str]:
    """Why an instrument run (`... -p <host> <tail>`) judged nothing, or None: its
    binaries reported no test (reported_tests), or a test INSTRUMENT_REQUIRED_PASSES
    names for its host did not print `test <name> ... ok`."""
    words = spelled.split()
    host = words[words.index("-p") + 1] if "-p" in words[:-1] else ""
    if sum(reported_tests(b) for b in binaries) == 0:
        return "its binaries reported 0 tests (passed + failed): its filter matched nothing"
    for name in INSTRUMENT_REQUIRED_PASSES.get(host, ()):
        line = re.compile(rf"^test {re.escape(name)} \.\.\. ok$", re.M)
        if not any(line.search(b.output) for b in binaries):
            return f"`test {name} ... ok` is not in its output"
    return None


def judge_command(record_rc: int, binaries: List[Binary], known: Dict[str, bool]) -> Tuple[bool, List[str], int]:
    """judge() over one command's binaries, as if cargo had run them, and the
    exit code cargo would have given: the record pass's when the build failed,
    else 101 when any binary failed. Plus what that single exit code hid: a
    record pass that exited non-zero fails the command whatever the binaries did
    (it runs no test, so its exit code is never a test failure a known-red row
    could excuse), and so does every binary binary_problem() names."""
    rc = record_rc or (101 if any(b.rc != 0 for b in binaries) else 0)
    ok, report = judge(rc, "".join(b.text() for b in binaries), known)
    if record_rc != 0:
        report.append(f"THE BUILD-AND-RECORD PASS EXITED {record_rc} (a compile error, or the recorder failed): nothing is excused")
        ok = False
    for b in binaries:
        problem = binary_problem(b)
        if problem:
            report.append(f"BINARY FAILED OUTSIDE ITS TEST LINES ({problem}): {b.display.strip()}")
            ok = False
    return ok, report, rc


def plan_time_bound(plan: Plan, env: Optional[Dict[str, str]] = None) -> Tuple[int, int, str]:
    """(ceiling s, stall s, the `time bound:` line) for a run of `plan`: the one
    rule (scripts/lib/crates_tests_time.py) over the crates it tests
    (Plan.crates()), whoever called the lane. The hook's lane and the land
    gate's leg get the same bound for the same number of crates
    (TimeBoundTest). ValueError for a TRUST_CRATES_TESTS_BUDGET_S or
    TRUST_CRATES_TESTS_STALL_S that is not a positive integer."""
    crates = plan.crates()
    return (crates_tests_time.budget_s(crates, env), crates_tests_time.stall_s(env),
            crates_tests_time.describe(crates, env))


def main(argv: Optional[Sequence[str]] = None) -> int:
    with forwarding_signals():
        return _main(argv)


def _main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Run crates/ tests for the crates a push touches.")
    parser.add_argument("--push-context", action="store_true", help="judge the refs in TRUST_PUSHED_REFS")
    parser.add_argument("--range", help="judge base...head instead (A..B)")
    parser.add_argument("--plan", action="store_true", help="print the plan and commands; run nothing")
    parser.add_argument("--also-members", default="",
                        help="comma-separated member dirs to test as well (scripts/land_gate.py: the members "
                             "the change reaches); only adds, and never drops an instrument run the range moves")
    args = parser.parse_args(argv)
    also = [d.strip().rstrip("/") for d in args.also_members.split(",") if d.strip()]

    started = time.monotonic()
    pushed = os.environ.get("TRUST_PUSHED_REFS", "")
    try:
        ranges, reading = resolve_ranges(args.push_context, args.range, pushed)
    except ValueError as exc:
        print(f"crates-tests: {exc}", file=sys.stderr)
        return 2
    print(f"SUBJECT ({reading}): {', '.join(ranges)}")
    try:
        paths = changed_paths(ranges)
    except RuntimeError as exc:
        # Red, not a skip: with no diff there is no member set to run, and
        # running every member would outlast the budget. Exit 2 blocks the push.
        print(f"crates-tests: could NOT READ the range — {exc}", file=sys.stderr)
        print("              usually a remote sha this clone never fetched (a force push over", file=sys.stderr)
        print("              someone else's tip): fetch, then retry. Nothing was judged.", file=sys.stderr)
        return 2

    # An instrument's subject can lie outside crates/ (any `*.json`, `proofs/codegen-equivalence/`):
    # such a push is in scope even with no crates/ path.
    if not also and not any(p.startswith("crates/") for p in paths) and not moved_instruments(paths):
        unrun = targo_trust_change_not_run(paths, ())
        if unrun:
            print(unrun)
        print(f"SKIPPED: no crates/ change in {len(paths)} changed path(s) — "
              f"{'see NOT RUN above' if unrun else 'this lane cannot be broken by it'}.")
        return 0

    try:
        meta_proc = subprocess.run(
            ["targo", "metadata", "--no-deps", "--format-version", "1", "--manifest-path", CRATES_MANIFEST],
            cwd=REPO_ROOT, capture_output=True, text=True, check=False,
        )
    except OSError as exc:
        print(f"crates-tests: cannot run `targo metadata`: {exc}", file=sys.stderr)
        return 2
    if meta_proc.returncode != 0:
        print(f"crates-tests: `targo metadata` failed:\n{meta_proc.stderr.strip()}", file=sys.stderr)
        return 2
    metadata = json.loads(meta_proc.stdout)
    try:
        members = workspace_members(metadata)
    except RuntimeError as exc:
        print(f"crates-tests: {exc}", file=sys.stderr)
        return 2
    if also:
        plan = plan_for(paths, members, own_workspace_roots(REPO_ROOT), also_dirs=also)
    else:
        plan = plan_for(paths, members, own_workspace_roots(REPO_ROOT))
    if plan.unknown_members:
        # LAND-GATE-HOOKLESS-1 round 5, D1: the land gate hands this lane the
        # members a change reaches and stores a PASS for each one when the lane
        # exits 0. Running without one of them and exiting 0 stored a PASS for a
        # crate nothing ran. A member here is a developer default-member or a
        # crates/<dir> own-workspace crate (scripts/lib/crates_lane_members.py).
        print(f"crates-tests: CANNOT JUDGE — --also-members names {len(plan.unknown_members)} dir(s) that are "
              f"no member of this lane (no developer default-member, no crates/<dir> own-workspace crate): "
              f"{', '.join(plan.unknown_members)}. Nothing ran: a pass here would be counted for crates no run "
              "tested.", file=sys.stderr)
        return 2
    try:
        plan.specs = package_specs(metadata, (REPO_ROOT / "Cargo.lock").read_text(encoding="utf-8"))
    except OSError:
        plan.specs = {}
    apply_host_limits(plan, REPO_ROOT, members)
    print_plan(plan)
    unrun = targo_trust_change_not_run(paths, plan.targo_trust_consumers())
    if unrun:
        print(unrun)
    if plan.empty():
        print("SKIPPED: the crates/ paths changed belong to no crate this lane can test (see above).")
        return 0

    problem = feature_target_directory_problem(plan, metadata, REPO_ROOT)
    if problem:
        print(f"crates-tests: CANNOT JUDGE — {problem}", file=sys.stderr)
        return 2

    commands = plan.commands()
    if args.plan:
        if plan.needs_targo_trust():
            print("would build: " + " ".join(TARGO_TRUST_BUILD))
        for cmd in commands:
            print("would run: " + " ".join(cmd))
        return 0

    problem = targo_is_targo()
    if problem:
        print(f"crates-tests: CANNOT JUDGE — {problem}", file=sys.stderr)
        return 2
    try:
        jobs = int(os.environ.get("TRUST_CRATES_TESTS_JOBS", default_jobs()))
    except ValueError:
        print("crates-tests: TRUST_CRATES_TESTS_JOBS must be an integer", file=sys.stderr)
        return 2
    if jobs < 1:
        print("crates-tests: TRUST_CRATES_TESTS_JOBS must be at least 1", file=sys.stderr)
        return 2
    try:
        test_threads = managed_test_threads(jobs)
    except ValueError as exc:
        print(f"crates-tests: CANNOT JUDGE — {exc}", file=sys.stderr)
        return 2
    if test_threads is not None:
        print(f"crates-tests: managed libtest allowance: CARGO_BUILD_JOBS={os.environ['CARGO_BUILD_JOBS']}, "
              f"binary pool={jobs}, inherited RUST_TEST_THREADS={os.environ.get('RUST_TEST_THREADS', 'unset')}; "
              f"recording RUST_TEST_THREADS={test_threads} before Cargo", flush=True)

    if not os.environ.get("CARGO_BUILD_JOBS"):
        # The build's rustc fan-out from the measured host (scripts/lib/host_budget.py,
        # `rustc-build`), not the repo-root .cargo/config.toml's `jobs = 4`, which
        # was sized for one 128 GiB host. A caller's CARGO_BUILD_JOBS wins.
        try:
            sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
            import host_budget  # noqa: E402
            host = host_budget.measure()
            bplan = host_budget.plan(host, "rustc-build")
            print(host_budget.describe_plan(host, bplan), file=sys.stderr)
            if bplan.admitted:
                os.environ["CARGO_BUILD_JOBS"] = str(bplan.jobs)
        except Exception as exc:  # noqa: BLE001 - unmeasurable: keep the configured default
            print(f"crates-tests: host budget unavailable ({exc}); keeping Cargo's configured jobs",
                  file=sys.stderr)

    try:
        budget, stall, bound_line = plan_time_bound(plan)
    except ValueError as exc:
        print(f"crates-tests: {exc}", file=sys.stderr)
        return 2
    barrier = os.environ.get(RUN_AFTER_ENV, "")
    try:
        owner_text = os.environ.get(RUN_AFTER_OWNER_ENV, "")
        owner = int(owner_text) if owner_text else None
        max_wait = float(os.environ.get(RUN_AFTER_MAX_ENV, DEFAULT_RUN_AFTER_MAX_S))
    except ValueError:
        print(f"crates-tests: {RUN_AFTER_OWNER_ENV} must be a pid and {RUN_AFTER_MAX_ENV} a number of seconds",
              file=sys.stderr)
        return 2
    # The one time-bound rule (scripts/lib/crates_tests_time.py), the same for
    # the hook and the land gate: a ceiling over the crates this run tests, and
    # a stall bound. Its ceiling counts from the lane's start, as the flat
    # budget did; its stall clock from here, before which the lane ran only
    # git and `targo metadata`.
    deadline = TimeBound(budget, stall, started=started)
    print(f"crates-tests: {bound_line}", flush=True)
    known = load_known_red(REPO_ROOT / KNOWN_RED_REL)
    not_judged = (
        "Nothing above counts as a pass. A STALL is a hang: find the binary that stopped\n"
        "printing above. A budget that ran out on a lane still moving: re-run with a larger\n"
        "TRUST_CRATES_TESTS_BUDGET_S, or run the commands yourself."
    )

    # 0. targo-trust, when a consumer's tests will run. Its private directory
    # holds the copy until every binary has run: they run after the record pass.
    with _scratch_dir("crates-tests-targo-trust.") as private:
        private_targo_trust: Optional[str] = None
        record_env: Optional[Dict[str, str]] = (
            dict(os.environ, RUST_TEST_THREADS=str(test_threads)) if test_threads is not None else None
        )
        if plan.needs_targo_trust():
            code, built = prebuild_targo_trust(deadline, private)
            if code == 3:
                print(f"\nNOT JUDGED: {built}.")
                for rest in commands:
                    print(f"  not run: {' '.join(rest)}")
                print(not_judged)
                return 3
            if code:
                print(f"crates-tests: {'CANNOT JUDGE — ' if code == 2 else ''}{built}", file=sys.stderr)
                return code
            record_env = dict(record_env if record_env is not None else os.environ, **{TARGO_TRUST_VAR: built})
            private_targo_trust = built

        # 1. Build each command's tests and record the binaries cargo would run.
        records: List[Tuple[str, int, List[Binary], Optional[str]]] = []
        with _scratch_dir("crates-tests-record.") as scratch:
            for index, (cmd, credit) in enumerate(plan.attributed_commands()):
                spelled = " ".join(cmd)
                record_dir = os.path.join(scratch, str(index))
                os.mkdir(record_dir)
                print(f"\nbuilding and recording: {spelled}", flush=True)
                t0 = time.monotonic()
                rc, output = run_with_deadline(with_runner_config(cmd, record_dir), deadline, record_env)
                if rc is None:
                    print(f"\nNOT JUDGED: {deadline.why()} building `{spelled}` "
                          f"({time.monotonic() - t0:.0f}s in).")
                    for rest in commands[index:]:
                        print(f"  not run: {' '.join(rest)}")
                    print(not_judged)
                    return 3
                try:
                    binaries = load_invocations(record_dir, output)
                except (OSError, ValueError, KeyError, RuntimeError) as exc:
                    print(f"crates-tests: CANNOT JUDGE — the record of `{spelled}` is unusable: {exc}", file=sys.stderr)
                    return 2
                if test_threads is not None:
                    lost = [b.argv[0] for b in binaries if b.env.get("RUST_TEST_THREADS") != str(test_threads)]
                    if lost:
                        print(f"crates-tests: CANNOT JUDGE — recorded RUST_TEST_THREADS differs from the "
                              f"managed allowance {test_threads}: {', '.join(lost)}", file=sys.stderr)
                        return 2
                # Cargo passes its own environment on; this checks it did, so the
                # tests run the copy and not whatever a stray variable named.
                handed = [b for b in binaries if b.env.get("CARGO_PKG_NAME") in TARGO_TRUST_CONSUMERS]
                if private_targo_trust is not None and handed:
                    want = private_targo_trust
                    lost = [b.argv[0] for b in handed if b.env.get(TARGO_TRUST_VAR) != want]
                    if lost:
                        print(f"crates-tests: CANNOT JUDGE — {TARGO_TRUST_VAR}={want} is missing from the "
                              f"record of {', '.join(lost)}", file=sys.stderr)
                        return 2
                    print(f"--- {TARGO_TRUST_VAR}={want} is in the record of each of "
                          f"{len(handed)} consumer test binaries", flush=True)
                print(f"--- recorded {len(binaries)} test binaries (build exit {rc}, "
                      f"{time.monotonic() - t0:.0f}s): {spelled}", flush=True)
                records.append((spelled, rc, binaries, credit))

        # The barrier (see the header): nothing below runs a test binary before it.
        waited = 0.0
        if barrier:
            print(f"\nwaiting for the barrier {barrier} ({RUN_AFTER_ENV}): no test binary runs "
                  "before it; the wait is not charged to the budget", flush=True)
            go, waited, why = wait_for_barrier(barrier, owner, max_wait)
            print(f"crates-tests: waited {waited:.0f}s at the barrier ({why}), "
                  f"not charged to the {budget}s budget", flush=True)
            if not go:
                print("\nNOT JUDGED: the barrier did not say `run`, so no test binary ran.")
                for spelled, _, binaries, _ in records:
                    print(f"  built, not run: {spelled} ({len(binaries)} test binaries)")
                print("Nothing above counts as a pass.")
                return 3
            deadline.extend(waited)

        # 2. Run every recorded binary, `jobs` at a time; then RUN_ALONE's, alone.
        everything = [b for _, _, binaries, _ in records for b in binaries]
        alone = [b for b in everything if binary_name(b.argv[0]) in RUN_ALONE]
        pooled = [b for b in everything if b not in alone]
        print(f"\nrunning {len(pooled)} test binaries, {jobs} at a time "
              f"(TRUST_CRATES_TESTS_JOBS; default {default_jobs()} on this host)", flush=True)
        finished = run_binaries(pooled, jobs, deadline)
        if finished and alone:
            print(f"\nrunning {len(alone)} test binaries alone (RUN_ALONE): "
                  f"{', '.join(sorted({binary_name(b.argv[0]) for b in alone}))}", flush=True)
            finished = run_binaries(alone, 1, deadline)
        if not finished:
            print(f"\nNOT JUDGED: {deadline.why()} with test binaries unfinished.")
            for b in everything:
                if b.rc is None:
                    print(f"  not run to completion: {b.display.strip()}")
            print(not_judged)
            return 3

    # 3. Judge each command as cargo's own run of it would have been judged.
    failed: List[str] = []
    for spelled, rc, binaries, credit in records:
        ok, report, rc = judge_command(rc, binaries, known)
        # An instrument run (credit None, Plan.attributed_commands) must have judged
        # something (INSTRUMENT_REQUIRED_PASSES).
        problem = instrument_problem(spelled, binaries) if credit is None else None
        if problem:
            report.append(f"INSTRUMENT JUDGED NOTHING ({problem}): {spelled}")
            ok = False
        for line in report:
            print(f"  {line}")
        verdict = ("PASS" if rc == 0 else f"PASS (known red only, exit={rc})") if ok else f"FAIL exit={rc}"
        busy = sum(b.seconds for b in binaries)
        print(f"--- {verdict} ({len(binaries)} binaries, {busy:.0f}s of test time): {spelled}", flush=True)
        if not ok:
            failed.append(spelled)

    # 4. The zero-test rule (tests_reported): a touched crate whose runs
    # reported no test was not judged, and is never counted a pass.
    counts = tests_reported(plan, records)
    if counts:  # an instrument-only push touches no crate it could name
        print("--- tests reported per touched crate (libtest's passed + failed, over all its runs): "
              + ", ".join(f"{name} {n}" for name, n in counts.items()), flush=True)
    unjudged = [name for name, n in counts.items() if n == 0]
    for name in unjudged:
        print(f"  NO TEST JUDGED: {name}: its runs reported 0 tests (passed + failed). Its tests are "
              "behind a feature no run enables (FEATURE_RUNS), behind a cfg this host does not "
              "satisfy (target_os, target_arch), on [[test]] targets whose required-features no "
              "run enables, all #[ignore]d, only doctests (`--tests` runs none), or absent; "
              "this lane judged nothing about it")

    total = time.monotonic() - started
    spent = f"{total - waited:.0f}s" + (f" (and {waited:.0f}s waiting at the barrier)" if barrier else "")
    if failed:
        print(f"\ncrates-tests: {len(failed)}/{len(commands)} run(s) FAILED in {spent}:")
        for spelled in failed:
            print(f"  {spelled}")
        return 1
    if unjudged:
        print(f"\nNOT JUDGED: {len(commands)}/{len(commands)} run(s) exited green in {spent}, but "
              f"{len(unjudged)} touched crate(s) reported no test: {', '.join(unjudged)}.")
        print("Nothing above counts as a pass for them. Give each a run that compiles its tests "
              "(a FEATURE_RUNS tail), or run its tests yourself.")
        return 3
    print(f"\ncrates-tests: {len(commands)}/{len(commands)} run(s) passed in {spent}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
