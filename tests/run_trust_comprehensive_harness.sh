#!/bin/bash
# Comprehensive Trust replacement test harness.
#
# The push profile contains live verifier and proof-input integrity checks
# only. It does not yet run the broad suites below or the gate self-tests: a
# defect, not policy (owner, 2026-11-09: "what check-waiving? that sounds
# wrong. we want verification on and for it to work."; docs/STATUS.md).
# Neither source publication nor empirical tests establish formal correctness.
#
# The default profile is the release profile. It is intentionally expensive:
# it builds the standalone Trust toolchain, runs the upstream Rust compatibility
# path, runs Trust-specific proof gates, runs install/dist gates, and writes a
# machine-readable report. Manifest and quick profiles exist only to validate
# the harness itself during development; they are not replacement evidence.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
# The file whose emit_gate_manifest this run executes; --record-last-green edits it.
MANIFEST_FILE="$SCRIPT_DIR/$(basename "$0")"
RECORD_LAST_GREEN=0
POSITIONAL=()
for arg in "$@"; do
    case "$arg" in
        --record-last-green) RECORD_LAST_GREEN=1 ;;
        *) POSITIONAL+=("$arg") ;;
    esac
done
set -- ${POSITIONAL[@]+"${POSITIONAL[@]}"}
MODE="${1:-release}"
RUN_STARTED_AT="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
RUN_ID="${TRUST_COMPREHENSIVE_RUN_ID:-$(date -u '+comprehensive-%Y%m%dT%H%M%SZ')}"
OUT_DIR="${TRUST_COMPREHENSIVE_OUT_DIR:-$TRUST_ROOT/reports/trust-comprehensive/$RUN_ID}"
LOG_DIR="$OUT_DIR/logs"
RESULTS_TSV="$OUT_DIR/results.tsv"
LAST_GREEN_TSV="$OUT_DIR/last_green.tsv"
REPORT_JSON="$OUT_DIR/report.json"
REPORT_MD="$OUT_DIR/report.md"
DIVERGENCE_LEDGER="$TRUST_ROOT/tests/trust-comprehensive/divergences.toml"
DEFAULT_FAIL_FAST=0
[ "$MODE" = "release" ] && DEFAULT_FAIL_FAST=1
FAIL_FAST="${TRUST_COMPREHENSIVE_FAIL_FAST:-$DEFAULT_FAIL_FAST}"

usage() {
    cat <<'USAGE'
Usage: tests/run_trust_comprehensive_harness.sh [--record-last-green] [release|quick|fast|suites|slow|manifest|list|--list|--help]

  --record-last-green
            After the run, write every date its LAST-GREEN lines offered into
            the manifest rows of this file: PASSED rows only (never SKIP), the
            run's UTC start date, only ever forward, and only where the row's
            command is unchanged since the run began.

Profiles:
  release   Full replacement evidence path. This is the default.
  quick     Fast local confidence path. Not replacement evidence.
  fast      Everything that needs no stage2 build: drift, supply-chain,
            style/lint ratchets, workspace compile and script tests.
  push      The pre-push tier. scripts/hooks/pre-push DERIVES its lane list
            from `--list push`; do not hand-list lanes there.
  suites    The compiletest suites, one gate per suite, in Trust mode.
  slow      Overnight lanes: Clean-kernel re-derivation.
  manifest  Static harness/script/ledger checks only. Not replacement evidence.
  list      Print the selected profile's gate manifest without executing it.

Outputs:
  reports/trust-comprehensive/<run-id>/results.tsv
  reports/trust-comprehensive/<run-id>/report.json
  reports/trust-comprehensive/<run-id>/report.md
  reports/trust-comprehensive/<run-id>/last_green.tsv  (the LAST-GREEN offers)

The harness never uploads or publishes artifacts. Any gate that prepares
publication evidence must stop at local/internal dry-run or rehearsal evidence.
USAGE
}

case "$MODE" in
    -h|--help|help)
        usage
        exit 0
        ;;
    --list|list)
        MODE="${2:-release}"
        case "$MODE" in
            release|quick|fast|push|suites|slow|manifest) ;;
            # A typo'd profile used to print the `all` rows and exit 0 — a SHORT
            # LIST that reads GREEN. scripts/hooks/pre-push derives its lane set
            # from `--list push`, so that fail-open is now a narrowed push gate.
            *) echo "FAIL: unknown profile for --list: $MODE" >&2; exit 2 ;;
        esac
        ;;
    release|quick|fast|push|suites|slow|manifest)
        ;;
    *)
        usage >&2
        exit 2
        ;;
esac

case "$FAIL_FAST" in
    0|1)
        ;;
    *)
        echo "FAIL: TRUST_COMPREHENSIVE_FAIL_FAST must be 0 or 1 (got: $FAIL_FAST)" >&2
        exit 2
        ;;
esac

timestamp_utc() {
    date -u '+%Y-%m-%dT%H:%M:%SZ'
}

epoch_seconds() {
    date '+%s'
}

safe_log_name() {
    printf '%s' "$1" | tr -c 'A-Za-z0-9_.-' '_'
}

gate_selected() {
    local profiles="$1"
    case ",$profiles," in *",$MODE,"*) return 0 ;; esac
    # `all` deliberately does NOT imply `push`: an `all` row is written by
    # someone thinking about coverage, and the push tier is a time budget. Left
    # implied, any future `all` row silently becomes a pre-push lane.
    [ "$MODE" = "push" ] && return 1
    case ",$profiles," in *",all,"*) return 0 ;; esac
    return 1
}

# The `trust.examples.complete-corpus-diagnostic` row remains a required
# release-profile regression tripwire. Its success is not evidence: the report
# serializer hard-codes `non-evidence-regression-diagnostic` to false proof and
# release-evidence flags and the distinct `diagnostic_passed` status.
# THE MANIFEST IS THE INVENTORY. A lane that exists in the tree but appears in
# no row below is a lane nobody runs, so `manifest.lane-coverage` walks the
# on-disk lane inventory and fails when a lane is unnamed here. Adding a gate
# script, an e2e, a witness/elide regression, or a compiletest suite without a
# row is therefore a hard error, not a silent omission.
#
# `oracle.*` rows check a verdict against RUNTIME truth, catching a false proof no
# self-consistent proof check can. All three were named by no row until 2026-08-26.
# The two trustc oracles cost under 1s each; `oracle.falseproof-search` sweeps 637
# variants in 4554s (measured 2026-08-26), too slow for the pre-push `push` tier
# (and for `fast`).
# It is RED on arrival by design — it finds the live `i += 100` false proof in all
# three lanes, certify included (guards.rs models it `x == x + 100`; UNSAT poisons
# the hypothesis, so the block proves vacuously). Do not skip it to get green.
#
# `oracle.soundness-corpus` (added 2026-10-14) runs the SBC M0.5 corpus
# (tests/trust-soundness-corpus: found false proofs, each with a native-execution
# witness and a correct twin) against every verifier the host has. It is
# ADVISORY (`required=false`) and in no `push` profile, because the corpus README
# keeps the gate non-blocking, and out of the pre-push hook, until it judges 0
# proved reproducers (DECISION_QUEUE 2026-10-15, M0.1); that is the day to make
# it required.
# It runs with `--strict` all the same, so the row's status is the corpus's
# verdict, fail-closed: exit 1 on any FALSE-PROVED or XFIXED cell, a SKIPPED
# requested verifier, an ERROR the entry does not whitelist (a missing, crashing
# or timed-out verifier, an anchor that matches no row), an unrecorded TWIN-LOST,
# an unconfirmed witness, and a run in which no verifier judged any reproducer
# (every cell skipped or n/a), which is not a pass. RED
# on arrival by design. Measured on 4d491f6103 with the store trustc the runner
# defaults to (toolchain 9192, 321aaeda7): vac-field-read-before-write is
# FALSE-PROVED, strict exit 1. The corpus README's census has 14 false proofs
# per trustc lane on that seal, each fixed on main after it was cut, so a run
# with TRUSTC=<a stage1 built from main> measures main.
#
# The block starting at `fast.pin-regression` is the 2026-08-26 catch-all sweep. Every
# lane class in `check_gate_lane_coverage.py` matched on a NAME, so every class had
# a next blind spot: `check_*` missed four adversarial oracles, `trust_*_gate.sh`
# missed two HYPHENATED gates. A catch-all now sweeps whatever the named classes
# do not claim; it surfaced 73 scripts, of which 46 are verdict-bearing and are
# rowed below. Several are RED on arrival and that is the point — `check-unsafe-
# coverage.sh` has all five expect-caught rows failing on a drifted exact-match
# grep while docs/high2-obligation-demo.md claims it "also passes live".
# (`run_trust_conformance.py` was the other, on a fixture deleted with its producer.)
# Do not silence a red here to get green; the red is the instrument working.
#
# Two rows in that block are green ONLY once something lands with them:
# `release.certified-scoreboard` names a baseline file that does not exist yet
# (without --baseline the scoreboard exits 0 unconditionally, which is a green
# that proves nothing), and `slow.corpus-census-faithfulness` needs the census
# binary built (its awk summary now exits 4 on KERNEL_REJECTED != 0,
# scripts/corpus_census.sh:147).
#
# The `push` profile IS the pre-push gate. scripts/hooks/pre-push hand-listed
# eight ids until 2026-08-27; the two lists could drift by eye, and one of them
# bundled ten checks behind a single id (`fast.pr-gate`), so a red inside the
# bundle could only be quarantined by darkening all ten. Adding `push` to a row
# is now the entire act of adding a pre-push lane. Measured 2026-08-27 (19 lanes then; the set grows —
# 15.7s wall on a docs-only push: toolchain-coherence 2.7s, pin-coherence 2.6s,
# tag-families-selftest 1.6s, measurement-provenance-selftest 1.4s,
# pin-regression-selftest 1.3s, oracle-freeze-selftest 0.87s, the rest <0.4s
# each, with `scoped.compiler-check` skipping instantly. Nothing enforces that
# ceiling; a row that costs minutes is how a gate teaches people --no-verify.
#
# Several push lanes need the refs git is pushing, which a fixed command string
# cannot receive: the hook exports TRUST_PUSHED_REFS, and with it UNSET the same
# command widens to its history reading, so the row stays runnable standalone.
# Most take `--push-context`; the two shell-scoped rows (`scoped.compiler-check`,
# `scoped.completion-gate-tests`) read it with no flag whenever it is set. The
# readers are not counted here (this line said "Four" long after there were
# more): `git grep -l TRUST_PUSHED_REFS -- 'scripts/check_*'` names them, and
# scripts/hooks/pre-push lists them as of its last measurement.
# CORRECTED 2026-09-28: the two scoped rows are no longer the only no-flag
# readers. `fast.patch-binds`, `fast.oracle-freeze` and `fast.doc-counts` read
# the variable whenever it is set and judge the PUSHED trees (doc-counts: skip,
# judge the checkout when it provably holds the pushed tree in scope, or
# refuse); until that day each judged the working tree, or HEAD plus it,
# whatever was pushed. With it unset, those three keep that working-tree
# reading, not a history one.
#
# `fast.dependency-constellation` joined them 2026-08-29 and is the reason the
# ceiling note above matters. It resolved its exclusion policy at whatever the
# CLONE's HEAD happened to be, so in a shared checkout sitting behind
# `origin/main` — where the policy had not landed yet — it was red for every
# push regardless of what was being pushed, and three commits went out under
# `--no-verify` in one day. The lane asks about the revision being PUBLISHED;
# now it reads that revision. The `test -f` conditional this row used to carry
# was a third revision again (the WORKING TREE) and moved into the tool as
# `--derive-when-receipt-absent`, so receipt presence is asked of the same
# revision as everything else.
#
# EVERY PIN LANE ABOVE IS A PUSH LANE, and that is the gap
# `supply-chain.fleet-pin-drift-sweep` closes. `fast.dependency-constellation`
# and `fast.submodule-remote-reachability` judge the revision in flight, so
# drift lands, sits, and is discovered by whoever pushes NEXT — never by the
# lane that created it. Measured 2026-08-30: four distinct pin failures in one
# day, each caught by an unrelated lane, one of them blocking the compiler repo
# for hours. `scripts/sweep_pin_drift.py` is the same questions with the
# subject changed from "what I am pushing" to "every submodule-bearing repo on
# this machine, at what it has PUBLISHED". Measured 2026-08-31: 21.1s for four
# superprojects and 17 gitlinks — one `git ls-remote` per distinct remote, no
# object transfer, no build, no build-tree lock, so it is safe beside a build
# and cheap enough for a timer. It is a `release` row rather than a `push` one
# on purpose: adding 21s of NETWORK to every push is how a gate teaches people
# --no-verify, and the sweep's whole point is that it does not need a push.
# `--constellation` adds one check_dependency_cycle_anchor.py run per repo
# (36.2s for Trust) against the published revision.
#
# `scripts/check_all.sh` (release.check-all) is the only runner for three gates:
# the temporal-fixture boundary, G19 build determinism, and stage2
# verify-examples. Its boundary gate has no standalone entry point —
# `run_temporal_fixture_boundary_gate` is private and asserts against
# `crate::temporal_cli::UNBOUND_TEMPORAL_EVIDENCE` (targo-trust/src/script_cli.rs:1883),
# so re-expressing it as a shell grep would mirror a constant into a file with
# nothing checking the mirror. A second, different exercise of that script lives
# in tests/e2e_check_all_tcargo_provenance.sh, which copies and RUNS the real
# scripts/check_all.sh in a synthetic repo.
#
# `fast.audited-trust-spec-sources` closes a TRIPWIRE NOBODY WATCHED. Verified
# Targo admits a contract proc-macro provider only when the sha256 of its
# manifest AND its library source equal the pins in
# `AUDITED_TRUST_SPEC_SOURCES` (src/tools/targo/src/compiler/mod.rs),
# because those crates run inside the verified compiler's address space and a
# crate NAME is not authority. Nothing compared that allowlist to the tree, so a
# stale pin could only be discovered by a verified build refusing. MEASURED
# 2026-09-11: `crates/trust-spec/src/lib.rs` had been pinned at its INITIAL
# commit's digest while the file moved on 2026-08-26/27, so every verified build
# that compiled `trust-spec` had been refused fleet-wide for two weeks — on
# main, on seal/15 and on seal/16 — and the pin was found by hand, not by a
# lane. The gate re-hashes each entry's files in ~4s and fails with BOTH
# digests and the fix line. It deliberately does not judge whether moved bytes
# are safe to admit: that is an audit a human writes beside the pin. Its
# `--selftest` plants fifteen defects (moved lib, moved manifest, a version key
# the manifest does not declare, a pin guarding nothing, a superproject-homed
# provider that an unrelated absent submodule must NOT excuse, a submodule-homed
# one it must, that same tree under `--require-all`, a run that resolved zero
# providers, `--print` on a drifted tree, an audit comment full of braces, a
# renamed allowlist, a zero-entry allowlist, an entry the parser cannot read)
# and asserts the verdict each time, so a zero-coverage run can never read as
# green.
#
# THE ROWS. These carry `fast,push,release` — the shape `fast.two-language-claim-
# ledger` and `fast.dependency-constellation` use, NOT the `fast,push` of
# `fast.oracle-freeze`/`fast.pin-regression`; the base commit's message said the
# latter and was wrong about its own file. The default mode is what `fast`/`push`
# run: it is fail-closed about drift, about a pin guarding nothing, about a
# provider missing from a home the SUPERPROJECT tracks, and about a run that
# resolved no providers at all — and advisory only about a provider whose home is
# a submodule this working tree has not furnished. `release.audited-trust-spec-
# sources-complete` adds `--require-all`, which is the seal bar: at release time
# every submodule is populated, so every pin must actually be compared.
#
# The FULL producer measurement (scripts/run_measurement_sweep.sh) is covered by
# no row; `fast.trust-ir-seam-blockers*` pin only the taxonomy.
#
# `fast.cfg-test-caller-skew` (2026-09-01) is here because `scoped.compiler-check`
# is the ONLY lane in this manifest that type-checks a `crates/**` TEST target, and
# it is also the most expensive thing in the repo — `x.py check --stage 1`, 9-11
# minutes, and it takes the exclusive build-tree lock. So the one lane that can see
# this class is exactly the lane a clone will not be running: `scripts/hooks-pin/`,
# which this repo's own CLAUDE.md tells shared machines to install, compiles nothing
# at all, and `--no-verify` leaves the same trace as a narrow hook, which is none.
# Measured cost of that gap, twice in eighteen hours and both from the same
# producer machine: `d26cb8c40e` (E0063, a `#[cfg(test)]` initializer missing
# `PendingConst::promoted_global`, repaired by `cf89d447db`) and `78a0bef5ff`
# (E0061, 45 `#[cfg(test)]` call sites left at the old arity, still red on
# `origin/main` at `ad074447848d29974bec329d7e3587bb92dc4d38` while this row was
# written). Both trees BUILT: `x.py build` and `x.py test tests/ui` compile lib
# targets, and a `#[cfg(test)]` body is not in a lib target, so the producer's own
# measurement loop cannot see this class however carefully it is run.
#
# The new row is not a second slow lane and must never become one. It reads the
# blobs in the pushed range with `git show` — no cargo, no x.py, no build tree, no
# lock, no network — which is what lets it also join the hand-listed narrow set in
# `scripts/hooks-pin/pre-push`, so the check no longer depends on which hook
# directory a clone happened to install. It judges only definitions the range
# CHANGED, and it declines rather than guesses: measured over the 300 single-commit
# ranges ending at `ad07444784` it reports exactly the three commits above and
# nothing else.
#
# `fast.run-make-fixture-lex` (2026-09-12) is the same shape of answer to the same
# shape of gap. NO push lane runs run-make — `suite.run-make` is a `suites` row
# costing a stage2 — and `90fe4d2c62` landed a Clean-island fixture that did not
# COMPILE AT ALL: a grave accent in the island's Lean `--` comment. The island is a
# true parser island, but its contents travel as Rust token trees and a grave accent
# starts no Rust token, so `tests/run-make/trust-ir-emit-clean-origin` died at its
# FIRST compilation and reached not one assertion. It sat broken for six hours until
# `691169cd1b`. The full recipe cannot be the gate — there is no stage1 in a fresh
# tree, and building one is hours under the exclusive build lock — but the DEFECT
# needs no compiler to see: the fixture did not LEX.
#
# So the row lexes instead. Measured 2026-09-12 over 83 sources: 0.7s wall for BOTH
# rows together (0.4s the check, 0.3s the selftest), ~4% of the 15.7s push budget,
# with no cargo, no x.py, no build tree, no lock and no network — cheap enough to
# join `scripts/hooks-pin/pre-push` as well, so the coverage does not depend on
# which hook directory a clone installed. Two things
# make it honest rather than decorative. It models Trust's own post-state PRIME rule
# (`compiler/rustc_parse/src/lexer/mod.rs`, D2/Q9) — without that, `ensures x' >= x`
# in `trust-e9-kernel-discharge-transport/cited.rs` reads as an unterminated
# character literal and the row would be red on arrival for the wrong reason. And it
# reads the INLINE sources too: a recipe that writes a fixture with
# `rfs::write("foo.rs", r#"..."#)` hides the same grave accent inside a raw string,
# where `rmake.rs` itself lexes perfectly — 20 such sources in the tree, 5 of them
# carrying Clean islands, invisible to any file-level check.
#
# It is a LEXER and claims nothing more: an unclosed `fn f(`, a wrong assertion, a
# failed obligation all lex fine and all pass. `--with-trustc` is the exactness
# cross-check against the real `-Zparse-crate-root-only` (83/83 agree, measured
# 2026-09-12) and is deliberately NOT a row: it needs a toolchain a fresh clone may
# not have, and at 158s it is ten times the entire push budget.
#
# `slow.compiler-unit-tests` (2026-09-27) EXECUTES the unit tests of the compiler
# crates a change touched. The crates/ sweeps cannot reach `compiler/**`,
# `scoped.compiler-check` compiles test targets without running one, and the two
# rows that do run some are fixed lists — `slow.mir-transform-ratchet`
# (rustc_mir_transform) and `quick.compiler-unit-tests` (rustc_driver_impl,
# rustc_session, rustc_mir_transform; never recorded green) — so a MIR
# wire-layout guard in rustc_metadata and the suites of the three rustc_private
# crates (trust-mir-extract, trust-thir-lower, trust-witness — Cargo.toml's
# `exclude`) ran only when someone typed the command. trust-mir-extract's and
# trust-thir-lower's were found red on main exactly that way (2026-09-24). The
# lane is scoped by the committed diff against origin/main — each touched
# compiler crate that has a `#[test]`, rustc_metadata as well when a MIR type in
# rustc_middle/src/mir moves, each touched rustc_private crate (after building
# the stage-1 `library` their fixtures need) — and delegates rustc_mir_transform
# and rustc_codegen_trust_cg (known-red set) to the ratchet, and runs the trust-cg
# run-make fixtures at stage 1. An out-of-scope diff exits 0 with a `WARN:` line,
# which the harness surfaces beside the PASS. It is `slow`, not `push`, because
# it is an x.py BUILD: the pre-push hook records that a build lane in the push
# tier collides with `scoped.compiler-check` on the build lock. Its `--selftest`
# builds nothing and is the push row. A release row is deliberately absent: at a
# release commit the diff against origin/main is empty, and a row that always
# skips there would read as release evidence while judging nothing.
#
# `release.two-language-programs` (roadmap WS8.8, added 2026-09-21): the
# two-language program battery — every complete Rust+Clean / standalone-Lean /
# package row of tests/e2e_two_language_programs.sh, INCLUDING the `trustc-ir`
# producer ratchets (WS5.1: Part A / Part A-Lean pinned in expected.json, judged
# by tools built from the first-party gitlinks) — as a row of its OWN. It needs a
# built compiler (every row compiles real programs), so it is release-only. Two
# things the corpus row could not give it: a verdict named by row rather than
# folded into `verify.e2e-shell-corpus`'s N-script tally, and the ARTIFACTS the
# run writes — the markdown table and the G1/G2/G3/G5/G6-tagged producer-ratchet
# evidence (`--ir-evidence`) under build/evidence/, which is what the
# two-language completion receipt binds. To keep it one run per release and
# not two, run_e2e_shell_corpus.sh skips this one script by name; the coverage
# checker's INDIRECT map names this row for the script, its rows and its judge.
# `last_green` stays `never` until a release run records a PASS.
#
# `slow.trust-cg-cer-gate` (2026-10-08, increment 5 step 5.4.1, INC5.4-CER-LANE in
# docs/DECISION_QUEUE.md) runs the call-event refinement gate's enforcing tests: the
# mutation battery (`call_event_gate`), the object readers (`compiled_object_reader`),
# the variadic attacks the frozen `call_event.rs` waiver names
# (`variadic_split_attacks`), the step-5.0 ABI guarantee (`abi_guarantee`), the
# bridge's shipping consumer (`f1_compile`) and, since 2026-10-14, the gate's evidence
# for pointer slots (`pointer_slots`, PTR.0 of
# docs/design/2026-10-13-step2-inc5-pointer-args-plan.md). Until this row they ran only
# when someone typed the command, which a shipping authority's enforcing tests cannot
# do. The features are explicit because five of the six files compile to ZERO tests
# without them (four need `kernel-recheck`, `abi_guarantee` needs `test-hooks`) and
# would pass vacuously. It is `slow`, not `push`: the clean kernel and trust-cg build under it,
# and the debug-build gate runs for minutes.
#
# `slow.feature-gated-tests-trust-cg-bridge` / `-trust-router` (2026-10-09),
# `-trust-vcgen` and `-trust-spec-temporal` (2026-10-27) run the
# `crates/` tests that exist only under a non-default feature. A file that opens
# with `#![cfg(feature = "...")]` compiles, in every lane that leaves the feature
# off, to a test binary that prints `running 0 tests` and PASSES. 35 of
# trust-cg-bridge's 54 test files are gated that way (20 `ay-proofs`, 10
# `test-hooks`, 3 `kernel-recheck`, 2 `ay-proofs`+`test-hooks`; a 36th is
# `target_arch = "aarch64"`), and 8 of trust-router's 22 (`ay-backend`). Measured
# by this lane, each file in the run where it runs the most, the 35 hold 350
# tests (352 with the aarch64 file) and the 8 hold 21, one of which checks nothing
# (below): 20 that do. No row ran those files; they ran only when somebody typed
# the command. Both libs gate test modules the same way. No other lane runs
# trust-cg-bridge's. trust-router's also run in the scoped push lane's two `--lib`
# tails (`scoped.crates-tests`: `ay-backend`, and
# `ay-certify,trust-build,trust-cg-backend,carcara-crosscheck`), but only on a push
# that touches trust-router. scripts/feature_gated_tests.py builds each configured
# (crate, feature set) with `--tests` (lib, bins, tests/*.rs) into its OWN target
# dir, crates/target-feature-gated-build.noindex (never crates/target, so it never
# contends with a push lane), takes the test executables from cargo's JSON, runs
# them through cargo's runner hook so each binary's output lands in a log of its
# own (no reliance on cargo's output order), and judges what each binary
# REPORTED. A failed or crashed binary, one that runs zero tests unless
# ZERO_TEST_ALLOWED names it with a reason (an allowlisted binary that does run a
# test is a red too: "delete the row"; so is a row whose `covered_by` run did not
# run it), a build failure, an empty selection, and a binary or test count below
# the run's measured floor all fail the row. A test NO_OP_TESTS names is shown
# and not counted (the table is empty: its one row, trust-router's
# `adjudicate_undischarged_vcs`, which asserts nothing, is now an `#[ignore]`d
# measurement driver that panics with its recipe without TRUST_ADJUDICATE_VC_LOG,
# so its binary is a ZERO_TEST_ALLOWED row), and a no-op row whose test stops
# running is a red. The floors are per run and equal that day's counts: deleting a test of
# either crate on purpose means lowering its run's floor in
# scripts/feature_gated_tests.py (RUNS) in the same commit. Runs: trust-cg-bridge
# `kernel-recheck,test-hooks` (what rustc_codegen_trust_cg links, plus the
# mutation hooks) and `test-hooks` (the ay-only grading path and the
# `not(feature = "kernel-recheck")` tests; its three kernel-only binaries are the
# allowlist's rows), trust-router `ay-backend`, and trust-router under exactly the
# set rustc_mir_transform links (`ay-backend,ay-certify,trust-build,
# trust-cg-output-gate,trust-vc-native`). Only that last run reaches the lib tests
# behind `trust-cg-output-gate` (trust_cg_backend.rs: two tests exist only under
# it, and the ones that call `verify_codegen` take its byte-level path). Its
# trust-build / trust-vc-native / trust-cg-backend lib coverage overlaps the
# scoped push tail. `ay-backend` stays a run of its own because `ay-certify`
# compiles out the `not(feature = "ay-certify")` tests. Not covered here:
# trust-router's `carcara-crosscheck` test modules (the scoped push tail is their
# only lane; the feature links GMP through `rug`).
# `slow.feature-gated-tests-trust-vcgen` (2026-10-27, FGT-LANE-3) runs trust-vcgen's
# `tests/infoflow_leak.rs`, which is `#![cfg(feature = "prototype-infoflow")]` (an
# experimental prototype) and was run by no lane until then. Its one run is
# NARROWED to `--test infoflow_leak`: the feature adds only the lib's
# `any(test, feature)`-gated `infoflow` module, which the lib's test build already
# compiles and only that file imports, so `--tests` would rebuild and re-run the
# default build's 200-odd binaries, the scoped push lane's already. The
# `--selftest` holds the tree to this: every feature-gated test target under
# crates/ (a leading `#![cfg(...)]` that names a feature, or `required-features`)
# must hold under its crate's default features or under a RUN that selects it (on
# 2026-10-27 the infoflow file and trust-spec-temporal's `model_prelude_patched`
# were its two reds); a narrowed run's features may flip no cfg in its crate's lib
# unit-test build without `--lib`, and in the lib the other targets link only by
# adding an inert top-level module nothing else names; they may reach no other
# crate's feature, the crate may have no build script, and no tests/ file the run
# does not select may name them (FGT-LANE-3 as amended); and every crate with a
# RUN has its `slow.feature-gated-tests-<crate>` row here (any last_green). MEASURED 2026-10-27 (18 cores,
# 1-minute load average 56 at the start, 49 at the end) on b2b85b18e3 (crates/
# as origin/main 723f9ec299), target dir cold: the row PASS in 524s (build
# 522s; 1 binary, 4 tests, 0 failed); `--tests` under the feature builds 211
# binaries.
# `slow.feature-gated-tests-trust-spec-temporal` (2026-10-27, FGT-LANE-4) runs that
# crate `--tests` under `test-support` from its OWN manifest (it is its own
# workspace root): its `[[test]] model_prelude_patched` has `required-features =
# ["test-support"]`, so the scoped push lane's featureless run never built it, and
# model_prelude_kernel.rs and model_theorems.rs gate tests on the feature item by
# item. Debug, like every run here: the prelude tests that are release-only
# (B1A-D42) show as ignored.
# `slow.feature-gated-tests-trust-verifier-api` (2026-11-06, CG-BRIDGE-LANES-1)
# runs that crate `--tests` under `native-trust-ir-claims`, which gates
# tests/native_contract_claim.rs and a lib module; no lane ran this crate's tests
# with it (trust-router's and trust-vc-bridge's `trust-build` enable it only as a
# dependency).
# `slow.feature-gated-tests-trust-bmc` (2026-11-06, BMC-LANE-1) runs that crate
# `--tests` under `trust-mc-native-trust-ir-bundle` (part of `trust-build`, the
# production lane), which gates tests/raw_postcondition_dispatch.rs and the lib's
# native trust-mc CHC lane. The integration file ran in no lane (`--selftest`
# flagged it). The lib's gated modules run in trust-bmc's `trust-build --lib` tail,
# and no push runs it: since 39b35cb9f7 (2026-11-02) `scoped.crates-tests` is in the
# fast profile only, and the pre-push hook runs the push profile, whose rows (8
# then; 10 since `fast.corpus-membership` and `fast.ledger-pins`, which compile
# nothing) run no crates/ test whatever a push touches. The tail runs in scripts/land_gate.py's
# crates-tests leg for any change that reaches trust-bmc (a pin move among them; it
# builds no integration file), in the fast profile's `scoped.crates-tests` when
# origin/main...HEAD touches trust-bmc, and by hand. 4 lib tests in that tail were
# red on main, failing closed on trust-mc's OperandConsumption guard (which came in
# with the trust-mc pin move 8862c94337): the bridge's unexecutable aggregate seed, a
# root array parameter, and a positive control that asserted PROVED through a poison
# `undef u64` GEP offset (now a refusal row). No push ran them, including the four
# 2026-11-03 commits that touched crates/trust-bmc with the guard already pinned
# (docs/DECISION_QUEUE.md BMC-LANE-1).
# `slow.feature-gated-tests-trust-build-tree` (2026-11-10, FGT-LANE-5) runs that
# crate `--tests` under `native-cli-tests,native-exec` from its OWN manifest (its
# own workspace root). Those features gate tests/fixed_run_public.rs and
# tests/fixed_test_graph_public.rs (`--selftest` flagged both) and the lib's
# actual-frontend tests, all of which execute this checkout's newly built Targo,
# Bootstrap and stage-1 compiler: the lane takes them from build/ under the build
# lock (a MEASUREMENT, like trust-router's) and is NOT JUDGED while one is not
# built, never green. Each of the two files runs its default case (cap2); its
# other cases (TRUST_FIXED_RUN_CASE, TRUST_FIXED_TEST_CASE) stay by hand. The two
# files also need the machine's native host CPU pool, which aterm's resource
# service initializes (trust-build-cpu's README) and the lane never creates: on a
# Mac without it both are red ("canonical native host pool must exist before
# legacy retirement"), as they were on m22 when the row was added.
# ONE HOST: the floors, the allowlist and the no-op rows were measured on
# aarch64-apple-darwin, and other hosts compile a different test set
# (`lean_isa_machine_sem_differential` is aarch64-only; trust-cg-bridge has
# Apple-aarch64-only tests, and files that skip native execution elsewhere). On
# another host a failure is still red, but a floor or zero-test finding is NOT
# JUDGED (exit 2): this row cannot go green there until that host's are measured.
# ONE ROW PER CRATE, not one for both: a red in one crate's tests must not darken
# the other's, the bundling lesson `fast.pr-gate` taught (above). It overlaps
# `slow.trust-cg-cer-gate` (INC5.4-CER-LANE: six trust-cg-bridge files) on
# purpose and leaves that row as it is. `slow`, not `push`: each run links 24-55
# fresh test executables and syspolicyd assesses every one on its first exec, one
# at a time host-wide (the push-lane attempt, parked on `wip/lane-phase2`, was
# abandoned for that). `release` on the argument `slow.trust-cg-cer-gate` makes:
# apart from trust-cg-bridge's test-only `test-hooks`, these are the features the
# shipped compiler links. Builds take no build lock (no crates/ build writes
# build/); each trust-router run holds it as a MEASUREMENT while its tests run
# (about 5 min, twice per row: 288s and 294s cold, 277s and 269s warm, on
# 2026-10-09), because its
# real-solver tests take `ay` from this checkout's build/host/stage2 (else
# stage1) trustc. Meanwhile an `x.py` build in the same checkout, a push's
# `scoped.compiler-check` among them, is refused or waits: FGT-LANE-1 in
# docs/DECISION_QUEUE.md. `fast.feature-gated-tests-selftest`
# (the push row, ~1s, builds nothing) drives the judge over canned output (a
# zero-test binary, a failing one, a crash, a stale allowlist or no-op row, a
# build failure, an empty selection, both floors, another host), the final
# verdict line, the log pruning, and the real runner over two fake executables.
# The target dir is 43G after a cold run of the four runs, per checkout, and
# nothing reclaims it (the builds are non-incremental, so
# scripts/reclaim_incremental.py finds nothing there):
# `rm -rf crates/target-feature-gated-build.noindex` from the checkout root does, and the
# next run builds cold. MEASURED 2026-10-09 (aarch64 macOS, 14 cores; 1-minute
# load average 6.2, 4.4 and 4.2 at each row's end): the rows' exact commands from
# a clean checkout of 1cdd117f3c, target dir deleted first. trust-cg-bridge PASS in
# 2181s (cold builds 232s+188s at -j4; 55+55 binaries, 1285+1083 tests, 0 failed),
# trust-router PASS in 1060s (cold builds 224s+254s; 24+24 binaries, 1202+1271
# tests, each count including the one no-op test, 0 failed), the selftest PASS in
# 1s. RE-MEASURED the same day, warm (that run's target dir), from a clean
# checkout of cd5cb2c6be, which added NO_OP_TESTS and the ONE HOST rule
# (1-minute load average 8.4, 5.8 and 5.4 at each row's end): trust-cg-bridge
# PASS in 1531s (55+55 binaries, 1285+1083 tests, 0 failed, the same three
# allowlisted binaries), trust-router PASS in 556s (24+24 binaries, 1201+1270
# tests counted, the no-op shown apart in each run, 0 failed), the selftest PASS
# in 1s (45 checks). Since 2026-10-09 trust-cg-bridge's floors are 1282+1080,
# not 1285+1083: three subprocess children in emit_determinism{,_multisym}.rs,
# which no cfg gates, are `#[ignore]`d (their parents pass --ignored).
#
# Columns: gate_id|profiles|category|required|last_green|command
#
# `last_green` is the ISO date of the most recent observed PASS, or `never`
# when this manifest has never recorded one. It is deliberately not inferred:
# a lane that has run green somewhere untracked still reads `never` here, which
# is the honest statement that the manifest has no evidence. A run prints a
# `LAST-GREEN` line for every PASSED gate whose recorded date is `never` or
# older than the run's UTC start date, and `--record-last-green` writes exactly
# those dates into these rows when the run ends (never backward, and not for a
# row whose command changed mid-run).
# A SKIPPED lane never supersedes `last_green`: a lane that exits 0 after
# printing a line beginning `SKIPPED: ` (the scoped lanes do, on an empty or
# out-of-scope diff) ran nothing, so run_gate grades it SKIP, prints no
# `LAST-GREEN` line, and the report records it `skipped`, never `passed`.
#
# `release.certified-monitor-e2e` must enter through the Rust-native
# `targo-trust` parent. The stage2 shell is a payload-only child with a deliberate
# direct-caller guard; invoking it here would make the release lane permanently
# red and, more importantly, could never mint native source authority.
#
# The intbound, widthconv, budget, and floatbits lanes are the authenticated
# native strict population used by the semantic-track release result. Their
# scripts retain stage1 defaults for historical developer probes, so the
# release manifest must bind each one to the canonical stage2 Targo explicitly.
#
# `fast.first-party-pin-lattice` (WS8.2, 2026-09-19) is the pin half of F-118:
# trust-ir, trust-cg and clean each name the others by exact revision in their
# own manifests and locks, and nothing made those names agree with the gitlinks
# this superproject builds. The row checks, from git objects only (no checkout,
# no network, never `~/clean`), that every trust-ir declaration and lock row at
# the trust-cg and clean gitlinks names the trust-ir gitlink R, that clean's
# trust-cg rows name the trust-cg gitlink G, and that `crates/clean-kernel` and
# the workspace rows it inherits are byte-identical between trust-ir's
# CLEAN_REVISION K and the clean gitlink C. It was ADVISORY (`required=false`)
# while the lane was red on arrival — 40 violations at `d9ea36f376` (L1 12,
# L2 21, L3 7), 7 (all L2) on 2026-09-27 main — because a required red row
# would have blocked every push until train T0 realigned the pins. T0 landed
# 2026-09-28 (docs/first-party-pin-ledger.md) with the lane green, so it is
# REQUIRED from that commit on. ~1s wall.
#
# `fast.vckind-exhaustiveness` / `fast.lean-front-door-gate` (added 2026-09-14):
# vckind_exhaustiveness's compile-time guard is already reached by
# fast.crates-workspace-check --all-targets; these two rows add RUNTIME
# execution of the vckind (4 tests since 2026-10-09) and lean-front-door (4 tests) guard
# targets in trust-integration-tests, which no row executed before.
#
# `scoped.completion-gate-tests` (added 2026-09-27) runs the release completion
# verifier's own controls: the fourteen `scripts/tests/completion_gate*_test.py`
# and `two_language*_test.py` modules, in one `python -B -m unittest` from the
# repo root under /usr/bin/python3. Until then NO lane ran them, and it showed:
# two G5 contract tests sat red on main, recorded only in a commit message, and
# `completion_gate_malformed_input_test.py` — the control for adversarially deep
# JSON — was RED under CPython 3.14, where a 1100-deep array parsed cleanly that
# 3.9 refused (docs/KNOWN_HAZARDS.md, "The completion gate's refusal of
# adversarial JSON depended on WHICH PYTHON ran it"). The only aggregate that
# globbed them, `scripts.tests.suite`, is fast-only and could not even import
# them. Category `soundness`, like `release.two-language-completion`, whose
# verifier this suite tests. COST: ~4-5 min (385 tests, 235-326 s measured
# 2026-09-27), paid ONLY when the push touches the gate, a checker, a suite
# module, or a tree file the suite loads (scripts/check_completion_gate_tests.sh
# lists each, with the line that loads it); every other push skips it
# instantly, like `scoped.compiler-check`. It refuses — red, never SKIPPED — on
# git < 2.41, python < 3.9, no /usr/bin/ssh-keygen, or a Clean submodule
# lacking its pinned commit, because a lane that passes without running is the
# failure it was added for. Scope uses `--no-renames` so a file moved OUT of scope
# still counts and `--ignore-submodules=none` so an ignore-configured first-party
# pin move still counts, and the suite runs under an empty HOME/XDG with no system or
# GIT_CONFIG_GLOBAL config, so an operator's `commit.gpgsign=true` cannot redden
# (or prompt inside) its fixture commits. Under the hook, scope is the union
# over TRUST_PUSHED_REFS of each update's TREE diff `<remote-sha>..<local-sha>`
# (so a force push that drops in-scope commits is in scope) and each new
# branch's `origin/main...<local-sha>` (origin/main...HEAD without the
# variable), and a range that cannot be diffed runs the suite;
# `scoped.compiler-check` scopes the same way, with the same block (both driven
# by scripts/tests/scoped_lane_push_scope_test.py, which the push row
# `fast.scoped-lane-scope-selftest` runs). Only the SCOPE follows the pushed
# refs: both lanes still run against the worktree.

# `scoped.crates-tests` (2026-09-23, TRUST-16) is the first push row that RUNS a
# `crates/` test. Before it, the push tier compiled `crates/` test targets
# (`scoped.compiler-check`) but never ran one, so trust-router's ay-backend suite
# went red on main (TRUST-13) with no push lane able to see it. It tests only
# the members the pushed range touches, plus the feature lanes in its
# FEATURE_RUNS table (`--lib` feature tails; the lane's header names them), under the
# lane's time bound (scripts/lib/crates_tests_time.py, CRATES-TIME-1: a stall bound,
# TRUST_CRATES_TESTS_STALL_S default 1800s, and a ceiling of max(14400s, 900s x crates)
# that TRUST_CRATES_TESTS_BUDGET_S replaces; until 2026-10-28 a flat 1200s). Running
# out of time is exit 3, NOT JUDGED. A push that touches no `crates/` path pays nothing.
# Measured 2026-09-23 at CARGO_BUILD_JOBS=4 with deps warm: 456s for a
# trust-router diff (red: TRUST-13, plus a 5s wall-clock test that fails under
# load) and 199s for a trust-types diff (green). docs/VALIDATION_LADDER.md
# lists what the lane cannot see. Since 2026-09-29 it runs the test binaries
# cargo records TRUST_CRATES_TESTS_JOBS at a time instead of one after another
# (the lane's header and the ladder give the protocol and the measurement).
# Since 2026-09-30 a push that touches trust-integration-tests first builds
# targo-trust (`targo --unverified build --manifest-path targo-trust/Cargo.toml
# --bin targo-trust --locked`) and hands its tests a private copy as
# TRUST_TARGO_TRUST_BIN: binary_to_trust_ir_e2e and scale_fixture_crate run
# it and fail without it. That build comes out of the same budget: 1-2s warm,
# 6m08s measured cold (2026-09-30), into targo-trust/target unless
# CARGO_TARGET_DIR says otherwise; a failed build is red, never a skip.
# `fast.seal-driver-sysrootcheck-selftest` (TRUST-17, 1.2s) moves the
# sysrootcheck mutation test into the push tier.
# Before that, only the `fast` profile's scripts.tests.suite glob reached it.
#
# `fast.scoped-lane-scope-selftest` (2026-09-27) runs
# scripts/tests/scoped_lane_push_scope_test.py, the control for the scope
# decision of BOTH shell-scoped rows above (pushed refs, force pushes, new
# branches, deletions, moves out of scope, quoted paths, ignored submodules, an
# undiffable range). Until then only the fast-only scripts.tests.suite glob
# reached it, so the block that decides whether a push pays for `x.py check`
# or the completion suite could regress to SKIPPED with no push lane noticing.
# Throwaway repositories and stubbed heavy commands, 12 tests: 10.5s at best,
# 17-25s at load average 3-4, measured 2026-09-27 under /usr/bin/python3 3.9.6
# and python3 3.14.5; one real run of either lane costs minutes. No PYTHONPATH
# needed: the test imports nothing from scripts/.
#
# The four `fast.<lane>-test` rows (2026-09-28) move four push lanes' own
# regression tests into the push tier. Each lane's subject changed that day
# (the push-lane scope sweep), and until then only the fast-only
# scripts.tests.suite glob ran the files that pin those subjects, so a push
# could regress what a lane judges with no push lane noticing. Each test builds
# throwaway repositories (real `git push`, bare destinations, copies of the
# checker) and reads nothing of this checkout but scripts/ and the files it
# names: measured 2026-09-28 from a sparse scratch clone holding only scripts/
# and this harness, with HEAD moved off the real tip, untracked junk in the
# worktree, `origin` pointing nowhere, outbound network denied
# (sandbox-exec), and the hook's TRUST_PUSHED_REFS/TRUST_PUSH_REMOTE exported:
# all four green. Wall times, 3 runs each under /bin/bash with stdin
# </dev/null at load average 2.4-3.1 on 10 cores:
#
# `fast.patch-binds-test` runs scripts/tests/check_patch_binds_test.sh: the
#   BINDS/UNBOUND/DUPLICATED/SKIPPED/MISSING states and the push reading (the
#   pushed trees and the submodule commits they pin, never the disk). 3.3-3.4s.
# `fast.revert-rationale-test` runs scripts/tests/check_revert_rationale_test.sh:
#   bare-revert mutations, destination-scoped updates, force pushes over an
#   unfetched tip, and real pushes through scripts/hooks-pin/pre-push. 7.0-7.2s.
# `fast.measurement-provenance-test` runs
#   scripts/tests/check_measurement_provenance_test.sh, which also runs the
#   gate's --selftest (the separate `fast.measurement-provenance-selftest` row)
#   and scripts/tests/measurement_provenance_push_scope_test.py. 8.2-8.4s.
# `fast.doc-counts-test` runs scripts/tests/check_doc_counts_test.sh: skip /
#   judge-the-checkout / refuse per pushed ref, the standing reading, and a real
#   push through a hook. 23.4-23.5s, the costliest of the four; its case list
#   was still growing when measured, so expect it to cost somewhat more. Its
#   `hidden_lean` case needs a case-sensitive directory
#   (DOC_COUNTS_TEST_CS_DIR) and is reported n/a, not passed, without one.
#
# Together ~43s added to every push. ADDED LATER the same day:
# scripts/tests/check_cfg_test_caller_skew_test.sh (5.4s) was not hermetic under
# the hook. It unset neither TRUST_PUSHED_REFS nor TRUST_PUSH_REMOTE, and the
# hook exports TRUST_PUSH_REMOTE (git's remote URL), so its no-destination
# control (K1-control) runs `--push-context` against that destination: an
# `ls-remote` of the real remote from inside a fixture repository. Measured
# 2026-09-28 with TRUST_PUSH_REMOTE alone set (to `origin`, or the https URL
# with network denied): exit 1, "the no-destination refusal did not name
# main's site"; green with it unset. Fixed the same day in the test
# (45376839b9), which now unsets both at its top as the other lane tests do,
# and then added as fast.cfg-test-caller-skew-test (~5s; ~51s for all five).
#
# `slow.program-index-repair-e2e` (2026-09-30) runs trust-backprop's
# real-compiler repair e2e: the program-index div-zero fixture through the stage2
# compiler, a deterministic repair, and the recompile, demanding fewer failed and
# more proved obligations. Until then it was not `#[ignore]`d although its doc
# and README said so, it early-returned GREEN whenever TRUST_REPAIR_E2E_TRUSTC
# was unset, and the README's `-- --ignored` command selected 0 tests and exited
# 0, so no run anywhere had to compile anything. It is now ignored, resolves
# build/host/stage2/bin/rustc by default (the variable is an override) and
# panics without a compiler; the row selects it by `--exact` name and, like
# slow.kernel-derivation's lane, demands `1 passed`, since libtest exits 0 on an
# empty selection. Not `push`: it needs a stage2. Measured 2026-09-30 against the
# 2026-09-29 stage2: 3s warm (the test itself ~3-4s), 108s with the test binary
# rebuilt; green, divzero 0 proved/1 failed -> 1 proved/0 failed.
#
# `quick.trust-cg-diamond-gate` (added 2026-09-19, WS7.11 / F-114): every
# `crates/trust-cg-bridge/tests/*` proven-output file is `#![cfg(feature =
# "ay-proofs")]`, and no row enabled that feature, so `quick.crates-lib-tests`
# and the landing crates/ lane compiled them to EMPTY targets. This row runs the
# block-param diamond fixture (the CondBr-diamond refutation class, its
# computing-arm cells, and the mutated-lowering twins that must come back
# `Refuted`) with the feature on. `--release` is load-bearing, not a speed
# preference: the gate's per-query ay budget is 120s wall, and at opt-level 0
# the u64 xor-arm cells cost ~170s CPU (measured 2026-09-19), so a debug run
# reports them `Unknown` — a completeness miss that would read as a red on
# every run. Optimized, the slowest cell (`sel`) is ~14s CPU.
#
# WS5.23 adds `quick.thir-lower-unit-tests` for a sharper version of the same
# class of reason. `trust-thir-lower` links `rustc_private`, so it is in the
# `exclude` list of `Cargo.toml` (docs/VALIDATION_LADDER.md rung 2):
# `targo ... -p trust-thir-lower` answers "did not match any packages" and
# `quick.crates-lib-tests` sweeps the crates workspace green WITHOUT compiling
# one line of it. The Rust producer's own unit tests — the artifact-publication
# ordering pins, the direct-obligation tiers, and WS5.23's F-099 guard that the
# `.trust-ir.txt` companion is `canonical` of the `.trust-ir.bin` — were
# therefore in NO standing lane. The only rung that reaches the crate is the
# per-crate x.py test step (`scripts/dev-test.sh` drives the same one), so the
# row spells that, whole-crate, and a new `#[cfg(test)] mod` in it is gated by
# existing. `last_green` stays `never` until a full-crate run is measured.
#
# WS5.14 adds `quick.clean-ir-producer-tests` for the same class of reason.
# `quick.crates-lib-tests` runs default-members with `--lib` ONLY, so every integration
# test under `crates/trust-clean-ir/tests/` — the Clean -> TrustIR producer's
# real-island evidence, from the kernel-agreement harnesses to WS5.13's boolean
# spellings and WS5.14's skip-reason texts — was in NO standing lane. The row is
# whole-crate rather than per-`--test`, so a new file in that directory is gated
# by existing, never by remembering to add a row. ~2 min, all lanes debug.
#
# `fast.driver-extra-symbols` (2026-10-12) is the push row for a defect no build
# and no other lane could see. rustc_span pre-interns a fixed list of strings; a
# driver (tippy, miri) hands the interner extra ones when it creates a session,
# and `Interner::prefill` panics on a string that is in both. c73702b157 added
# `VecDeque` and `BinaryHeap` to the predefined list while tippy's list named
# both; it reached main with 35f9d0897f on 2026-10-09, and from then on every
# tippy start died while the compiler built, `scoped.compiler-check` (`x.py
# check`, which type-checks tippy) stayed green, and `tippy-driver --version`
# (all the toolchain output contract runs) answered. No push row builds or
# starts tippy: a type-check is as far as any of them goes, and a name defined
# in both lists is not a type error (tippy's constant shadows the glob
# re-export). A toolchain was sealed that way (trust-2615acef, 2026-10-12);
# aterm's merge gate found it before promotion.
# The row reads compiler/rustc_span/src/symbol.rs as
# compiler/rustc_macros/src/symbols.rs builds it (keyword and symbol VALUES,
# the generated digits and letters, the AppendOnly tail) and each driver's
# `generate! { .. }` list, compares the STRINGS, and names every collision with
# both file:line. Its parse is cross-checked against the file's own
# SYMBOL_DIGITS_BASE pin and its model of both macros against their source, and
# every other use of the extra-symbol mechanism under compiler/ library/ src/
# crates/ targo-trust/ must classify, so a third driver's list cannot go
# unread. No build, no toolchain: 1.3 s on the working tree, measured
# 2026-10-12 (python3 3.14 and /usr/bin/python3 3.9.6). It is a pushed-refs
# reader: under the hook each pushed commit is judged from its own tree, so it
# runs on EVERY push and needs no scope rule: a push that touches neither list
# re-reads two unchanged files. Measured the same day: exit 1 with exactly the
# two collisions on origin/main 2615acefeb (`--rev origin/main`), exit 0 with
# the two names gone from tippy's list.
# `fast.driver-extra-symbols-test` runs
# scripts/tests/check_driver_extra_symbols_test.py: the tokenizer and both list
# readers on the value forms where a name is not its string, the verdict end to
# end in throwaway repositories (the measured collision, collisions by value
# under other names, a same-name pair that is not one, the prefill, a repeat in
# one list, an unknown driver, a drifted macro, a contradicted pin), the push
# reading in both directions, and the checkout's own lists against an
# independent line reader. 37 tests, 10-17 s (load average 5-25), both
# Pythons. It unsets the hook's TRUST_* and GIT_* variables for its fixtures.
#
# `scoped.bootstrap-script-tests` (2026-10-12) runs the bootstrap recreator's
# and the sealing script's own tests, scripts/tests/recreate_bootstrap_test.py
# and scripts/tests/promote_toolchain_test.sh, on a push that changes
# scripts/recreate_bootstrap.py, scripts/promote-toolchain.sh, either test, or
# code those load (scripts/check_bootstrap_script_tests.sh lists every file
# with its load site). Until then only the fast-only scripts.tests.suite glob
# ran them, which the hook does not run: a7ebff4816 and 5a2d23c537 changed
# exactly those two scripts that day and each went out under PRE-PUSH: GREEN
# with neither test run. Like the two shell-scoped rows above, it takes its
# scope from the pushed refs and prints `SKIPPED: ` when out of scope. Unlike
# them it does not then test whatever the worktree holds: the tests load
# files of a checkout, so it first establishes that this checkout HOLDS the
# pushed commit's tree (the same tree as HEAD, no modified tracked file, the
# scope files byte-identical to the commit's blobs, every submodule the commit
# pins checked out at its pin and clean) and refuses, red, with nothing run,
# when it cannot (`git push origin other-branch`; a stale first-party
# worktree, answered with scripts/submodule_sync.sh as the older lanes answer
# it). It needs Python >= 3.11 and says so instead of skipping classes. It
# sits AFTER scoped.crates-tests in manifest order, so the hook's audit of
# what may run beside the crates build (the scoped rows before that one) is
# as it was. NOT SEEN, and printed on every run: tree files the two tests
# read as data (868 Cargo.toml manifests incl. those of the first-party
# submodules, four documents, six src/bootstrap files, six tests/ui/trust
# probes); a push that changes only those is not tested by this row.
# MEASURED 2026-10-12, the lane run as the hook exports a push (one arm64
# Mac, python3 3.14.6, 1-minute load average 1.5-4), twice:
#   in scope and green: 213 s and 232 s. recreate_bootstrap_test.py is 29-30 s
#     of that (202 tests); promote_toolchain_test.sh is 180-200 s (54 cases;
#     alone, the same hour, 197 s at 41% of one core: it waits more than it
#     computes). So an in-scope push pays about four minutes, not the one or
#     two this row was expected to cost;
#   in scope and RED on a scratch commit that breaks the recreator (its seed
#     validation child started without the no-bytecode environment): 4 of 202
#     tests fail, the promote test still runs, 229-231 s;
#   in scope and RED on a scratch commit that breaks the sealer (its
#     tool-start gate returning at once): the promote test fails after 6-7 s
#     ("the tool-start gate did not start the candidate and then the seal"),
#     37-39 s in all;
#   SKIPPED in 0.1 s for a docs-only commit pushed from the checkout and for a
#     docs-only landing of main (d712442cbe);
#   IN SCOPE for both landings named above (0a1bc12a09..a7ebff4816 and
#     a7ebff4816..5a2d23c537), and refused in 0.1 s from a checkout that holds
#     neither tree;
#   refused in a checkout without submodule worktrees: nine modules named,
#     with the scripts/submodule_sync.sh command.
# `fast.bootstrap-script-tests-selftest` runs
# scripts/tests/check_bootstrap_script_tests_test.py on every push: the
# lane's scope list re-derived from the scripts and tests in both directions
# (a load no entry names, an entry nothing loads), and the lane itself in
# throwaway repositories with stub tests (every refusal above, a red test, a
# test file that reports no test, a missing test file, no Python >= 3.11).
# 16 tests, 12.9-15.0 s under /usr/bin/python3 3.9.6 and python3 3.14.6. The
# scope decision it shares with the two older lanes is
# fast.scoped-lane-scope-selftest's, which drives all three since that day:
# 13 tests, 17.6-19.3 s (11.7-14.0 s on origin/main 5a2d23c537, the same
# hour, for two lanes). So these two rows add about 20 s to every push.
# A mutation check of both tests, the same day: 30 one-line mutants of the
# lane (each identity check and each refusal dropped, a red or an empty test
# passed, the hook's variables handed to the tests, any Python accepted, a
# scope entry dropped or invented, scope matched as a substring, the row moved
# before scoped.crates-tests, and the shared block's readings changed) all
# turn one of the two red.
# AFTER AN INDEPENDENT REVIEW, the same day (approve-with-notes; its own runs,
# on a scratch checkout under a load average of 16: green in 248 s, RED on a
# mutant of each script, SKIPPED for a docs-only commit):
#   its one surviving mutant was a sealer whose `--require-provenance` arm
#     did nothing. The promote test asked for that requirement only through
#     TRUST_REQUIRE_BUILD_PROVENANCE, so this row stayed green on it. The test
#     now has a case that spells the flag (55 cases; the figures above are of
#     the 54-case file). On that mutant it fails at its seventh case, after
#     40 s ("--require-provenance did not refuse a legacy top-level stamp");
#     on the real sealer the 55 cases pass, in 232 s;
#   a red here is not always the code. From 13:08 to 13:15 that day, while
#     another session's test suite ran on the machine (1-minute load average
#     2.6-10.6), recreate_bootstrap_test.py took 174 s and 176 s instead of
#     30 s, at 13-14% of one core, with three failures between the two
#     runs: twice the identity probe of a freshly written stand-in tool came
#     back empty (its limit is 10 s), and once a git credential helper ran
#     out its 10 s. Seven minutes later it was 202 tests, OK, in 30 s, on the
#     same blobs. Re-run the row alone before reading such a red.
# AFTER THE STAGE-RECEIPT CHANGE, the same day (the sealer names the
# recreator's receipt and its own tool-start result in a seal's PROVENANCE;
# the recreator records its arguments in the receipt; the receipt reader
# scripts/lib/stage_receipt_provenance.py joins the scope, 16 files):
#   promote_toolchain_test.sh has 71 cases (16 more: three promotions that
#     reach the copy, two refused before it, nine dry runs, two that read a
#     seal an earlier case cut) and recreate_bootstrap_test.py 210 tests (8
#     more, one of them a row for every check of the receipt reader). The lane
#     as `bash scripts/check_bootstrap_script_tests.sh origin/main` on the
#     branch commit holding those blobs, 1-minute load average 4.9 falling to
#     4.5: green in 259 s, 31 s of it the recreate test and 228 s the promote
#     test. origin/main's 55-case file took 198 s on the same Mac an hour
#     earlier (load average 13), so the row is about half a minute dearer: a
#     promotion that seals costs this test about 6 s, one refused before the
#     copy about 3 s, a dry run 0.4 s (the new cases timed alone, load
#     average 14);
#   each of the 16 new cases fails on the sealer of origin/main c2eb05f22f
#     (the cases run alone against that script, every assertion counted);
#   a mutation check of both tests: 65 one-line mutants (13 of the sealer, 42
#     of the reader, 10 of the recreator: the receipt not read before the copy
#     or not again after it, the two readings not compared, a record or a row
#     not written or taken from the wrong run, each check of the reader
#     dropped, the arguments not handed over, not written, not checked, or
#     demanded of an old receipt) all turn one of the two red.
# AFTER THAT CHANGE'S REVIEW, the same day (which characters an argument may
# hold is three code point ranges, the same in the recreator and in
# promotion's reader, where both had asked str.isprintable(); the recorded
# command line is one bounded line of ASCII; the seal says what the receipt
# check does not reach):
#   promote_toolchain_test.sh has 76 cases (5 more, all dry runs: an atpkg
#     receipt, a public release-ready one, an argument holding a character
#     Unicode 14 assigned, arguments too long for a line, the argument
#     `not-recorded`) and recreate_bootstrap_test.py 211 tests (1 more). The
#     two files run directly, one after the other, on those blobs: 30 s and
#     239 s (1-minute load average 2.1 before the first and 17.8 after the
#     second);
#   the three reader mutants the review found alive (the lineage mode read off
#     the Trust-from-Trust flag, an atpkg build printed as a freshly
#     materialized seed, release-ready printed as internal-release-ready) and
#     22 mutants of the review's fixes (a rule that asks the interpreter's
#     Unicode tables again, in either file; a range dropped or widened; an
#     argument written as itself, or with a quote or a backslash unescaped;
#     the bound dropped, moved, or kept by cutting; the seal saying again who
#     wrote the receipt) all turn one of the two red: 25 of 25.
# AFTER THE LLVM-IDENTITY CHANGE, 2026-10-13 (a Stage2+ receipt says which LLVM
# its stage carries, a release-class receipt needs that identity stated, and
# the seal names it: docs/DECISION_QUEUE.md, "a seal knows which LLVM it
# carries"):
#   promote_toolchain_test.sh has 92 cases (85 before: one more promotion that
#     seals, three dry runs that record, three that refuse) and
#     recreate_bootstrap_test.py 225 tests (14 more). The lane as the hook
#     exports a push to main (TRUST_PUSHED_REFS, one update), on the branch
#     commit holding those blobs, 1-minute load average 2.1 before and 16
#     after: green in 293 s, 34 s of it the recreate test and 259 s the
#     promote test;
#   the 7 new promote cases, and the one whose assertions changed, fail on the
#     sealer and reader of origin/main a1112f7077 (the 35 stage-receipt cases
#     run alone against those scripts, every assertion counted: 18 record a
#     failure there, none here); the 14 new recreate tests error there (what
#     they test does not exist);
#   a mutation check of both tests: 95 one-line mutants (79 of the recreator,
#     14 of the reader, 2 of the sealer: an identity stated without evidence,
#     a comparison dropped from the evidence, the fingerprint missing a file, a
#     link or a directory, the record left or quoted when it must not be, a
#     build refused that claims no release, the status word chosen without the
#     record) all turn one of the two red.
# AFTER THE REVIEW OF THAT CHANGE, the same day (same DECISION_QUEUE entry,
# "Changed after review"). The paragraph above describes the first commit,
# 3425097b40, two of whose rules were withdrawn: the receipt's status word no
# longer depends on the LLVM record, and `--fresh-seed`, the documented build
# command, is no longer refused for it. The record refuses nothing by default;
# `--require-llvm-identity`, on the recreator and on the sealer, is the
# fail-closed flag. Measured on the closing commit's blobs:
#   recreate_bootstrap_test.py has 228 tests (225: three new, and two of the
#     first commit's rewritten for the rules that replaced theirs) and
#     promote_toolchain_test.sh 101 cases (92: the
#     release-word refusal is gone; ten new: four refusals under the flag, two
#     seals under it, one seal WITHOUT it under --require-provenance, two dry
#     runs, one that asks three sealed artifacts);
#   main() with exactly the documented arguments, over a real scratch build
#     directory holding an LLVM with no record, under origin/main's recreator
#     and under this one: the same exit (0), the same steps, the same x.py
#     call, the same status word, the same receipt but for `llvm_identity`,
#     and the LLVM directory (stamp and files, bytes and mtimes) untouched in
#     both. The committed test of it turns red under either mutant the review
#     found alive in the first commit;
#   of the 15 recreate tests the closing commit adds or changes, 12 are red on
#     the first commit's scripts and all 15 on origin/main's (the three that
#     pass on the first commit pin what it already did: the cleanliness of all
#     three identity paths, the dot files left out of the fingerprint, the
#     malformed-record table); of the 44 stage-receipt cases of the promote
#     test, 14 record a failure on the first commit's sealer and reader and 27
#     on origin/main's, the ten new cases among both;
#   a mutation check of the closing commit: 71 one-edit mutants (54 of the
#     recreator, 8 of the reader, 9 of the sealer: the documented command
#     refused or its LLVM removed again, the status word made to follow the
#     record, a refusal without its command, the flag accepted and not asked,
#     --require-provenance made to imply it, a failed build's record left on
#     weaker conditions) all turn one of the two red. One of the reader's (the
#     flag taken in any position) survived the first pass and got its test.
# AFTER THE INDEPENDENT RE-READ OF THAT COMMIT, the same day (same
# DECISION_QUEUE entry, "Changed after the independent re-read"). The second
# commit, 0ea1ada74d, stated an LLVM linked through --llvm-config on the hash of
# the llvm-config executable alone, so the flag had a way around it; and a
# deeply nested file where an LLVM's build record would be crashed the
# documented command before x.py, where origin/main builds. An external LLVM is
# never stated now, and no state of the build directory crashes or changes
# that command. Measured on the third commit's blobs:
#   recreate_bootstrap_test.py has 230 tests (228: two new, five changed) and
#     promote_toolchain_test.sh 103 cases (101: a refusal under the flag for a
#     stage2 that links an external LLVM, and a dry-run refusal of the
#     stated-external record the second commit wrote); run directly, one after
#     the other, each green on its first run: 40 s and 296 s;
#   main() with exactly the documented arguments (and --llvm-config where the
#     state is one) over a real scratch checkout and build directory, 21
#     states, under origin/main's recreator, the second commit's and this one's
#     (the re-read's own harness): the same exit, steps, x.py call, LLVM
#     directory when x.py starts, and receipt but for `llvm_identity`, in 21 of
#     21 for this commit and 20 of 21 for the second (the file of 200000 `[`).
#     With the flag the second commit builds both --llvm-config states and
#     this one refuses both before x.py, with the stage0 put back;
#   the seven recreate tests this commit adds or changes are all red on the
#     second commit's scripts and on origin/main's; of the 46 stage-receipt
#     cases of the promote test (every assertion counted), 5 record a failure
#     on the second commit's sealer and reader and 29 on origin/main's, the two
#     new cases among both;
#   a mutation check of this commit: 42 one-edit mutants (32 of the recreator
#     and 3 of the reader against the recreate test, 3 of the sealer and 4 of
#     the reader against the promote test's stage-receipt cases: an external
#     LLVM stated again or with the checkout's ids beside it, the flag not
#     refusing one or telling it to run the same command again, each
#     catch-everything narrowed back to what the file system raises, the
#     stage0 left aside when the refusal's own text fails) all turn one of the
#     two red, over a baseline that is green.
# AFTER THE FOLLOW-UP TO THAT CHANGE'S THIRD READING, the same day (same
# DECISION_QUEUE entry, "The follow-up"). promote-toolchain.sh refuses a word
# after its path, and an option-shaped --lineage operand, as it refuses an
# unknown option (exit 3); the recreator's --verify-stage-provenance and
# --no-build refuse a remainder (exit 2); the receipt reader refuses an operand
# that begins with `-`; an LLVM of unknown mode is defined and carries no id
# of the checkout. Measured on the blobs of that commit:
#   recreate_bootstrap_test.py has 231 tests (230: one new, two changed) and
#     promote_toolchain_test.sh 113 cases (103: seven refusals of a word after
#     the path or of an option for an operand, one seal and two dry runs of an
#     LLVM of unknown mode); run directly, one after the other, at a 1-minute
#     load average of 2: 38 s and 320 s;
#   on origin/main 381ac1ea0d's scripts, all 8 of the new recreate test's
#     subtests, 5 subtests of the changed mode test and the 3 new rows of the
#     reader's command line are red; of the 10 new promote cases (fail made
#     non-fatal, every assertion counted) 9 are red, the one that passes
#     there being the dry run of an unknown record without ids (main's reader
#     already writes not-recorded when the record holds none);
#   a mutation check of the new checks: 27 one-edit mutants (14 of the
#     recreator and 5 of the reader against the recreate test, 8 of the sealer
#     against the whole promote test) each turn red a case that targets them,
#     over a baseline that is green.
# AFTER THAT FOLLOW-UP'S REVIEW, closed 2026-10-14 (same entry, "The
# follow-up's review"). Three modes refuse an option they do not use
# (promote-toolchain.sh --gate-only takes none, --provenance only
# --require-llvm-identity, exit 3; the recreator's --verify-stage-provenance
# only --stage, --host, its three requirements and --check, exit 2); a value
# given twice is refused (--lineage; --stage, --host, --jobs, --llvm-config);
# so are an empty path or reader operand, and a TRUST_REQUIRE_BUILD_PROVENANCE
# that is neither 0 nor 1. Measured on the blobs of that commit:
#   recreate_bootstrap_test.py has 233 tests (231: two new, one changed) and
#     promote_toolchain_test.sh 132 cases (113: nineteen new); run directly,
#     one after the other: 54 s and 426 s (1-minute load 4.5 at its start);
#   on the follow-up's scripts (b8aacbece6) the new recreate rows (12 options,
#     5 values and one through main, 3 reader operands) are red, and 18 of the
#     19 new promote cases, fail made non-fatal (the 19th, `--lineage -`, was
#     refused there already); on origin/main all 19 are red;
#   a mutation check of the new checks: 32 one-edit mutants (16 of the sealer
#     against the promote cases of the refusals, 15 of the recreator and 1 of
#     the reader against the new and changed recreate tests) each turn red a
#     case that targets them, over an unchanged control that is green.
#
# `scoped.targo-trust-unit-tests` (2026-10-14, TRUST-KI-1014-3) runs
# targo-trust's unit binary (`targo --unverified test --manifest-path
# targo-trust/Cargo.toml --locked --bin targo-trust`, default features) on a
# push that changes what that binary is built from: targo-trust/, the root
# .cargo/, or a local package of its dependency graph as `targo metadata`
# resolves it (its directory, Cargo.toml for a crates/ package, the
# first-party gitlink holding one; scripts/check_targo_trust_unit_tests.sh
# says why each). Until then no push row ran one targo-trust test. Not the
# integration binaries: the whole suite is 16-22 min (quick.targo-trust-tests
# keeps it). Its scope decision is the shared block, driven by
# fast.scoped-lane-scope-selftest with a stub `targo`; it fails toward
# running when the graph cannot be read, is red when the run reports no passed
# test, and refuses (exit 2) without targo. It sits after
# scoped.bootstrap-script-tests, so nothing it builds overlaps the crates
# build. MEASURED 2026-10-14 (18-core Mac, 1-minute load 26-62):
#   in scope (this lane's own branch, targo-trust/ changed), the unit binary
#     already built: green, 2238 passed, in 37 s; a cold build of its test
#     profile took 6.6 min and an incremental one after a targo-trust change
#     33 s;
#   SKIPPED in 0.06 s for a docs-only commit (e8fd0e4ce1) and in 0.7 s for a
#     crates/ commit outside the graph (2b25908ee2, trust-thir-lower: the
#     graph read); IN SCOPE for a trust-vcgen commit (0b59290ff2), a
#     first-party/ay pin move (58fd7e3205) and a trust-clean fixture change
#     (16c324eb3f), with a stand-in targo;
#   red (exit 1) for a stand-in run that fails and for one that reports 0
#     passed; exit 2 with no targo on PATH;
#   fast.scoped-lane-scope-selftest: 13 tests OK (4 skipped, the bootstrap
#     lane's), 41-48 s with the fourth lane against 44 s without it at a load
#     of 50-60 (noise above the lane's own cost).
#
# `fast.clean-proof-obligations` (2026-10-09) runs trust-integration-tests'
# `clean_proof_obligations::tests`, the in-process half of the Clean proof
# gates: g16_multiplier_equivalence.lean and i128_mul_corner_bounds.lean must
# still PROVE the theorems the binary gates name (each registered by the file
# and accepted by `audit_cited_theorem`: a `theorem`, closure free of
# non-foundational axioms), the load-bearing ones must keep their pinned
# statements (structural equality of the kernel terms, so neither `True` nor
# the value a closed `rfl` witness computes to stands in),
# MAX_RECHECKABLE_MUL_WIDTH in trust-cg-bridge's verify_output.rs must be
# declared once and stay 8 while G16Mul.ay_blast_agrees is unproved, and three
# red controls hold (a theorem leaning on `axiom bad : False` is refused on its
# own account; a `def` wearing a required name is not a proof; a required
# theorem restated under its own name fails its pin). Until then only the
# binary gates asserted the names and the cap, nothing asserted a statement,
# and every one of those gates passed with a NOTICE whenever no `clean`
# executable was found: every fresh clone and worktree. A `--lib` filter that
# selects nothing exits 0, so the row demands >= 8 passed (the module's eight
# tests). The push lane reaches the same tests through its
# CROSS_CRATE_INSTRUMENTS entry when proofs/codegen-equivalence/,
# proofs/trust-soundness/, crates/trust-cg-bridge/src/ or trust-certify's
# src/clean_island* moves. Measured 2026-10-09: 14s warm at load average ~10
# (30s at ~20; the G16 file's in-process check is most of the test time),
# 4m19s from an empty target dir at ~8; renaming
# CornerBox.mul_box_upper, restating CornerBox.corner_witness_negative as
# `True`, or setting the cap to 9, turns it red while fast.lean-front-door-gate
# stays green.
#
# `slow.clean-binary-proof-gates` (2026-10-09) is the binary half. It refuses
# unless first-party/clean is checked out at its gitlink with no change, an
# untracked file included (an untracked build.rs or .cargo/config.toml changes
# the binary as surely as an edit does; ignored build output does not count),
# builds `clean` from it (`--release --locked`, the bin cargo reports), exports
# that path as TRUST_CLEAN_BIN, and runs the five `#[ignore]`d gates
# (ay_blast_correspondence, structured_multiplier_proof, i128_corner_bounds_proof,
# codegen_equivalence, trust_soundness_ouroboros) by `--exact` name, demanding
# `1 passed; 0 failed` from each. Without the variable they panic with the build
# recipe. Before, they searched beside the test binary, build/*/stage{2,3}/bin
# and first-party/clean/target, and passed with a NOTICE when nothing was there;
# on the measured host they found the 2026-09-29 stage2 `clean`, not the pin.
# Measured 2026-10-09 at load average ~20, cold target dir: 15m12s, of which the
# release build of `clean` was 13m50s and the five gates 1.6-21s each; again at
# ~10 after the review fixes: 11m37s (release build 10m37s), and a failed build
# leaves no temporary file behind.
#
# `slow.storage-geometry-visitors` (2026-11-10, SCRIPTS-REDS-20261110) runs the
# native half of scripts/check_storage_geometry_visitors.py (b092a86cf0): it
# extracts the exact Storage-handling declarations from eight
# crates/trust-thir-lower/src files, compiles them against the checked-out
# first-party/trust-ir with the probe's tests.rs, runs them through
# scripts/build-slot, and passes only on exactly the five named controls with
# zero failed or ignored. Its source hashes, tool identity and IR commit are
# bookended. Nothing else runs these controls: trust-thir-lower's own unit
# tests have none for Storage geometry. The script-test aggregate covers only
# the --prepare-only extraction and the population reporter
# (storage_geometry_probe_reporter_test.py). `slow`, not `fast`: the probe has
# no committed lock, so `targo metadata` resolves tracing and trust-ir's
# registry dependencies when it runs; the targo is the one on PATH, which the
# probe refuses unless it answers as genuine Targo. Measured 2026-11-10 on
# 7a51dcee84 (inputs unchanged through 6f508f2264): exit 0, 5 passed /
# 0 failed / 0 ignored, a 2m09s cold build after a ~19 min admission wait.
#
# `slow.targo-dependency-filename-process` (2026-11-10, TARGO-FILENAME-PROCESS-ROW-1)
# runs scripts/tests/targo_dependency_filename_process.py, the real process
# regression DECISION_QUEUE names for Targo's compiler-filename inventory
# (935dc6f944, a243bae0a2): four legal Unix source filenames (trailing space,
# terminal backslash, CR, LF), each with a decoy beside it, through cold, warm,
# same-size-and-mtime edit and warm builds of `targo --unverified run`; it
# passes only when every phase executes the real source's value and freshness
# is exactly as expected (LF must rebuild with `content-fingerprint-unavailable`).
# Its producers are explicit: this tree's stage2 targo and trustc, and a fresh
# evidence directory. The script-test aggregate does not run it (it is not a
# *_test file), and sdk_targo_current_component.py's own LF control judges a
# component record, not this tree's Targo. `slow`, not `release`, until a first
# green on a stage2 carrying a243bae0a2: none existed on the authoring host. The
# deployed seal pairing (29ebb403de) fails its first phase, `malformed dep-info
# format, trailing \` (measured 2026-11-10), so the row does discriminate.
#
# `fast.asl1-reference-custody` (2026-11-10, SCRIPTS-REDS-20261110) runs
# scripts/trust_core/asl1/check_reference.py, the committed-source half of the
# ASL1 CC1 foundation: the retained BSD ASLRef files under
# scripts/trust_core/asl1/reference/ must match reference/SOURCE.json (pinned
# herdtools7 ASLRefEAC1 commit, BSD-3-Clause, no licensed Arm package) byte for
# byte with no file added or missing, and the leaf denominator must hold: 26
# AST.mli binary operators, Import.lean's RawOp mirroring them in order, exactly
# ADD/SUB supported and the other 24 listed as refused in Fixtures.lean, six
# literal constructors. Offline, no arguments, a nonzero exit on any drift.
# It landed 2026-11-07 (d65ecb0cd4) in no row. Its producer halves
# (build_exporter.py, producer_controls.py) need an owned OCaml prefix and a
# caller-built exporter and are MANUAL_ONLY in check_gate_lane_coverage.py.
# Measured 2026-11-10 on 7a51dcee84: exit 0, BSD_SOURCE_CUSTODY_AND_DENOMINATOR_PASS,
# under 0.1s.
#
# `fast.upstream-revision-consistency` (2026-10-28) holds every spelling of the
# upstream baseline revision to tests/upstream-rust/baseline.toml: the port
# command documented there and release/trust-version.toml [rust_alignment].
# The native CLI derives its default from the selected baseline; controls
# reject reintroduced fixed defaults. This began as a push row after stale
# defaults survived the 2026-10-16 migration. The current focused development
# push profile retains it as an explicit required fast diagnostic, which
# migration qualification runs directly. Python 3.9 is sufficient. Measured
# 2026-10-28: 8 tests, under 0.1s; that historical execution remains scoped.
#
# `fast.corpus-membership` (2026-11-10, CORPUS-MEMBERSHIP-AT-LANDING-1 in
# docs/DECISION_QUEUE.md) is the one push row outside the eight live-verifier
# and proof-input rows DEV-MAIN-FOCUSED-VALIDATION-20261102 kept, and the
# record argues why. trust-json's and trust-toml's acceptance gates pin their
# corpus MEMBERSHIP exactly (`corpus_membership_matches_the_pinned_manifest`),
# tracked `*.json`/`*.toml` documents are added by ordinary work everywhere,
# and no landing ran either Rust test, so main went red at each such landing
# (twice on 2026-11-10). The row applies both membership rules to the PUSHED
# tree from git objects, compiling nothing (about a second), and keys each
# cause, so a red main already carries is INHERITED and only the landing that
# moves a membership must carry its re-pin
# (`python3 scripts/check_corpus_membership.py --write`). It reads
# TRUST_PUSHED_REFS whenever it is set; unset, it judges HEAD. Python 3.9 is
# sufficient. Its tests: scripts/tests/check_corpus_membership_test.py (the
# rule against each header's documented command, on this checkout and on
# adversarial trees) and land_gate_test's CorpusMembershipInheritedRedTests
# (graded by push-rows).
#
# `fast.ledger-pins` (2026-11-10, LEDGER-PIN-CURRENCY-AT-LANDING-1) is the
# second push row outside those eight, on the same argument. The escape-audit
# ledger (scripts/gates/land-escape-audits.toml) and the IR read set
# (scripts/ir_cohort_physical_read_set.json) pin reviewed blobs; both products
# fail closed on a moved pin (an unresolved site reads everything; the IR-only
# run does not narrow), so a stale pin costs scope, never a verdict. But their
# currency tests hold the live entries to the live tree, no landing ran them
# for a change to a pinned premise or reader, and main went red three times on
# 2026-11-10 until someone else renewed the pin. The row reads the PUSHED tree
# from git objects (well under a second) and FAILs each pin that moved unless
# its entry is renewed or explicitly marked `lapsed` in the same push; it keys
# each (`escape-audits <table> <file> MOVED <path> <pinned blob>`, `ir-read-set
# <reader> MOVED <pinned blob>`, ...), so a red main carries is INHERITED. Its
# refusal says how to renew or lapse. Python 3.11+ (tomllib; it re-executes
# under the newest one on PATH). Its tests: scripts/tests/check_ledger_pins_test.py
# (fixture trees, and `--mutants`).
#
# `fast.land-rows-coverage` (2026-11-15, LAND-ROWS-COVERAGE-AT-LANDING-1) is the
# third, on the same argument. The landing gate's row table (gates/land.toml)
# must name every tracked scripts/tests/*_test.py exactly once, as a [[row]] or
# a [[not_run]]; land_gate_test's ValidationDependencyTests holds the tree to it,
# but a landing that only adds a test module never runs that test, and main
# went red for every session twice on 2026-11-15 (8f4a08d99b78, 4c33bc0df3ef)
# until someone else registered the module. The row (`land_gate.py rows
# --check`, a subcommand, not a new script) applies land_select's one rule to
# the PUSHED commit from git objects (under a second: one ls-tree, one
# cat-file), names each uncovered, doubly-covered or untracked file with the
# [[row]] that registers it, and keys each (`land-rows UNCOVERED <path>`, ...),
# so a red main carries is INHERITED. A commit cut before the table (no table,
# and a land_select.py that never names it) has no such rule: `NOT IN FORCE`,
# SKIPPED. Python 3.11+ (tomllib): land_gate.py
# re-executes under the newest python3.1x on PATH and exits 2 when there is
# none, so the row FAILs there; it never skips. Its tests: land_gate_test's
# LandRowsCoverageCheckTests (fixture commits, the real HEAD, push-rows grading).
#
# `fast.luminal-domination-ledger` holds tests/luminal-domination/capabilities.json
# (one row per Luminal capability; docs/PLAN.md section 4) to its schema, to the
# plan (every capability row names a `PKG-U` row of docs/PLAN.md), and to the two
# pinned counts: rows whose `exit` names a command, and capability rows. It runs
# no exit command, so it says how many rows are NAMED and nothing about how many
# are met. A commit that fills, adds or removes a ledger row moves the pins here
# in the same change. `slow.luminal-domination-met` (2026-11-14, PKG-U13f, the
# first package to fill a row) is the `--run` row: it runs every named exit and
# FAILs when one does not exit 0 with its `LUMINAL-ROW <id> PASS` line, so a
# named row cannot rot unseen. It is slow, never push: today's exits build
# crates/trust-luminal-rows against trust-ir and SemR (`lake build semr_eval`),
# and they need `targo` and Lean on the host. Its tests: scripts/tests/luminal_domination_test.py
# (fixture ledgers; it also holds both rows' commands and this row's pins to
# the committed ledger).
emit_gate_manifest() {
    cat <<'EOF'
manifest.syntax.comprehensive|all|harness|true|2026-09-30|bash -n tests/run_trust_comprehensive_harness.sh
manifest.syntax.superset|all|harness|true|2026-09-30|bash -n tests/run_trust_superset_suite.sh
manifest.syntax.robust|all|harness|true|2026-09-30|bash -n tests/run_trust_robust_suite.sh
manifest.syntax.targo-cli|all|harness|true|2026-09-30|bash -n tests/e2e_targo_trust_cli.sh
manifest.syntax.targo-root-resolution|all|harness|true|2026-09-30|bash -n tests/e2e_targo_trust_root_resolution.sh
manifest.syntax.run-tests-after-build-failclosed|all|harness|true|2026-09-30|bash -n tests/e2e_run_tests_after_build_fail_closed.sh
manifest.syntax.gate-scripts|all|harness|true|2026-09-30|bash scripts/check_gate_script_syntax.sh
manifest.ledgers|all|harness|true|2026-09-30|test -f tests/upstream-rust/test-exceptions.toml && test -f tests/upstream-rust/patches.toml && test -f tests/upstream-rust/divergence-audit.toml && test -f tests/trust-added/compiletest-exceptions.toml && test -f tests/trust-added/manifest.toml && test -f tests/trust-comprehensive/divergences.toml
manifest.canonical-targo-e2e-names|all|harness|true|2026-09-30|test -x tests/e2e_targo_trust_cli.sh && test -x tests/e2e_targo_trust_root_resolution.sh && test ! -e tests/e2e_cargo_trust_cli.sh && test ! -e tests/e2e_cargo_trust_root_resolution.sh
manifest.lane-coverage|all|harness|true|2026-09-30|python3 scripts/check_gate_lane_coverage.py
fast.native-admission-oracle-tests|fast,release|script-tests|true|never|python3 tests/native-admission-census/test_run.py
fast.two-language-wire-grader-selftest|fast,release|infrastructure|true|2026-09-30|python3 tests/two-language-programs/wire_grade.py --selftest
fast.conversion-guide-paths|fast,release|drift|true|2026-09-30|bash scripts/check_conversion_guide_paths.sh
fast.ledger-expirations|fast|ledger|true|2026-09-30|python3 scripts/check_ledger_expirations.py --warn-days 14
fast.upstream-revision-consistency|fast|drift|true|never|python3 -B scripts/tests/upstream_revision_consistency_test.py
fast.toolchain-coherence|fast|drift|true|2026-09-30|python3 scripts/check_toolchain_coherence.py
fast.proc-macro-install-names|fast|drift|true|2026-09-30|python3 scripts/check_proc_macro_install_names.py
fast.seed-freshness|fast|bootstrap|true|2026-08-27|scripts/check_seed_freshness.py
fast.help-surfaces|fast|drift|true|2026-09-30|python3 scripts/check_help_surfaces.py
fast.help-surfaces-selftest|fast|drift|true|2026-09-30|python3 scripts/check_help_surfaces.py --selftest
fast.trust-ir-tag-families|fast,release|drift|true|2026-09-30|python3 scripts/trust_ir_tag_families.py --check
fast.trust-ir-tag-families-selftest|fast,release|drift|true|2026-09-30|python3 scripts/trust_ir_tag_families.py --selftest
fast.trust-ir-seam-blockers|fast,release|drift|true|2026-09-30|python3 scripts/trust_ir_producer_scorecard.py --check-seam-blockers
fast.trust-ir-seam-blockers-selftest|fast,release|drift|true|2026-09-30|python3 scripts/trust_ir_producer_scorecard.py --selftest-seam-blockers
fast.trust-ir-verifier-acceptance-pins|fast,push,release|soundness|true|2026-09-29|python3 scripts/trust_ir_verifier_acceptance_pins.py --check
fast.mir-transform-ratchet-selftest|fast,release|drift|true|2026-09-30|bash scripts/check_trust_verify_suite_ratchet.sh --selftest
fast.compiler-unit-tests-selftest|fast,release|compile|true|2026-09-27|bash scripts/check_compiler_unit_tests.sh --selftest
fast.call-summary-labels|fast|drift|true|2026-09-30|python3 scripts/check_call_summary_labels.py
fast.call-summary-labels-selftest|fast|drift|true|2026-09-30|python3 scripts/check_call_summary_labels.py --selftest
fast.cfg-test-caller-skew|fast,push|compile|true|2026-09-30|python3 scripts/check_cfg_test_caller_skew.py --push-context
fast.cfg-test-caller-skew-selftest|fast|compile|true|2026-09-30|python3 scripts/check_cfg_test_caller_skew.py --selftest
fast.cfg-test-caller-skew-test|fast|compile|true|2026-09-30|bash scripts/tests/check_cfg_test_caller_skew_test.sh
fast.run-make-fixture-lex|fast|compile|true|2026-09-30|python3 scripts/check_run_make_fixture_lex.py
fast.run-make-fixture-lex-selftest|fast|compile|true|2026-09-30|python3 scripts/check_run_make_fixture_lex.py --selftest
fast.fixture-span-paths|fast|compile|true|2026-09-30|python3 scripts/check_fixture_span_paths.py
fast.fixture-span-paths-selftest|fast|compile|true|2026-09-30|python3 scripts/check_fixture_span_paths.py --selftest
fast.driver-extra-symbols|fast|compile|true|never|python3 scripts/check_driver_extra_symbols.py
fast.driver-extra-symbols-test|fast|compile|true|never|python3 -B scripts/tests/check_driver_extra_symbols_test.py
fast.pin-coherence|fast,push|supply-chain|true|2026-09-30|bash scripts/check_pin_coherence.sh
fast.first-party-pin-lattice|fast|supply-chain|true|2026-09-30|scripts/check_first_party_pin_lattice.py
fast.dependency-constellation|fast,release|supply-chain|true|2026-09-17|scripts/check_dependency_cycle_anchor.py --push-context --derive-when-receipt-absent
fast.dependency-constellation-selftest|fast,release|supply-chain|true|2026-09-30|scripts/check_dependency_cycle_anchor.py --selftest
fast.oracle-freeze|fast,push|soundness|true|2026-09-30|bash scripts/check_frozen_files.sh
fast.oracle-freeze-selftest|fast|soundness|true|2026-09-30|bash scripts/check_frozen_files.sh --selftest
fast.revert-rationale|fast,push|soundness|true|2026-09-30|bash scripts/check_revert_rationale.sh --push-context
fast.revert-rationale-test|fast|soundness|true|2026-09-30|bash scripts/tests/check_revert_rationale_test.sh
fast.measurement-provenance|fast,push|soundness|true|2026-08-20|bash scripts/check_measurement_provenance.sh --push-context
fast.measurement-provenance-selftest|fast|soundness|true|2026-09-30|bash scripts/check_measurement_provenance.sh --selftest
fast.measurement-provenance-test|fast|soundness|true|2026-09-30|bash scripts/tests/check_measurement_provenance_test.sh
fast.bridge-pin|fast,push|supply-chain|true|2026-09-30|bash scripts/check_bridge_pin.sh --check
fast.patch-binds|fast,push|supply-chain|true|2026-09-30|python3 scripts/check_patch_binds.py
fast.patch-binds-test|fast|supply-chain|true|2026-09-30|bash scripts/tests/check_patch_binds_test.sh
fast.audited-trust-spec-sources|fast,push,release|supply-chain|true|2026-09-30|python3 scripts/check_audited_trust_spec_sources.py
fast.audited-trust-spec-sources-selftest|fast,release|supply-chain|true|2026-09-30|python3 scripts/check_audited_trust_spec_sources.py --selftest
fast.asl1-reference-custody|fast|supply-chain|true|never|python3 scripts/trust_core/asl1/check_reference.py
fast.cargo-lock-hygiene|fast|supply-chain|true|2026-11-06|scripts/check_cargo_lock_hygiene.py
fast.cargo-lock-hygiene-selftest|fast|supply-chain|true|2026-11-06|scripts/check_cargo_lock_hygiene.py --selftest
slow.cargo-lock-hygiene-mutants|slow|supply-chain|true|2026-11-06|python3 scripts/tests/check_cargo_lock_hygiene_mutants.py
fast.cargo-manifest-alignment|fast|supply-chain|true|2026-09-30|python3 scripts/check_cargo_manifest_alignment.py
fast.corpus-membership|fast,push|drift|true|2026-11-10|python3 scripts/check_corpus_membership.py
fast.ledger-pins|fast,push|drift|true|2026-11-10|python3 scripts/check_ledger_pins.py
fast.land-rows-coverage|fast,push|drift|true|never|python3 -B scripts/land_gate.py rows --check
fast.luminal-domination-ledger|fast,release|drift|true|never|python3 -B scripts/luminal_domination.py --ledger tests/luminal-domination --expect-named 4 --expect-total 475
slow.luminal-domination-met|slow|product|true|never|python3 -B scripts/luminal_domination.py --ledger tests/luminal-domination --run
fast.submodule-remote-reachability|fast,push|supply-chain|true|2026-09-30|python3 scripts/check_submodule_remote_reachability.py --push-context
fast.submodule-remote-reachability-selftest|fast|supply-chain|true|2026-09-30|python3 scripts/check_submodule_remote_reachability.py --self-check
fast.doc-counts|fast|docs|true|2026-09-30|bash scripts/check_doc_counts.sh
fast.doc-counts-test|fast|docs|true|2026-09-30|bash scripts/tests/check_doc_counts_test.sh
fast.trust-version-sync|fast|drift|true|2026-09-30|scripts/trust_version_sync.py --check
slow.frontier-ratchet|slow|frontier|true|never|"${TRUST_FRONTIER_TARGO:-build/host/stage2/bin/targo-trust}" self-improve --baseline "${TRUST_FRONTIER_BASELINE:-reports/trust-frontier-baseline.json}" --require-no-regression
slow.call-summary-census|slow|frontier|true|2026-08-29|bash scripts/call_summary_census.sh --out reports/call-summary-census-gate
slow.call-summary-census-aggregator|slow|frontier|true|2026-08-29|bash scripts/call_summary_census.sh --selftest
slow.upstream-rust-test-toolchain|slow|upstream|true|never|bash scripts/check_upstream_rust_test_toolchain.sh
slow.closure-slice-facts|slow|frontier|true|never|bash scripts/closure_slice_facts.sh
slow.daily-driver-probes|slow|frontier|true|never|bash scripts/daily_driver_probes.sh
slow.open-dispatch-ladder|slow|frontier|true|never|bash scripts/open_dispatch_ladder.sh
slow.vec-literal-lowering|slow|frontier|true|never|bash scripts/vec_literal_lowering.sh
slow.panicking-std-battery|slow,release|soundness|true|never|bash scripts/panicking_std_battery.sh
slow.fn-pointer-witness|slow,release|soundness|true|never|bash scripts/fn_pointer_witness.sh
slow.forged-std-name-witness|slow,release|soundness|true|never|bash scripts/forged_std_name_witness.sh
slow.daily-driver-bench|slow|frontier|false|never|bash scripts/daily_driver_bench.sh
slow.ordinary-rust-sweep|slow|frontier|false|never|bash scripts/ordinary_rust_sweep.sh
slow.idiomatic-rust-sample|slow|frontier|false|never|bash scripts/idiomatic_rust_sample.sh
slow.storage-geometry-visitors|slow|compile|true|never|python3 scripts/check_storage_geometry_visitors.py --output "$(mktemp -d)/out" --targo "$(command -v targo)"
slow.targo-dependency-filename-process|slow|compile|true|never|python3 scripts/tests/targo_dependency_filename_process.py --targo "$(pwd -P)/build/host/stage2/bin/targo" --rustc "$(pwd -P)/build/host/stage2/bin/trustc" --evidence "$(mktemp -d)/evidence"
release.audited-trust-spec-sources-complete|release|supply-chain|true|2026-09-24|python3 scripts/check_audited_trust_spec_sources.py --require-all
release.submodule-lock-coherence|release|supply-chain|true|never|bash scripts/check_submodule_lock_coherence.sh
release.ay-projection-certificate|release|supply-chain|true|2026-09-17|bash scripts/check_ay_projection_certificate.sh
release.trust-mir-extract|release|compile|true|2026-09-17|bash scripts/check_trust_mir_extract.sh
release.two-language-completion|release|soundness|true|never|TRUST_TOP_VERIFIER_PATH="${TRUST_TWO_LANGUAGE_TOP_VERIFIER:-/etc/trust/two_language_completion_gate.py}" && test -n "${TRUST_TWO_LANGUAGE_TOP_VERIFIER_SHA256:-}" && TRUST_TOP_VERIFIER_ACTUAL="$(/usr/bin/shasum -a 256 "$TRUST_TOP_VERIFIER_PATH")" && test "${TRUST_TOP_VERIFIER_ACTUAL%% *}" = "${TRUST_TWO_LANGUAGE_TOP_VERIFIER_SHA256}" && python3 "$TRUST_TOP_VERIFIER_PATH" --candidate-verifier scripts/two_language_completion_gate.py --receipt "${TRUST_TWO_LANGUAGE_COMPLETION_RECEIPT:-build/two-language-completion/receipt.json}" --root . --trusted-owner-key "${TRUST_TWO_LANGUAGE_OWNER_KEY:-/etc/trust/two-language-owner.pub}"
release.two-language-programs|release|product|true|never|mkdir -p build/evidence && TRUSTC=build/host/stage2/bin/trustc bash tests/e2e_two_language_programs.sh --out build/evidence/two-language-programs.md --ir-evidence build/evidence/two-language-programs-ir.json
scoped.compiler-check|all|supply-chain|true|2026-09-17|bash scripts/check_compiler_targets_build.sh
scoped.completion-gate-tests|all|soundness|true|2026-09-27|bash scripts/check_completion_gate_tests.sh

scoped.crates-tests|fast|crates|true|2026-09-23|python3 scripts/check_crates_tests_scoped.py --push-context
scoped.bootstrap-script-tests|fast|bootstrap|true|never|bash scripts/check_bootstrap_script_tests.sh
scoped.targo-trust-unit-tests|fast|crates|true|never|bash scripts/check_targo_trust_unit_tests.sh
fast.bootstrap-script-tests-selftest|fast|harness|true|never|python3 -B scripts/tests/check_bootstrap_script_tests_test.py
fast.crates-tests-scoped-selftest|fast|harness|true|2026-09-30|python3 scripts/tests/check_crates_tests_scoped_test.py
fast.seal-driver-sysrootcheck-selftest|fast|harness|true|2026-09-30|bash scripts/tests/seal_driver_sysrootcheck_test.sh
fast.scoped-lane-scope-selftest|fast|harness|true|2026-09-30|python3 -B scripts/tests/scoped_lane_push_scope_test.py
fast.land-gate-selftest|fast|harness|true|never|python3 -B scripts/tests/land_gate_test.py
fast.prewarm-push-selftest|fast|harness|true|never|python3 -B scripts/tests/prewarm_push_test.py
fast.xpy-build-lock-selftest|fast|harness|true|never|python3 -B scripts/tests/xpy_build_lock_test.py
fast.compiler-check-consult-test|fast|harness|true|never|bash scripts/tests/compiler_check_selector_consult_test.sh
slow.land-gate-mutants|slow|harness|true|never|python3 -B scripts/tests/land_gate_test.py --mutants
slow.land-gate|slow|harness|true|never|scripts/land_gate.py run
fast.tcb-panic-freedom|fast|soundness|true|2026-07-25|bash scripts/check_tcb_panic_freedom.sh
verify.executes|fast,push|soundness|true|2026-09-30|bash scripts/check_verifier_executes.sh
fast.tcb-document-exhaustiveness|fast|soundness|true|2026-09-30|targo --unverified test --manifest-path Cargo.toml -p trust-integration-tests --test tcb_document_exhaustiveness --locked
fast.vckind-exhaustiveness|fast|soundness|true|2026-09-30|targo --unverified test --manifest-path Cargo.toml -p trust-integration-tests --test vckind_exhaustiveness --locked
fast.lean-front-door-gate|fast|soundness|true|2026-09-30|targo --unverified test --manifest-path Cargo.toml -p trust-integration-tests --test lean_front_door_gate --locked
fast.clean-proof-obligations|fast|soundness|true|never|OUT="$(targo --unverified test --manifest-path Cargo.toml -p trust-integration-tests --lib --locked -- clean_proof_obligations::tests:: 2>&1)"; S=$?; printf '%s\n' "$OUT"; N="$(sed -nE 's/^test result: ok\. ([0-9]+) passed; 0 failed.*/\1/p' <<<"$OUT")"; if [ "$S" -ne 0 ]; then (exit "$S"); elif [ -n "$N" ] && [ "$N" -ge 8 ]; then true; else echo "FAIL: clean_proof_obligations::tests reported ${N:-no} passed, expected at least 8; a filter that selects nothing exits 0 having run no test" >&2; false; fi
fast.tcb-direct-trust-vc-certificate-boundary|fast|soundness|true|2026-09-30|targo --unverified test --manifest-path Cargo.toml -p trust-vc-bridge --features trust-build direct_mir_memory_admission_binds_the_alethe_certificate_but_never_rechecks_it --locked
fast.tcb-direct-trust-vc-kernel-shape|fast|soundness|true|2026-09-30|targo --unverified test --manifest-path Cargo.toml -p trust-certify --test direct_trust_vc_lane_shape --locked
fast.tidy|fast|style|true|2026-07-25|python3 x.py test --stage 1 src/tools/tidy
fast.crates-workspace-check|fast|compile|true|2026-09-30|targo --unverified check --manifest-path Cargo.toml --all-targets --keep-going --locked
fast.targo-trust-check|fast|compile|true|2026-09-30|targo --unverified check --manifest-path targo-trust/Cargo.toml --all-targets --keep-going --locked
fast.compiler-check|fast|compile|true|2026-09-30|RUSTC_BOOTSTRAP=1 python3 x.py check --stage 1 compiler
scripts.tests.suite|fast|script-tests|true|never|bash scripts/check_script_tests.sh
fast.reports-script-copies|fast|harness|true|2026-09-25|python3 scripts/check_reports_script_copies.py
quick.superset|quick|verification|true|never|bash tests/run_trust_superset_suite.sh quick
quick.robust-smoke|quick|compatibility|true|never|bash tests/run_trust_robust_suite.sh smoke
quick.crates-lib-tests|quick|crates|true|never|targo --unverified test --manifest-path Cargo.toml --lib --locked --no-fail-fast
quick.trust-cg-diamond-gate|quick|soundness|true|2026-09-19|targo --unverified test --release --manifest-path Cargo.toml -p trust-cg-bridge --features test-hooks --test trust_ir_gate_diamond_shapes --locked
quick.clean-ir-producer-tests|quick|crates|true|2026-09-19|targo --unverified test --manifest-path Cargo.toml -p trust-clean-ir --locked
quick.thir-lower-unit-tests|quick|compile|true|never|RUSTC_BOOTSTRAP=1 python3 x.py test --stage 1 crates/trust-thir-lower
quick.targo-trust-tests|quick|crates|true|2026-09-28|targo --unverified test --manifest-path targo-trust/Cargo.toml --locked --no-fail-fast
quick.compiler-unit-tests|quick|compile|true|never|RUSTC_BOOTSTRAP=1 python3 x.py test --stage 1 compiler/rustc_driver_impl compiler/rustc_session compiler/rustc_mir_transform
quick.falsification-classifier|quick|compile|true|2026-09-14|bash tests/trust-falsification/classify_verdict_test.sh
trust.added.quick|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh quick
stage2.build|release|bootstrap|true|2026-09-29|python3 x.py build --stage 2
release.native-admission-census|release|resource-attribution|true|never|python3 tests/native-admission-census/run.py --bin build/host/stage2/bin --verify-stage-provenance
upstream.trust-compat|release|upstream|true|never|TRUST_STRICT=1 TRUST_SUPERSET_ASSUME_STAGE2=1 bash tests/run_trust_superset_suite.sh trust-compat
upstream.porting|release|upstream|true|never|TRUST_STRICT=1 TRUST_RELEASE_GATE=1 TRUST_UPSTREAM_RUST_PORT_RELEASE=1 bash tests/run_trust_superset_suite.sh upstream-rust-porting
trust.examples.complete-corpus-diagnostic|release|non-evidence-regression-diagnostic|true|never|env -u TRUST_RELEASE_GATE TRUST_COMPLETE_CORPUS_DIAGNOSTIC=1 bash tests/e2e_verify_suite.sh
trust.added.compiletest|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh trust-added-compiletest
trustc.native|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh trustc-native
native-contracts.pipeline-v2|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh native-contracts-pipeline-v2
trust.extra|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh trust-extra
binary.decompilation-golden|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh binary-decompilation-golden
semantic.parity|release|compatibility|true|never|bash tests/e2e_semantic_parity.sh
robust.launch|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh launch
robust.public-distribution|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh public-distribution
robust.prepublish|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh prepublish
robust.installed|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh installed
robust.installed-default|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh installed-default
robust.stage0-lineage|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh stage0-lineage
gate.status|release|reporting|true|never|bash tests/report_trust_gate_status.sh
integrated.full-verify|release|integrated|true|never|scripts/build.sh full-verify
verify.e2e-shell-corpus|release|e2e|true|never|bash scripts/run_e2e_shell_corpus.sh
verify.falsification|release|soundness|true|never|bash scripts/trust_falsification_gate.sh
verify.codegen|release|soundness|true|never|bash scripts/trust_codegen_gate.sh
verify.ownership|release|soundness|true|never|bash scripts/trust_ownership_gate.sh
verify.superiority|release|soundness|true|never|bash scripts/trust_superiority_gate.sh
verify.temporal|release|soundness|true|never|bash scripts/trust_temporal_gate.sh
verify.clean-certification|release|soundness|true|never|bash scripts/trust_clean_certification_gate.sh
oracle.array-bounds-soundness|release|soundness|true|2026-08-26|python3 scripts/trustc_array_bounds_soundness_oracle.py
oracle.generics-soundness|release|soundness|true|2026-08-26|python3 scripts/trustc_generics_soundness_oracle.py
oracle.falseproof-search|slow,release|soundness|true|never|python3 scripts/trust_falseproof_search.py
oracle.soundness-corpus|slow|soundness|false|never|python3 scripts/trust-soundness-corpus.py --strict
witness.replay-regression|release|witness|true|2026-09-14|python3 tests/trust-witness/replay_regression.py
witness.auto-router-smoke|release|witness|true|2026-09-14|python3 tests/trust-witness/auto_router_smoke.py
witness.closure-parity-smoke|release|witness|true|never|python3 tests/trust-witness/closure_parity_smoke.py
witness.generics-parity-smoke|release|witness|true|never|python3 tests/trust-witness/generics_parity_smoke.py
witness.precise-parity-smoke|release|witness|true|never|python3 tests/trust-witness/precise_parity_smoke.py
witness.offload-guard-regression|release|witness|true|never|TRUST_WITNESS_TRUSTC=build/host/stage2/bin/trustc python3 -B tests/trust-witness/offload_guard_regression.py
witness.offload-source-rekey-regression|release|witness|true|never|TRUST_WITNESS_TRUSTC=build/host/stage2/bin/trustc python3 -B tests/trust-witness/offload_source_rekey_regression.py
elide.regression|release|elide|true|2026-09-14|python3 tests/trust-elide/elide_regression.py
elide.loop-refutation-regression|release|elide|true|2026-09-29|python3 tests/trust-elide/loop_refutation_regression.py --trustc build/host/stage2/bin/trustc --out "$(mktemp -d)/out"
release.trust-f1-ladder-fixture|release|soundness|true|never|python3 -B scripts/trust_f1_ladder.py --trustc build/host/stage2/bin/trustc --corpus tests/trust-f1-ladder --out-dir "$(mktemp -d)/out" --mode fixture --expect programs:f1-strict=1 --expect micro:f1-strict=4 --expect programs:f1-allow-unknown=4 --expect micro:f1-allow-unknown=21
release.trust-f1-ladder-fixture-checked|release|soundness|true|never|python3 -B scripts/trust_f1_ladder.py --trustc build/host/stage2/bin/trustc --corpus tests/trust-f1-ladder --out-dir "$(mktemp -d)/out" --mode fixture-checked --expect programs:f1-strict=0 --expect micro:f1-strict=1 --expect programs:f1-allow-unknown=0 --expect micro:f1-allow-unknown=4
release.trust-f1-ladder-default|release|soundness|true|never|python3 -B scripts/trust_f1_ladder.py --trustc build/host/stage2/bin/trustc --corpus tests/trust-f1-ladder --out-dir "$(mktemp -d)/out" --mode default --expect programs:f1-strict=0 --expect micro:f1-strict=1 --expect programs:llvm-verified=5 --expect micro:llvm-verified=9
elide.mir-dump-regression|release|elide|true|2026-09-29|python3 tests/trust-elide/mir_dump_regression.py --trustc build/host/stage2/bin/trustc --out "$(mktemp -d)/out"
suite.ui|suites|compiletest|true|never|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/ui
suite.ui-fulldeps|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/ui-fulldeps
suite.crashes|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/crashes
suite.codegen-llvm|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/codegen-llvm
suite.codegen-units|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/codegen-units
suite.assembly-llvm|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/assembly-llvm
suite.assembly-gcc|suites|compiletest|true|never|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/assembly-gcc
suite.incremental|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/incremental
suite.debuginfo|suites|compiletest|true|never|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/debuginfo
suite.mir-opt|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/mir-opt
suite.pretty|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/pretty
suite.run-make|suites|compiletest|true|never|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/run-make
suite.run-make-cargo|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/run-make-cargo
suite.build-std|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/build-std
suite.coverage|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/coverage
suite.coverage-run-rustdoc|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/coverage-run-rustdoc
suite.rustdoc-html|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/rustdoc-html
suite.rustdoc-ui|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/rustdoc-ui
suite.rustdoc-json|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/rustdoc-json
suite.rustdoc-js|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/rustdoc-js
suite.rustdoc-js-std|suites|compiletest|true|2026-09-30|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/rustdoc-js-std
suite.rustdoc-gui|suites|compiletest|false|never|tests/upstream-rust/check_exception_lanes.py --run -- python3 x.py test --stage 2 tests/rustdoc-gui
slow.kernel-derivation|slow|kernel|true|2026-09-28|bash scripts/trust_kernel_derivation_lane.sh
slow.program-index-repair-e2e|slow|e2e|true|never|OUT="$(targo --unverified test --manifest-path Cargo.toml -p trust-backprop --test program_index_real_verifier_repair_e2e --locked -- --ignored --exact real_stage2_program_index_divzero_repair_improves_proof_counts --nocapture 2>&1)"; S=$?; printf '%s\n' "$OUT"; if [ "$S" -ne 0 ]; then (exit "$S"); elif grep -q '^test result: ok\. 1 passed; 0 failed' <<<"$OUT"; then true; else echo "FAIL: libtest exited 0 but did not report 1 passed; a filter that selects nothing, or only an ignored test, exits 0 having run no test" >&2; false; fi
slow.clean-binary-proof-gates|slow|soundness|true|never|PIN="$(git rev-parse HEAD:first-party/clean)" && AT="$(git -C first-party/clean rev-parse HEAD)" && DIRTY="$(git -C first-party/clean status --porcelain)" && if [ "$AT" = "$PIN" ] && [ -z "$DIRTY" ]; then true; else echo "FAIL: first-party/clean must be checked out at its pin $PIN with no change, untracked files included (HEAD $AT; changes: ${DIRTY:-none}); this row measures a clean built from the pin (git submodule update --init first-party/clean)" >&2; exit 1; fi && J="$(mktemp)" && { targo --unverified build --manifest-path first-party/clean/Cargo.toml -p clean --bin clean --release --locked --message-format json-render-diagnostics >"$J"; B=$?; TRUST_CLEAN_BIN="$(python3 -c 'import json,sys; ms=[json.loads(l) for l in open(sys.argv[1]) if l.startswith("{")]; ex=[m["executable"] for m in ms if m.get("reason")=="compiler-artifact" and m.get("target",{}).get("name")=="clean" and "bin" in m.get("target",{}).get("kind",[]) and m.get("executable")]; print(ex[-1] if ex else "")' "$J")"; rm -f "$J"; (exit "$B"); } && if [ -x "$TRUST_CLEAN_BIN" ]; then true; else echo "FAIL: cargo reported no executable for first-party/clean's clean bin" >&2; exit 1; fi && export TRUST_CLEAN_BIN && echo "TRUST_CLEAN_BIN=$TRUST_CLEAN_BIN (built from first-party/clean at $PIN)" && for T in ay_blast_correspondence_gate structured_multiplier_proof_gate i128_corner_bounds_proof_gate codegen_equivalence_gate trust_soundness_ouroboros_gate; do OUT="$(targo --unverified test --manifest-path Cargo.toml -p trust-integration-tests --test "$T" --locked -- --ignored --exact "$T" --nocapture 2>&1)"; S=$?; printf '%s\n' "$OUT"; if [ "$S" -ne 0 ]; then exit "$S"; fi; if grep -q '^test result: ok\. 1 passed; 0 failed' <<<"$OUT"; then true; else echo "FAIL: $T did not report 1 passed; 0 failed; libtest exits 0 on a selection that runs no test" >&2; exit 1; fi; done
canary.is-whnf-mint-gate|slow,release|soundness|true|2026-08-24|bash scripts/trust_control_canary.sh
fast.pin-regression|fast|supply-chain|true|2026-09-30|bash scripts/check_pin_regression.sh --push-context
fast.pin-regression-selftest|fast|supply-chain|true|2026-09-30|bash scripts/check_pin_regression.sh --selftest
fast.seal-driver-guard-mutation|fast,release|harness|true|2026-09-30|bash scripts/seal_driver.sh guardtest
fast.self-verify-crate-selftest|fast|soundness|true|2026-09-30|bash scripts/trust_self_verify_crate.sh --selftest
fast.submodule-worktree-pins|fast|drift|true|2026-09-30|bash scripts/submodule_sync.sh
fast.trust-conformance|fast,release|non-evidence-regression-diagnostic|true|2026-09-30|python3 scripts/run_trust_conformance.py
fast.trust-conformance-selftest|fast,release|infrastructure|true|never|python3 scripts/run_trust_conformance.py --selftest
fast.trust-ir-flip-burnin-selftest|fast,release|soundness|true|2026-09-30|python3 scripts/trust_ir_flip_burnin.py --selftest
fast.trust-ir-frontier-table-selftest|fast,release|drift|true|2026-09-30|python3 scripts/trust_ir_frontier_table.py --selftest
slow.bridge-replay|slow,release|soundness|true|never|bash scripts/trust_bridge_replay_lane.sh
slow.trust-cg-cer-gate|slow,release|soundness|true|never|targo --unverified test --manifest-path Cargo.toml -p trust-cg-bridge --features kernel-recheck,test-hooks --test call_event_gate --test compiled_object_reader --test variadic_split_attacks --test abi_guarantee --test f1_compile --test pointer_slots --locked
slow.feature-gated-tests-trust-cg-bridge|slow,release|soundness|true|never|python3 scripts/feature_gated_tests.py --crate trust-cg-bridge
slow.feature-gated-tests-trust-router|slow,release|soundness|true|never|python3 scripts/feature_gated_tests.py --crate trust-router
slow.feature-gated-tests-trust-vcgen|slow,release|soundness|true|never|python3 scripts/feature_gated_tests.py --crate trust-vcgen
slow.feature-gated-tests-trust-spec-temporal|slow,release|soundness|true|never|python3 scripts/feature_gated_tests.py --crate trust-spec-temporal
slow.feature-gated-tests-trust-certify|slow,release|soundness|true|never|python3 scripts/feature_gated_tests.py --crate trust-certify
slow.feature-gated-tests-trust-verifier-api|slow,release|soundness|true|never|python3 scripts/feature_gated_tests.py --crate trust-verifier-api
slow.feature-gated-tests-trust-bmc|slow,release|soundness|true|never|python3 scripts/feature_gated_tests.py --crate trust-bmc
slow.feature-gated-tests-trust-build-tree|slow,release|soundness|true|never|python3 scripts/feature_gated_tests.py --crate trust-build-tree
fast.feature-gated-tests-selftest|fast,release|soundness|true|never|python3 scripts/feature_gated_tests.py --selftest
slow.corpus-census-faithfulness|slow,release|drift|true|never|bash scripts/corpus_census.sh crates/target/debug/corpus-census-2026-07-24 crates/trust-clean/fixtures build/census 1800
slow.mf-r5-full-union|slow,release|drift|true|never|R=reports/build/mf-r5-$(date -u +%Y%m%dT%H%M%SZ); python3 scripts/mf_r5_full_union.py --output $R --receipt $R.json
slow.mir-transform-ratchet|slow,release|drift|true|2026-09-27|bash scripts/check_trust_verify_suite_ratchet.sh
slow.compiler-unit-tests|slow|compile|true|never|bash scripts/check_compiler_unit_tests.sh
slow.self-verify-crate-ratchet|slow,release|soundness|true|never|bash scripts/trust_self_verify_crate.sh
slow.showcase-demo|slow|demo|true|never|bash scripts/showcase-demo.sh --quick
slow.submodule-coherence|slow,release|supply-chain|true|never|bash scripts/submodule-coherence-gate.sh
slow.win-cross-check|slow,release|compatibility|true|never|bash scripts/win_cross_check.sh
release.assumption-ledger-stage1|release|soundness|true|never|bash scripts/gate_assumption_ledger_stage1.sh
release.certified-monitor-e2e|release|harness|true|2026-09-30|build/host/stage2/bin/targo-trust trust release validate certified-monitors --stage2-sysroot build/host/stage2
release.certified-scoreboard|release|soundness|true|2026-09-30|python3 scripts/trust_certified_scoreboard.py --baseline tests/self-proof/certified-scoreboard.baseline
release.cite-discharge|release|soundness|true|never|python3 scripts/trust_cite_discharge.py --structural target/trust/survey/ny-cert-structural.json --contracts target/trust/survey/ny-cert-contracts.json --cite-map first-party/ny/crates/ny-cert/proofs/cite-map.json --corpus first-party/clean
release.crates-io-native-compat|release|compatibility|true|never|bash scripts/compat_check.sh
release.ddc-double-compilation|release|soundness|false|never|bash scripts/ddc_compare.sh seed upstream --dry-run
release.fresh-clone-seed-consume|release|bootstrap|true|never|bash scripts/ci_fresh_clone_consume_test.sh --stage 2
release.lambda-calculus-downstream-diagnostic|release|diagnostic|false|never|scripts/collect_lambda_calculus_diagnostic.py --repo-root . --output build/evidence/lambda-calculus-diagnostic.json
release.mint-and-prove-seed|release|bootstrap|true|never|S=build/seed-$(date -u +%Y%m%dT%H%M%SZ); bash scripts/mint_and_prove_seed.sh --seed-dir $S --proof-build-dir $S-proof
release.native-solver-sample-verification|release|soundness|true|never|python3 scripts/run_native_solver_sample_verification.py
release.off-stock-rust-preflight|release|supply-chain|true|never|bash scripts/prove_rust_free_build.sh
release.realcode-coverage-receipt|release|evidence|true|never|python3 scripts/collect_realcode_coverage_evidence.py --repo-root . --output build/evidence/realcode-coverage-receipt.json
release.repro-backend-dylib-selfcompare|slow,release|reproducibility|true|never|bash scripts/repro_build_selfcompare.sh
release.repro-wholestage2-selfcompare|slow,release|reproducibility|false|never|bash scripts/repro_wholestage2_selfcompare.sh
release.rustc-mir-differential-oracle|release|soundness|true|2026-09-29|TRUSTC=build/host/stage2/bin/trustc bash scripts/differential/rustc_mir_differential_oracle.sh
release.self-proof-all-trust|release|soundness|true|never|PATH=build/host/stage2/bin:$PATH bash scripts/prove_self_all_trust.sh
release.self-verify-oracle|release|soundness|true|2026-09-29|TRUSTC=build/host/stage2/bin/trustc bash scripts/trust_self_verify.sh
release.stage0-payload-fetchability|release|supply-chain|true|2026-08-26|python3 scripts/fetch_trust_stage0_payloads.py --json
release.stage0-seed-discovery|release|bootstrap|false|never|scripts/discover_trust_stage0_seed.py --json
release.stage2-noverify-mir-transform|release|compile|true|never|bash scripts/stage2_noverify_rustc_mir_transform_test.sh
release.stage2-noverify-self-build|release|bootstrap|true|never|bash scripts/stage2_noverify_self_build.sh
release.stage2-verify-self-build|release|soundness|true|never|build/host/stage2/bin/targo trust repo stage2-verify-self-build
release.strict-superiority-artifacts|release|evidence|true|never|bash scripts/collect_strict_superiority_artifacts.sh
release.tests-after-build|release|harness|true|never|bash scripts/run_tests_after_build.sh
release.trust-frontend-proof|fast,release|harness|true|2026-09-30|sh scripts/prove-trust-frontend-gate.sh
release.trust-ir-flip-burnin|release|soundness|true|never|python3 scripts/trust_ir_flip_burnin.py --trustc build/host/stage2/bin/trustc --out-dir target/trust/flip-burnin
release.trust-ir-lineage-reconcile|release|soundness|true|never|python3 scripts/trust_ir_lineage_reconcile.py --dump target/trust/ir-dump --flip-log target/trust/ir-dump/flip.log
release.trustir-olean-vendor-identity|release|supply-chain|true|2026-09-28|bash scripts/regen-trustir-oleans.sh --check
release.unsafe-coverage-completeness|release|soundness|true|never|bash scripts/check-unsafe-coverage.sh
release.upstream-rust-adopted-evidence|release|upstream|true|never|scripts/run_upstream_rust_adopted_evidence.py --strict-exit
suites.ledger-max-same-day|fast,release|ledger|true|2026-09-30|python3 tests/ledger/test_max_same_day.py
suites.trust-contract-probes|release|soundness|true|2026-08-27|bash tests/trust-contract/contract_clause_sort_match.sh && bash tests/trust-contract/contract_field_projection.sh && bash tests/trust-contract/contract_inline_repro.sh
suites.provability-ratchet|release|soundness|true|2026-08-27|python3 tests/trust-provability/ratchet.py --check
suites.e6-fragment-probe|release|harness|true|never|python3 tests/e6-fragment-probe/run.py
suites.two-language-battery|release|harness|true|2026-09-14|python3 tests/two-language-battery/test_run.py
fast.ir-cohort|fast,release|supply-chain|true|2026-09-30|python3 scripts/check_ir_cohort.py
release.spec-surface-parity|release|soundness|true|2026-08-27|python3 scripts/check_spec_surface_parity.py --toolchain-bin build/host/stage2/bin
fast.raw-enum-tag-fixtures|fast,release|soundness|true|2026-09-30|python3 scripts/regen_raw_enum_tag_fixtures.py --check
fast.trust-ir-corpus-lock|fast,release|supply-chain|true|2026-09-30|python3 scripts/trust_ir_corpus_lock.py --check
release.ratio-strict|release|soundness|true|2026-09-16|bash scripts/trust_ratio_strict_gate.sh
release.hex-strict|release|soundness|true|2026-09-16|bash scripts/trust_hex_strict_gate.sh
release.utf-strict|release|soundness|true|2026-09-16|bash scripts/trust_utf_strict_gate.sh
release.endian-strict|release|soundness|true|never|bash scripts/trust_endian_strict_gate.sh
release.varint-strict|release|soundness|true|never|bash scripts/trust_varint_strict_gate.sh
release.index-strict|release|soundness|true|2026-09-16|bash scripts/trust_index_strict_gate.sh
release.checksum-strict|release|soundness|true|never|bash scripts/trust_checksum_strict_gate.sh
release.radix64-strict|release|soundness|true|never|bash scripts/trust_radix64_strict_gate.sh
release.align-strict|release|soundness|true|2026-09-16|bash scripts/trust_align_strict_gate.sh
release.fixed-strict|release|soundness|true|never|bash scripts/trust_fixed_strict_gate.sh
release.interval-strict|release|soundness|true|2026-09-16|bash scripts/trust_interval_strict_gate.sh
release.timearith-strict|release|soundness|true|2026-09-16|bash scripts/trust_timearith_strict_gate.sh
release.bits-strict|release|soundness|true|never|bash scripts/trust_bits_strict_gate.sh
release.modular-strict|release|soundness|true|never|bash scripts/trust_modular_strict_gate.sh
release.intbound-strict|release|soundness|true|never|TARGO="$(pwd -P)/build/host/stage2/bin/targo" bash scripts/trust_intbound_strict_gate.sh
release.widthconv-strict|release|soundness|true|never|TARGO="$(pwd -P)/build/host/stage2/bin/targo" bash scripts/trust_widthconv_strict_gate.sh
release.budget-strict|release|soundness|true|never|TARGO="$(pwd -P)/build/host/stage2/bin/targo" bash scripts/trust_budget_strict_gate.sh
release.bitfield-strict|release|soundness|true|never|bash scripts/trust_bitfield_strict_gate.sh
release.floatbits-strict|release|soundness|true|never|TARGO="$(pwd -P)/build/host/stage2/bin/targo" bash scripts/trust_floatbits_strict_gate.sh
fast.floatbits-twin-parity|fast,release|soundness|true|2026-09-30|python3 scripts/trust_floatbits_twin_parity.py crates/trust-floatbits/src/lib.rs crates/trust-floatbits/src/contracts.rs
release.strict-pass-frontier|release|soundness|true|never|bash scripts/trust_strict_pass_frontier.sh
fast.kernel-authority-vacuity|fast,release|soundness|true|2026-09-30|python3 scripts/check_kernel_authority_vacuity.py
release.check-all|release|harness|true|never|bash scripts/check_all.sh
acceptance.b4-slot-distinguishability|release|acceptance|false|never|bash scripts/b4_slot_acceptance.sh build/host/stage2/bin/rustc
supply-chain.first-party-pin-reachability|release|supply-chain|true|never|python3 scripts/audit_first_party_pins.py --fetch --probe
supply-chain.fleet-pin-drift-sweep|release|supply-chain|true|2026-08-31|python3 scripts/sweep_pin_drift.py
EOF
}

list_gates() {
    local gate_id profiles category required last_green command
    emit_gate_manifest \
        | while IFS='|' read -r gate_id profiles category required last_green command; do
        [ -n "$gate_id" ] || continue
        if gate_selected "$profiles"; then
            printf '%s\t%s\t%s\t%s\t%s\n' \
                "$gate_id" "$category" "$required" "$last_green" "$command"
        fi
    done
}

if [ "${1:-}" = "--list" ] || [ "${1:-}" = "list" ]; then
    list_gates
    exit 0
fi

# THE REPORT WRITER IS PYTHON >= 3.10, AND A BARE `python3` CAN BE OLDER (3.9.6 ON
# THE MACHINE WHERE THIS WAS MEASURED, 2026-09-10).
#
# The inline writer below uses PEP 604 unions (`str | None`) and `tomllib`
# (3.11, or the `tomli` backport). Handed to a 3.9 `python3` it dies with
# `TypeError: unsupported operand type(s) for |: 'type' and 'NoneType'` AFTER
# every lane has already run: results.tsv is complete, report.json/report.md are
# never written, and an all-green run exits 1. Select the interpreter the way
# scripts/check_script_tests.sh and scripts/hooks/pre-push do (newest first,
# then the bare `python3`), but PROVE the candidate can run the writer before a
# single lane starts -- an hour of lanes followed by a report that cannot be
# written is exactly the failure this guards against. No candidate qualifies:
# fail closed here, not at the end. This selection is not exported, so each
# gate script owns its own interpreter floor: a row runs a script that needs
# 3.11 (stdlib tomllib, no tomli fallback) DIRECTLY, never as `python3 <script>`
# — the script's shebang/polyglot header picks a >=3.11 interpreter, and
# scripts/tests/python_floor_test.py refuses a row that routes one through a
# bare `python3` (HOST-01B). Rows for scripts with no floor still say `python3`.
report_python_ok() {
    "$1" - <<'PY' >/dev/null 2>&1
import sys
if sys.version_info < (3, 10):
    raise SystemExit(1)
try:
    import tomllib
except ModuleNotFoundError:
    import tomli  # noqa: F401
PY
}

REPORT_PYTHON=""
for candidate in python3.14 python3.13 python3.12 python3.11 python3 python; do
    if command -v "$candidate" >/dev/null 2>&1 && report_python_ok "$candidate"; then
        REPORT_PYTHON="$candidate"
        break
    fi
done
if [ -z "$REPORT_PYTHON" ]; then
    echo "FAIL: no python >= 3.10 with tomllib (or tomli) on PATH; tried python3.14 python3.13 python3.12 python3.11 python3 python." >&2
    echo "      The report writer needs it, so no lane was run: results without report.json/report.md are not a harness run." >&2
    exit 2
fi
echo "report python: $REPORT_PYTHON ($("$REPORT_PYTHON" --version 2>&1))"

# EVERY CARGO-DRIVEN LANE BELOW SAYS `targo --unverified`, NOT `cargo`. Two
# reasons, both measured 2026-09-12:
#
#  * Under the `trust` toolchain a bare `cargo` verifies EVERY compilation unit,
#    because stock cargo has no per-unit verification policy and compiles each
#    dependency as its own primary crate. `cargo test -p trust-integration-tests`
#    died with `could not compile unicode-ident` on proof obligations that have
#    nothing to do with the lane under test. Targo's per-unit engine scopes
#    dependencies off, and `--unverified` lowers onto the single compiler
#    off-switch for the whole build. These lanes type-check and run tests; they
#    carry no proof claim and must not pretend to, which is exactly what the
#    banner `--unverified` prints says out loud.
#  * `targo --unverified` is SELF-DISCRIMINATING, and that is why the flag is in
#    the row rather than hidden in a variable. A stage whose `targo` was never
#    rebuilt ships upstream cargo under the name `targo`; CLAUDE.md's Build
#    section records four discriminators (inode, two version-string tests, the
#    `trust` subcommand) that were each measured WRONG. `--unverified` is the one
#    that has held: only a real targo accepts it, so a disguised cargo fails the
#    lane loudly instead of silently running it with no scoping at all.
#
# `RUSTC_BOOTSTRAP=1` went with them: the toolchain targo pins is
# `channel = "trust"`, which opens the `#![feature(...)]` gates natively instead
# of faking them on stock rustc.
#
# Proven before a single lane starts, and ONLY when a selected lane needs it — a
# release-profile run names no targo lane and must not be blocked by a tool it
# never invokes. Lane rows stay literal (`targo`, never `$TARGO`) on the same
# convention as the report interpreter above: a row a human cannot paste into a
# shell is a row nobody ever re-runs by hand.
targo_ok() {
    command -v targo >/dev/null 2>&1 && targo --unverified --version >/dev/null 2>&1
}

selected_lanes_need_targo() {
    local gate_id profiles category required last_green command
    while IFS='|' read -r gate_id profiles category required last_green command; do
        [ -n "$gate_id" ] || continue
        gate_selected "$profiles" || continue
        case "$command" in *"targo --unverified "*) return 0 ;; esac
    done < <(emit_gate_manifest)
    return 1
}

if selected_lanes_need_targo && ! targo_ok; then
    resolved="$(command -v targo 2>/dev/null || echo '<not on PATH>')"
    echo "FAIL: profile $MODE selects lanes that run \`targo --unverified\`, but no real targo answered." >&2
    echo "      command -v targo -> $resolved" >&2
    if [ "$resolved" != "<not on PATH>" ]; then
        echo "      It is on PATH but rejected \`--unverified\`, which means it is upstream cargo" >&2
        echo "      shipped under the name targo — running these lanes through it would verify" >&2
        echo "      every third-party dependency and fail on unrelated obligations." >&2
    fi
    echo "      No lane was run. Any of these fixes it:" >&2
    echo "        * atpkg already manages one: \`atpkg list\`, then \`atpkg update\` (its shell.d" >&2
    echo "          hook puts the managed bin/ on PATH; a non-login shell may not have sourced it)." >&2
    echo "        * build one: \`scripts/install-trust-toolchain.sh\` (~15-36 min cold)." >&2
    echo "        * use a stage you already built: put build/host/stage1/bin first on PATH, then" >&2
    echo "          re-check with \`targo --unverified --version\`." >&2
    exit 2
fi

mkdir -p "$LOG_DIR"
printf 'gate_id\tcategory\trequired\tlast_green\tstarted_at\tended_at\tduration_seconds\texit_code\tcommand\tlog_path\tskipped\n' >"$RESULTS_TSV"
: >"$LAST_GREEN_TSV"

# A PASSING LANE COULD SAY NOTHING AT ALL, AND THAT IS HOW A DATED FLEET STOP
# ARRIVES UNANNOUNCED.
#
# run_gate writes every lane's stdout and stderr to a log and, on PASS, printed
# one word: PASS. Nobody opens the log of a lane that passed. So a lane that
# KNOWS something is coming -- the retired `fast.two-language-claim-ledger` lane
# knew the exact instant a claim lease lapsed -- had no channel to say so. (That lane
# and its selftest row were removed on 2026-09-30: the ledger ref it read was deleted
# from origin on 2026-09-26/27.)
#
# This is that channel, and it is deliberately one line of contract: a lane
# announces by printing a line beginning `WARN:`, and this surfaces those lines
# on the harness's own stdout even when the lane passed. It is not a status: the
# lane still PASSES, the exit code is untouched, and nothing here can fail a run.
# Controlled end-to-end against the real run_gate by
# scripts/tests/gate_warning_surface_test.sh, in both directions -- a WARN line
# is surfaced, and a lane that emits none produces no output here.
surface_gate_warnings() {
    local gate_id="$1" log_path="$2" verb="${3:-passed}" line found=0
    [ -f "$log_path" ] || return 0
    while IFS= read -r line; do
        found=1
        echo "$line"
    done < <(grep -E '^[[:space:]]*WARN: ' "$log_path" || true)
    [ "$found" -eq 1 ] && echo "warnings: $gate_id $verb and reported the above"
    return 0
}

# A LANE THAT RAN NOTHING IS NOT A LANE THAT PASSED.
#
# The scoped lanes exit 0 in ~0s when the diff they are scoped to is empty or
# touches nothing they cover -- deliberately: a nonzero skip would redden every
# docs-only push and teach `--no-verify`. run_gate graded that exit 0 PASS and
# printed the LAST-GREEN line, so a lane that checked NOTHING could ratchet its
# own `last_green` forward (measured 2026-09-27 at a clean origin/main:
# scoped.compiler-check, scoped.completion-gate-tests and scoped.crates-tests
# all PASS in 0s, each with a LAST-GREEN offer).
#
# A lane says it skipped the way it says WARN: one line beginning `SKIPPED: `.
# A zero exit with that line is graded SKIP -- no LAST-GREEN line, `skipped`
# = true in results.tsv, `skipped` (never `passed`) in the report. The exit code
# is untouched, so a skip still blocks nothing. A non-zero exit is FAIL whatever
# the log says. Controlled end-to-end against the real run_gate by
# scripts/tests/gate_warning_surface_test.sh, in both directions -- a lane
# printing the token is SKIP with no LAST-GREEN line, and one that does not is
# PASS with it.
gate_skipped() {
    local log_path="$1"
    [ -f "$log_path" ] || return 1
    grep -qE '^[[:space:]]*SKIPPED: ' "$log_path"
}

run_gate() {
    local gate_id="$1"
    local category="$2"
    local required="$3"
    local last_green="$4"
    local command="$5"
    local log_name log_path started_at ended_at started_epoch ended_epoch duration status
    local skipped=false skip_reason

    log_name="$(safe_log_name "$gate_id").log"
    log_path="$LOG_DIR/$log_name"
    started_at="$(timestamp_utc)"
    started_epoch="$(epoch_seconds)"

    echo
    echo "=== gate: $gate_id ==="
    echo "category: $category"
    echo "last green: $last_green"
    echo "command:  $command"
    echo "log:      $log_path"

    set +e
    (
        cd "$TRUST_ROOT" || exit 2
        bash -o pipefail -c "$command"
    ) >"$log_path" 2>&1
    status=$?
    set -u

    ended_at="$(timestamp_utc)"
    ended_epoch="$(epoch_seconds)"
    duration=$((ended_epoch - started_epoch))
    if [ "$status" -eq 0 ] && gate_skipped "$log_path"; then
        skipped=true
    fi

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$gate_id" "$category" "$required" "$last_green" "$started_at" "$ended_at" \
        "$duration" "$status" "$command" "$log_path" "$skipped" >>"$RESULTS_TSV"

    if [ "$skipped" = "true" ]; then
        # No LAST-GREEN line: a run that checked nothing is no evidence of green.
        skip_reason="$(grep -m1 -E '^[[:space:]]*SKIPPED: ' "$log_path" | sed -E 's/^[[:space:]]*SKIPPED: //')"
        echo "status:   SKIP (${duration}s)"
        echo "skipped:  $skip_reason"
        echo "          ran nothing, so last_green stays $last_green (a SKIP is not a PASS)"
        surface_gate_warnings "$gate_id" "$log_path" skipped
    elif [ "$status" -eq 0 ]; then
        echo "status:   PASS (${duration}s)"
        surface_gate_warnings "$gate_id" "$log_path"
        if last_green_advances "$last_green"; then
            echo "LAST-GREEN: update the manifest row for $gate_id to ${RUN_STARTED_AT%%T*}"
            printf '%s\t%s\t%s\n' "$gate_id" "${RUN_STARTED_AT%%T*}" "$command" >>"$LAST_GREEN_TSV"
        fi
    else
        echo "status:   FAIL exit=$status (${duration}s)"
        echo "--- tail: $log_path"
        tail -n 80 "$log_path" || true
        echo "--- end tail"
    fi

    return "$status"
}

# The one supersession rule: `never`, or a date before the run's UTC start
# date. A later date (a row edited mid-run) is never moved backward.
last_green_advances() {
    case "$1" in
        never) return 0 ;;
        [0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]) [[ "$1" < "${RUN_STARTED_AT%%T*}" ]] ;;
        *) return 1 ;;
    esac
}

# --record-last-green: apply this run's LAST-GREEN offers to MANIFEST_FILE. The
# writer re-checks each row as it is on disk (forward only, same command) and
# replaces the file by rename: bash is still reading this script through an
# open descriptor, and an in-place rewrite would shift what it reads next.
record_last_green() {
    "$REPORT_PYTHON" - "$MANIFEST_FILE" "$LAST_GREEN_TSV" <<'PY'
import os
import re
import stat
import sys
import tempfile
from pathlib import Path

manifest = Path(sys.argv[1]).resolve()
offers = {}
for line in Path(sys.argv[2]).read_text(encoding="utf-8").splitlines():
    gate_id, day, command = line.split("\t", 2)
    offers[gate_id] = (day, command)

DATE = re.compile(r"\d{4}-\d{2}-\d{2}")
lines = manifest.read_text(encoding="utf-8").splitlines(keepends=True)
try:
    start = lines.index("emit_gate_manifest() {\n")
    body = next(i for i in range(start, len(lines)) if lines[i].rstrip("\n").endswith("<<'EOF'")) + 1
    end = lines.index("EOF\n", body)
except (ValueError, StopIteration):
    sys.exit(f"record-last-green: no emit_gate_manifest heredoc in {manifest}")

recorded, seen = [], set()
for i in range(body, end):
    fields = lines[i].rstrip("\n").split("|", 5)
    if len(fields) != 6 or fields[0] not in offers:
        continue
    gate_id, old = fields[0], fields[4]
    day, command = offers[gate_id]
    seen.add(gate_id)
    if fields[5] != command:
        print(f"last-green: {gate_id} NOT recorded: its command changed during the run")
    elif DATE.fullmatch(day) and (old == "never" or (DATE.fullmatch(old) and old < day)):
        fields[4] = day
        lines[i] = "|".join(fields) + "\n"
        recorded.append(f"{gate_id}: {old} -> {day}")
for gate_id in sorted(set(offers) - seen):
    print(f"last-green: {gate_id} NOT recorded: no manifest row has that id")

if recorded:
    fd, tmp = tempfile.mkstemp(dir=manifest.parent, prefix=f".{manifest.name}.")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            fh.writelines(lines)
        os.chmod(tmp, stat.S_IMODE(manifest.stat().st_mode))
        os.replace(tmp, manifest)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)
print(f"last-green: recorded {len(recorded)} row(s) in {manifest}")
for entry in recorded:
    print(f"  {entry}")
PY
}

selected_count=0
failed_count=0

while IFS='|' read -r gate_id profiles category required last_green command; do
    [ -n "$gate_id" ] || continue
    if ! gate_selected "$profiles"; then
        continue
    fi
    selected_count=$((selected_count + 1))
    run_gate "$gate_id" "$category" "$required" "$last_green" "$command"
    status=$?
    if [ "$status" -ne 0 ]; then
        failed_count=$((failed_count + 1))
        if [ "$FAIL_FAST" = "1" ] && [ "$required" = "true" ]; then
            break
        fi
    fi
done < <(emit_gate_manifest)

if [ "$selected_count" -eq 0 ]; then
    echo "FAIL: no gates selected for profile $MODE" >&2
    exit 2
fi

RUN_ENDED_AT="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"

set +e
"$REPORT_PYTHON" - "$TRUST_ROOT" "$MODE" "$RUN_ID" "$RUN_STARTED_AT" "$RUN_ENDED_AT" \
    "$RESULTS_TSV" "$DIVERGENCE_LEDGER" "$REPORT_JSON" "$REPORT_MD" <<'PY'
import csv
import json
import os
import platform
import subprocess
import sys
from datetime import date
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover
    import tomli as tomllib

root = Path(sys.argv[1])
profile = sys.argv[2]
run_id = sys.argv[3]
started_at = sys.argv[4]
ended_at = sys.argv[5]
results_path = Path(sys.argv[6])
ledger_path = Path(sys.argv[7])
report_json = Path(sys.argv[8])
report_md = Path(sys.argv[9])


def run_git(*args: str) -> str | None:
    try:
        proc = subprocess.run(
            ["git", "-C", str(root), *args],
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError:
        return None
    if proc.returncode != 0:
        return None
    return proc.stdout.strip()


def rel(path: str) -> str:
    p = Path(path)
    try:
        return str(p.relative_to(root))
    except ValueError:
        return str(p)


def load_ledger(path: Path) -> tuple[list[dict], list[str]]:
    if not path.exists():
        return [], [f"missing comprehensive divergence ledger: {rel(str(path))}"]
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        return [], [f"invalid comprehensive divergence ledger: {exc}"]
    errors: list[str] = []
    if data.get("schema_version") != "0.1.0":
        errors.append("comprehensive divergence ledger schema_version must be 0.1.0")
    divergences = data.get("divergences", [])
    if not isinstance(divergences, list):
        errors.append("comprehensive divergence ledger divergences must be a list")
        divergences = []
    return [d for d in divergences if isinstance(d, dict)], errors


def as_date(value):
    if isinstance(value, date):
        return value
    if isinstance(value, str):
        return date.fromisoformat(value)
    raise ValueError(f"not a date: {value!r}")


divergences, ledger_errors = load_ledger(ledger_path)
today = date.today()
UNQUARANTINABLE_GATE_IDS = {"fast.dependency-constellation"}

rows: list[dict] = []
non_evidence_categories = {"non-evidence-regression-diagnostic", "infrastructure"}
with results_path.open("r", encoding="utf-8", newline="") as fh:
    reader = csv.DictReader(fh, delimiter="\t")
    for row in reader:
        row["required"] = row["required"].lower() == "true"
        row["duration_seconds"] = int(row["duration_seconds"])
        row["exit_code"] = int(row["exit_code"])
        # run_gate's SKIP grade: exit 0 after a `SKIPPED: ` line, i.e. the lane
        # ran nothing. Never graded `passed` below.
        row["skipped"] = (row.get("skipped") or "false").lower() == "true"
        if row["category"] in non_evidence_categories:
            row["evidence_classification"] = "not_evidence"
            row["proof_evidence"] = False
            row["release_evidence"] = False
        else:
            # This harness does not infer evidence eligibility merely from an
            # unrecognized category. Dedicated consumers must classify it.
            row["evidence_classification"] = "unspecified"
            row["proof_evidence"] = None
            row["release_evidence"] = None
        rows.append(row)


def matching_divergences(row: dict) -> list[dict]:
    if row["exit_code"] == 0:
        return []
    if row["gate_id"] in UNQUARANTINABLE_GATE_IDS:
        # Dependency authority cannot be replaced by a divergence ledger row.
        return []
    matches: list[dict] = []
    for divergence in divergences:
        if divergence.get("status") != "active":
            continue
        if divergence.get("gate_id") != row["gate_id"]:
            continue
        try:
            expires_on = as_date(divergence["expires_on"])
        except Exception:
            continue
        if expires_on < today:
            continue
        allowed_exit_codes = divergence.get("allowed_exit_codes", [])
        if allowed_exit_codes and row["exit_code"] not in allowed_exit_codes:
            continue
        patterns = divergence.get("allowed_patterns", [])
        if patterns:
            try:
                log_text = Path(row["log_path"]).read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            if not any(pattern in log_text for pattern in patterns):
                continue
        matches.append(divergence)
    return matches


for row in rows:
    row["log_path"] = rel(row["log_path"])
    matching = matching_divergences(row)
    if row["exit_code"] == 0 and row["skipped"]:
        # A lane that ran nothing is not evidence of anything, and it must not
        # count toward evidence_eligible_passed or read as a green in report.md.
        row["status"] = "skipped"
    elif row["exit_code"] == 0:
        row["status"] = (
            "diagnostic_passed"
            if row["evidence_classification"] == "not_evidence"
            else "passed"
        )
    elif matching:
        row["status"] = "documented_divergence"
        row["divergence_ids"] = [divergence.get("id") for divergence in matching]
        row["divergence_issues"] = [divergence.get("issue") for divergence in matching]
        row["divergence_expires_on"] = sorted(
            {str(divergence.get("expires_on")) for divergence in matching}
        )
        row["divergence_id"] = ", ".join(row["divergence_ids"])
    else:
        row["status"] = "failed"

counts: dict[str, int] = {}
for row in rows:
    counts[row["status"]] = counts.get(row["status"], 0) + 1

required_failed = [row for row in rows if row["required"] and row["status"] == "failed"]
required_divergent = [
    row for row in rows if row["required"] and row["status"] == "documented_divergence"
]

if ledger_errors:
    verdict = "failed_harness_ledger"
elif required_failed:
    verdict = "failed_undocumented"
elif required_divergent:
    verdict = "blocked_documented_divergence"
else:
    verdict = "passed"

report = {
    "schema_version": "trust.comprehensive-test-harness.v1",
    "run_id": run_id,
    "profile": profile,
    "started_at": started_at,
    "ended_at": ended_at,
    "verdict": verdict,
    "host": {
        "platform": platform.platform(),
        "machine": platform.machine(),
        "python": platform.python_version(),
    },
    "git": {
        "commit": run_git("rev-parse", "HEAD"),
        "branch": run_git("branch", "--show-current"),
        "status_porcelain": run_git("status", "--porcelain=v1"),
    },
    "policy": {
        "public_uploads_allowed": False,
        "default_profile_is_release": True,
        "documented_divergence_blocks_replacement_claim": True,
        "non_evidence_categories": sorted(non_evidence_categories),
        "non_evidence_success_can_block_but_never_satisfies_evidence": True,
        "upstream_per_test_ledger": "tests/upstream-rust/test-exceptions.toml",
        "trust_added_compiletest_ledger": "tests/trust-added/compiletest-exceptions.toml",
        "command_divergence_ledger": rel(str(ledger_path)),
        "unquarantinable_gate_ids": sorted(UNQUARANTINABLE_GATE_IDS),
    },
    "summary": {
        "total": len(rows),
        "counts": counts,
        "evidence_eligible_passed": sum(
            1
            for row in rows
            if row["status"] == "passed"
            and row["evidence_classification"] != "not_evidence"
        ),
        "non_evidence_diagnostic_passed": sum(
            1 for row in rows if row["status"] == "diagnostic_passed"
        ),
        "ledger_errors": ledger_errors,
    },
    "gates": rows,
}

report_json.parent.mkdir(parents=True, exist_ok=True)
report_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")

lines = [
    "# Trust Comprehensive Harness Report",
    "",
    f"- Run id: `{run_id}`",
    f"- Profile: `{profile}`",
    f"- Verdict: `{verdict}`",
    f"- Commit: `{report['git']['commit'] or 'unknown'}`",
    f"- Started: `{started_at}`",
    f"- Ended: `{ended_at}`",
    f"- Command divergence ledger: `{rel(str(ledger_path))}`",
    "",
    "Public uploads are forbidden and were not part of this harness contract.",
    "A required non-evidence diagnostic can block this run, but its success is not proof or release evidence.",
    "",
    "## Gate Results",
    "",
    "| Gate | Category | Evidence | Status | Exit | Seconds | Log |",
    "| --- | --- | --- | --- | ---: | ---: | --- |",
]
for row in rows:
    lines.append(
        f"| `{row['gate_id']}` | `{row['category']}` | "
        f"`{row['evidence_classification']}` | `{row['status']}` | {row['exit_code']} | "
        f"{row['duration_seconds']} | `{row['log_path']}` |"
    )

skipped_rows = [row for row in rows if row["status"] == "skipped"]
if skipped_rows:
    lines.extend(
        [
            "",
            "## Skipped Lanes",
            "",
            "These exited 0 after printing `SKIPPED:` -- they ran nothing. A skip is not a pass",
            "and never supersedes a manifest row's `last_green`.",
            "",
        ]
    )
    lines.extend(
        f"- `{row['gate_id']}` (last green `{row['last_green']}`); see `{row['log_path']}`."
        for row in skipped_rows
    )

if ledger_errors:
    lines.extend(["", "## Harness Ledger Errors", ""])
    lines.extend(f"- {error}" for error in ledger_errors)

if required_failed:
    lines.extend(["", "## Undocumented Failures", ""])
    lines.extend(
        f"- `{row['gate_id']}` failed with exit {row['exit_code']}; see `{row['log_path']}`."
        for row in required_failed
    )

if required_divergent:
    lines.extend(["", "## Documented Divergences", ""])
    lines.extend(
        f"- `{row['gate_id']}` is documented by `{row.get('divergence_id')}` "
        f"through `{', '.join(row.get('divergence_expires_on', []))}`."
        for row in required_divergent
    )

report_md.write_text("\n".join(lines) + "\n", encoding="utf-8")

print(f"wrote {rel(str(report_json))}")
print(f"wrote {rel(str(report_md))}")

raise SystemExit(0 if verdict == "passed" else 1)
PY
report_status=$?
set -u

if [ "$RECORD_LAST_GREEN" = "1" ] && ! record_last_green; then
    echo "FAIL: --record-last-green could not update $MANIFEST_FILE" >&2
    [ "$report_status" -ne 0 ] || report_status=2
fi

echo
echo "Comprehensive harness report:"
echo "  JSON: $REPORT_JSON"
echo "  MD:   $REPORT_MD"

exit "$report_status"
