#!/bin/bash
# Comprehensive Trust replacement test harness.
#
# The default profile is the release profile. It is intentionally expensive:
# it builds the standalone Trust toolchain, runs the upstream Rust compatibility
# path, runs Trust-specific proof gates, runs install/dist gates, and writes a
# machine-readable report. Manifest and quick profiles exist only to validate
# the harness itself during development; they are not replacement evidence.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
MODE="${1:-release}"
RUN_STARTED_AT="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
RUN_ID="${TRUST_COMPREHENSIVE_RUN_ID:-$(date -u '+comprehensive-%Y%m%dT%H%M%SZ')}"
OUT_DIR="${TRUST_COMPREHENSIVE_OUT_DIR:-$TRUST_ROOT/reports/trust-comprehensive/$RUN_ID}"
LOG_DIR="$OUT_DIR/logs"
RESULTS_TSV="$OUT_DIR/results.tsv"
REPORT_JSON="$OUT_DIR/report.json"
REPORT_MD="$OUT_DIR/report.md"
DIVERGENCE_LEDGER="$TRUST_ROOT/tests/trust-comprehensive/divergences.toml"
DEFAULT_FAIL_FAST=0
[ "$MODE" = "release" ] && DEFAULT_FAIL_FAST=1
FAIL_FAST="${TRUST_COMPREHENSIVE_FAIL_FAST:-$DEFAULT_FAIL_FAST}"

usage() {
    cat <<'USAGE'
Usage: tests/run_trust_comprehensive_harness.sh [release|quick|fast|suites|slow|manifest|list|--list|--help]

Profiles:
  release   Full replacement evidence path. This is the default.
  quick     Fast local confidence path. Not replacement evidence.
  fast      Everything that needs no stage2 build: drift, supply-chain,
            style/lint ratchets, workspace compile, script tests, and the
            payload-independent js262 lanes.
  push      The pre-push tier. scripts/hooks/pre-push DERIVES its lane list
            from `--list push`; do not hand-list lanes there.
  suites    The compiletest suites, one gate per suite, in Trust mode.
  slow      Overnight lanes: Clean-kernel re-derivation, js262 calibration.
  manifest  Static harness/script/ledger checks only. Not replacement evidence.
  list      Print the selected profile's gate manifest without executing it.

Outputs:
  reports/trust-comprehensive/<run-id>/results.tsv
  reports/trust-comprehensive/<run-id>/report.json
  reports/trust-comprehensive/<run-id>/report.md

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
# variants in 4554s (measured 2026-08-26), too slow for the pre-push `fast` tier.
# It is RED on arrival by design — it finds the live `i += 100` false proof in all
# three lanes, certify included (guards.rs models it `x == x + 100`; UNSAT poisons
# the hypothesis, so the block proves vacuously). Do not skip it to get green.
#
# The block after `slow.js262-calibrate` is the 2026-08-26 catch-all sweep. Every
# lane class in `check_gate_lane_coverage.py` matched on a NAME, so every class had
# a next blind spot: `check_*` missed four adversarial oracles, `trust_*_gate.sh`
# missed two HYPHENATED gates. A catch-all now sweeps whatever the named classes
# do not claim; it surfaced 73 scripts, of which 46 are verdict-bearing and are
# rowed below. Several are RED on arrival and that is the point — `check-unsafe-
# coverage.sh` has all five expect-caught rows failing on a drifted exact-match
# grep while docs/high2-obligation-demo.md claims it "also passes live", and
# `run_trust_conformance.py` is missing a publication.json its own corpus requires.
# Do not silence a red here to get green; the red is the instrument working.
#
# Two rows in that block are green ONLY once something lands with them:
# `release.certified-scoreboard` names a baseline file that does not exist yet
# (without --baseline the scoreboard exits 0 unconditionally, which is a green
# that proves nothing), and `slow.corpus-census-faithfulness` needs the census
# binary built AND its awk summary taught to enforce KERNEL_REJECTED == 0, which
# it prints as "(MUST be 0)" and does not check.
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
# Four push lanes need the refs git is pushing, which a fixed command string
# cannot receive. They take `--push-context`: the hook exports
# TRUST_PUSHED_REFS, and with it UNSET the same command widens to its history
# reading, so the row stays runnable standalone.
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
# `crate::temporal_cli::UNBOUND_TEMPORAL_EVIDENCE` (targo-trust/src/script_cli.rs:2185),
# so re-expressing it as a shell grep would mirror a constant into a file with
# nothing checking the mirror. A second, different exercise of that script lives
# in tests/e2e_check_all_tcargo_provenance.sh, which copies and RUNS the real
# scripts/check_all.sh in a synthetic repo.
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
# Columns: gate_id|profiles|category|required|last_green|command
#
# `last_green` is the ISO date of the most recent observed PASS, or `never`
# when this manifest has never recorded one. It is deliberately not inferred:
# a lane that has run green somewhere untracked still reads `never` here, which
# is the honest statement that the manifest has no evidence. A run prints a
# `LAST-GREEN` line for every gate whose recorded date it just superseded.
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
emit_gate_manifest() {
    cat <<'EOF'
manifest.syntax.comprehensive|all|harness|true|2026-07-25|bash -n tests/run_trust_comprehensive_harness.sh
manifest.syntax.superset|all|harness|true|2026-07-25|bash -n tests/run_trust_superset_suite.sh
manifest.syntax.robust|all|harness|true|2026-07-25|bash -n tests/run_trust_robust_suite.sh
manifest.syntax.targo-cli|all|harness|true|2026-07-25|bash -n tests/e2e_targo_trust_cli.sh
manifest.syntax.targo-root-resolution|all|harness|true|2026-07-25|bash -n tests/e2e_targo_trust_root_resolution.sh
manifest.syntax.run-tests-after-build-failclosed|all|harness|true|2026-07-25|bash -n tests/e2e_run_tests_after_build_fail_closed.sh
manifest.syntax.gate-scripts|all|harness|true|2026-07-25|bash scripts/check_gate_script_syntax.sh
manifest.ledgers|all|harness|true|2026-07-25|test -f tests/upstream-rust/test-exceptions.toml && test -f tests/upstream-rust/patches.toml && test -f tests/upstream-rust/divergence-audit.toml && test -f tests/trust-added/compiletest-exceptions.toml && test -f tests/trust-added/manifest.toml && test -f tests/trust-comprehensive/divergences.toml
manifest.canonical-targo-e2e-names|all|harness|true|2026-07-25|test -x tests/e2e_targo_trust_cli.sh && test -x tests/e2e_targo_trust_root_resolution.sh && test ! -e tests/e2e_cargo_trust_cli.sh && test ! -e tests/e2e_cargo_trust_root_resolution.sh
manifest.lane-coverage|all|harness|true|2026-07-25|python3 scripts/check_gate_lane_coverage.py
fast.two-language-claim-ledger|fast,push,release|soundness|true|2026-09-01|python3 scripts/check_two_language_claim_ledger.py --ledger-ref refs/remotes/origin/goals/TRUST-TWO-LANGUAGE-100 --integration-ref refs/remotes/origin/main --push-context --require-mirrors --mirror-ref-prefix refs/remotes/origin/claims
fast.two-language-claim-ledger-selftest|fast,push,release|soundness|true|2026-09-01|python3 scripts/tests/two_language_claim_ledger_test.py
fast.ledger-expirations|fast,push|ledger|true|2026-08-27|python3 scripts/check_ledger_expirations.py --warn-days 14
fast.toolchain-coherence|fast,push|drift|true|2026-08-27|python3 scripts/check_toolchain_coherence.py
fast.seed-freshness|fast,push|bootstrap|true|2026-08-27|python3 scripts/check_seed_freshness.py
fast.trust-ir-tag-families|fast,push,release|drift|true|2026-08-27|python3 scripts/trust_ir_tag_families.py --check
fast.trust-ir-tag-families-selftest|fast,push,release|drift|true|2026-08-27|python3 scripts/trust_ir_tag_families.py --selftest
fast.trust-ir-seam-blockers|fast,push,release|drift|true|2026-08-27|python3 scripts/trust_ir_producer_scorecard.py --check-seam-blockers
fast.trust-ir-seam-blockers-selftest|fast,push,release|drift|true|2026-08-27|python3 scripts/trust_ir_producer_scorecard.py --selftest-seam-blockers
fast.mir-transform-ratchet-selftest|fast,push,release|drift|true|2026-08-27|bash scripts/check_trust_verify_suite_ratchet.sh --selftest
fast.call-summary-labels|fast,push|drift|true|2026-08-29|python3 scripts/check_call_summary_labels.py
fast.call-summary-labels-selftest|fast,push|drift|true|2026-08-29|python3 scripts/check_call_summary_labels.py --selftest
fast.cfg-test-caller-skew|fast,push|compile|true|2026-09-01|python3 scripts/check_cfg_test_caller_skew.py --push-context
fast.cfg-test-caller-skew-selftest|fast,push|compile|true|2026-09-01|python3 scripts/check_cfg_test_caller_skew.py --selftest
fast.pin-coherence|fast,push|supply-chain|true|2026-08-27|bash scripts/check_pin_coherence.sh
fast.dependency-constellation|fast,push,release|supply-chain|true|never|scripts/check_dependency_cycle_anchor.py --push-context --derive-when-receipt-absent
fast.dependency-constellation-selftest|fast,push,release|supply-chain|true|2026-08-29|scripts/check_dependency_cycle_anchor.py --selftest
fast.oracle-freeze|fast,push|soundness|true|2026-08-27|bash scripts/check_frozen_files.sh
fast.oracle-freeze-selftest|fast,push|soundness|true|2026-08-27|bash scripts/check_frozen_files.sh --selftest
fast.revert-rationale|fast,push|soundness|true|never|bash scripts/check_revert_rationale.sh --push-context
fast.measurement-provenance|fast,push|soundness|true|2026-08-20|bash scripts/check_measurement_provenance.sh --push-context
fast.measurement-provenance-selftest|fast,push|soundness|true|2026-08-27|bash scripts/check_measurement_provenance.sh --selftest
fast.bridge-pin|fast,push|supply-chain|true|2026-08-27|bash scripts/check_bridge_pin.sh --check
fast.patch-binds|fast,push|supply-chain|true|2026-08-27|python3 scripts/check_patch_binds.py
fast.cargo-lock-hygiene|fast|supply-chain|true|never|python3 scripts/check_cargo_lock_hygiene.py
fast.cargo-manifest-alignment|fast|supply-chain|true|never|python3 scripts/check_cargo_manifest_alignment.py
fast.submodule-remote-reachability|fast,push|supply-chain|true|2026-08-28|python3 scripts/check_submodule_remote_reachability.py --push-context
fast.submodule-remote-reachability-selftest|fast,push|supply-chain|true|2026-08-30|python3 scripts/check_submodule_remote_reachability.py --self-check
fast.doc-counts|fast|docs|true|never|bash scripts/check_doc_counts.sh
slow.frontier-ratchet|slow|frontier|true|never|bash scripts/check_frontier_ratchet.sh
slow.call-summary-census|slow|frontier|true|2026-08-29|bash scripts/call_summary_census.sh --out reports/call-summary-census-gate
slow.call-summary-census-aggregator|slow|frontier|true|2026-08-29|bash scripts/call_summary_census.sh --selftest
slow.upstream-rust-test-toolchain|slow|upstream|true|never|bash scripts/check_upstream_rust_test_toolchain.sh
release.ay-projection-certificate|release|supply-chain|true|never|bash scripts/check_ay_projection_certificate.sh
release.trust-mir-extract|release|compile|true|never|bash scripts/check_trust_mir_extract.sh
release.two-language-completion|release|soundness|true|never|TRUST_TOP_VERIFIER_PATH="${TRUST_TWO_LANGUAGE_TOP_VERIFIER:-/etc/trust/two_language_completion_gate.py}" && test -n "${TRUST_TWO_LANGUAGE_TOP_VERIFIER_SHA256:-}" && TRUST_TOP_VERIFIER_ACTUAL="$(/usr/bin/shasum -a 256 "$TRUST_TOP_VERIFIER_PATH")" && test "${TRUST_TOP_VERIFIER_ACTUAL%% *}" = "${TRUST_TWO_LANGUAGE_TOP_VERIFIER_SHA256}" && python3 "$TRUST_TOP_VERIFIER_PATH" --candidate-verifier scripts/two_language_completion_gate.py --receipt "${TRUST_TWO_LANGUAGE_COMPLETION_RECEIPT:-build/two-language-completion/receipt.json}" --root . --trusted-owner-key "${TRUST_TWO_LANGUAGE_OWNER_KEY:-/etc/trust/two-language-owner.pub}"
scoped.compiler-check|all,push|supply-chain|true|never|bash scripts/check_compiler_targets_build.sh
fast.tcb-panic-freedom|fast|soundness|true|2026-07-25|bash scripts/check_tcb_panic_freedom.sh
fast.tcb-document-exhaustiveness|fast|soundness|true|never|RUSTC_BOOTSTRAP=1 cargo test --manifest-path crates/Cargo.toml -p trust-integration-tests --test tcb_document_exhaustiveness --locked
fast.tcb-direct-trust-vc-certificate-boundary|fast|soundness|true|never|RUSTC_BOOTSTRAP=1 cargo test --manifest-path crates/Cargo.toml -p trust-vc-bridge --features trust-build direct_mir_memory_admission_binds_the_alethe_certificate_but_never_rechecks_it --locked
fast.tcb-direct-trust-vc-kernel-shape|fast|soundness|true|never|RUSTC_BOOTSTRAP=1 cargo test --manifest-path crates/Cargo.toml -p trust-certify --test direct_trust_vc_lane_shape --locked
fast.tidy|fast|style|true|2026-07-25|python3 x.py test --stage 1 src/tools/tidy
fast.crates-workspace-check|fast|compile|true|never|RUSTC_BOOTSTRAP=1 cargo check --manifest-path crates/Cargo.toml --workspace --all-targets --keep-going --locked
fast.targo-trust-check|fast|compile|true|never|RUSTC_BOOTSTRAP=1 cargo check --manifest-path targo-trust/Cargo.toml --all-targets --keep-going --locked
fast.compiler-check|fast|compile|true|2026-07-25|RUSTC_BOOTSTRAP=1 python3 x.py check --stage 1 compiler
fast.js262-corpus-verify|fast|trustjs|true|never|RUSTC_BOOTSTRAP=1 cargo run --manifest-path crates/Cargo.toml -p trust-js-differential -- corpus-verify
fast.js262-ledger-validate|fast|trustjs|true|never|RUSTC_BOOTSTRAP=1 cargo run --manifest-path crates/Cargo.toml -p trust-js-differential -- validate
fast.js262-selftest|fast|trustjs|true|never|RUSTC_BOOTSTRAP=1 cargo run --manifest-path crates/Cargo.toml -p trust-js-differential -- selftest
scripts.tests.suite|fast|script-tests|true|never|bash scripts/check_script_tests.sh
quick.targo-domination-unit|quick|harness|true|never|cargo test --manifest-path targo-trust/Cargo.toml trust_added_dispatch_accepts_full_verify_trust_compat_mode
quick.superset|quick|verification|true|never|bash tests/run_trust_superset_suite.sh quick
quick.robust-smoke|quick|compatibility|true|never|bash tests/run_trust_robust_suite.sh smoke
quick.crates-lib-tests|quick|crates|true|never|RUSTC_BOOTSTRAP=1 cargo test --manifest-path crates/Cargo.toml --workspace --lib --locked --no-fail-fast
quick.targo-trust-tests|quick|crates|true|never|RUSTC_BOOTSTRAP=1 cargo test --manifest-path targo-trust/Cargo.toml --locked --no-fail-fast
quick.compiler-unit-tests|quick|compile|true|never|RUSTC_BOOTSTRAP=1 python3 x.py test --stage 1 compiler/rustc_driver_impl compiler/rustc_session compiler/rustc_mir_transform
quick.falsification-classifier|quick|compile|true|never|bash tests/trust-falsification/classify_verdict_test.sh
trust.added.quick|release|blocked-release-inventory|true|never|TRUST_RELEASE_GATE=1 bash tests/run_trust_robust_suite.sh quick
stage2.build|release|bootstrap|true|never|python3 x.py build --stage 2
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
witness.replay-regression|release|witness|true|never|python3 tests/trust-witness/replay_regression.py
witness.auto-router-smoke|release|witness|true|never|python3 tests/trust-witness/auto_router_smoke.py
witness.closure-parity-smoke|release|witness|true|never|python3 tests/trust-witness/closure_parity_smoke.py
witness.generics-parity-smoke|release|witness|true|never|python3 tests/trust-witness/generics_parity_smoke.py
witness.precise-parity-smoke|release|witness|true|never|python3 tests/trust-witness/precise_parity_smoke.py
elide.regression|release|elide|true|never|python3 tests/trust-elide/elide_regression.py
suite.ui|suites|compiletest|true|never|python3 x.py test --stage 2 tests/ui
suite.ui-fulldeps|suites|compiletest|true|never|python3 x.py test --stage 2 tests/ui-fulldeps
suite.crashes|suites|compiletest|true|never|python3 x.py test --stage 2 tests/crashes
suite.codegen-llvm|suites|compiletest|true|never|python3 x.py test --stage 2 tests/codegen-llvm
suite.codegen-units|suites|compiletest|true|never|python3 x.py test --stage 2 tests/codegen-units
suite.assembly-llvm|suites|compiletest|true|never|python3 x.py test --stage 2 tests/assembly-llvm
suite.incremental|suites|compiletest|true|never|python3 x.py test --stage 2 tests/incremental
suite.debuginfo|suites|compiletest|true|never|python3 x.py test --stage 2 tests/debuginfo
suite.mir-opt|suites|compiletest|true|never|python3 x.py test --stage 2 tests/mir-opt
suite.pretty|suites|compiletest|true|never|python3 x.py test --stage 2 tests/pretty
suite.run-make|suites|compiletest|true|never|python3 x.py test --stage 2 tests/run-make
suite.run-make-cargo|suites|compiletest|true|never|python3 x.py test --stage 2 tests/run-make-cargo
suite.build-std|suites|compiletest|true|never|python3 x.py test --stage 2 tests/build-std
suite.coverage|suites|compiletest|true|never|python3 x.py test --stage 2 tests/coverage
suite.coverage-run-rustdoc|suites|compiletest|true|never|python3 x.py test --stage 2 tests/coverage-run-rustdoc
suite.rustdoc-html|suites|compiletest|true|never|python3 x.py test --stage 2 tests/rustdoc-html
suite.rustdoc-ui|suites|compiletest|true|never|python3 x.py test --stage 2 tests/rustdoc-ui
suite.rustdoc-json|suites|compiletest|true|never|python3 x.py test --stage 2 tests/rustdoc-json
suite.rustdoc-js|suites|compiletest|true|never|python3 x.py test --stage 2 tests/rustdoc-js
suite.rustdoc-js-std|suites|compiletest|true|never|python3 x.py test --stage 2 tests/rustdoc-js-std
suite.rustdoc-gui|suites|compiletest|false|never|python3 x.py test --stage 2 tests/rustdoc-gui
slow.kernel-derivation|slow|kernel|true|never|bash scripts/trust_kernel_derivation_lane.sh
canary.is-whnf-mint-gate|slow,release|soundness|true|2026-08-24|bash scripts/trust_control_canary.sh
slow.js262-calibrate|slow|trustjs|true|never|bash scripts/js262/calibrate.sh
fast.cutover-gate-validator|fast|harness|true|2026-08-26|python3 scripts/cutover_gate/test_validate.py
fast.pin-regression|fast,push|supply-chain|true|never|bash scripts/check_pin_regression.sh --push-context
fast.pin-regression-selftest|fast,push|supply-chain|true|2026-08-27|bash scripts/check_pin_regression.sh --selftest
fast.seal-driver-guard-mutation|fast,release|harness|true|2026-08-26|bash scripts/seal_driver.sh guardtest
fast.self-verify-crate-selftest|fast|soundness|true|2026-08-26|bash scripts/trust_self_verify_crate.sh --selftest
fast.submodule-worktree-pins|fast|drift|true|2026-08-26|bash scripts/submodule_sync.sh
fast.trust-conformance|fast,release|conformance|true|never|python3 scripts/run_trust_conformance.py
fast.trust-ir-flip-burnin-selftest|fast,release|soundness|true|2026-08-26|python3 scripts/trust_ir_flip_burnin.py --selftest
fast.trust-ir-frontier-table-selftest|fast,release|drift|true|2026-08-26|python3 scripts/trust_ir_frontier_table.py --selftest
slow.bridge-replay|slow,release|soundness|true|never|bash scripts/trust_bridge_replay_lane.sh
slow.corpus-census-faithfulness|slow,release|drift|true|never|bash scripts/corpus_census.sh crates/target/debug/corpus-census-2026-07-24 crates/trust-clean/fixtures build/census 1800
slow.mf-r5-full-union|slow,release|drift|true|never|R=reports/build/mf-r5-$(date -u +%Y%m%dT%H%M%SZ); python3 scripts/mf_r5_full_union.py --output $R --receipt $R.json
slow.mir-transform-ratchet|slow,release|drift|true|never|bash scripts/check_trust_verify_suite_ratchet.sh
slow.self-verify-crate-ratchet|slow,release|soundness|true|never|bash scripts/trust_self_verify_crate.sh
slow.showcase-demo|slow|demo|true|never|bash scripts/showcase-demo.sh --quick
slow.submodule-coherence|slow,release|supply-chain|true|never|bash scripts/submodule-coherence-gate.sh
slow.win-cross-check|slow,release|compatibility|true|never|bash scripts/win_cross_check.sh
release.assumption-ledger-stage1|release|soundness|true|never|bash scripts/gate_assumption_ledger_stage1.sh
release.certified-monitor-e2e|release|harness|true|never|build/host/stage2/bin/targo-trust trust release validate certified-monitors --stage2-sysroot build/host/stage2
release.certified-scoreboard|release|soundness|true|never|python3 scripts/trust_certified_scoreboard.py --baseline tests/self-proof/certified-scoreboard.baseline
release.cite-discharge|release|soundness|true|never|python3 scripts/trust_cite_discharge.py --structural target/trust/survey/ny-cert-structural.json --contracts target/trust/survey/ny-cert-contracts.json --cite-map first-party/ny/crates/ny-cert/proofs/cite-map.json --corpus first-party/clean
release.crates-io-native-compat|release|compatibility|true|never|bash scripts/compat_check.sh
release.ddc-double-compilation|release|soundness|false|never|bash scripts/ddc_compare.sh config-stage0 trust-stage2
release.fresh-clone-seed-consume|release|bootstrap|true|never|bash scripts/ci_fresh_clone_consume_test.sh --stage 2
release.lambda-calculus-downstream-diagnostic|release|diagnostic|false|never|python3 scripts/collect_lambda_calculus_diagnostic.py --repo-root . --output build/evidence/lambda-calculus-diagnostic.json
release.mint-and-prove-seed|release|bootstrap|true|never|S=build/seed-$(date -u +%Y%m%dT%H%M%SZ); bash scripts/mint_and_prove_seed.sh --seed-dir $S --proof-build-dir $S-proof
release.native-solver-sample-verification|release|soundness|true|never|python3 scripts/run_native_solver_sample_verification.py
release.off-stock-rust-preflight|release|supply-chain|true|never|bash scripts/prove_rust_free_build.sh
release.realcode-coverage-receipt|release|evidence|true|never|python3 scripts/collect_realcode_coverage_evidence.py --repo-root . --output build/evidence/realcode-coverage-receipt.json
release.repro-backend-dylib-selfcompare|slow,release|reproducibility|true|never|bash scripts/repro_build_selfcompare.sh
release.repro-wholestage2-selfcompare|slow,release|reproducibility|false|never|bash scripts/repro_wholestage2_selfcompare.sh
release.rustc-mir-differential-oracle|release|soundness|true|never|TRUSTC=build/host/stage2/bin/trustc bash scripts/differential/rustc_mir_differential_oracle.sh
release.self-proof-all-trust|release|soundness|true|never|PATH=build/host/stage2/bin:$PATH bash scripts/prove_self_all_trust.sh
release.self-verify-oracle|release|soundness|true|never|TRUSTC=build/host/stage2/bin/trustc bash scripts/trust_self_verify.sh
release.stage0-payload-fetchability|release|supply-chain|true|2026-08-26|python3 scripts/fetch_trust_stage0_payloads.py --json
release.stage0-seed-discovery|release|bootstrap|false|never|python3 scripts/discover_trust_stage0_seed.py --json
release.stage2-noverify-mir-transform|release|compile|true|never|bash scripts/stage2_noverify_rustc_mir_transform_test.sh
release.stage2-noverify-self-build|release|bootstrap|true|never|bash scripts/stage2_noverify_self_build.sh
release.stage2-verify-self-build|release|soundness|true|never|bash scripts/stage2_verify_self_build.sh
release.strict-superiority-artifacts|release|evidence|true|never|bash scripts/collect_strict_superiority_artifacts.sh
release.tests-after-build|release|harness|true|never|bash scripts/run_tests_after_build.sh
release.trust-frontend-proof|fast,release|harness|true|never|sh scripts/prove-trust-frontend-gate.sh
release.trust-ir-flip-burnin|release|soundness|true|never|python3 scripts/trust_ir_flip_burnin.py --trustc build/host/stage2/bin/trustc --out-dir target/trust/flip-burnin
release.trust-ir-lineage-reconcile|release|soundness|true|never|python3 scripts/trust_ir_lineage_reconcile.py --dump target/trust/ir-dump --flip-log target/trust/ir-dump/flip.log
release.trustir-olean-vendor-identity|release|supply-chain|true|never|bash scripts/regen-trustir-oleans.sh --check
release.unsafe-coverage-completeness|release|soundness|true|never|bash scripts/check-unsafe-coverage.sh
release.upstream-rust-adopted-evidence|release|upstream|true|never|python3 scripts/run_upstream_rust_adopted_evidence.py --strict-exit
suites.ledger-max-same-day|fast,release|ledger|true|2026-08-27|python3 tests/ledger/test_max_same_day.py
suites.trust-contract-probes|release|soundness|true|2026-08-27|bash tests/trust-contract/contract_clause_sort_match.sh && bash tests/trust-contract/contract_field_projection.sh && bash tests/trust-contract/contract_inline_repro.sh
suites.provability-ratchet|release|soundness|true|2026-08-27|python3 tests/trust-provability/ratchet.py --check
suites.e6-fragment-probe|release|harness|true|never|python3 tests/e6-fragment-probe/run.py
suites.two-language-battery|release|harness|true|never|python3 tests/two-language-battery/test_run.py
fast.ir-cohort|fast,release|supply-chain|true|2026-08-27|python3 scripts/check_ir_cohort.py
release.spec-surface-parity|release|soundness|true|2026-08-27|python3 scripts/check_spec_surface_parity.py --toolchain-bin build/host/stage2/bin
fast.raw-enum-tag-fixtures|fast,release|soundness|true|2026-08-27|python3 scripts/regen_raw_enum_tag_fixtures.py --check
fast.trust-ir-corpus-lock|fast,release|supply-chain|true|2026-08-27|python3 scripts/trust_ir_corpus_lock.py --check
release.ratio-strict|release|soundness|true|never|bash scripts/trust_ratio_strict_gate.sh
release.hex-strict|release|soundness|true|never|bash scripts/trust_hex_strict_gate.sh
release.utf-strict|release|soundness|true|never|bash scripts/trust_utf_strict_gate.sh
release.endian-strict|release|soundness|true|never|bash scripts/trust_endian_strict_gate.sh
release.varint-strict|release|soundness|true|never|bash scripts/trust_varint_strict_gate.sh
release.index-strict|release|soundness|true|never|bash scripts/trust_index_strict_gate.sh
release.checksum-strict|release|soundness|true|never|bash scripts/trust_checksum_strict_gate.sh
release.radix64-strict|release|soundness|true|never|bash scripts/trust_radix64_strict_gate.sh
release.align-strict|release|soundness|true|never|bash scripts/trust_align_strict_gate.sh
release.fixed-strict|release|soundness|true|never|bash scripts/trust_fixed_strict_gate.sh
release.interval-strict|release|soundness|true|never|bash scripts/trust_interval_strict_gate.sh
release.timearith-strict|release|soundness|true|never|bash scripts/trust_timearith_strict_gate.sh
release.bits-strict|release|soundness|true|never|bash scripts/trust_bits_strict_gate.sh
release.modular-strict|release|soundness|true|never|bash scripts/trust_modular_strict_gate.sh
release.intbound-strict|release|soundness|true|never|TARGO="$(pwd -P)/build/host/stage2/bin/targo" bash scripts/trust_intbound_strict_gate.sh
release.widthconv-strict|release|soundness|true|never|TARGO="$(pwd -P)/build/host/stage2/bin/targo" bash scripts/trust_widthconv_strict_gate.sh
release.budget-strict|release|soundness|true|never|TARGO="$(pwd -P)/build/host/stage2/bin/targo" bash scripts/trust_budget_strict_gate.sh
release.bitfield-strict|release|soundness|true|never|bash scripts/trust_bitfield_strict_gate.sh
release.floatbits-strict|release|soundness|true|never|TARGO="$(pwd -P)/build/host/stage2/bin/targo" bash scripts/trust_floatbits_strict_gate.sh
fast.floatbits-twin-parity|fast,release|soundness|true|2026-08-31|python3 scripts/trust_floatbits_twin_parity.py crates/trust-floatbits/src/lib.rs crates/trust-floatbits/src/contracts.rs
release.strict-pass-frontier|release|soundness|true|never|bash scripts/trust_strict_pass_frontier.sh
fast.kernel-authority-vacuity|fast,release|soundness|true|2026-08-28|python3 scripts/check_kernel_authority_vacuity.py
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

mkdir -p "$LOG_DIR"
printf 'gate_id\tcategory\trequired\tlast_green\tstarted_at\tended_at\tduration_seconds\texit_code\tcommand\tlog_path\n' >"$RESULTS_TSV"

# A PASSING LANE COULD SAY NOTHING AT ALL, AND THAT IS HOW A DATED FLEET STOP
# ARRIVES UNANNOUNCED.
#
# run_gate writes every lane's stdout and stderr to a log and, on PASS, printed
# one word: PASS. Nobody opens the log of a lane that passed. So a lane that
# KNOWS something is coming -- `fast.two-language-claim-ledger` knows the exact
# instant a claim lease lapses and takes the whole fleet's pushes with it -- had
# no channel to say so, and the first news of the stop was the stop.
#
# This is that channel, and it is deliberately one line of contract: a lane
# announces by printing a line beginning `WARN:`, and this surfaces those lines
# on the harness's own stdout even when the lane passed. It is not a status: the
# lane still PASSES, the exit code is untouched, and nothing here can fail a run.
# Controlled end-to-end against the real run_gate by
# scripts/tests/gate_warning_surface_test.sh, in both directions -- a WARN line
# is surfaced, and a lane that emits none produces no output here.
surface_gate_warnings() {
    local gate_id="$1" log_path="$2" line found=0
    [ -f "$log_path" ] || return 0
    while IFS= read -r line; do
        found=1
        echo "$line"
    done < <(grep -E '^[[:space:]]*WARN: ' "$log_path" || true)
    [ "$found" -eq 1 ] && echo "warnings: $gate_id passed and reported the above"
    return 0
}

run_gate() {
    local gate_id="$1"
    local category="$2"
    local required="$3"
    local last_green="$4"
    local command="$5"
    local log_name log_path started_at ended_at started_epoch ended_epoch duration status

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

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$gate_id" "$category" "$required" "$last_green" "$started_at" "$ended_at" \
        "$duration" "$status" "$command" "$log_path" >>"$RESULTS_TSV"

    if [ "$status" -eq 0 ]; then
        echo "status:   PASS (${duration}s)"
        surface_gate_warnings "$gate_id" "$log_path"
        if [ "$last_green" != "${started_at%%T*}" ]; then
            echo "LAST-GREEN: update the manifest row for $gate_id to ${started_at%%T*}"
        fi
    else
        echo "status:   FAIL exit=$status (${duration}s)"
        echo "--- tail: $log_path"
        tail -n 80 "$log_path" || true
        echo "--- end tail"
    fi

    return "$status"
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
        if [ "$FAIL_FAST" = "1" ]; then
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
python3 - "$TRUST_ROOT" "$MODE" "$RUN_ID" "$RUN_STARTED_AT" "$RUN_ENDED_AT" \
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
non_evidence_categories = {"non-evidence-regression-diagnostic"}
with results_path.open("r", encoding="utf-8", newline="") as fh:
    reader = csv.DictReader(fh, delimiter="\t")
    for row in reader:
        row["required"] = row["required"].lower() == "true"
        row["duration_seconds"] = int(row["duration_seconds"])
        row["exit_code"] = int(row["exit_code"])
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
    if row["exit_code"] == 0:
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

echo
echo "Comprehensive harness report:"
echo "  JSON: $REPORT_JSON"
echo "  MD:   $REPORT_MD"

exit "$report_status"
