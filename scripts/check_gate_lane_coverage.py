#!/usr/bin/env python3
"""Every test lane in the tree must be named by the gate manifest.

A lane that exists but appears in no manifest row is a lane nobody runs, and
nothing announces that: the file sits in the tree looking maintained while no
orchestrator ever invokes it. This walks the on-disk lane inventory and fails
when a lane is unnamed, so adding an e2e script, a gate script, an adversarial
oracle, a witness or elide regression, a `scripts/tests/` test, or a compiletest
suite forces a manifest row in the same change.

Coverage is literal by default: a lane is covered when its repo-relative path
appears verbatim in some row's command. Lanes reached through an aggregate
(a glob runner, a `targo trust` subcommand) are covered by naming that
aggregate in `INDIRECT` below, which keeps the indirection written down instead
of inferred. `MANUAL_ONLY` is the one remaining exit: a tool whose interface
cannot be a row at all, listed with the reason. `DOC_ENFORCEMENT_LANES` adds one
more class: a document that claims a test keeps it honest must name a test that
a manifest row actually runs.

It also validates the manifest's own shape: six pipe-separated columns, a
recognized profile set, and a `last_green` that is either `never` or an ISO
date that is not in the future.

It also validates the divergence ledger against the manifest: every `active`
row of tests/trust-comprehensive/divergences.toml must name a `gate_id` that is
a manifest row. The harness matches a quarantine only by gate id, so a row
naming a gate that does not exist can never match anything — it sits in the
ledger reading like a quarantine, warns and then expires under
`fast.ledger-expirations`, and quarantines nothing (found 2026-09-14: the
`verify.precision` row had named a gate that never existed, for two months).

Rules guard the pre-push gate, which derives its ENTIRE lane list from the
rows carrying the `push` profile: some row must carry that profile,
`scripts/hooks/pre-push` must `run_lane` no gate id literally, must derive
its lanes from the manifest (`--list push`), must export TRUST_PUSHED_REFS
to them, and must derive the TRUST_PUSHED_REFS reader set from this checker
(`--push-refs-readers`, via `push_refs_reader_gate_ids`) instead of naming
two or more of those readers itself. Each failure re-creates a
hand-maintained second inventory of the kind removed on 2026-08-27. These
are behavior checks on the hook's derivation commands, not pins on its
comment prose: the earlier rule policed a `# PUSH CONTEXT.` section by
heading, and went stale when the hook's header was rewritten on
2026-11-02 (DECISION_QUEUE 2026-11-03, gate-lane-coverage
repair).

Usage:
    scripts/check_gate_lane_coverage.py
    scripts/check_gate_lane_coverage.py --list-uncovered
    scripts/check_gate_lane_coverage.py --push-refs-readers

Exit codes:
    0   every lane is named and every row is well-formed
    1   an unnamed lane or a malformed row

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import re
import sys
from datetime import date, datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
HARNESS = REPO_ROOT / "tests" / "run_trust_comprehensive_harness.sh"
DIVERGENCES = REPO_ROOT / "tests" / "trust-comprehensive" / "divergences.toml"

KNOWN_PROFILES = {"all", "manifest", "fast", "push", "quick", "suites", "slow", "release"}

# Lanes that no row names directly, each with the aggregate that does run them.
# A lane belongs here only when the aggregate genuinely executes it; the point
# of the table is that the indirection is stated, not that the lane is excused.
INDIRECT: dict[str, str] = {
    # The whole `tests/e2e_*.sh` corpus runs as one lane.
    "tests/e2e_*.sh": "scripts/run_e2e_shell_corpus.sh",
    # `scripts/tests/*` run as one lane.
    "scripts/tests/*": "scripts/check_script_tests.sh",
    # daily_toolchain_stage_test.py reads this portable owner fixture and
    # executes its actual declarations in ConsumerOutcomeTests. The
    # fixture is not an independent test program; the aggregate globs its
    # *_test.py caller (checked 2026-10-25).
    "scripts/tests/fixtures/publication_daily_consumer_outcomes.py": (
        "scripts/check_script_tests.sh"
    ),
    # scripts/tests/produce_vf5_proposal_test.py loads the driver from its path
    # and runs its functions; the aggregate globs scripts/tests/*_test.py.
    "scripts/produce_vf5_proposal.py": "scripts/check_script_tests.sh",
    # trust_core_specr_regen_test.py runs the real regeneration driver and
    # mutations of its pinned inputs, translator and generated outputs. The
    # driver executes the converter/selectors and imports the lowering modules
    # below. Keep these paths exact so a new sibling still needs classification.
    "scripts/trust_core/specr/regen.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/conformance/mrjson.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/conformance/records2clean.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/conformance/select_slice.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/calls.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/common.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/emit_fns.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/emit_types.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/items.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/lower.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/specr2clean.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/tyres.py": "scripts/check_script_tests.sh",
    # tests/e2e_two_language_programs.sh sets
    # ROWS_DIR="$TRUST_ROOT/tests/two-language-programs" and drives one row per
    # directory under it. Since 2026-09-21 (roadmap WS8.8) the script is a row
    # of its own, `release.two-language-programs`, and run_e2e_shell_corpus.sh
    # skips it by name so the battery runs once per release, not twice; the
    # script's own path appears verbatim in that row's command, so the script
    # is covered literally and its rows through it. Read, not assumed: all
    # three links re-checked 2026-09-21.
    "tests/two-language-programs": "tests/e2e_two_language_programs.sh",
    # This directory contains the real two-run qualifier and its oracle
    # controls. native_admission_gate_errors requires both exact rows below,
    # including the release qualifier's immutable-provenance mode.
    "tests/native-admission-census": (
        "python3 tests/native-admission-census/run.py --bin build/host/stage2/bin "
        "--verify-stage-provenance"
    ),
    # The producer-ratchet judge (roadmap WS5.1). tests/e2e_two_language_programs.sh
    # sets IR_JUDGE="$TRUST_ROOT/scripts/two_language_producer_ratchets.py" and
    # runs `run --row <ir-*>` once per row of its `trustc-ir` lane, so it is
    # exercised wherever that battery is; its toolchain-free half (the replay of
    # the audit run, audit-check over every pin, the refusal-class twin, the
    # WS8.8 island-mutation control) is
    # scripts/tests/two_language_producer_ratchets_test.py, run by
    # check_script_tests.sh. Read, not assumed: both links checked 2026-09-21.
    "scripts/two_language_producer_ratchets.py": "tests/e2e_two_language_programs.sh",
    # The 2026-09-17..19 capability lanes. Each entry was READ, not assumed:
    # every driver names its corpus directory in its own source (verified by
    # grep on 2026-09-20), and every driver is itself named by a `slow.*`
    # manifest row added in the same change, so the indirection terminates in a
    # row rather than in another indirection.
    #   scripts/closure_slice_facts.sh   -> tests/closure-slice-facts
    #   scripts/daily_driver_probes.sh   -> tests/daily-driver-realistic (its `D=`)
    #   scripts/fn_pointer_witness.sh    -> tests/fn-pointer-witness
    #   scripts/open_dispatch_ladder.sh  -> tests/open-dispatch-ladder
    #   scripts/ordinary_rust_sweep.sh   -> tests/ordinary-rust-sweep
    #   scripts/panicking_std_battery.sh -> tests/panicking-std-battery
    #   scripts/vec_literal_lowering.sh  -> tests/vec-literal-lowering
    "tests/closure-slice-facts": "scripts/closure_slice_facts.sh",
    "tests/daily-driver-realistic": "scripts/daily_driver_probes.sh",
    "tests/fn-pointer-witness": "scripts/fn_pointer_witness.sh",
    "tests/open-dispatch-ladder": "scripts/open_dispatch_ladder.sh",
    "tests/ordinary-rust-sweep": "scripts/ordinary_rust_sweep.sh",
    "tests/panicking-std-battery": "scripts/panicking_std_battery.sh",
    "tests/vec-literal-lowering": "scripts/vec_literal_lowering.sh",
    # scripts/idiomatic_rust_sample.sh:27 globs
    # "$ROOT"/tests/idiomatic-rust-sample/*.rs, and that driver is itself named
    # by the `slow.idiomatic-rust-sample` row added with this entry, so the
    # indirection terminates in a row. Read, not assumed: checked 2026-09-20.
    "tests/idiomatic-rust-sample": "scripts/idiomatic_rust_sample.sh",
    # `scripts/check_*` checkers reached through an aggregate a row DOES name.
    # Verified by reading the aggregate, not by assuming: the e2e script execs
    # the real checker (not a synthetic copy) inside the corpus lane.
    # tests/e2e_certified_monitor_lock_source_gate.sh runs "$ROOT/scripts/...".
    "scripts/check_lockfile_no_git_sources.sh": "scripts/run_e2e_shell_corpus.sh",
    # The shell is deliberately payload-only and rejects direct callers. The
    # Rust-native release parent performs the controlled-Git authority checks,
    # invokes this exact payload, reopens its sealed output, and alone publishes
    # the native-authority receipt.
    "scripts/stage2_certified_monitor_e2e.sh": (
        "targo-trust trust release validate certified-monitors"
    ),
    # --- classified 2026-08-26, from the catch-all sweep ---
    # compat_check.sh is a 35-line entry point whose last statement is
    # `exec "$PYTHON_BIN" ... compat_check.py`, so the shell row's exit status
    # IS this module's verdict. The pair is covered by naming the shell half.
    "scripts/compat_check.py": "scripts/compat_check.sh",
    # tests/e2e_trust_local_rustup_install.sh runs the REAL script (not a copy,
    # not a stub) against a genuinely installed sysroot, then asserts that
    # `rustup which --toolchain <name> trustc` resolves inside that sysroot.
    "scripts/rustup-link-trust.sh": "scripts/run_e2e_shell_corpus.sh",
    # tests/e2e_full_verifier_three_suite_sample.sh binds it as
    # RUSTC_PRIVATE_SYSROOT_FILTER. It is a narrow rustc-argv rewriter, so it
    # could never be a row of its own; this records WHERE it is exercised.
    "scripts/trust_rustc_private_sysroot_filter.py": "scripts/run_e2e_shell_corpus.sh",
    # scripts/tests/trust_ir_rowdiff_test.py imports the module and drives the
    # real comparator in-process. What that pins is the comparator's FIELD SET —
    # the defect it was written for, after six scratchpad copies disagreed about
    # which fields count and `spliced`/`instr_count`/`lineage` went unwatched.
    # A real two-artifact comparison still has no scheduled home; give it a row
    # if a sweep ever publishes a standing control artifact.
    "scripts/trust_ir_rowdiff.py": "scripts/check_script_tests.sh",
    # scripts/tests/prune_seal_symlinks_test.py loads the REAL module by path
    # (importlib.util.spec_from_file_location on scripts/prune_seal_symlinks.py)
    # and drives `prune_escaping_symlinks` in-process against a temporary seal
    # tree, both ways: escaping links removed, in-seal links kept, second pass
    # empty. That test runs under the `scripts.tests.suite` row via
    # scripts/check_script_tests.sh, which globs scripts/tests/*_test.py. Its
    # production caller is scripts/promote-toolchain.sh:665, a mutating
    # promotion tool that is itself not a row.
    "scripts/prune_seal_symlinks.py": "scripts/check_script_tests.sh",
    # The full script-test aggregate imports these exact production modules.
    # bootstrap_dependency_closure_test.py and daily_toolchain_stage_test.py
    # load their real owners; the latter includes actual nested-signal controls.
    "scripts/bootstrap_dependency_closure.py": "scripts/check_script_tests.sh",
    "scripts/daily_toolchain_stage.py": "scripts/check_script_tests.sh",
    # linux_root_input_closure_test.py and its fixture census load the committed
    # input closure, archive and record modules through the authenticated loader.
    "scripts/tests/linux_root_input_fixture.py": "scripts/check_script_tests.sh",
    "scripts/seed_input_closure.py": "scripts/check_script_tests.sh",
    "scripts/seed_input_records.py": "scripts/check_script_tests.sh",
    "scripts/seed_input_committed.py": "scripts/check_script_tests.sh",
    "scripts/seed_input_archives.py": "scripts/check_script_tests.sh",
    # seed_dependency_sources_test.py exercises the byte, Git-object/path and
    # local-source implementations through the real seed source loader.
    "scripts/seed_dependency_bytes.py": "scripts/check_script_tests.sh",
    "scripts/seed_dependency_git.py": "scripts/check_script_tests.sh",
    "scripts/seed_dependency_git_paths.py": "scripts/check_script_tests.sh",
    "scripts/seed_dependency_local.py": "scripts/check_script_tests.sh",
    "scripts/seed_dependency_objects.py": "scripts/check_script_tests.sh",
    # linux_root_custody_test.py and seed_observed_commands_test.py load the
    # custody/contract owners and their command, event, Git and I/O helpers.
    "scripts/seed_custody_source.py": "scripts/check_script_tests.sh",
    "scripts/seed_producer_custody.py": "scripts/check_script_tests.sh",
    "scripts/seed_producer_contract.py": "scripts/check_script_tests.sh",
    "scripts/seed_observed_commands.py": "scripts/check_script_tests.sh",
    "scripts/seed_observed_events.py": "scripts/check_script_tests.sh",
    "scripts/seed_observed_git.py": "scripts/check_script_tests.sh",
    "scripts/seed_observed_io.py": "scripts/check_script_tests.sh",

    # The promotion suite runs the real committed-source/helper controls, and
    # the bootstrap-script lane watches both the helper and its TOML writer.
    "scripts/freeze_toolchain_sources.py": "scripts/check_bootstrap_script_tests.sh",
    # Imported by recreate_bootstrap_test.py: fixture account lookup, real
    # subprocess/flock admission, and no access to the user's machine slot pool.
    "scripts/build-slot": "scripts/check_bootstrap_script_tests.sh",
    # The promotion suite copies this exact helper into its fixture repository
    # and executes it through real candidate/sealed-destination surface checks.
    # Complete synthetic library fixtures and thirteen added refusal cases
    # exercise its structural contract; they make no metadata/proof claim.
    "scripts/verify_sysroot_libraries.py": "scripts/check_bootstrap_script_tests.sh",
    # Step 2 increment 4d, sub-step 4d.0a: the channel-C census instrument (the shim population
    # increment 4d must retire). scripts/tests/channel_c_survey_test.py loads the REAL module and
    # drives its row parser on channel C's row shapes and `survey()` end to end with a fake
    # compiler, plus `main()` for real on a vacuous census. That test runs under the
    # `scripts.tests.suite` row. Census runs over a corpus are measurements (recorded in the
    # 4d plan and docs/KNOWN_HAZARDS.md), not gates.
    "scripts/channel_c_survey.py": "scripts/check_script_tests.sh",
    # The two-language completion gate and its eight per-gate checkers. They are
    # judges of evidence, not gates of their own: scripts/two_language_completion_gate.py
    # runs each checker (a read-only snapshot under `python -I`) only inside an
    # acceptance run that binds a receipt, and no receipt exists today. The
    # `release.two-language-completion` row names the gate literally, but only as
    # the CANDIDATE an externally pinned top verifier (/etc/trust) judges, which
    # no machine has yet — so that row is not where the gate's code executes.
    # Their verdict surfaces (the v2 verdict shape, every conjunct's structural
    # rule, the evidence-binding refusals, the malformed/deep-JSON refusals) are
    # driven end to end by the fourteen scripts/tests/completion_gate*_test.py /
    # two_language*_test.py modules, which scripts/check_completion_gate_tests.sh
    # runs as the push-profile `scoped.completion-gate-tests` row whenever a push
    # touches them. Until 2026-09-27 G2/G5/G7 were listed here under
    # scripts/check_script_tests.sh — a fast-only row, never green, that could not
    # import these tests — and G1/G3/G4/G6/G8 under nothing at all.
    # Read, not assumed: each checker is imported by
    # scripts/tests/completion_gate_malformed_input_test.py:12-20 and exercised
    # by its own completion_gates_g*_test.py (checked 2026-09-27).
    "scripts/two_language_completion_gate.py": "scripts/check_completion_gate_tests.sh",
    "scripts/completion_gates/check_g1_rust_input.py": "scripts/check_completion_gate_tests.sh",
    "scripts/completion_gates/check_g2_lean_input.py": "scripts/check_completion_gate_tests.sh",
    "scripts/completion_gates/check_g3_producer_totality.py": "scripts/check_completion_gate_tests.sh",
    "scripts/completion_gates/check_g4_semantic_faithfulness.py": "scripts/check_completion_gate_tests.sh",
    "scripts/completion_gates/check_g5_mixed_linking.py": "scripts/check_completion_gate_tests.sh",
    "scripts/completion_gates/check_g6_proof_authority.py": "scripts/check_completion_gate_tests.sh",
    "scripts/completion_gates/check_g7_codegen_authority.py": "scripts/check_completion_gate_tests.sh",
    "scripts/completion_gates/check_g8_release_reproducibility.py": "scripts/check_completion_gate_tests.sh",
    # The two-language program battery's inventory checker (coverage only: a full
    # battery run visits every fixture under tests/two-language-programs/
    # exactly once). Its production caller is tests/e2e_two_language_programs.sh:927,
    # reached only by the release-profile `verify.e2e-shell-corpus` row; the
    # lane that runs it on push is scripts/tests/two_language_program_inventory_test.py:13,
    # which loads the REAL checker by path against the real harness and row
    # directories plus mutated copies — one of the fourteen modules the
    # `scoped.completion-gate-tests` row runs (checked 2026-09-27).
    "scripts/check_two_language_program_inventory.py": "scripts/check_completion_gate_tests.sh",
    # The G3 producer (subject index + producer body join). No gate runs it as
    # a step yet: it is an evidence producer an acceptance run would invoke.
    # scripts/tests/two_language_subject_index_test.py runs the REAL script as a
    # subprocess on the G3 checker's own fixture, feeds its output back to
    # check_g3_producer_totality.py, and is one of the fourteen modules the
    # `scoped.completion-gate-tests` row runs (checked 2026-09-29).
    "scripts/two_language_subject_index.py": "scripts/check_completion_gate_tests.sh",
    # scripts/tests/ui_trust_budget_sensitivity_test.py loads the REAL module by
    # path for its directive reader (compiletest's line splitting, every
    # `compile-flags` line accumulating, edition first, revision scoping,
    # recursive discovery) and runs the REAL script end to end against a fake
    # compiler that logs every invocation: the default pattern must compile
    # tests/ui/trust/memory_safe/reject_diverging_call_gap.rs with both of its
    # flag lines, and a sweep in which nothing compiles must exit 3. That test
    # runs under the `scripts.tests.suite` row via scripts/check_script_tests.sh.
    # A real sweep needs a prebuilt stage1 and minutes of compile time; it is a
    # measurement, not a gate.
    "scripts/ui_trust_budget_sensitivity.py": "scripts/check_script_tests.sh",
    # Core vocabulary v0 (design 2026-09-16 §5.2 Stage 0.2): the constructor and
    # UB-reason names that D0.3 (exit E0.6), D0.2 (E0.7) and D0.6 (E0.8b) map
    # into, so those zero-unmapped exits count against one namespace.
    # scripts/tests/trust_core_core_vocabulary_test.py loads the REAL module by
    # path, runs it on the pinned MiniRust and Reference clones and this tree's
    # design, table, document, review registry and rustc sources asserting the
    # published counts, and mutates copies of every input to show each predicate
    # (and the review layer) fails; the `scripts.tests.suite` row runs it via
    # scripts/check_script_tests.sh, which globs scripts/tests/*_test.py.
    "scripts/trust_core/core_vocabulary.py": "scripts/check_script_tests.sh",
    # The durable source cache every Trust core checker reads (MiniRust, the Reference, the FLS,
    # a-mir-formality, the RFCs, rust-lang/rust's library at the EXTERNAL_PINS.toml revisions).
    # scripts/check_script_tests.sh runs it before the suite, so the `scripts.tests.suite` row
    # exercises it on every run; the trust_core tests then fail naming it if a fetch failed.
    "scripts/trust_core/fetch_sources.py": "scripts/check_script_tests.sh",
    # The shared layer of the Trust core Phase 0 checkers (design 2026-09-16
    # §5.2 Stage 0.2): pins from docs/trust-core/EXTERNAL_PINS.toml, citation
    # resolution at the pins, uniqueness, generated blocks, reviewed judgments
    # (docs/trust-core/reviews/) and immutable snapshots. It is a library, not a
    # gate: core_vocabulary.py imports it on every run, and
    # scripts/tests/trust_core_common_test.py loads the REAL module by path and
    # drives each function on real inputs beside a mutated copy; both tests run
    # under the `scripts.tests.suite` row via scripts/check_script_tests.sh.
    "scripts/trust_core/common.py": "scripts/check_script_tests.sh",
    # trust_core_vf3_census_test.py imports the actual census and exercises
    # --check against the committed Git pin, beside mutated records, parser
    # refusals and fragment controls. The aggregate runs that *_test.py;
    # this is control coverage, not a current compiler proof measurement.
    "scripts/trust_core/vf3_census.py": "scripts/check_script_tests.sh",
    # D0.3, the MIR constructor and intrinsic table (design 2026-09-16 §5.1 item 2,
    # §5.2 Stage 0.2): exit E0.6 "Zero unmapped MIR enum variants; the count is
    # published", invariant I-RCC-TOTAL. It runs on common.py.
    # scripts/tests/trust_core_mir_constructor_table_test.py loads the REAL module by
    # path, runs it on the pinned MiniRust clone and this tree's compiler/, library/,
    # design, vocabulary, table, document and review registry (the vocabulary checker
    # included) asserting the published counts, and mutates copies of every input to show
    # each predicate (and the review layer) fails; the `scripts.tests.suite` row runs it
    # via scripts/check_script_tests.sh, which globs scripts/tests/*_test.py.
    "scripts/trust_core/mir_constructor_table.py": "scripts/check_script_tests.sh",
    # A maintenance tool, run by hand when a trust-core ledger goes stale on line
    # moves; its classify/rewrite refusals are exercised by
    # scripts/tests/trust_core_reanchor_citations_test.py, which the script-test
    # aggregate runs.
    "scripts/trust_core/reanchor_citations.py": "scripts/check_script_tests.sh",
    # D0.6 MiniRust baseline, design exit E0.8b ("D0.6 and D0.7 have 0 unmapped
    # rows", docs/design/2026-09-16-trust-core-architecture.md §5.2 Stage 0.2),
    # and the seed of D-1's divergence ledger, on the shared layer (common.py).
    # scripts/tests/trust_core_minirust_baseline_test.py loads the REAL checker by
    # path, runs it on the pinned MiniRust and Reference clones and this tree's
    # design, Core vocabulary, table, document and review registry asserting
    # every published count, and mutates copies of the MiniRust clone, the
    # table, the vocabulary, the design and the document to show each violation
    # class fails, and that a changed judgment fails until a review record
    # covers it. The `scripts.tests.suite` row runs it via
    # scripts/check_script_tests.sh, which globs scripts/tests/*_test.py; the
    # checker needs the pinned clones ($TRUST_CORE_SOURCES), so it is not a row
    # of its own, and the test FAILS, never skips, when a clone is absent.
    "scripts/trust_core/minirust_baseline.py": "scripts/check_script_tests.sh",
    # D0.2, the UB coverage matrix (design 2026-09-16 §5.2 Stage 0.2, exit E0.7:
    # "Every Reference UB bullet maps to a reason or an LD entry: 0 unmapped";
    # its Stacked-Borrows-specific list feeds E2.2.1). The checker exits non-zero
    # on any unmapped Reference unit or Miri tests/fail file, stale row, unknown
    # reason or LD id, wrong pin, or unreviewed judgment change.
    # scripts/tests/trust_core_ub_coverage_matrix_test.py loads the REAL module by
    # path, runs it on the pinned clones and this tree asserting the published
    # counts, and mutates temporary copies of every input; the
    # `scripts.tests.suite` row runs it via scripts/check_script_tests.sh.
    "scripts/trust_core/ub_coverage_matrix.py": "scripts/check_script_tests.sh",
    # The VF3 census instrument: scripts/tests/trust_core_vf3_census_test.py
    # loads the REAL module by path (spec_from_file_location + exec_module)
    # and drives it; that test runs under the `scripts.tests.suite` row.
    "scripts/trust_core/vf3_census.py": "scripts/check_script_tests.sh",
    # stack_feedback_test.py imports the real module and runs its planning,
    # custody, execution, failure and cancellation paths against stand-ins.
    # The fast-profile scripts.tests.suite aggregate executes that test module.
    "scripts/stack_feedback.py": "scripts/check_script_tests.sh",
    # The specr MiniRust-slice translator + conformance generator tree.
    # scripts/tests/trust_core_specr_regen_test.py loads regen.py by path
    # and drives its CLI (check/write) on copies of the whole specr tree;
    # regen subprocess-runs specr2clean/specr2clean.py (importing common,
    # items, emit_types, lower, emit_fns, and through them calls and
    # tyres) and conformance/select_slice.py + records2clean.py (both
    # importing mrjson). Every file below is on that executed chain (read
    # 2026-10-26; the regen test measured 17 tests OK the same day). The
    # one exception is conformance/summarize.py, which nothing runs: it is
    # in MANUAL_ONLY below.
    "scripts/trust_core/specr/regen.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/calls.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/common.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/emit_fns.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/emit_types.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/items.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/lower.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/specr2clean.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/specr2clean/tyres.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/conformance/mrjson.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/conformance/records2clean.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/specr/conformance/select_slice.py": "scripts/check_script_tests.sh",
    # D0.1, the Trust Language Decisions ledger and I-PRECEDENCE
    # (docs/design/2026-09-16-trust-core-architecture.md, Stage 0.2; the
    # invariant's enforcement is "a ledger schema check in CI; the published
    # counts (V11); a mutation fixture ... must fail"), on the shared layer
    # scripts/trust_core/common.py. scripts/tests/trust_core_language_decisions_test.py
    # loads the REAL module by path, runs it on the pinned clones (rust-lang/rfcs
    # as a full clone), this tree's design, library and tests at HEAD, the table,
    # document, snapshots and review registry asserting the published counts, and
    # mutates copies of every input so each predicate fails (a ranked source
    # outside its kind's declared search scope, a Reference admonition ranked
    # without a rule, the design's rustc-only fixture without the de-facto label,
    # a matched line with no disposition, a completion status that disagrees with
    # rfcbot); a judgment change (a role, a reason, a scope, a prose section)
    # fails REVIEW until a new review record reviews it. Exit E0.8 (the
    # OD-5 ruling) is the same checker with --require-ruled, which that test shows
    # fails while rulings are pending or conflicts remain.
    "scripts/trust_core/language_decisions.py": "scripts/check_script_tests.sh",
    # D0.7 static-semantics source map, design exit E0.8b ("D0.6 and D0.7 have
    # 0 unmapped rows", docs/design/2026-09-16-trust-core-architecture.md §5.2
    # Stage 0.2), on the shared layer scripts/trust_core/common.py.
    # scripts/tests/trust_core_static_semantics_source_map_test.py loads the
    # REAL checker by path, runs it on the committed ledger, document and review
    # registry (against the registry's git history) and the pinned FLS,
    # Reference, a-mir-formality, rust-lang/rfcs and rust-lang/rust
    # standard-library clones (all read from git objects at their pins)
    # asserting the published counts, and overlays mutated files on the pinned
    # trees and mutates copies of the ledger and the document to show each
    # predicate, and the review layer, fails. It runs under the
    # `scripts.tests.suite` row via scripts/check_script_tests.sh, which globs
    # scripts/tests/*_test.py. The checker needs the pinned clones
    # ($TRUST_CORE_SOURCES), so it is not a row of its own; the test FAILS,
    # never skips, when they are absent.
    "scripts/trust_core/static_semantics_source_map.py": "scripts/check_script_tests.sh",
    # Design exit D0.4 (docs/design/2026-09-16-trust-core-architecture.md, Stage 0.2:
    # "Retirement plan for the six semantics (RC-6), each with its exit stage") and
    # §6's freeze ("Existing ones stay only as differential oracles until their D0.4
    # exit"), built on scripts/trust_core/common.py.
    # scripts/tests/trust_core_semantics_retirement_test.py loads the REAL module by
    # path, runs it on the real tree, submodule gitlinks and pinned MiniRust clone
    # asserting the published measurements, and mutates copies of the table,
    # document and registry and overlays of repository trees to show each predicate
    # (freeze by content and change classes, host crates, namespaces, declared
    # searches, crate graph, gate rows and sources, probe, document) and the review
    # layer fail; that test runs under the `scripts.tests.suite` row via
    # scripts/check_script_tests.sh.
    "scripts/trust_core/semantics_retirement.py": "scripts/check_script_tests.sh",
    # E0.12, the Stage 0.5 denominators (docs/design/2026-09-16-trust-core-architecture.md
    # §5.2 Stage 0.5: "All published, each with its predicate: 0 denominators without one"),
    # on the shared layer scripts/trust_core/common.py. The checker maps every item of the
    # design's Stage 0.5 list to its rows, refuses a row without a predicate, a blocked row
    # without its reason and unblock condition and an input without a pin, reads the design's
    # numbers against their rows, and re-runs each record's script at the record's pin, failing
    # on any drift. scripts/tests/trust_core_denominators_test.py loads the REAL module by path,
    # runs it on the real records (every script re-measuring at its pin), the design and
    # docs/trust-core/DENOMINATORS.md asserting the published counts, and mutates copies of the
    # records, the document and the design (a drifted value, a dropped predicate, an unpinned
    # input, an unmapped design item, ...) to show each predicate fails; the
    # `scripts.tests.suite` row runs it via scripts/check_script_tests.sh.
    "scripts/trust_core/denominators.py": "scripts/check_script_tests.sh",
    # The per-record measurement scripts. scripts/trust_core/denominators.py runs each one
    # with `--check --rev <the record's pin>` (std-surface: `--check`, at its recorded commit)
    # on every run, so the same test exercises every script end to end on its real inputs;
    # the test also runs the self-tests of templates, std-surface and odt, imports from the
    # artifact cache alone, and on every host the exit-3 path (a pinned input this host does
    # not hold) of imports, std-surface, odt and the gate. odt's Rust prelude probe
    # (scripts/trust_core/denominators/odt_prelude_probe/, not a lane: no .py or .sh) is run by
    # `odt.py --probe-prelude`, which must reproduce the committed dump the gate re-reads.
    "scripts/trust_core/denominators/checkpoint-a.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/denominators/hosts.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/denominators/imports.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/denominators/odt.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/denominators/std-surface.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/denominators/templates.py": "scripts/check_script_tests.sh",
    "scripts/trust_core/denominators/ui-tests.py": "scripts/check_script_tests.sh",
    # Its only production caller is the `--compat-summary` branch of
    # scripts/check_upstream_rust_test_toolchain.sh, which the
    # slow.upstream-rust-test-toolchain row does NOT pass, so that row is not
    # its coverage. scripts/tests/validate_upstream_rust_compat_summary_test.py
    # runs the real file by path, and drives the preflight's summary branch too.
    "scripts/validate_upstream_rust_compat_summary.py": "scripts/check_script_tests.sh",
    # collect_realcode_coverage_evidence.py:38 names it as ANALYZER_REL and runs
    # it on every collection (line ~1330), and that collector is the
    # release.realcode-coverage-receipt row. Its fail-closed parsing is also
    # driven by scripts/tests/realcode_coverage_analyze_test.py.
    "scripts/realcode-coverage/analyze.py": "scripts/collect_realcode_coverage_evidence.py",
    # --- classified 2026-10-14: seven lanes red on origin/main f5fd4d81d5, three more by
    # 4d491f6103. Each link was read, not assumed, on 4d491f6103. ---
    # The SBC M0.5 corpus (docs/plans/2026-10-08-soundness-by-construction.md). Its runner,
    # scripts/trust-soundness-corpus.py:69-70 and :160, globs entries/*/entry.json under it,
    # and the runner is the `oracle.soundness-corpus` row, so the indirection ends in a row.
    "tests/trust-soundness-corpus": "scripts/trust-soundness-corpus.py",
    # Remaining Python helper of the Lean bridge audit: the bignum screen runs
    # before comparison under release.trustir-olean-vendor-identity. Tool-pair
    # admission now belongs to the compiled bridge utility and its native tests.
    # lean_olean_bignums_test.py also drives the real helper under scripts.tests.suite.
    "scripts/lean_olean_bignums.py": "scripts/regen-trustir-oleans.sh",
    # The cut's seed-publishing act. A real run needs a minted pack and, with --publish, the
    # release credential (it releases archives and pushes a branch), so it cannot be a row.
    # scripts/tests/publish_seed_cut_test.sh copies the REAL script into a fixture repository
    # and drives it end to end (a stub `targo` that must never be called, since no candidate
    # gate is asked after D27's 2026-10-17 amendment, a stub `gh`, a local bare remote: 11
    # checks of its refusals and of both acts' order); check_script_tests.sh runs it, since it
    # globs scripts/tests/*_test.sh.
    "scripts/publish_seed_cut.sh": "scripts/check_script_tests.sh",
    # A library with no entry point: recreate_bootstrap.py and mint_seed_support.py load it
    # by path (seed_host_ledger_module()). scripts/tests/dual_host_seed_ledger_test.py:22 and
    # seed_proof_bounds_test.py:20 import the REAL module and drive its admission and bound
    # checks; both run under the `scripts.tests.suite` row. (The scoped
    # `scoped.bootstrap-script-tests` row lists it in its SCOPE too, through the recreator.)
    # Measured 2026-10-14 on macOS: both tests are red under the default TMPDIR, whose
    # /var parent is a symlink the module refuses by design, and green under a
    # symlink-free TMPDIR. That red is the tests' fixture root, not this classification.
    "scripts/seed_host_ledger.py": "scripts/check_script_tests.sh",
    # The first-Linux initializer authenticates source and external archives;
    # it does not build or admit a seed. linux_root_initialization_test.py drives
    # its real CLI refusal, actual archive/Git/runtime inputs and the separate
    # initialization validator's evidence custody under scripts.tests.suite.
    "scripts/initialize_linux_root_seed.py": "scripts/check_script_tests.sh",
    "scripts/produce_linux_root_seed.py": "scripts/check_script_tests.sh",
    # The untrusted VF5 proposal driver (5cdca7e325) needs a separately built
    # prepare_vf5_inputs image, so no row runs its CLI on real inputs;
    # scripts/tests/produce_vf5_proposal_test.py drives it under scripts.tests.suite.
    "scripts/produce_vf5_proposal.py": "scripts/check_script_tests.sh",
    "scripts/seed_root_initialization.py": "scripts/check_script_tests.sh",
    # The fixed-point evidence validator (PKG-S6): a library with no entry point that
    # seed_host_ledger.py loads by path (fixed_point_module()).
    # scripts/tests/fixed_point_first_host_test.py drives every rule over a small
    # self-consistent record, and fixed_point_linux_seed_test.py drives it through the
    # producer's `record`; both run under the `scripts.tests.suite` row.
    "scripts/seed_fixed_point.py": "scripts/check_script_tests.sh",
    # The producer loads this payload-only cohort assembler. Its real inert
    # archive/channel/legacy/shared-source controls run in linux_root_cohort_test.py.
    "scripts/seed_initialization_cohort.py": "scripts/check_script_tests.sh",
    # Exact629's initialization-only surface is runtime-probed by the producer;
    # historical_seed_surface_test.py drives actual inert CLI/socket children.
    "scripts/seed_historical_surface.py": "scripts/check_script_tests.sh",
    # The linux-root producer's payload library: modules with no entry point,
    # loaded by path through __trust_source_loader__ by the producer and by
    # each other. Each is EXECUTED by a scripts/tests module (read 2026-10-26,
    # loader calls, not name mentions): linux_root_custody_test.py raw-loads
    # seed_custody_source, seed_producer_custody and seed_producer_contract
    # and drives seed_observed_events fixtures; seed_observed_commands_test.py
    # loads seed_observed_commands and seed_observed_events (each of which
    # loads seed_observed_io at module level); seed_dependency_sources_test.py
    # loads seed_dependency_git (loading seed_dependency_bytes/_objects/
    # _git_paths at module level) and seed_dependency_local;
    # linux_root_input_fixture.py + its census test load seed_input_closure
    # (loading seed_input_records/_committed/_archives), and
    # produce_linux_root_seed.py loads seed_input_closure in production. All
    # run under the `scripts.tests.suite` row. Measured 2026-10-26 on macOS:
    # the dependency/input/bootstrap-closure/vf3 tests are green;
    # linux_root_custody_test.py and seed_observed_commands_test.py error on
    # Linux-only surfaces (socket protocol, /proc/<pid>/stat) --- the same
    # environment-red family as seed_host_ledger's TMPDIR note above, not a
    # defect in this classification.
    "scripts/seed_custody_source.py": "scripts/check_script_tests.sh",
    "scripts/seed_producer_contract.py": "scripts/check_script_tests.sh",
    "scripts/seed_producer_custody.py": "scripts/check_script_tests.sh",
    "scripts/seed_observed_commands.py": "scripts/check_script_tests.sh",
    "scripts/seed_observed_events.py": "scripts/check_script_tests.sh",
    "scripts/seed_observed_io.py": "scripts/check_script_tests.sh",
    "scripts/seed_dependency_bytes.py": "scripts/check_script_tests.sh",
    "scripts/seed_dependency_git.py": "scripts/check_script_tests.sh",
    "scripts/seed_dependency_git_paths.py": "scripts/check_script_tests.sh",
    "scripts/seed_dependency_local.py": "scripts/check_script_tests.sh",
    "scripts/seed_dependency_objects.py": "scripts/check_script_tests.sh",
    "scripts/seed_input_archives.py": "scripts/check_script_tests.sh",
    "scripts/seed_input_closure.py": "scripts/check_script_tests.sh",
    "scripts/seed_input_committed.py": "scripts/check_script_tests.sh",
    "scripts/seed_input_records.py": "scripts/check_script_tests.sh",
    # A test helper, not a test: linux_root_input_fixture_census_test.py loads
    # it by path and drives its bounded checkout census; it runs under that
    # test's row. (Not *_test.py, so the aggregate's glob never names it.)
    "scripts/tests/linux_root_input_fixture.py": "scripts/check_script_tests.sh",
    # The bootstrap dependency-closure judge: recreate_bootstrap.py loads it
    # in production; scripts/tests/bootstrap_dependency_closure_test.py loads
    # the REAL module by path and drives its closure checks against
    # src/bootstrap. That test runs under the `scripts.tests.suite` row.
    "scripts/bootstrap_dependency_closure.py": "scripts/check_script_tests.sh",
    # --- classified 2026-11-10 (SCRIPTS-REDS-20261110): lanes added 2026-11-05..09
    # with no manifest row while `manifest.lane-coverage` (profile `all`) went
    # unrun. Each link below is a load CALL SITE read on 7a51dcee84, not a name
    # mention, and each test was run as check_script_tests.sh runs it (`python3
    # -B <file>`, PYTHONPATH=root, stdin /dev/null) and passed on that tree. ---
    # The citation-fact reader of the freeze gate. scripts/check_frozen_files.sh's
    # judge_side builds its path (line 635) and runs `bash "$facts_script" --repo
    # "$SIDE_ROOT" --commit "$SIDE_COMMIT"` (line 636) whenever a waiver row carries
    # ENFORCED-BY citations; the `fast.oracle-freeze` row (fast,push) runs that gate.
    # When the compiled reader is unavailable the gate says so on stderr and judges
    # with its original reader, so the citation verdict is never skipped.
    "scripts/oracle_freeze_facts.sh": "scripts/check_frozen_files.sh",
    # Normal stage0/1 x.py build/test with the recreator's bound inputs: an
    # operator wrapper over x.py. bootstrap_xpy_environment_test.py:19-21 loads
    # the REAL module by path and drives main() (lines 76, 183, 190, 207) with a
    # fixture x.py; it needs first-party/clean checked out (mint_clean_lean_inputs
    # fixture reads lean_worlds.tsv), as every full clone has.
    "scripts/bootstrap_xpy.py": "scripts/check_script_tests.sh",
    # The compiletest invocation-census reader. compiletest_census_test.py:10-11
    # imports the REAL module (SCHEMA, read_census, join_observations,
    # boolean_lane) and drives its twelve reader controls.
    "scripts/compiletest_census.py": "scripts/check_script_tests.sh",
    # Daily staging's Git object and registry CONNECT transports.
    # daily_toolchain_stage.py loads both in production (lines 566, 724);
    # daily_toolchain_stage_test.py exec()s the REAL files (daily_dependency_git.py
    # at lines 784, 845, 1080; daily_registry_proxy.py at line 1170) and copies
    # both into its staged source (lines 613-614). The test also runs under
    # `scoped.bootstrap-script-tests`, whose SCOPE lists both.
    "scripts/daily_dependency_git.py": "scripts/check_script_tests.sh",
    "scripts/daily_registry_proxy.py": "scripts/check_script_tests.sh",
    # Retained-mint revalidation, loaded by mint_and_prove_seed.sh (line 442) and
    # mint_seed_support.py (line 2087). mint_seed_recovery_test.py:17-19 loads the
    # REAL module and drives its inspect/prepare refusals (44 tests).
    "scripts/mint_seed_recovery.py": "scripts/check_script_tests.sh",
    # SDK component binders that promote-toolchain.sh runs while sealing (lines
    # 1613/1718, 1623/1726/1809). A real run mutates a new seal from separately
    # built inputs, so none can be a row. Each test loads the REAL module:
    # native_sdk_tools_test.py:13-16, sdk_frontend_component_test.py:17-19,
    # sdk_targo_component_test.py:16-20 and targo_test_budget_callers_test.py:26,
    # sdk_targo_transport_witness_test.py:15-18 and targo_test_budget_callers_test.py:27.
    "scripts/native_sdk_tools.py": "scripts/check_script_tests.sh",
    "scripts/sdk_frontend_component.py": "scripts/check_script_tests.sh",
    "scripts/sdk_targo_component.py": "scripts/check_script_tests.sh",
    "scripts/sdk_targo_transport_witness.py": "scripts/check_script_tests.sh",
    # Landed on main (316ad3890d) while this classification was in flight:
    # sdk_targo_component.py:1225 exec()s it in production
    # (_current_operational_owner), and sdk_targo_current_component_test.py:15
    # loads the REAL module (4 tests).
    "scripts/sdk_targo_current_component.py": "scripts/check_script_tests.sh",
    # Stage1 producer-image retention, run by hand right after a normal emission
    # (--repo-root/--emission-result/--host/--target/--output name that build).
    # retain_stage1_emission_test.py:15-17 loads the REAL module (20 tests).
    "scripts/retain_stage1_emission.py": "scripts/check_script_tests.sh",
    # Compiler1-owned development-image retention, run by hand after a BUILD
    # (docs/BUILD_AND_INSTALL.md). retain_development_emission_test.py:16-19
    # loads the REAL module.
    "scripts/retain_development_emission.py": "scripts/check_script_tests.sh",
}

# Lanes no row CAN name, each with the reason the interface forbids it. This is
# not a quiet-the-checker list: an entry must still exist on disk, and it errors
# once a row does name it. Listing a manual tool keeps it in the inventory —
# widening a glob past it would make it invisible again, which is the failure
# this whole file exists to catch.
MANUAL_ONLY: dict[str, str] = {
    "scripts/check_sdk_frontend.py": (
        "caller-selected exported-SDK metadata canary: requires an independent "
        "SDK root, its exact full compiler commit, and a fresh evidence directory. "
        "No manifest lane exports or selects that immutable SDK (searched scripts/ "
        "and tests/ 2026-11-03). Guessing a local stage or using this checkout's "
        "HEAD would judge another artifact and fabricate export qualification. "
        "The canary remains manually invocable and explicitly unverified; it "
        "does not replace native/runtime-closure, linking or release checks. "
        "When an SDK export lane invokes it with those exact producer inputs, "
        "move this entry to INDIRECT naming that real aggregate"
    ),
    "scripts/trust_core/specr/conformance/summarize.py": (
        "report instrument run by hand: builds a per-test table from a "
        "`clean check --json` report file and the conformance index named "
        "on its command line. Nothing in the tree invokes it (searched "
        "scripts/, tests/, docs/, first-party/clean 2026-10-26); its "
        "inputs only exist after a manual clean check run, which no row "
        "performs. If a conformance runner starts calling it, this entry "
        "must move to INDIRECT naming that aggregate"
    ),
    "scripts/seed_observed_git.py": (
        "payload library with no loader yet (read 2026-10-26): nothing in "
        "scripts/ or src/tools loads it; its only reference is "
        "seed_producer_custody.py's mandatory source-hash manifest, which "
        "hashes it as policy source for a producer stage not yet built. "
        "It has no entry point a row could run. The day a producer or a "
        "test loads it, this entry must move to INDIRECT naming that "
        "aggregate, like its seed_* siblings"
    ),
    "scripts/falsification_corpus_quick.sh": (
        "manual advisory triage against ANY caller-selected trustc (default stage1), "
        "not the release authority: records survivors/tool failures and only reports "
        "proved-case completeness gaps. Its interface does not authenticate the "
        "selected compiler or bind it to this tree; a row cannot upgrade that "
        "measurement into the separately named scripts/trust_falsification_gate.sh "
        "stage2 verdict. The release gate remains in the manifest"
    ),
    "scripts/pre_push_shadow.sh": (
        "D13 stage C shadow, not a check: scripts/hooks/pre-push launches it "
        "DETACHED after the live verdict is final, it never blocks and nothing "
        "reads its exit status (its own header); its evidence is a log for the "
        "promote-to-enforcing ruling. A gate row would make an advisory shadow "
        "a blocking lane, which D13 stages only on measured evidence"
    ),
    "scripts/prewarm_push.sh": (
        "operator landing loop, not a check: it rebases, prewarms the pre-push "
        "gate and PUSHES to origin/main; the gate it runs is scripts/hooks/pre-push, "
        "whose lanes are already rows. Running it as a lane would push on every run"
    ),
    "scripts/measure_ever_init_ladder.py": (
        "measurement instrument, not a check (T3 C01, SEAL-1): takes --stage1 (a "
        "BUILT stage1 sysroot) and compiles generated ever_init_N.rs rungs alone "
        "under taskpolicy and /usr/bin/time -l, recording footprint, RSS, wall "
        "time and stop tallies. Its subject is memory on an idle host, which no "
        "row can assert, and it needs a stage compiler the fast tier never builds"
    ),
    "scripts/vc_row_parity.py": (
        "measurement instrument, not a check (T3 C01, plan S16): builds "
        "trust-vcgen's examples/vc_row_parity_probe.rs in a parent and a candidate "
        "tree and diffs their row digests. Its subject is a PAIR of trees named on "
        "its command line (the L4/L5 landings' parents), which a row over one tree "
        "cannot supply"
    ),
    "scripts/trust_ir_cg_census.py": (
        "measurement instrument, not a check: takes --trustc (a BUILT stage "
        "sysroot's bin/trustc) and --out-dir, compiles library/core (or, with "
        "--crate alloc, library/alloc against the sysroot's core) through the "
        "trust-ir-cg backend and writes refusals.jsonl / gap_table.md for the "
        "self-host campaign (docs/campaigns/2026-09-10-selfhost-trust-ir-cg.md, "
        "G3). Its docstring says a crate that compiles is NOT evidence, so it "
        "carries no verdict a row could assert, and it needs a stage compiler "
        "the fast tier never builds. Its harness logic (dep resolution, static "
        "roots, the tracked diag-json option, reparse nulls) is pinned offline "
        "by scripts/tests/trust_ir_cg_census_test.py, which the suite runs"
    ),
    "scripts/tests/lean_island_census_live.py": (
        "measurement driver, not a check; exercised through its adjacent "
        "*_live_test.py mocks, which the aggregate runs; live use needs "
        "--trustc/--out"
    ),
    "scripts/tests/rust_instance_census_live.py": (
        "measurement driver, not a check; exercised through its adjacent "
        "*_live_test.py mocks, which the aggregate runs; live use needs "
        "--trustc/--out"
    ),
    "scripts/seal_line_audit.py": (
        "check of a dated record against a commit no clone of origin holds (SEAL-1 clause 4, "
        "SEAL-1-P5A): it re-derives docs/audits/2026-10-17-seal-line-audit.tsv from "
        "`git rev-list dfd8b72138d..321aaeda754`, and the seal 321aaeda754 is reachable only "
        "from m3's local tag atpkg-trust-9192-seal or the preserve bundle "
        "(~/trust-seal-preserve/seal-321aaeda7.bundle, the audit's section 7). A fresh clone "
        "has neither, so a row would fail on a missing object, not on the record. Git only; "
        "its 2026-10-17 run is quoted in the audit, and no offline self-test drives it"
    ),
    # --- classified 2026-11-10 (SCRIPTS-REDS-20261110); each file read on 7a51dcee84 ---
    "scripts/check_primitive_decimal_component.py": (
        "caller-selected exported-SDK component check, the same class as "
        "check_sdk_frontend.py: every one of --sdk, --sdk-inventory, "
        "--sdk-inventory-sha256, --cargo-inputs, --wrapper, --build-slot and "
        "--expected-compiler is required and names an immutable SDK root, its "
        "byte inventory and the full compiler commit its trustc must report; it "
        "also requires a clean committed tree and the pinned Lean under aterm's "
        "package store. No manifest lane exports or selects that SDK (searched "
        "scripts/ and tests/ 2026-11-10), and guessing a local stage would judge "
        "another artifact. Its Rust controls (scripts/tests/primitive_decimal_component.rs) "
        "compile only inside that SDK view. When an SDK export lane invokes it with "
        "those exact inputs, move this entry to INDIRECT naming that aggregate"
    ),
    "scripts/compiletest_census_smoke.py": (
        "real-compiler qualification driver, not a self-test: --compiletest, "
        "--rustc, --sysroot and a fresh --out are required, and the compiletest "
        "binary must be a Trust build carrying --trust-invocation-census. No lane "
        "builds or names a compiletest binary (the compiletest suites run through "
        "x.py, which builds its own), and nothing in the tree invokes this file "
        "(searched 2026-11-10). The census READER it asserts over is "
        "scripts/compiletest_census.py, which the script-test aggregate drives "
        "through compiletest_census_test.py"
    ),
    "scripts/trust_core/asl1/build_exporter.py": (
        "producer build, not a check: fetches 64 pinned ASLRef files through Agh "
        "(network) and builds the external OCaml exporter with an owned host-tool "
        "prefix (OCaml 4.14.2, Dune, Menhir, Zarith, GMP) named by --tool-bin and "
        "--library-dir, into fresh --source-dir/--build-dir paths. No lane "
        "provisions that prefix (scripts/trust_core/asl1/README.md). The committed "
        "source custody it relies on is rowed: fast.asl1-reference-custody runs "
        "scripts/trust_core/asl1/check_reference.py"
    ),
    "scripts/trust_core/asl1/producer_controls.py": (
        "native producer controls over a caller-built exporter: --producer must "
        "name the exporter.exe that build_exporter.py (manual, above) produced and "
        "--out a fresh path; no lane builds that producer. It runs the producer on "
        "the 13 committed fixtures/*.asl cases and compares its output with the "
        "committed fixtures/packets/*.bin and Asl1/WireFixtures.lean bytes, so "
        "without the producer there is nothing to compare. The committed source "
        "custody is rowed: fast.asl1-reference-custody"
    ),
}

# Documents that name a test as the thing keeping them true, mapped to that
# test's file and the cargo package that owns it. A claim of the form "this test
# fails if the document drifts" is worth exactly as much as whatever runs the
# test, and docs/TCB.md carried that claim while its test sat in no manifest row
# at all (found 2026-07-25). Both halves are closed here: the document must
# still name the file, and some row must run it. A cargo test target is
# addressed by package plus `--test` selector rather than by path, so this class
# is matched on the selector instead of the literal-path rule used above.
DOC_ENFORCEMENT_LANES: dict[str, tuple[str, str]] = {
    "docs/TCB.md": (
        "crates/trust-integration-tests/tests/tcb_document_exhaustiveness.rs",
        "trust-integration-tests",
    ),
}

# Compiletest suites are directories under `tests/`; these are not suites.
NON_SUITE_TEST_DIRS = {
    "__pycache__",  # interpreter droppings; reporting it trains readers to ignore the red
    "auxiliary",
    "compat",
    "crashes",
    "fixtures",
    # Targo test plans (`targo test --plan tests/test-plans/<lane>.toml`), not a
    # compiletest suite. Targo's own test ops::cargo_test::plan_checked_in
    # (targo-core/src/ops/cargo_test/plan_checked_in.rs) holds each plan to the tree.
    "test-plans",
    # One `.baseline` ledger, consumed by rowed lanes (trust_self_verify_crate.sh,
    # trust_certified_scoreboard.py); `x.py test tests/self-proof` is not a thing.
    # Written down 2026-08-26 because it would otherwise read covered by ACCIDENT:
    # coverage is a substring test, and `release.certified-scoreboard` names
    # `tests/self-proof/certified-scoreboard.baseline`, which contains the
    # directory path. A silent green is the failure this whole file exists to
    # catch, so the exemption is stated rather than collected.
    # A committed CONTROL CORPUS (four native-bundle dumps), not a compiletest
    # suite: `slow.call-summary-census` runs the script that reads it, and that
    # script fails on zero summaries or zero declines, so the corpus is guarded
    # by a rowed lane rather than by being one.
    "trust-call-summary-census",
    "self-proof",
    # Script collections and ledgers, not compiletest suites — `x.py test <dir>`
    # is meaningless for all five. Each RUNNER is rowed instead (`suites.*`), so
    # the lane runs; only the directory-as-suite reading is dropped. Measured
    # 2026-08-27, each by running it: ledger 0, trust-contract 0/0/0,
    # provability-ratchet 0, e6-fragment-probe 1 (toolchain != HEAD),
    # two-language-battery 1 (1 error of 11). The two reds are rowed RED on
    # purpose — rowing only the green ones would be picking the score.
    "e6-fragment-probe",
    # A plan for `targo test --plan`, not a compiletest suite. targo-core's
    # `plan_checked_in` unit tests hold every name in it to the tree, and the
    # land gate's `native-targo-tests` leg (`x.py test --stage 1
    # src/tools/targo`) runs them.
    "test-plans",
    "known-red",  # known-red baselines, each consumed by its ratchet (rustc_mir_transform.txt and rustc_codegen_trust_cg.txt: the unit-suite ratchet; crates-tests.txt: check_crates_tests_scoped.py)
    "ledger",
    "trust-contract",
    "trust-provability",
    "two-language-battery",
    "trust-added",
    "trust-comprehensive",
    "trust-elide",
    "trust-falsification",
    "trust-witness",
    "upstream-rust",
}


def manifest_rows() -> list[list[str]]:
    """The manifest rows, read out of `emit_gate_manifest`'s quoted heredoc.

    Read rather than executed: the harness runs gates when sourced, and this
    check must be able to inspect the manifest without running anything.
    """
    text = HARNESS.read_text(encoding="utf-8")
    start = text.index("emit_gate_manifest() {")
    body = text[text.index("<<'EOF'", start) + len("<<'EOF'") : text.index("\nEOF\n", start)]
    return [line.split("|") for line in body.strip("\n").split("\n") if line.strip()]


def active_divergences(text: str) -> list[tuple[str, str]]:
    """`(id, gate_id)` for every `status = "active"` row of the divergence ledger.

    Read with a line-anchored scan rather than `tomllib`: the manifest row runs
    this checker as bare `python3`, which is the 3.9 CommandLineTools build on a
    macOS box, and the ledger is one `key = "value"` per line with no multi-line
    strings. Only `active` rows are returned because the harness's
    `matching_divergences` matches only those; a retired row keeps its
    historical gate_id as part of the record and is not checked.
    """
    rows = []
    for block in re.split(r"^\[\[divergences\]\]\s*$", text, flags=re.MULTILINE)[1:]:
        fields = dict(re.findall(r'^(id|gate_id|status) = "([^"]*)"', block, re.MULTILINE))
        if fields.get("status") == "active":
            rows.append((fields.get("id", "<no id>"), fields.get("gate_id", "<no gate_id>")))
    return rows


def divergence_gate_errors(rows: list[list[str]], ledger_text: str) -> list[str]:
    """An active quarantine must name a gate id that is a manifest row."""
    manifest_ids = {row[0] for row in rows if len(row) == 6}
    return [
        f"divergence {div_id} names gate_id {gate_id}, which is no manifest row — "
        "a quarantine that can never match is not a quarantine"
        for div_id, gate_id in active_divergences(ledger_text)
        if gate_id not in manifest_ids
    ]


def lane_inventory() -> dict[str, list[Path]]:
    """Every runnable lane in the tree, grouped by the class it belongs to."""
    tests = REPO_ROOT / "tests"
    scripts = REPO_ROOT / "scripts"
    inventory: dict[str, list[Path]] = {
        "e2e": sorted(tests.glob("e2e_*.sh")),
        # Gates, canaries and lanes. A canary is exactly the artifact this checker
        # exists for: `trust_control_canary.sh` was written because the `is_whnf`
        # mint gate sat closed for a month with no instrument reporting it.
        # The pattern was `trust_*_gate.sh` until 2026-08-26, which missed
        # `prove-trust-frontend-gate.sh` and `submodule-coherence-gate.sh` — the
        # same blind-spot class as the orphaned oracles, one character wide
        # (HYPHEN, not underscore). Match the suffix, never a project prefix.
        "gate-script": sorted(
            {
                p
                for suffix in ("gate", "canary", "lane")
                for sep in ("_", "-")
                for p in scripts.rglob(f"*{sep}{suffix}.sh")
                if p.parent != scripts / "tests"
            }
        ),
        # The `scripts/check_*` family: the freeze gate, the provenance gate,
        # the pin/patch/lock coherence gates, the ratchets. This class was
        # MISSING until 2026-08-22, and it is the class most of this repo's
        # soundness gates live in — so the checker whose whole job is "a lane
        # that exists but appears in no manifest row is a lane nobody runs"
        # could not see them. Measured the day it was added: of 24 checkers,
        # 11 were named by a row, 4 more are reached through a named aggregate
        # (INDIRECT above), and NINE were named by nothing at all. Five of the
        # nine were RED when first run — including scripts/check_patch_binds.py,
        # which reports the ay-chc patch UNBOUND (manifest 0.13.0 vs Cargo.lock
        # 0.10.0), i.e. `--locked` cannot hold for that patch and the resolver
        # silently falls back to the original git rev.
        "checker": sorted(
            list(scripts.glob("check_*.sh")) + list(scripts.glob("check_*.py"))
        ),
        # Adversarial oracles: generate programs, compare a verdict against
        # RUNTIME TRUTH. Measured 2026-08-26 — FIVE named by nothing (the four
        # known ones plus scripts/differential/), `trust_falseproof_search.py`
        # dormant since 2026-08-01 while the 2026-08-21 vacuous-hypothesis false
        # proof sat live (`i += 100` modelled as `x == x + 100`, UNSAT, so every
        # obligation in the block proved); that search finds it in ~15 min.
        # Globs stay loose and recursive: the failure mode is the NEXT oracle
        # landing outside the pattern, not these five.
        "oracle": sorted(
            {
                p
                for pattern in (
                    "*oracle*.py", "*oracle*.sh",
                    "*_search.py", "*_search.sh",
                    "*soundness*.py", "*soundness*.sh",
                    "*fuzz*.py", "*fuzz*.sh",
                    "*differential*.py", "*differential*.sh",
                )
                for p in scripts.rglob(pattern)
                if p.parent != scripts / "tests"  # owned by `script-test` below
            }
        ),
        "script-test": sorted(
            p for p in scripts.glob("tests/*") if p.suffix in (".py", ".sh")
        ),
        "witness": sorted((tests / "trust-witness").glob("*.py")),
        "elide": sorted((tests / "trust-elide").glob("*.py")),
        "suite": sorted(
            p
            for p in tests.iterdir()
            if p.is_dir() and p.name not in NON_SUITE_TEST_DIRS
        ),
        "orchestrator": sorted(tests.glob("run_trust_*_suite.sh")),
    }
    # `tests/crashes` is a compiletest suite despite sitting in the exclusion
    # list above, which exists to keep ledger and fixture directories out.
    inventory["suite"].append(tests / "crashes")
    inventory["suite"].sort()

    # CATCH-ALL. Every class above matches on a NAME, so every class above has a
    # next blind spot: `check_*` missed the oracles, `trust_*_gate.sh` missed the
    # two hyphenated gates. Measured 2026-08-26 — 168 scripts under scripts/, 128
    # inventoried, FORTY invisible. Sweep whatever the named classes did not claim
    # so a lane can never hide by being spelled differently; the escape hatch is a
    # written reason (MANUAL_ONLY / INDIRECT), never a silent glob miss.
    claimed = {p for lanes in inventory.values() for p in lanes}
    inventory["unclassified"] = sorted(
        p
        for p in list(scripts.rglob("*.sh")) + list(scripts.rglob("*.py"))
        if p not in claimed
        and p.parent != scripts / "tests"
        and "__pycache__" not in p.parts
        and not _is_tooling(p.relative_to(REPO_ROOT).as_posix())
    )
    return inventory


# Roles that are NOT lanes: they are invoked BY a lane, by git, or by a human
# setting a machine up, and none of them can pass or fail. Exempted by ROLE with a
# written reason rather than by silently widening a glob — the same discipline as
# MANUAL_ONLY, and reviewable in one place. Anything not matched here is a lane
# until someone says otherwise in writing.
TOOLING_ROLES: tuple[tuple[str, str], ...] = (
    ("scripts/lib/", "sourced by other scripts; not independently runnable"),
    ("scripts/hooks/", "hook bodies; git runs them, and pre-push derives its lanes from the manifest's push profile"),
    ("scripts/hooks-pin/", "ditto, the narrow pin-only hook set"),
    ("scripts/install-", "one-shot machine setup, run by a human"),
    ("scripts/dev-", "developer convenience wrappers around x.py"),
    ("scripts/build-", "build drivers and memory governors, not verdict-bearing"),
    ("scripts/__init__.py", "package marker"),
    ("scripts/fetch-first-party.sh", "materializes sibling repos for a standalone clone; no verdict"),
    ("scripts/promote-toolchain.sh", "seals and channel-flips a built stage2; mutating promotion, no verdict"),
    (
        "scripts/freeze_toolchain_sources.py",
        "mutating promotion helper that writes a committed source snapshot; no compiler or proof verdict; "
        "its Git and confinement controls run in the scoped bootstrap-script lane",
    ),
    (
        "scripts/prune_seal_symlinks.py",
        "mutating helper called by promote-toolchain.sh on a newly copied seal; "
        "removes escaping links, does not check a gate; its controls run in the script-test aggregate",
    ),
    (
        "scripts/lean_island_census.py",
        "measurement-only census reader: preserves failed and partial compiler observations; "
        "nonzero exits reject malformed transcripts, not language or product acceptance; "
        "its controls run in the script-test aggregate",
    ),
    (
        "scripts/rust_instance_census.py",
        "measurement-only census reader: parses the independent actual-collector census and "
        "never awards G1 completeness; nonzero exits reject malformed input or invocation, "
        "not product acceptance; its controls run in the script-test aggregate",
    ),
    (
        "scripts/dispatch_cost.py",
        "measurement-only: prints the GPU dispatch round trip of one Apple-silicon machine at "
        "one moment (docs/STATUS.md \"Dispatch cost\") and is no input to any verdict; nonzero "
        "exits reject a failed probe, malformed probe output or an unsupported host, not "
        "product acceptance; its controls run in the script-test aggregate",
    ),
    # --- classified 2026-08-26, from the catch-all sweep ---
    # EXACT PATHS, not families, even where the ROLE is shared: `_is_tooling`
    # matches by prefix, and every tempting family prefix here would swallow a
    # future gate. `scripts/trust_ir_` covers reporters AND three verdict
    # lanes (flip-burnin, frontier-table, lineage-reconcile); `scripts/trust-`
    # covers two wrappers today and anything tomorrow. A shared ROLE is recorded
    # by repeating one reason across the paths that share it, which reviews the
    # same and cannot go blind. Widening any of these to a directory or a stem
    # recreates the exact blind spot this file exists to close.
    #
    # Mutating bootstrap/seed materialization: each one PRODUCES a toolchain.
    ("scripts/create_local_genesis_stage0.py", "mutating bootstrap/seed materialization; produces a toolchain, judges nothing"),
    ("scripts/recreate_bootstrap.py", "mutating bootstrap/seed materialization; produces a toolchain, judges nothing"),
    (
        "scripts/seed_staircase.py",
        "mutating bootstrap/seed materialization: hours-long x.py rungs from the pinned seed that "
        "produce a toolchain; its admission refusals are inputs to a human-run build, not a gate "
        "verdict; its controls run in the script-test aggregate",
    ),
    (
        "scripts/linux_refresh_toolchain.py",
        "mutating bootstrap/seed materialization: drives seed_staircase.py through one hours-long rung "
        "on a Linux host, optionally a second build and a no-flip seal; its refusals are inputs to a "
        "human-run build, not a gate verdict; its controls run in the script-test aggregate",
    ),
    (
        "scripts/fixed_point_linux_seed.py",
        "mutating bootstrap/seed materialization: prepares a neutral root and drives seed_staircase.py "
        "through the hours-long builds of one commit on a Linux host that differ only in stage 0, and "
        "its dist; it records what a later validator judges, commits the add-host branch in a clone "
        "under its root, judges a clone of that branch with the branch's own scripts and uploads the "
        "archives (never pushing); its refusals are inputs to a human-run build and landing, not a gate "
        "verdict; its controls run in the script-test aggregate",
    ),
    ("scripts/seed_stage0_after_tests.sh", "mutating bootstrap/seed materialization; produces a toolchain, judges nothing"),
    ("scripts/win-genesis/win_genesis.py", "mutating bootstrap/seed materialization; produces a toolchain, judges nothing"),
    # Argv-dispatch helpers owned by one shell driver each.
    ("scripts/mint_seed_support.py", "subcommand helper for one shell driver; no standalone verdict"),
    ("scripts/off_stock_rust_audit.py", "subcommand helper for one shell driver; no standalone verdict"),
    # Build plumbing: they forward the wrapped command's status or record a number.
    ("scripts/cargo-concurrency-cap.sh", "build plumbing: wrappers, locks and samplers that forward or record"),
    ("scripts/monitor-build-memory.sh", "build plumbing: wrappers, locks and samplers that forward or record"),
    ("scripts/run_measurement_sweep.sh", "build plumbing: wrappers, locks and samplers that forward or record"),
    ("scripts/trust_survey.sh", "build plumbing: wrappers, locks and samplers that forward or record"),
    (
        "scripts/trust_fast_iterate.sh",
        "developer build driver: mutates an existing stage1 tree, then optionally forwards "
        "caller-selected test paths to x.py; no fixed corpus or independent gate verdict",
    ),
    # Analysis instruments. Each prints a table to rank the next slice; the only
    # nonzero exits are input errors. If one of these numbers should be
    # ENFORCED, the gate is a threshold over the artifact these emit, not these.
    (
        "scripts/trust_core/specr/conformance/summarize.py",
        "formats a supplied Clean report and theorem index into per-test JSON; "
        "reports failed rows but sets no acceptance threshold or failure exit",
    ),
    ("scripts/trust_upstream_test_inventory.py", "analysis report; nonzero only on bad input, never a verdict"),
    (
        "scripts/machine_preflight.sh",
        "host-fitness report: judges THIS MACHINE (orphaned hogs, wedged cargo locks, disk, "
        "submodule lock drift), not the tree; its exit depends on other processes on the "
        "host, so no row could assert it",
    ),
    # The rest, one role each.
    ("scripts/generate_mir_fixtures.sh", "regenerates checked-in MIR fixtures; a generator, not a verdict"),
    (
        "scripts/trust_platform/regen_census_fixtures.sh",
        "regenerates trust-platform-census's checked-in trust-ir dumps from a named --trustc "
        "and rewrites tests/ir; a generator, not a verdict. Its output is judged by "
        "crates/trust-platform-census/tests/dump_provenance.rs, which reads its REGEN_NAMES",
    ),
)


def _is_tooling(rel: str) -> bool:
    return any(
        rel.startswith(pattern) if pattern.endswith(("/", "-")) else rel == pattern
        for pattern, _reason in TOOLING_ROLES
    )


def _named_by(rel: str, commands: str) -> bool:
    """True when some row's command names `rel` as a WHOLE path, not a prefix.

    Coverage was a bare substring test until 2026-08-26, which is fail-OPEN for a
    directory lane: a row naming `tests/self-proof/certified-scoreboard.baseline`
    marked the whole `tests/self-proof` SUITE covered, though nothing runs it as a
    suite. Running one file inside a directory is not running the directory.
    """
    return re.search(re.escape(rel) + r"(?![\w./-])", commands) is not None


PRE_PUSH_HOOK = "scripts/hooks/pre-push"


PUSH_REFS_ENV = "TRUST_PUSHED_REFS"

# A command token that is a gate script: the check scripts are the readers, and
# the landing gate's subcommands that judge the pushed commits when the variable
# is set (`land_gate.py rows --check`, fast.land-rows-coverage). Only those
# subcommands: land_gate.py names the variable for push-rows too, so a push row
# running any other subcommand is not presumed to read the push.
# New checks are land_gate.py subcommands, not new scripts/check_* files.
_CHECK_SCRIPT = re.compile(r"^scripts/(?:check_[\w.-]+\.(?:py|sh)|land_gate\.py)$")
_LAND_GATE = "scripts/land_gate.py"
_LAND_GATE_PUSH_READERS = frozenset({"rows"})
# A self-test invocation of a check script builds its own scratch world and is
# not a reader of the push in flight.
_SELF_TEST_FLAG = re.compile(r"^--self[\w-]*$")


def push_refs_reader_gate_ids(rows: list[list[str]], root: Path = REPO_ROOT) -> list[str]:
    """The `push` rows that read TRUST_PUSHED_REFS, in manifest order.

    A row reads it when its command runs a `scripts/check_*` script (or a
    scripts/land_gate.py subcommand in _LAND_GATE_PUSH_READERS) whose source
    names TRUST_PUSHED_REFS, unless that invocation is the script's
    self-test. Some of these rows opt in with `--push-context`; others take no
    flag and read the variable whenever it is set, so the flag alone misses
    them (measured 2026-09-28: it found half).

    This set is DERIVED from the manifest and the scripts it runs.
    scripts/hooks/pre-push prints it on every run (via `--push-refs-readers`),
    and nothing else may keep a copy of it.
    """
    readers = []
    for row in rows:
        if len(row) != 6 or "push" not in row[1].split(","):
            continue
        tokens = row[5].split()
        if any(_SELF_TEST_FLAG.match(token) for token in tokens):
            continue
        scripts = [(i, token) for i, token in enumerate(tokens) if _CHECK_SCRIPT.match(token)]
        if not scripts:
            continue
        at, first = scripts[0]
        subcommand = tokens[at + 1] if at + 1 < len(tokens) else ""
        if first == _LAND_GATE and subcommand not in _LAND_GATE_PUSH_READERS:
            continue
        script = root / first
        try:
            text = script.read_text(encoding="utf-8")
        except OSError:
            continue
        if PUSH_REFS_ENV in text:
            readers.append(row[0])
    return readers


def pre_push_hook_errors(rows: list[list[str]], hook_text: str, root: Path = REPO_ROOT) -> list[str]:
    """The pre-push hook derives its lanes; it keeps no second copy of any set.

    Behavior checks on what the hook DOES, not on its comment prose:

    * A literal `run_lane <id>` anywhere duplicates the `push` profile.
    * The hook must derive its lane list from the manifest: an actual
      `--list push` invocation of the harness. Without it the lane set comes
      from somewhere this checker cannot see.
    * The hook must export TRUST_PUSHED_REFS, or the lanes that judge the
      pushed refs silently judge the checkout instead.
    * The hook must derive the TRUST_PUSHED_REFS reader set by invoking this
      checker with `--push-refs-readers`; its inherited-red grading consumes
      that variable, so a hand-written value is a second inventory.
    * The hook must not name two or more distinct derived readers anywhere:
      naming the set IS copying it, and the copy went stale again and again
      (2026-08-30 to 2026-09-28) because nothing compared it with the
      manifest. One lane named for lane-specific behavior (a scheduling or
      overlap special case) is not a copy of the set.

    The pre-2026-11-03 rule policed a `# PUSH CONTEXT.` comment section by
    heading and counted number words inside it; it went stale when the hook
    header was rewritten on 2026-11-02, while every
    behavior above was unchanged. Prose is not policed anymore.
    """
    errors = []
    readers = push_refs_reader_gate_ids(rows, root)
    lines = hook_text.splitlines()
    if not re.search(r"--list\s+push\b", hook_text):
        errors.append(
            f"{PRE_PUSH_HOOK}: does not derive its lanes from the gate manifest "
            "(`--list push`); the manifest's `push` profile is the only lane list"
        )
    if not re.search(r"^\s*export\s+TRUST_PUSHED_REFS=", hook_text, re.MULTILINE):
        errors.append(
            f"{PRE_PUSH_HOOK}: does not export TRUST_PUSHED_REFS; the lanes that "
            "judge the pushed refs would judge the checkout instead"
        )
    if "check_gate_lane_coverage.py --push-refs-readers" not in hook_text:
        errors.append(
            f"{PRE_PUSH_HOOK}: does not derive the TRUST_PUSHED_REFS reader set "
            "(`check_gate_lane_coverage.py --push-refs-readers`); that set is "
            "derived from the manifest and the scripts it runs, never listed"
        )
    for n, line in enumerate(lines, 1):
        if re.match(r"\s*run_lane\s+[A-Za-z]", line):
            errors.append(
                f"{PRE_PUSH_HOOK}:{n}: run_lane with a literal gate id; the `push` "
                "profile in the gate manifest is the only lane list"
            )
    named = [
        gate_id
        for gate_id in readers
        # Bounded on both sides: `xfast.foo` or `self-fast.foo` is a
        # different token, and `fast.foo-selftest` a different id.
        if re.search(r"(?<![\w.-])" + re.escape(gate_id) + r"(?![\w-])", hook_text)
    ]
    if len(named) >= 2:
        errors.append(
            f"{PRE_PUSH_HOOK}: names {len(named)} lanes that read "
            f"TRUST_PUSHED_REFS ({', '.join(named)}); that set is derived "
            "(`--push-refs-readers`) and the hook prints it, so a copy can "
            "only drift"
        )
    return errors


def native_admission_gate_errors(rows: list[list[str]]) -> list[str]:
    """Keep real native qualification distinct from its fast oracle controls.

    Profiles: the oracle controls run in `fast` and `release` and are not yet
    a per-push check (a defect, docs/STATUS.md); the census itself stays
    `release`-only with its
    exact immutable-provenance command. Neither row may go optional.
    """
    required = (
        ("fast.native-admission-oracle-tests", "fast,release", "script-tests",
         "python3 tests/native-admission-census/test_run.py"),
        ("release.native-admission-census", "release", "resource-attribution",
         "python3 tests/native-admission-census/run.py --bin build/host/stage2/bin "
         "--verify-stage-provenance"),
    )
    errors = []
    for gate_id, profiles, category, command in required:
        matches = [row for row in rows if len(row) == 6 and row[0] == gate_id]
        if len(matches) != 1:
            errors.append(f"{gate_id}: must have exactly one manifest row")
        elif (matches[0][1], matches[0][2], matches[0][3], matches[0][5]) != (
            profiles, category, "true", command
        ):
            errors.append(f"{gate_id}: required profiles and exact qualification command changed")
    return errors


def check() -> tuple[list[str], list[str]]:
    errors: list[str] = []
    uncovered: list[str] = []
    rows = manifest_rows()
    if not rows:
        return (["gate manifest is empty"], [])
    errors.extend(native_admission_gate_errors(rows))
    errors.extend(divergence_gate_errors(rows, DIVERGENCES.read_text(encoding="utf-8")))

    today = datetime.now(timezone.utc).date()
    seen_ids: set[str] = set()
    for row in rows:
        if len(row) != 6:
            errors.append(f"row has {len(row)} columns, expected 6: {'|'.join(row)}")
            continue
        gate_id, profiles, _category, required, last_green, _command = row
        if gate_id in seen_ids:
            errors.append(f"{gate_id}: duplicate gate id")
        seen_ids.add(gate_id)
        for profile in profiles.split(","):
            if profile not in KNOWN_PROFILES:
                errors.append(f"{gate_id}: unknown profile {profile!r}")
        if required not in ("true", "false"):
            errors.append(f"{gate_id}: required must be true/false, got {required!r}")
        if last_green != "never":
            if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", last_green):
                errors.append(
                    f"{gate_id}: last_green must be `never` or ISO date, got {last_green!r}"
                )
            else:
                recorded = date.fromisoformat(last_green)
                if recorded > today:
                    errors.append(
                        f"{gate_id}: last_green {last_green} is in the future; a gate "
                        "cannot have passed on a day that has not happened"
                    )

    # This is the product-completion claim, not merely a script covered by the
    # script-test aggregate. Keep its release invocation exact enough that a
    # renamed profile, optional row, or omitted external trust root cannot make
    # the production gate disappear while lane coverage stays green.
    completion_rows = [
        row for row in rows if len(row) == 6 and row[0] == "release.two-language-completion"
    ]
    if len(completion_rows) != 1:
        errors.append(
            "release.two-language-completion: must have exactly one manifest row"
        )
    else:
        _gate_id, profiles, category, required, _last_green, command = completion_rows[0]
        if profiles != "release":
            errors.append(
                "release.two-language-completion: profiles must be exactly `release`"
            )
        if category != "soundness":
            errors.append(
                "release.two-language-completion: category must be `soundness`"
            )
        if required != "true":
            errors.append("release.two-language-completion: must be required")
        expected_command = (
            'TRUST_TOP_VERIFIER_PATH="${TRUST_TWO_LANGUAGE_TOP_VERIFIER:-'
            '/etc/trust/two_language_completion_gate.py}" && '
            'test -n "${TRUST_TWO_LANGUAGE_TOP_VERIFIER_SHA256:-}" && '
            'TRUST_TOP_VERIFIER_ACTUAL="$(/usr/bin/shasum -a 256 '
            '"$TRUST_TOP_VERIFIER_PATH")" && '
            'test "${TRUST_TOP_VERIFIER_ACTUAL%% *}" = '
            '"${TRUST_TWO_LANGUAGE_TOP_VERIFIER_SHA256}" && '
            'python3 "$TRUST_TOP_VERIFIER_PATH" --candidate-verifier '
            'scripts/two_language_completion_gate.py --receipt '
            '"${TRUST_TWO_LANGUAGE_COMPLETION_RECEIPT:-build/two-language-completion/receipt.json}" '
            '--root . --trusted-owner-key '
            '"${TRUST_TWO_LANGUAGE_OWNER_KEY:-/etc/trust/two-language-owner.pub}"'
        )
        if command != expected_command:
            errors.append(
                "release.two-language-completion: command must be exactly the "
                "externally pinned, owner-keyed production completion invocation"
            )

    # scripts/hooks/pre-push derives its whole lane set from `--list push`, so an
    # empty push profile is a gate that reports GREEN having run nothing, and a
    # literal `run_lane <id>` there is the hand-maintained second inventory this
    # collapse removed — two lane sets agreeing only by eye.
    if not [r for r in rows if len(r) == 6 and "push" in r[1].split(",")]:
        errors.append(
            "no row carries the `push` profile; scripts/hooks/pre-push derives its "
            "lanes from it and a gate with no lanes is not a green gate"
        )
    hook_path = REPO_ROOT / PRE_PUSH_HOOK
    if not hook_path.exists():
        errors.append(f"{PRE_PUSH_HOOK}: the installed pre-push gate is gone")
    else:
        errors.extend(pre_push_hook_errors(rows, hook_path.read_text(encoding="utf-8")))

    command_list = [row[-1] for row in rows if len(row) == 6]
    commands = "\n".join(command_list)
    for aggregate in INDIRECT.values():
        if aggregate not in commands:
            errors.append(
                f"{aggregate} is the declared aggregate for an indirect lane class "
                "but no manifest row runs it"
            )

    for lane, reason in MANUAL_ONLY.items():
        if not (REPO_ROOT / lane).exists():
            errors.append(f"{lane}: declared manual-only, but the file is gone")
        elif lane in commands:
            errors.append(
                f"{lane}: a manifest row runs it, so the MANUAL_ONLY exemption "
                f"({reason}) no longer holds; drop the entry"
            )

    for lane_class, lanes in lane_inventory().items():
        for lane in lanes:
            rel = lane.relative_to(REPO_ROOT).as_posix()
            if _named_by(rel, commands):
                continue
            # The whole `tests/e2e_*.sh` corpus runs under run_e2e_shell_corpus.sh.
            if lane_class == "e2e":
                continue
            # scripts/check_script_tests.sh globs exactly `*_test.py` and
            # `*_test.sh`; anything else under scripts/tests/ is NOT run by the
            # aggregate and must be named by a row or written down below.
            if lane_class == "script-test" and lane.name.endswith(("_test.py", "_test.sh")):
                continue
            if rel in INDIRECT or rel in MANUAL_ONLY:
                continue
            uncovered.append(f"{lane_class}: {rel}")

    for doc, (test_path, package) in DOC_ENFORCEMENT_LANES.items():
        doc_file = REPO_ROOT / doc
        test_file = REPO_ROOT / test_path
        if not doc_file.exists():
            errors.append(f"{doc}: declared doc-enforcement lane, but the document is gone")
            continue
        if not test_file.exists():
            errors.append(f"{doc}: enforcing test {test_path} does not exist")
            continue
        if test_path not in doc_file.read_text(encoding="utf-8"):
            errors.append(
                f"{doc}: no longer names {test_path} as the test that keeps it true; "
                "either restore the claim or drop the pair from DOC_ENFORCEMENT_LANES"
            )
        selector = f"--test {test_file.stem}"
        if not any(
            selector in command and f"-p {package}" in command for command in command_list
        ):
            uncovered.append(f"doc-enforcement ({doc}): {test_path}")

    return (errors, uncovered)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--list-uncovered",
        action="store_true",
        help="Print uncovered lanes and exit 0; for triage, not for gating.",
    )
    parser.add_argument(
        "--push-refs-readers",
        action="store_true",
        help="Print the push rows that read TRUST_PUSHED_REFS, space-separated, "
        "and exit 0; scripts/hooks/pre-push prints this on every run.",
    )
    args = parser.parse_args()

    if args.push_refs_readers:
        print(" ".join(push_refs_reader_gate_ids(manifest_rows())))
        return 0

    errors, uncovered = check()

    if args.list_uncovered:
        for lane in uncovered:
            print(lane)
        return 0

    if errors:
        print("GATE MANIFEST MALFORMED:", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
    if uncovered:
        print("LANES IN NO MANIFEST ROW:", file=sys.stderr)
        for lane in uncovered:
            print(f"  {lane}", file=sys.stderr)
        print(
            "\nEach lane above exists in the tree and no gate runs it. Add a row to\n"
            "`emit_gate_manifest` in tests/run_trust_comprehensive_harness.sh, or add\n"
            "the lane to `INDIRECT` naming the aggregate that already runs it. Only\n"
            "a lane whose interface cannot be a row belongs in `MANUAL_ONLY`, with\n"
            "the reason written down.",
            file=sys.stderr,
        )
    if errors or uncovered:
        return 1

    print(
        "GATE LANE COVERAGE OK: every e2e, gate script, adversarial oracle, script "
        "test, witness/elide regression, compiletest suite, orchestrator "
        "and declared doc-enforcement test is named by the gate manifest."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
