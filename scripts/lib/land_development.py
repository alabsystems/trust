"""Permanent, explicit source-main checks for validation execution components.

This inventory assigns supported changed programs/components concrete focused tests. It does not
claim that the product's diagnostic readsets are unchanged or complete: those
remain visible in the full plan. Unknown inputs refuse this profile.
"""
from dataclasses import dataclass, field
import ast
import json
import hashlib
import posixpath
import re
import sys
from pathlib import Path


SCHEDULER_COMPONENTS = frozenset(("src/jobserver_utils", "src/tools/compiletest", "src/tools/run-make-support"))
CONTROLLER_COMPONENT = "crates/trust-resource-controller"
PROVENANCE_COMPONENT = "crates/trust-resource-provenance"
# Reviewed existing compiler-identity build script: its feature inputs are
# CLIENT and CHANNEL. This binds only declaration eligibility, no probe grant.
CONTROLLER_BUILD_SCRIPT_SHA256 = "4960ab64459c6874cdba10aa1e982066e1fdf70091b7c7cfa667490e98486e36"
BOOTSTRAP_COMPONENT = "src/bootstrap"
BUILD_TREE_COMPONENT = "crates/trust-build-tree"
COMPONENTS = SCHEDULER_COMPONENTS | {"crates/trust-build-cpu", CONTROLLER_COMPONENT, PROVENANCE_COMPONENT, BOOTSTRAP_COMPONENT, BUILD_TREE_COMPONENT}
TOOL_NAME_GUIDE = "docs/USING_TRUST.md"
TOOL_NAME_OWNER = "crates/trust-release"
TOOL_NAME_TEST = TOOL_NAME_OWNER + "/tests/tool_name_source_inputs.rs"
TOOL_NAME_LEG = "development-package-tool-name-source-inputs"
TOOL_NAME_CASES = 4
# These exact audited copies feed the production tool-name checker. The
# compile-class row is a conservative union with unrelated include_str inputs;
# the guide itself is copied at runtime. Never generalize to a package reader.
TOOL_NAME_READERS = {
    (TOOL_NAME_OWNER, "runtime", TOOL_NAME_TEST + " (audited)"),
    ("targo-trust", "compile", "targo-trust/tests/release_cli.rs (audited)"),
    ("targo-trust", "runtime", "targo-trust/tests/support/release_fixture.rs (audited)"),
}
TOOL_NAME_READER_PINS = {
    ".cargo/config.toml": "c40792b17196ff3ca64b30f3965c6e95cd980bf6",
    "Cargo.toml": "0e9f4d0888d84bc82bc3ea914c952eaaa4a5fc1c",
    "Cargo.lock": "ca9f2d59984e545af480f026e9d4d2016eb90e38",
    TOOL_NAME_TEST: "5ba31588e0e8030756f86513e717c65c0ebf9093",
    "crates/trust-release/Cargo.toml": "9dd61372b43dc28a9546d1e91b6b7596c9f693f9",
    "crates/trust-release/src/lib.rs": "150bba3a8ce97a36866fe7207974353e17f447d8",
    "targo-trust/Cargo.toml": "d2ca77c79e1ddade011cab3a0211da0a1cc84a7c",
    "targo-trust/src/main.rs": "11a65e120710c03b26c90eac14ffab5df691b713",
    "targo-trust/src/release_cli/mod.rs": "fec1c12fed0940e61c9c3547a4d09849f1fc9a13",
    "targo-trust/src/release_cli/gates.rs": "12562f4d3802e492294a456fa3730e55457e57a3",
    "targo-trust/tests/release_cli.rs": "bc74768f90711c5c18b85d7af17b1c00371b4f25",
    "targo-trust/tests/support/release_fixture.rs": "a713cec75254d5a5bc5ecf9d47f0e7815da02e23",
}
TOOL_NAME_ABSENT_CONFIGS = (".cargo/config", "targo-trust/.cargo/config", "targo-trust/.cargo/config.toml")
NATIVE_DOMAIN_SOURCES = frozenset((
    "crates/trust-build-cpu/src/native_domain.rs",
    "crates/trust-build-cpu/src/native_domain/tests.rs",
    "crates/trust-build-cpu/src/external_debt.rs",
))
# This private accessor only exposes the identity already held by ExternalDebt.
# Any other external-debt implementation change retains dependent scheduler
# qualification. NativeDomain itself is not used by those scheduler consumers.
RETAINED_IDENTITY_ACCESSOR = b"\n    pub(crate) fn retained_identity(&self) -> (u64, u64) {\n        (self.binding.root_dev, self.binding.root_ino)\n    }\n"
LOCAL_GIT_WORKSPACE = "src/tools/targo"
LOCAL_GIT_CORE = LOCAL_GIT_WORKSPACE + "/crates/targo-core"
LOCAL_GIT_IMPORT = LOCAL_GIT_CORE + "/src/sources/git/local_import/"
LOCAL_GIT_FIXTURE = LOCAL_GIT_WORKSPACE + "/tests/local_git_source_cache.rs"
LOCAL_GIT_CORE_LEG = "development-package-targo-local-git-core"
LOCAL_GIT_FIXTURE_LEG = "development-package-targo-local-git-fixture"
LOCAL_GIT_LOCK = LOCAL_GIT_WORKSPACE + "/Cargo.lock"
ORACLE_WAIVERS = "scripts/frozen-waivers.txt"
# Only the reviewed API plumbing may share the DATA component's checks.
# Any unrelated registry/fetch implementation edit keeps ordinary discovery.
LOCAL_GIT_EXPORT = LOCAL_GIT_CORE + "/src/sources/git/mod.rs"
LOCAL_GIT_REGISTRY = LOCAL_GIT_CORE + "/src/sources/registry/mod.rs"
LOCAL_GIT_FETCH = LOCAL_GIT_WORKSPACE + "/src/bin/cargo/commands/fetch.rs"
LOCAL_GIT_BRIDGES = frozenset((LOCAL_GIT_EXPORT, LOCAL_GIT_REGISTRY, LOCAL_GIT_FETCH))
LOCAL_GIT_SNAPSHOT_EXPORT = b"pub use local_import::snapshot_locked_cache_data;\n"
LOCAL_GIT_REGISTRY_DECL = b"fn short_name(id: SourceId, is_shallow: bool) -> String {"
# Additive native DATA option/dispatch only; the normal fetch implementation
# must remain byte-identical. Complete native CLI cases still run afresh.
LOCAL_GIT_FETCH_ADDITIONS = (
    b"""        .arg(opt("local-cargo-data-cache", "Copy bounded stored Git and sparse crates.io cache DATA into a fresh Cargo home, then resolve normally (requires --locked --offline)")
            .value_name("PATH")
            .conflicts_with_all(["local-git-source-cache", "local-git-object-source", "local-git-source-copy-budget", "local-git-source-preflight"]))
        .arg(opt("local-cargo-registry-data-cache", "Read only registry DATA from a separate original Cargo cache owner")
            .value_name("PATH").requires("local-cargo-data-cache"))
""",
    b"""    if let Some(donor) = args.get_one::<String>("local-cargo-data-cache") {
        targo::sources::git::snapshot_locked_cache_data(
            &ws,
            std::path::Path::new(donor),
            args.get_one::<String>("local-cargo-registry-data-cache")
                .map(std::path::Path::new),
        )?;
    }

""",
)
TARGO_CLEANUP_LEG = "development-package-targo-cleanup"
TARGO_NATIVE_CORE_LEG = "development-package-targo-native-core"
TARGO_CORE_EXAMPLE_LEG = "development-targo-core-example-check"
TARGO_CORE_EXAMPLE = LOCAL_GIT_CORE + "/examples/trust_compiler_query.rs"
TARGO_COMPILER_CONTEXT_VISIBILITY = LOCAL_GIT_CORE + "/src/compiler/mod.rs"
TARGO_PRIVATE_CONTEXT_HELPERS = ("lib_search_paths_context", "extern_args_context")
TARGO_LOCK = LOCAL_GIT_WORKSPACE + "/Cargo.lock"
TARGO_MANIFEST = LOCAL_GIT_WORKSPACE + "/Cargo.toml"
TARGO_BUILD_SCRIPT = LOCAL_GIT_WORKSPACE + "/build.rs"
TARGO_BUILD_RS = LOCAL_GIT_WORKSPACE + "/crates/build-rs"
TARGO_BUILD_INPUT_SOURCES = frozenset((TARGO_MANIFEST, TARGO_BUILD_SCRIPT))
TARGO_RUSTC_INPUT_BEFORE = b'''    let compiler = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    #[expect(
        clippy::disallowed_types,
        reason = "build-time compiler identity probe, never native resource authority"
    )]
'''
TARGO_RUSTC_INPUT_AFTER = b'    let compiler = build_rs::input::rustc();\n'
TARGO_TRIAGEBOT = LOCAL_GIT_WORKSPACE + "/triagebot.toml"
TARGO_CHECKOUT_LAYOUT_OLD = LOCAL_GIT_CORE + "/src/ops/checkout_inputs.rs"
TARGO_CHECKOUT_LAYOUT_NEW = LOCAL_GIT_CORE + "/src/ops/checkout_inputs/mod.rs"
TARGO_CHECKOUT_LAYOUT_ADAPTER = "scripts/lib/native_checkout.py"
TARGO_CHECKOUT_LAYOUT_PATHS = frozenset((
    TARGO_CHECKOUT_LAYOUT_OLD, TARGO_CHECKOUT_LAYOUT_NEW, TARGO_CHECKOUT_LAYOUT_ADAPTER,
))
TARGO_CHECKOUT_LAYOUT_TEST = "scripts.tests.land_development_test.TargoCheckoutLayoutTests"
TARGO_CLEANUP_FIXTURE = LOCAL_GIT_WORKSPACE + "/tests/clean_intermediates_only.rs"
TARGO_CLEANUP_CORE_SOURCES = frozenset(LOCAL_GIT_CORE + "/src/" + path for path in (
    "ops/cargo_clean.rs", "compiler/layout.rs", "util/flock.rs", "workspace/profiles.rs",
))
TARGO_CLEANUP_SOURCES = TARGO_CLEANUP_CORE_SOURCES | {
    LOCAL_GIT_WORKSPACE + "/src/bin/cargo/commands/clean.rs", TARGO_CLEANUP_FIXTURE,
    LOCAL_GIT_WORKSPACE + "/tests/clean_intermediates_only/physical_alias.rs",
    LOCAL_GIT_WORKSPACE + "/tests/fixtures/clean-enospc.c",
    LOCAL_GIT_WORKSPACE + "/tests/fixtures/clean-enospc-probe.c",
}
# These private native execution components have their own real custody,
# projection, original-bank and fresh-kernel parent controls. Cleanup's four
# CLI cases do not answer for edits to these components or arbitrary kernels.
TARGO_NATIVE_MODULE_MOVES = {
    LOCAL_GIT_CORE + "/src/" + stem + ".rs": LOCAL_GIT_CORE + "/src/" + stem + "/mod.rs"
    for stem in ("compiler/candidate_dependencies", "compiler/candidate_runner", "compiler/native_job",
                 "compiler/resource_runtime_v3", "ops/cargo_vendor", "native_job_service/comparison",
                 "native_job_service/verification", "resource_v3/candidate_coordinator",
                 "compiler/candidate_semantics", "ops/cargo_vendor/cohort",
                 "native_job_service/verification/census", "native_job_service/verification/kernel",
                 "workspace/package")
}
# These modules only move to satisfy the normal file layout. The native-core
# controls do not own semantic changes to vendor, census or package logic.
TARGO_LAYOUT_ONLY_MOVES = {
    old: new for old, new in TARGO_NATIVE_MODULE_MOVES.items()
    if old.removeprefix(LOCAL_GIT_CORE + "/src/") in {
        "compiler/resource_runtime_v3.rs", "ops/cargo_vendor.rs", "ops/cargo_vendor/cohort.rs",
        "resource_v3/candidate_coordinator.rs", "native_job_service/verification/census.rs", "workspace/package.rs",
    }
}
TARGO_NATIVE_CORE_SOURCES = frozenset(LOCAL_GIT_CORE + "/src/" + path for path in (
    "compiler/build_runner/mod.rs", "compiler/candidate_runner/lifecycle.rs",
    "compiler/candidate_semantics.rs", "compiler/mod.rs", "compiler/native_job/produced.rs",
    "compiler/native_job/verification.rs", "native_job_service/comparison/publication.rs",
    "native_job_service/verification/kernel.rs", "native_job_service/verification/kernel/tests.rs",
    "resource_v3/executor/capture/mod.rs", "resource_v3/executor/mod.rs", "resource_v3/mod.rs",
    "resource_v3/native_job/outputs.rs", "resource_v3/native_job/startup.rs",
    "resource_v3/workload/bank/local.rs", "resource_v3/workload/bank/mod.rs",
)) | frozenset(TARGO_NATIVE_MODULE_MOVES) | frozenset(TARGO_NATIVE_MODULE_MOVES.values())
TARGO_CLEANUP_CASES = tuple("clean_intermediates_" + name for name in (
    "recovers_with_real_enospc_and_keeps_compiled_outputs",
    "refuses_missing_busy_or_aliased_original_locks",
    "refuses_nested_final_artifact_root_before_unlink", "honors_custom_profile_and_explicit_target",
))
# Complete names, passed as OR filters after Cargo's `--` with --exact. A
# removed/unsupported case therefore reduces the required population and fails.
# Do not select fresh_kernel_component_child directly: without its parent's
# private environment it returns without exercising the mathematical checks.
TARGO_NATIVE_CORE_CASES = (
    *("compiler::native_job::verification::tests::" + name for name in (
        "failed_actual_command_remains_failed_after_namespace_restoration",
        "duplicate_native_failure_keeps_both_outcomes_without_creating_a_command",
        "poisoned_recorder_keeps_actual_incoming_failure_without_restoring_usability")),
    "native_job_service::verification::kernel::tests::native_math_hints_receive_fresh_kernel_checks_without_a_native_node_grant",
    *("resource_v3::workload::bank::tests::" + name for name in (
        "ordinary_or_foreign_primary_cannot_promote_itself_to_local_publication",
        "retained_compiler_loan_observes_both_actual_bank_returns_without_reopening_it",
        "preparation_observation_preserves_original_reservation_and_refuses_alias_or_bound_member",
        "empty_current_table_never_erases_an_earlier_compiler_binding_for_output_custody",
        "cached_live_policy_receives_actual_busy_loans_instead_of_the_full_held_domain",
        "full_actual_reservation_is_distinct_from_dispatch_and_physical_slots_stay_held",
        "primaries_and_compiler_extras_share_one_held_table_and_live_memory_cpu_ceiling",
        "compiler_materialization_requires_its_original_success_and_cannot_replace_host_return",
        "positive_host_return_and_original_helper_retirement_are_both_required_in_either_order",
        "park_blocks_new_primaries_and_extras_but_preserves_current_positive_return_path",
        "affirmative_before_request_cancels_only_the_original_unexposed_primary",
        "query_and_compiler_borrow_the_same_original_table_with_distinct_member_purposes",
        "concurrent_queue_borrowers_never_duplicate_or_exceed_the_actual_policy_width",
        "foreign_root_invocation_sequence_or_unbound_primary_poisons_without_lending_any_original",
        "native_bound_drop_and_wrong_worker_return_keep_the_original_unknown_abort")),
    *("compiler::layout::projection_tests::" + name for name in (
        "path_projection_preserves_split_roots_target_and_profile_without_creation",
        "path_projection_keeps_new_layout_package_hash_and_artifact_paths",
        "check_projection_omits_artifact_layout_and_preserves_intermediate_paths",
        "path_projection_preserves_non_unicode_root_bytes")),
    "compiler::candidate_dependencies::tests::retired_consumer_does_not_stay_active_through_retained_reader_copies",
    "compiler::native_job::observation_tests::selected_observation_freezes_preparation_and_refuses_cross_graph_identity",
)
TARGO_NATIVE_TEST_SOURCES = (
    LOCAL_GIT_CORE + "/src/compiler/native_job/verification.rs",
    LOCAL_GIT_CORE + "/src/native_job_service/verification/kernel/tests.rs",
    LOCAL_GIT_CORE + "/src/resource_v3/workload/bank/tests.rs",
    LOCAL_GIT_CORE + "/src/compiler/layout.rs",
)
CONTROLLER_DESCRIPTORS = "crates/trust-resource-controller"
CONTROLLER_DESCRIPTOR_SOURCES = frozenset((
    CONTROLLER_DESCRIPTORS + "/src/descriptors.rs",
    CONTROLLER_DESCRIPTORS + "/src/descriptors/tests.rs",
))
CONTROLLER_DESCRIPTOR_LEG = "development-package-trust-resource-controller-descriptors"
# The agent-facing toolchain package. Its complete own suite is the full
# profile's `targo-trust` leg (landing_targo.COMMAND), which development runs
# unchanged for a change this package owns. Its consumers (the binary that
# crates/trust-integration-tests and native Targo run, the sysroot Bootstrap
# ships) and the path dependencies it builds keep their own owners or refuse.
TARGO_TRUST_COMPONENT = "targo-trust"
TARGO_TRUST_MANIFEST = TARGO_TRUST_COMPONENT + "/Cargo.toml"
TARGO_TRUST_LEG = "targo-trust"
# The default-feature suite cfg-removes code under the in-process features
# Bootstrap ships (`#[cfg(feature = "trust-mc-in-process")]` and the rest are
# never type-checked there). The shipped surface is read from the one function
# every Bootstrap targo-trust build and test step calls (tool.rs
# targo_trust_in_process_features; test.rs "Test the same feature surface that
# bootstrap ships"), never copied here, and runs as a second fresh suite.
TARGO_TRUST_SHIPPED_FEATURES_SOURCE = "src/bootstrap/src/core/build_steps/tool.rs"
TARGO_TRUST_SHIPPED_FEATURES_FN = "targo_trust_in_process_features"
TARGO_TRUST_SHIPPED_LEG = "targo-trust-shipped-features"
# Only these subtrees of the package are its own sources: the suite builds
# every src/ and tests/ target (no [[test]]/[[bench]] table, autodiscovery).
# Anything else (README.md, benches/, examples/, top-level files) refuses.
TARGO_TRUST_SOURCE_ROOTS = (TARGO_TRUST_COMPONENT + "/src/", TARGO_TRUST_COMPONENT + "/tests/")
# Configuration that changes a judgement or a checkout the suite does not make
# (fmt, tippy, git attributes), refused at any depth (compared folded). Any
# dot-named component and any .toml under targo-trust refuse too.
TARGO_TRUST_CONFIG_NAMES = frozenset((
    "rustfmt.toml", "clippy.toml", "tippy.toml", "trustfmt.toml", "rust-toolchain", "deny.toml",
))
# Files that name a targo-trust path (targo_trust_sites). A Rust source's
# reads of single files are the Cargo graph's (direct_reads); its root
# references are a walk (TARGO_TRUST_ROOT_READERS). Markdown and prose are
# never executed. Every other file naming a changed path must be one of:
#   * a root reader with its declared handling (TARGO_TRUST_ROOT_READERS),
#   * a reader whose own check development runs (TARGO_TRUST_READER_CHECKS),
#   * a scripts/tests/*_test.py module, which runs as a validation test,
#   * a file that names the path without reading its content
#     (TARGO_TRUST_NAME_ONLY: the whole file; TARGO_TRUST_NAME_ONLY_REFS: one
#     spelling inside a file that otherwise reads), with the reason;
# or that path refuses this profile.
TARGO_TRUST_READER_CHECKS = {
    # Hashes the prose of every help surface under its scan_roots (one is
    # targo-trust/src) against data/help_surfaces.json's read-verified rows.
    "development-reader-help-surfaces": (
        ["scripts/check_help_surfaces.py"],
        ("scripts/check_help_surfaces.py", "data/help_surfaces.json")),
    # Refuses a machine path in committed fixtures (targo-trust/src/fixtures);
    # pre_push_shadow.sh names the same roots to select that fast row.
    "development-reader-fixture-span-paths": (
        ["scripts/check_fixture_span_paths.py"],
        ("scripts/check_fixture_span_paths.py", "scripts/pre_push_shadow.sh")),
    # Holds targo-trust's FORBIDDEN_TRUST_PUBLIC_* sets (pipeline/surface.rs)
    # equal to bootstrap.py's authority.
    "development-reader-toolchain-coherence": (
        ["scripts/check_toolchain_coherence.py"],
        ("scripts/check_toolchain_coherence.py",)),
    # Root readers (TARGO_TRUST_ROOT_READERS): every driver extra-symbol site
    # under its SCAN_ROOTS; every Trust-owned manifest and lock under TRUST_TOPS.
    "development-reader-driver-extra-symbols": (
        ["scripts/check_driver_extra_symbols.py"],
        ("scripts/check_driver_extra_symbols.py",)),
    "development-reader-cargo-lock-hygiene": (
        ["scripts/check_cargo_lock_hygiene.py"],
        ("scripts/check_cargo_lock_hygiene.py",)),
}
TARGO_TRUST_NAME_ONLY = {
    "scripts/gates/land-escape-audits.toml":
        "the Cargo reader audit table: its rows are the graph's reads, which direct_reads checks",
    "gates/land.toml":
        "the validation row table: a row's selects_on path selects its tests, which this ownership runs",
    "scripts/lib/land_development.py":
        "this inventory; the tool-name custody pins are compared by blob before any use",
    "rustfmt.toml":
        "the formatter's ignore list names paths and reads none of them",
    "src/tools/tippy/tests/ui/trust_creusot_spec_sugar_fixable.fixed":
        "expected lint output quoting the harness path",
    "src/tools/tippy/tests/ui/trust_creusot_spec_sugar_fixable.stderr":
        "expected lint output quoting the harness path",
    "src/tools/targo/crates/cargo-util-schemas/manifest.schema.json":
        "a schema description string naming the source",
}
TARGO_TRUST_NAME_ONLY_REFS = {
    # The gate's own tests build synthetic repositories under these names.
    ("scripts/tests/land_gate_test.py", "targo-trust/*.rs"): "fixture audit row in a synthetic repository",
    ("scripts/tests/land_gate_test.py", "targo-trust/src/doctor.rs"): "fixture path in a synthetic repository",
    ("scripts/tests/land_gate_test.py", "targo-trust/tests/cli.rs"): "fixture path in a synthetic repository",
    ("scripts/tests/land_gate_test.py", "targo-trust/src/pipeline/surface.rs"):
        "fixture path in a synthetic repository",
    ("scripts/tests/land_gate_test.py", "targo-trust/src/fixtures"): "fixture path in a synthetic repository",
    ("scripts/tests/land_gate_test.py", "targo-trust/src/fixtures/span.jsonl"):
        "fixture path in a synthetic repository",
    ("scripts/tests/land_gate_test.py", "targo-trust/src"): "fixture scan root in a synthetic repository",
    ("scripts/tests/land_gate_test.py", "targo-trust/*/doctor.rs"): "fixture glob in a synthetic repository",
    # The two tool-name evidence rows are audit table keys; the test reads the
    # audit table, not these files.
    ("scripts/tests/land_gate_test.py", "targo-trust/tests/support/release_fixture.rs"): "audit row key",
    ("scripts/tests/land_gate_test.py", "targo-trust/tests/release_cli.rs"): "audit row key",
    ("scripts/tests/land_development_test.py", "targo-trust/src/release_cli/mod.rs"):
        "fixture bytes in a synthetic repository",
    # Root references (TARGO_TRUST_ROOT): leg ids, fixture roots and prefix
    # tests in the gate's own tests, never a walk of this checkout.
    ("scripts/tests/land_gate_test.py", TARGO_TRUST_COMPONENT): "leg ids and synthetic-repository roots",
    ("scripts/land_gate.py", TARGO_TRUST_COMPONENT):
        "the caller-configuration probe reads targo-trust/.cargo, a dot path this ownership refuses",
    ("scripts/tests/check_cargo_lock_hygiene_mutants.py", TARGO_TRUST_COMPONENT):
        "mutant text of check_cargo_lock_hygiene.py's TRUST_TOPS, whose check runs",
    ("scripts/check_crates_tests_scoped.py", TARGO_TRUST_COMPONENT):
        "a prefix test on the changed path list that selects the scoped targo-trust row",
    ("tests/e2e_check_all_tcargo_provenance.sh", TARGO_TRUST_COMPONENT):
        "creates an empty directory of that name in a temporary repository",
}
# The spelling of a root reference: the package directory itself, which names
# every file under it (targo_trust_ref_names).
TARGO_TRUST_ROOT = TARGO_TRUST_COMPONENT
# A scan-root list names the package beside another source root.
TARGO_TRUST_SOURCE_TOPS = ("compiler", "library", "src", "crates", "tests", "scripts", "first-party",
                           "examples", "benchmarks")
# Readers that walk the targo-trust directory (or a directory in it) instead of
# naming one file: another package's directory read in the Cargo graph
# (targo_trust_directory_readers) and every root reference a tracked file
# spells (targo_trust_refs: a scan-root list, a repository-anchored join, a
# `targo-trust/` prefix). Keyed by the reader's file or package directory, the
# longest key containing it winning; each says what development does for it:
#   census     -- the compiler's single-issuer census (TARGO_TRUST_CENSUS_SOURCE)
#                 needs stage 1, which this profile never builds; a changed
#                 targo-trust file whose text names one of the identifiers
#                 it counts refuses.
#   check      -- that leg runs fresh on this tree.
#   builds     -- Bootstrap compiles the package; targo-trust-shipped-features
#                 compiles and tests the same feature surface.
#   diagnostic -- tidy's style count ratchet: the same broad sweep over
#                 crates/ that every crates/ development owner leaves to the
#                 full profile. It is no soundness tripwire.
#   names      -- names the tool, a binary or a fixture root; never a walk.
# An entry with a line pin (every kind but check and builds) holds exactly
# the root-reference lines (targo_trust_root_line) in the files it covers;
# a new or changed one lapses it and the path refuses until someone re-reads
# the reader. A Cargo package whose harvested literals make it a directory
# reader without spelling a walk pins none. A root reader with no entry
# refuses.
TARGO_TRUST_CENSUS_SOURCE = "compiler/rustc_mir_transform/src/trust_verify/tests.rs"
TARGO_TRUST_CENSUS_FN = "source_reference_facts_have_a_single_production_issuer"
# sha256 of that function, `fn` line to closing brace: the identifiers below
# are read from it, so a census that changes how it counts lapses this.
TARGO_TRUST_CENSUS_SHA256 = "868c12eeda7f478e3e602a22b5e5b8522b1cfdcbe54d205ea8f4a5de816ecc15"
# trust-cg-bridge's tripwire that the measurement API and the trap oracle never
# reach a shipping lane: a text scan of every .rs and Cargo.toml under
# targo-trust, run fresh as its one exact libtest test.
TARGO_TRUST_TRIPWIRE_COMPONENT = "crates/trust-cg-bridge"
TARGO_TRUST_TRIPWIRE_TEST = "compiler_consumer::census::no_compiler_caller"
TARGO_TRUST_TRIPWIRE_LEG = "development-package-trust-cg-bridge-no-compiler-caller"
TARGO_TRUST_ROOT_READERS = {
    "compiler/rustc_mir_transform": ("census", None, frozenset((
        '("targo-trust", repo.join("targo-trust")),',)),
        "the census walks targo-trust for second issuers of a TCB authority token"),
    TARGO_TRUST_TRIPWIRE_COMPONENT: ("check", TARGO_TRUST_TRIPWIRE_LEG, None,
                                     "no_compiler_caller scans targo-trust for the trap oracle"),
    "scripts/check_driver_extra_symbols.py": ("check", "development-reader-driver-extra-symbols", None,
                                              "SCAN_ROOTS names targo-trust for driver symbol lists"),
    "scripts/check_cargo_lock_hygiene.py": ("check", "development-reader-cargo-lock-hygiene", None,
                                            "TRUST_TOPS names targo-trust for its manifests and locks"),
    "src/bootstrap": ("builds", None, None,
                      "builds, tests, installs and distributes the package from its directory"),
    "src/tools/tidy": ("diagnostic", None, frozenset((
        'let targo_trust_path = root_path.join("targo-trust");',)),
        "style_ratcheted counts style findings over crates/ and targo-trust/"),
    "src/tools/targo": ("names", None, frozenset((
        '&root.join("targo-trust"),',
        'root.join("targo-trust"),',
        'let command = root.join("targo-trust");')),
        "the dispatched and authenticated executable's name, and fixture roots and binaries in its tests"),
    "crates/trust-build-tree": ("names", None, frozenset(), "repo-lock management matches the tool name"),
    "crates/trust-stage-receipt": ("names", None, frozenset(), "a stage's binary names"),
    "crates/trust-version": ("names", None, frozenset(),
                             "the tool's name and its manifest version row, read from targo-trust/Cargo.toml only"),
}


def integration_recipes(platform):
    # jobserver-error checks Linux descriptor diagnostics and declares only-linux.
    # An ignored platform case cannot satisfy a required native recipe terminal.
    portable = ("tests/run-make/parallel-rustc-no-overwrite",)
    return portable + (("tests/run-make/jobserver-error",) if platform.startswith("linux") else ())


INTEGRATION_RECIPES = integration_recipes(sys.platform)
EXIT_RECIPE = "tests/run-make/compiletest-scheduler-exit"
SCHEDULER_MODULE = "src/tools/compiletest/src/scheduler.rs"
# Full diagnostic selftests remain available. A source edit to the selector
# runs the affected policy/reader/cache/custody controls, not every historical
# gate experiment or a compiler/workspace build.
SELECTOR_TESTS = (
    "scripts.tests.land_manifest_test", "scripts.tests.land_development_test",
    "scripts.tests.land_gate_test.TreeIndexBlobTests",
    "scripts.tests.land_gate_test.SelectorTests",
    "scripts.tests.land_gate_test.ValidationDependencyTests",
    "scripts.tests.land_gate_test.CacheKeyTests",
    "scripts.tests.land_gate_test.CheckoutBindingTests",
    "scripts.tests.land_gate_test.NeedsTests",
    "scripts.tests.land_gate_test.NativeSourcePublicationTests",
    "scripts.tests.land_gate_test.DiscoverySnapshotTests",
    "scripts.tests.land_gate_test.LiveGraphRefreshTests",
    "scripts.tests.land_gate_test.ProseClassificationRefreshTests",
    "scripts.tests.land_gate_test.EscapeCacheContextTests",
)
PROGRAM_TESTS = {
    # Existing Bootstrap preflight validator and its fixture. Keep the full
    # diagnostic subject mapping additive; this explicit profile runs the
    # same declared program tests without selecting compiler diagnostics.
    "tools/preflight.py": (
        "scripts.tests.build_dir_symlink_test", "scripts.tests.check_bootstrap_script_tests_test",
        "scripts.tests.preflight_pin_rollback_disclosure_test", "scripts.tests.preflight_test",
        "scripts.tests.python_floor_test", "scripts.tests.targo_tool_preflight_test",
    ),
    "scripts/tests/preflight_test.py": ("scripts.tests.preflight_test",),
    "scripts/ir_cohort_physical_read_set.json": (
        "scripts.tests.land_gate_test.IrDiagnosticPhysicalInputsTests", "scripts.tests.check_ledger_pins_test"),
    "scripts/lib/land_select.py": SELECTOR_TESTS,
    # The row table the selector builds its validation tables from (PKG-LIVE-4):
    # an edit to it is an edit to the selector's data, owned as the selector is.
    "gates/land.toml": SELECTOR_TESTS,
    "scripts/lib/land_manifest.py": SELECTOR_TESTS,
    "scripts/lib/land_development.py": SELECTOR_TESTS,
    "scripts/land_gate.py": SELECTOR_TESTS + (
        "scripts.tests.land_gate_row_custody_test",
        "scripts.tests.remote_tips_process_test",
        "scripts.tests.land_gate_test.CoverageLegTests",
        "scripts.tests.land_gate_test.SuiteJudgeTests",
        "scripts.tests.land_gate_test.GraphVerificationTests",
        "scripts.tests.land_gate_test.HooklessRound3Tests",
        "scripts.tests.land_gate_test.HooklessRound5Tests",
        "scripts.tests.land_gate_test.ScalerTests",
        "scripts.tests.land_gate_test.FailFastTests",
        "scripts.tests.land_gate_test.CacheOutcomeTests",
        "scripts.tests.land_gate_test.SourceDiagnosticRunTests",
    ),
    "scripts/check_compiler_targets_build.sh": SELECTOR_TESTS,
    "scripts/gates/land-escape-audits.toml": (
        "scripts.tests.land_development_test",
        "scripts.tests.land_gate_test.EscapeAuditTests",
        "scripts.tests.land_gate_test.ListingAndNotPathTests",
        "scripts.tests.land_gate_test.EscapeAuditRenewalTests",
        "scripts.tests.land_gate_test.FixtureEscapeAuditTests",
    ),
    "scripts/tests/land_manifest_test.py": ("scripts.tests.land_manifest_test",),
    "scripts/tests/land_development_test.py": ("scripts.tests.land_development_test",),
    # The passive census reader and its real fixture have the same exact
    # owner in full diagnostic selection. Do not admit neighbouring scripts
    # or every additive VALIDATION_TEST_SUBJECTS input (the row table's
    # selects_on paths that are not validation programs) to this profile.
    "scripts/compiletest_census.py": ("scripts.tests.compiletest_census_test",),
    "scripts/tests/compiletest_census_test.py": ("scripts.tests.compiletest_census_test",),
    # Preserve every declared validation owner of the train, including its
    # bootstrap-reader, Python-floor and SDK-dispatch consumers. A source-main
    # edit runs these whole modules; it earns no compiler/release qualification.
    "scripts/daily_toolchain_stage.py": (
        "scripts.tests.check_bootstrap_script_tests_test", "scripts.tests.daily_dependency_git_selection_test",
        "scripts.tests.daily_toolchain_stage_test",
        "scripts.tests.python_floor_test", "scripts.tests.sdk_diagnostic_test",
    ),
    "scripts/tests/daily_toolchain_stage_test.py": (
        "scripts.tests.check_bootstrap_script_tests_test", "scripts.tests.daily_dependency_git_selection_test",
        "scripts.tests.daily_toolchain_stage_test",
    ),
    "scripts/trust_verify_cost.py": ("scripts.tests.trust_verify_cost_test",),
    "scripts/tests/trust_verify_cost_test.py": ("scripts.tests.trust_verify_cost_test",),
    "scripts/retain_development_emission.py": ("scripts.tests.retain_development_emission_test",),
    "scripts/tests/retain_development_emission_test.py": ("scripts.tests.retain_development_emission_test",),
    "scripts/produce_vf5_proposal.py": ("scripts.tests.produce_vf5_proposal_test",),
    "scripts/tests/produce_vf5_proposal_test.py": ("scripts.tests.produce_vf5_proposal_test",),
    "scripts/trust-soundness-corpus.py": ("scripts.tests.trust_soundness_corpus_test",),
    "scripts/tests/trust_soundness_corpus_test.py": ("scripts.tests.trust_soundness_corpus_test",),
    "scripts/tests/fixtures/trust_soundness_corpus_native_rows.json": ("scripts.tests.trust_soundness_corpus_test",),
    "tests/trust-soundness-corpus/README.md": ("scripts.tests.trust_soundness_corpus_test",),
    "scripts/lib/push_destination.sh": ("scripts.tests.push_destination_test",),
    "scripts/tests/push_destination_test.py": ("scripts.tests.push_destination_test",),
}

# The large selector test module has explicit class ownership. Only existing
# test-method body edits can use this narrower profile; imports, fixtures,
# declarations, signatures and unknown classes retain the full fallback.
TEST_BODY_PROGRAM = "scripts/tests/land_gate_test.py"
TEST_BODY_CLASSES = frozenset(test.rsplit(".", 1)[1] for test in (
    *PROGRAM_TESTS["scripts/land_gate.py"], *PROGRAM_TESTS["scripts/gates/land-escape-audits.toml"])
    if test.startswith("scripts.tests.land_gate_test."))


def changed_test_classes(graph, base, path):
    import land_select as ls

    def shape(raw, existing_classes=None, existing_methods=None, *, gate_first=False):
        tree = ast.parse(raw.decode("utf-8"), type_comments=True)
        if gate_first:
            # This exact bootstrap ordering starts source capture before the
            # scaler is loaded. No import, helper or test population changes.
            for position, pair in enumerate(zip(tree.body, tree.body[1:])):
                if all(isinstance(node, ast.Import) and len(node.names) == 1
                       and node.names[0].asname is None for node in pair) and [
                        node.names[0].name for node in pair] == ["host_budget", "land_gate"]:
                    tree.body[position:position + 2] = reversed(pair)
                    break
        bodies, declared = {}, set()
        for node in list(tree.body):
            if isinstance(node, ast.ClassDef) and node.name in TEST_BODY_CLASSES:
                if node.name in declared:
                    raise ValueError("duplicate declared test owner")
                declared.add(node.name)
                added_class = existing_classes is not None and node.name not in existing_classes
                for method in list(node.body):
                    if isinstance(method, ast.FunctionDef) and method.name.startswith("test_"):
                        key = (node.name, method.name)
                        if key in bodies:
                            raise ValueError("duplicate declared test method")
                        bodies[key] = ast.dump(method, include_attributes=False)
                        if existing_methods is not None and key not in existing_methods:
                            node.body.remove(method)
                        else:
                            method.body = [ast.Pass()]
                if added_class:
                    tree.body.remove(node)
        return ast.dump(tree, include_attributes=False), bodies, declared
    try:
        before = ls.TreeIndex.load(graph.index.repo, base)
        if before.entries.get(path, (None,))[0] not in ("100644", "100755"):
            raise ValueError("test module has no existing regular source")
        old_raw = before.read_blobs([path])[path]
        old_shape, old, owners = shape(old_raw)
        new_shape, new, current_owners = shape(graph.index.read_blobs([path])[path], owners, old)
        bootstrap_order = old_shape != new_shape and shape(old_raw, gate_first=True)[0] == new_shape
        if bootstrap_order:
            if not {"DiscoverySnapshotTests", "ScalerTests"} <= owners & current_owners:
                raise ValueError("provenance import ordering lacks its required test owners")
            old_shape = new_shape
        if old_shape != new_shape or not old.keys() <= new.keys():
            raise ValueError("test change extends beyond declared test owners")
        classes = sorted((current_owners - owners) |
                         {owner for (owner, method), body in new.items() if old.get((owner, method)) != body})
        if bootstrap_order:
            classes = sorted(set(classes) | {"DiscoverySnapshotTests", "ScalerTests"})
        if not classes:
            raise ValueError("no changed supported test-method body")
        return ["scripts.tests.land_gate_test." + owner for owner in classes], None
    except (OSError, RuntimeError, UnicodeError, SyntaxError, ValueError, KeyError) as error:
        return [], f"{path}: {error}"


@dataclass
class Scope:
    packages: list = field(default_factory=list)
    recipes: list = field(default_factory=list)
    tests: list = field(default_factory=list)
    errors: list = field(default_factory=list)
    local_git_import: bool = False
    controller_descriptors: bool = False
    oracle_citations: bool = False
    targo_native_core: bool = False
    targo_cleanup: bool = False
    targo_core_example: bool = False
    tool_name_guide: bool = False
    targo_trust: bool = False
    # (package dir, integration test name, audited test source): another
    # package's audited test that reads a changed targo-trust file.
    reader_tests: list = field(default_factory=list)
    # TARGO_TRUST_READER_CHECKS legs: non-Cargo readers of a changed
    # targo-trust file whose own check runs.
    reader_checks: list = field(default_factory=list)


def safe_regular(graph, path):
    """Exact regular tracked input, without foreign or ambiguous traversal."""
    import land_select as ls
    if graph.index.entries.get(path, (None,))[0] not in ("100644", "100755"):
        return False
    parts = path.split("/")
    spellings = ls._index_spellings(graph)
    for n in range(1, len(parts) + 1):
        prefix = "/".join(parts[:n])
        if spellings.get(ls.fold(prefix)) != {prefix}:
            return False
        if n < len(parts) and prefix in graph.index.entries:
            return False
    return True


def tool_name_inputs_available(graph):
    """Reviewed reader and actual-input custody; changed readers need review."""
    import land_select as ls
    package = graph.packages.get(TOOL_NAME_OWNER)
    if (package is None or package.name != "trust-release"
            or graph.opaque_owner(TOOL_NAME_OWNER)):
        return False
    for path in (TOOL_NAME_GUIDE, TOOL_NAME_TEST, *TOOL_NAME_READER_PINS):
        if not safe_regular(graph, path) or graph.opaque_owner(path):
            return False
    if graph.owner(TOOL_NAME_TEST) != TOOL_NAME_OWNER:
        return False
    if not all(graph.index.entries[path][1] == blob for path, blob in TOOL_NAME_READER_PINS.items()):
        return False
    spellings = ls._index_spellings(graph)
    for path in TOOL_NAME_ABSENT_CONFIGS:
        parts = path.split("/")
        for n in range(1, len(parts) + 1):
            prefix = "/".join(parts[:n])
            variants = spellings.get(ls.fold(prefix), set())
            if (any(variant in graph.index.entries for variant in variants)
                    or variants and variants != {prefix} or n == len(parts) and variants):
                return False
    audits = ls.load_audits(graph)
    for _owner, cls, site in TOOL_NAME_READERS:
        source = site.removesuffix(" (audited)")
        audit = audits.get(source)
        if (not ls.audit_holds(graph, source, audit) or audit.get("class") != cls
                or audit.get("test_only") is not True or TOOL_NAME_GUIDE not in audit.get("reads", ())):
            return False
    return True


def audited_site(read):
    """The source file of an audit row's read (content or listing), else None."""
    suffix = " (audited listing)" if read.listing else " (audited)"
    return read.site[:-len(suffix)] if read.site.endswith(suffix) else None


def audited_reader_test(graph, package, read):
    """The integration test target an audited, test-only runtime read runs in.

    Only `<package>/tests/<name>.rs (audited)`, the exact Cargo default test
    target of a package with no declared/disabled test targets, whose audit
    still holds for the current blobs. That fresh target is the reader itself.
    A compile-class, production or unaudited reader returns None.
    """
    import land_select as ls
    source = audited_site(read)
    prefix = package.dir + "/tests/"
    name = source[len(prefix):-len(".rs")] if source and source.startswith(prefix) and source.endswith(".rs") else ""
    if (read.cls != "runtime" or not read.test_only or read.cwd or read.doctest
            or not re.fullmatch(r"[A-Za-z0-9_-]+", name)
            or not safe_regular(graph, source) or graph.owner(source) != package.dir
            or graph.opaque_owner(source)):
        return None
    audit = ls.load_audits(graph).get(source)
    if (not ls.audit_holds(graph, source, audit) or audit.get("class") != "runtime"
            or audit.get("test_only") is not True):
        return None
    manifest = package.dir + "/Cargo.toml"
    try:
        if not safe_regular(graph, manifest):
            return None
        document = ls.tomllib.loads(graph.index.read_blobs([manifest])[manifest].decode("utf-8"))
    except (OSError, RuntimeError, UnicodeError, ValueError, KeyError):
        return None
    if "test" in document or document.get("package", {}).get("autotests", True) is not True:
        return None
    return name


def targo_trust_shipped_features(graph):
    """The features Bootstrap builds, tests and ships targo-trust with, read
    from the one function its build and test steps call; None when that
    function is not exactly one literal list of features targo-trust declares."""
    import land_select as ls
    source = TARGO_TRUST_SHIPPED_FEATURES_SOURCE
    try:
        if not safe_regular(graph, source) or not safe_regular(graph, TARGO_TRUST_MANIFEST):
            return None
        blobs = graph.index.read_blobs([source, TARGO_TRUST_MANIFEST])
        text = blobs[source].decode("utf-8")
        declared = ls.tomllib.loads(blobs[TARGO_TRUST_MANIFEST].decode("utf-8")).get("features")
    except (OSError, RuntimeError, UnicodeError, ValueError, KeyError):
        return None
    name = re.escape(TARGO_TRUST_SHIPPED_FEATURES_FN)
    if len(re.findall(r"\bfn\s+" + name + r"\b", text)) != 1:
        return None
    found = re.findall(r"^(?:pub(?:\([a-z]+\))?\s+)?fn " + name + r"\(\) -> Vec<String> \{\n(.*?)^\}$",
                       text, re.S | re.M)
    if len(found) != 1:
        return None
    body = "\n".join(line for line in found[0].splitlines() if not line.strip().startswith("//"))
    listed = re.fullmatch(r'\s*\[\s*((?:"[A-Za-z0-9_-]+"\s*,\s*)*"[A-Za-z0-9_-]+"\s*,?)\s*\]\s*'
                          r'\.into_iter\(\)\s*\.map\(str::to_owned\)\s*\.collect\(\)\s*', body)
    if not listed:
        return None
    features = re.findall(r'"([^"]+)"', listed.group(1))
    if (len(set(features)) != len(features) or not isinstance(declared, dict)
            or any(feature not in declared for feature in features)):
        return None
    return features


def targo_trust_source(path):
    """Why `path`, under targo-trust, is no source file of the package, or None."""
    import land_select as ls
    if not path.startswith(TARGO_TRUST_SOURCE_ROOTS):
        return "only src/ and tests/ files are targo-trust sources"
    parts = ls.fold(path).split("/")
    if any(part.startswith(".") for part in parts) or parts[-1] in TARGO_TRUST_CONFIG_NAMES \
            or parts[-1].endswith(".toml"):
        return "configuration or attribute file the targo-trust suite does not judge"
    return None


_TARGO_TRUST_SEGMENT = r"[A-Za-z0-9_.*?\[\]{}-]+"
_TARGO_TRUST_LITERAL = re.compile(r"targo-trust(?:/" + _TARGO_TRUST_SEGMENT + r")+")
_TARGO_TRUST_JOINED = re.compile(r"""["']targo-trust["'](?:\s*[/,]\s*["']""" + _TARGO_TRUST_SEGMENT + r"""["'])+""")
# Root references: the quoted package directory beside another quoted source
# root (a scan-root list), joined onto a repository root with nothing after
# it, a shell repository variable followed by it, or a quoted prefix ending in
# `/`. A join that continues (`/ "src"`) is _TARGO_TRUST_JOINED's.
_TARGO_TRUST_QUOTED_ROOT = re.compile(r"""["']targo-trust/?["'](?!\s*[/,]\s*["'])""")
_TARGO_TRUST_QUOTED_TOP = re.compile(r"""["']([A-Za-z0-9_.-]+)/?["']""")
_TARGO_TRUST_ANCHORED_ROOT = re.compile(
    r"""\b(?:REPO|ROOT|REPO_ROOT|ROOT_DIR|TRUST_ROOT|repo|root|root_path|repo_root|root_dir|repo_dir|workspace_root)\b"""
    r"""\s*(?:\.join\(\s*|/\s*)["']targo-trust/?["'](?!\s*[/,]\s*["'])""")
_TARGO_TRUST_SHELL_ROOT = re.compile(
    r"""\$\{?(?:ROOT|REPO|REPO_ROOT|ROOT_DIR|TRUST_ROOT|repo|root|repo_root)\}?/targo-trust/?(?=["'\s)]|$)""")
_TARGO_TRUST_PREFIX_ROOT = re.compile(r"""["']targo-trust/["']""")
_HASH_COMMENTED = (".py", ".sh", ".bash", ".toml", ".yml", ".yaml")


def targo_trust_code_lines(path, text):
    """The lines of `text` that are not whole-line comments: `#` in scripts
    and TOML, `//` in Rust, `--` in Lean. Docstrings and strings count."""
    hashed = path.endswith(_HASH_COMMENTED) or text.startswith("#!")
    for line in text.splitlines():
        stripped = line.lstrip()
        if ((hashed and stripped.startswith("#")) or (path.endswith(".rs") and stripped.startswith("//"))
                or (path.endswith(".lean") and stripped.startswith("--"))):
            continue
        yield line


def targo_trust_refs(path, text):
    """Each targo-trust path `text` spells: below the package root literally
    (`targo-trust/src/x.rs`, a glob such as `targo-trust/*.rs`) or as joined
    quoted components (`"targo-trust" / "src"`, `"targo-trust", "src"`), and
    the package root itself (TARGO_TRUST_ROOT) where a line walks it: a
    scan-root list, a repository-anchored join, a `targo-trust/` prefix. A
    Rust source spells only root references here; the Cargo graph has its
    reads of single files (direct_reads). Comment lines are skipped."""
    refs = set()
    rust = path.endswith(".rs")
    for line in targo_trust_code_lines(path, text):
        if not rust:
            refs.update(match.group(0).rstrip(".,") for match in _TARGO_TRUST_LITERAL.finditer(line))
            refs.update("/".join(re.findall(r"""["']([^"']+)["']""", match.group(0)))
                        for match in _TARGO_TRUST_JOINED.finditer(line))
        if targo_trust_root_line(line):
            refs.add(TARGO_TRUST_ROOT)
    return refs


def targo_trust_root_line(line):
    """Whether `line` spells the package root as a walk (TARGO_TRUST_ROOT)."""
    return bool((_TARGO_TRUST_QUOTED_ROOT.search(line)
                 and any(match.group(1) in TARGO_TRUST_SOURCE_TOPS
                         for match in _TARGO_TRUST_QUOTED_TOP.finditer(line)))
                or _TARGO_TRUST_ANCHORED_ROOT.search(line) or _TARGO_TRUST_SHELL_ROOT.search(line)
                or _TARGO_TRUST_PREFIX_ROOT.search(line))


def targo_trust_ref_names(ref, path):
    """Whether reference `ref` names `path`: exactly, as a directory above it
    (the package root names every path), or as a glob; compared folded."""
    import fnmatch
    import land_select as ls
    ref, path = ls.fold(ref).rstrip("/"), ls.fold(path)
    if any(ch in ref for ch in "*?["):
        return fnmatch.fnmatchcase(path, ref)
    return path == ref or path.startswith(ref + "/")


def targo_trust_sites(graph):
    """{file: (references, root lines)} for every tracked regular file
    outside targo-trust/ and vendor/, other than Markdown and prose, whose
    text contains `targo-trust`, at the graph's commit: its targo_trust_refs
    and its non-comment lines that spell the root as a walk, stripped. None when git
    cannot answer. Read directly (not through the graph's classification
    reads): this is no classification input."""
    import land_select as ls
    cached = graph.__dict__.get("_targo_trust_sites")
    if cached is not None and cached[0] == graph.index.rev:
        return cached[1]
    command = ls._grep_command(graph, [*ls.GREP_AS_TEXT, "-l", "-z", "-F", "-e", TARGO_TRUST_COMPONENT,
                                       graph.index.rev, "--", ".",
                                       ls.GREP_EXCLUDE_LITERAL + TARGO_TRUST_COMPONENT,
                                       ls.GREP_EXCLUDE_LITERAL + "vendor"])
    import subprocess
    proc = subprocess.run(command, capture_output=True, env=ls.git_env(LC_ALL="C"))
    if proc.returncode not in (0, 1):
        return None
    prefix = graph.index.rev + ":"
    files = [raw[len(prefix):] if raw.startswith(prefix) else raw
             for raw in proc.stdout.decode("utf-8", "surrogateescape").split("\0") if raw]
    files = [file for file in files
             if not file.endswith(".md") and not ls.is_prose(file)
             and graph.index.entries.get(file, (None,))[0] in ("100644", "100755")]
    sites = {}
    if files:
        shas = {graph.index.entries[file][1] for file in files}
        try:
            out = ls.git(graph.index.repo, "cat-file", "--batch",
                         input_bytes=b"".join(sha.encode() + b"\n" for sha in sorted(shas)))
        except RuntimeError:
            return None
        blobs, pos = {}, 0
        for _ in shas:
            newline = out.find(b"\n", pos)
            header = out[pos:newline].split()
            if newline < 0 or len(header) != 3 or header[1] != b"blob":
                return None
            size = int(header[2])
            blobs[header[0].decode()] = out[newline + 1:newline + 1 + size]
            pos = newline + 1 + size + 1
        for file in files:
            text = blobs[graph.index.entries[file][1]].decode("utf-8", "replace")
            lines = frozenset(line.strip() for line in targo_trust_code_lines(file, text)
                              if targo_trust_root_line(line))
            sites[file] = (targo_trust_refs(file, text), lines)
    graph.__dict__["_targo_trust_sites"] = (graph.index.rev, sites)
    return sites


def targo_trust_root_reader(key):
    """The TARGO_TRUST_ROOT_READERS key covering file or directory `key`."""
    covering = [entry for entry in TARGO_TRUST_ROOT_READERS if key == entry or key.startswith(entry + "/")]
    return max(covering, key=len) if covering else None


def targo_trust_census_identifiers(graph):
    """The identifiers the compiler's single-issuer census counts, read from
    its function while that function is the one TARGO_TRUST_CENSUS_SHA256
    pins and it still walks targo-trust; None otherwise."""
    import hashlib
    source = TARGO_TRUST_CENSUS_SOURCE
    try:
        if not safe_regular(graph, source):
            return None
        text = graph.index.read_blobs([source])[source].decode("utf-8")
    except (OSError, RuntimeError, UnicodeError, KeyError):
        return None
    found = re.findall(r"^fn " + re.escape(TARGO_TRUST_CENSUS_FN) + r"\(\) \{\n.*?^\}$", text, re.S | re.M)
    if len(found) != 1 or len(re.findall(r"\bfn " + re.escape(TARGO_TRUST_CENSUS_FN) + r"\b", text)) != 1:
        return None
    if hashlib.sha256(found[0].encode("utf-8")).hexdigest() != TARGO_TRUST_CENSUS_SHA256:
        return None
    names = re.findall(r'^\s*const [A-Z_]+: &str = "([A-Za-z_][A-Za-z0-9_]*)";$', found[0], re.M)
    return sorted(set(names)) if names and '"targo-trust"' in found[0] else None


def targo_trust_root_handling(graph, key, path):
    """(checks, error) for root reader entry `key` and the changed `path`."""
    kind, leg, pinned, _reason = TARGO_TRUST_ROOT_READERS[key]
    if pinned is not None:
        sites = targo_trust_sites(graph)
        if sites is None:
            return set(), f"{path}: cannot read root reader {key}'s targo-trust lines"
        lines = frozenset().union(*(found for file, (_refs, found) in sites.items()
                                    if file == key or file.startswith(key + "/")))
        if lines != pinned:
            changed = sorted(lines ^ pinned)
            return set(), (f"{path}: root reader {key} has other targo-trust lines than were read "
                           f"(TARGO_TRUST_ROOT_READERS; first difference: {changed[0]!r}); re-read it")
    if kind == "check":
        return {leg}, None
    if kind == "census":
        names = targo_trust_census_identifiers(graph)
        if names is None:
            return set(), (f"{path}: {TARGO_TRUST_CENSUS_SOURCE} {TARGO_TRUST_CENSUS_FN} is not the census "
                           "that was read (TARGO_TRUST_CENSUS_SHA256); re-read it")
        try:
            # A deleted path names nothing; any other is read at this commit.
            data = graph.index.read_blobs([path])[path] if path in graph.index.entries else b""
        except (OSError, RuntimeError, KeyError):
            return set(), f"{path}: cannot read it for the single-issuer census"
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError:
            if path.endswith(".rs"):
                # The census reads every such file with read_to_string(...).expect(..),
                # so a .rs that is not UTF-8 panics it: refuse, never judge by a
                # lossy decode it does not make.
                return set(), (f"{path}: is not UTF-8, which {TARGO_TRUST_CENSUS_SOURCE} "
                               f"{TARGO_TRUST_CENSUS_FN} reads strictly; that census needs stage 1, "
                               "which this profile never builds")
            text = data.decode("utf-8", "replace")
        named = [name for name in names if name in text]
        if named:
            return set(), (f"{path}: names {', '.join(named)}, which {TARGO_TRUST_CENSUS_SOURCE} "
                           f"{TARGO_TRUST_CENSUS_FN} counts as a TCB authority issuer; that census needs "
                           "stage 1, which this profile never builds")
    return set(), None


def targo_trust_readers(graph, path):
    """(checks, tests, errors) for the non-Cargo files and the root readers
    that name `path`."""
    import land_select as ls
    sites = targo_trust_sites(graph)
    if sites is None:
        return set(), set(), [f"{path}: cannot list the files that name targo-trust paths"]
    checks, tests, errors = set(), set(), []
    for file, (refs, _lines) in sorted(sites.items()):
        named = sorted(ref for ref in refs if targo_trust_ref_names(ref, path))
        if not named or file in TARGO_TRUST_NAME_ONLY:
            continue
        key = targo_trust_root_reader(file)
        if key is not None:
            found, error = targo_trust_root_handling(graph, key, path)
            checks |= found
            if error:
                errors.append(error)
            continue
        check = next((leg for leg, (_command, readers) in TARGO_TRUST_READER_CHECKS.items()
                      if file in readers), None)
        if check is not None:
            checks.add(check)
            continue
        if all((file, ref) in TARGO_TRUST_NAME_ONLY_REFS for ref in named):
            continue
        module = re.fullmatch(r"scripts/tests/([A-Za-z0-9_]+_test)\.py", file)
        name = "scripts.tests." + module.group(1) if module else None
        if (name is not None and name not in ls.VALIDATION_UNJUDGED_MODULES
                and name not in ls.VALIDATION_UNMAPPED_RED):
            tests.add(name)
            continue
        if TARGO_TRUST_ROOT in named:
            errors.append(f"{path}: root reader {file} walks targo-trust and has no development check")
        else:
            errors.append(f"{path}: non-Cargo reader {file} has no development check")
    return checks, tests, errors


def targo_trust_directory_readers(graph, selection, path):
    """(package, read) for each read of another package whose target is a
    directory of targo-trust above `path` (the package root included): a
    walk, which direct_reads leaves to the full readsets."""
    import land_select as ls
    folded = ls.fold(path)
    found = []
    for package in graph.packages.values():
        if package.dir == TARGO_TRUST_COMPONENT:
            continue
        for read in package.reads:
            target = ls.fold(read.target).rstrip("/")
            if (read.listing and path in selection.in_place) or any(ch in target for ch in "*?["):
                continue
            if (target == ls.fold(TARGO_TRUST_COMPONENT) or target.startswith(ls.fold(TARGO_TRUST_COMPONENT) + "/")) \
                    and folded.startswith(target + "/"):
                found.append((package, read))
    return found


def targo_trust_reader_scope(graph, selection, path):
    """(reader_checks, tests, reader_tests, errors) for a changed targo-trust
    `path`: every reader outside the package must be a check this profile
    runs, an audited test target that runs fresh, or a declared name-only
    site; anything else refuses."""
    import land_select as ls
    readers, foreign, checks, errors = set(), set(), set(), []
    # Another package compiling this file in, or reading it exactly, is a
    # consumer the targo-trust suite does not test. An audited test-only
    # reader runs as its own fresh integration test target.
    for package, read in direct_reads(graph, selection, path):
        if package.dir == TARGO_TRUST_COMPONENT:
            continue
        test = audited_reader_test(graph, package, read)
        if test is None:
            foreign.add(package.dir)
        else:
            readers.add((package.dir, test, audited_site(read)))
    errors.extend(f"{path}: direct reader {reader} has no development check" for reader in sorted(foreign))
    # A package walking a directory above it: declared, audited, or refused.
    walkers = set()
    for package, read in targo_trust_directory_readers(graph, selection, path):
        test = audited_reader_test(graph, package, read)
        if test is not None:
            readers.add((package.dir, test, audited_site(read)))
            continue
        key = targo_trust_root_reader(package.dir)
        if key is None:
            walkers.add(f"{path}: directory reader {package.dir} walks {read.target} and has no development check")
            continue
        found, error = targo_trust_root_handling(graph, key, path)
        checks |= found
        if error:
            walkers.add(error)
    errors.extend(sorted(walkers))
    # A checker, gate, data file or root walker that names the file.
    found, tests, refused = targo_trust_readers(graph, path)
    checks |= found
    errors.extend(error for error in refused if error not in errors)
    if path in TOOL_NAME_READER_PINS:
        errors.append(f"{path}: land_development.TOOL_NAME_READER_PINS holds its blob for the tool-name "
                      "guide's custody; a change must renew that pin, which the full profile judges")
    # The Python checks whose declared subject is this exact file.
    tests = set(tests) | set(ls.VALIDATION_TEST_SUBJECTS.get(path, ()))
    return checks, tests, readers, errors


def tool_name_reader_owned(graph, package, read, path):
    import land_select as ls
    if (path != TOOL_NAME_GUIDE or read.target != path
            or (package.dir, read.cls, read.site) not in TOOL_NAME_READERS
            or not read.test_only or read.cwd or read.listing or read.doctest
            or not tool_name_inputs_available(graph)):
        return False
    source = read.site.removesuffix(" (audited)")
    audit = ls.load_audits(graph).get(source)
    return (ls.audit_holds(graph, source, audit)
            and audit.get("class") == read.cls and audit.get("test_only") is True
            and path in audit.get("reads", ()))


def targo_source_owner(path):
    if path in TARGO_NATIVE_CORE_SOURCES or path in TARGO_CLEANUP_CORE_SOURCES or path == TARGO_CORE_EXAMPLE:
        return LOCAL_GIT_CORE
    if path in TARGO_CLEANUP_SOURCES:
        return LOCAL_GIT_WORKSPACE
    return None


def targo_module_move(graph, base, path):
    """A removed old module has one explicit regular same-module destination."""
    import land_select as ls
    destination = TARGO_NATIVE_MODULE_MOVES.get(path)
    if destination is None or path in graph.index.entries or not safe_regular(graph, destination):
        return False
    try:
        before = ls.Graph(ls.TreeIndex.load(graph.index.repo, base), {}, {}, [], {}, {})
        return safe_regular(before, path) and destination not in before.index.entries
    except (OSError, RuntimeError, ValueError):
        return False


def targo_layout_move(graph, base, path):
    import land_select as ls
    old = next((old for old, new in TARGO_LAYOUT_ONLY_MOVES.items() if path in (old, new)), None)
    if old is None or not targo_module_move(graph, base, old):
        return False
    try:
        before = ls.TreeIndex.load(graph.index.repo, base)
        new = TARGO_LAYOUT_ONLY_MOVES[old]
        return before.read_blobs([old])[old] == graph.index.read_blobs([new])[new]
    except (OSError, RuntimeError, ValueError, KeyError):
        return False


def targo_checkout_layout_move(graph, base):
    """Only the module-file move, self-include spelling and Python locator.

    This grants no ownership of handler or adapter behavior. Ordinary core
    compilation/regressions remain separate from checker qualification.
    """
    import land_select as ls
    old, new, adapter = TARGO_CHECKOUT_LAYOUT_OLD, TARGO_CHECKOUT_LAYOUT_NEW, TARGO_CHECKOUT_LAYOUT_ADAPTER
    try:
        before = ls.Graph(ls.TreeIndex.load(graph.index.repo, base), {}, {}, [], {}, {})
        if (ls._index_spellings(graph).get(ls.fold(old))
                or ls._index_spellings(before).get(ls.fold(new))
                or not safe_regular(before, old) or not safe_regular(graph, new)
                or not safe_regular(before, adapter) or not safe_regular(graph, adapter)
                or before.index.entries[old][0] != graph.index.entries[new][0]
                or before.index.entries[adapter][0] != graph.index.entries[adapter][0]
                or graph.owner(new) != LOCAL_GIT_CORE or graph.opaque_owner(new)):
            return False
        manifests = [owner + "/Cargo.toml" for owner in (LOCAL_GIT_WORKSPACE, LOCAL_GIT_CORE)]
        for path in manifests:
            if not safe_regular(before, path) or not safe_regular(graph, path):
                return False
            if before.index.entries[path] != graph.index.entries[path]:
                # Only this separate exact build repair may compose. scope()
                # still requires its script/manifest/lock bundle for each
                # changed input; the core manifest remains byte-identical.
                if path != TARGO_MANIFEST or not targo_build_rs_manifest_addition(
                        before.index.read_blobs([path])[path], graph.index.read_blobs([path])[path]):
                    return False
        original = before.index.read_blobs([old, adapter])
        current = graph.index.read_blobs([new, adapter])
        old_include, new_include = b'include_bytes!("checkout_inputs.rs")', b'include_bytes!("mod.rs")'
        old_locator = b'NATIVE_SOURCE = "' + old.encode() + b'"\n'
        new_locator = b'NATIVE_SOURCE = "' + new.encode() + b'"\n'
        return (original[old].count(old_include) == 1 and original[old].count(new_include) == 0
                and current[new] == original[old].replace(old_include, new_include, 1)
                and original[adapter].count(old_locator) == 1
                and original[adapter].count(new_locator) == 0
                and current[adapter] == original[adapter].replace(old_locator, new_locator, 1))
    except (OSError, RuntimeError, ValueError, KeyError):
        return False


def targo_context_visibility_only(graph, base):
    """Only privatize the two existing context helpers, preserving all bodies.

    The general compiler module has no blanket native-core owner. An already
    private helper in the actual base stays byte-identical; only the remaining
    public prefixes may change, and at least one must actually change.
    """
    import land_select as ls
    path = TARGO_COMPILER_CONTEXT_VISIBILITY
    try:
        before = ls.Graph(ls.TreeIndex.load(graph.index.repo, base), {}, {}, [], {}, {})
        if not safe_regular(before, path) or not safe_regular(graph, path):
            return False
        old = before.index.read_blobs([path])[path]
        new = graph.index.read_blobs([path])[path]
        expected, changed = old, False
        for name in TARGO_PRIVATE_CONTEXT_HELPERS:
            signature = name.encode() + b"<L: std::borrow::Borrow<layout::LayoutPaths>>("
            public, private = b"\npub fn " + signature, b"\nfn " + signature
            if old.count(public) == 1 and old.count(private) == 0:
                expected = expected.replace(public, private, 1)
                changed = True
            elif old.count(public) != 0 or old.count(private) != 1:
                return False
        return changed and new == expected
    except (OSError, RuntimeError, ValueError, KeyError):
        return False


def targo_unused_patch_blocks(raw):
    """Read the writer's suffix framing without normalizing any row body."""
    import land_select as ls
    document = ls.tomllib.loads(raw.decode("utf-8"))
    rows = document["patch"]["unused"]
    header = b"\n[[patch.unused]]\n"
    parts = raw.split(header)
    if not isinstance(rows, list) or not rows or len(parts) != len(rows) + 1:
        raise ValueError("unused patch rows do not have the writer's framing")
    for body, row in zip(parts[1:], rows):
        if (not isinstance(row, dict) or not isinstance(row.get("name"), str) or not row["name"]
                or not isinstance(row.get("version"), str) or not row["version"]):
            raise ValueError("unused patch row has no literal package identity")
        if not body.endswith(b"\n") or body.endswith(b"\n\n"):
            raise ValueError("unused patch row has a different separator/trailer")
        parsed = ls.tomllib.loads((header[1:] + body).decode("utf-8"))
        if (set(parsed) != {"patch"} or set(parsed["patch"]) != {"unused"}
                or parsed["patch"]["unused"] != [row]):
            raise ValueError("unused patch block contains another input")
    return parts[0], tuple(parts[1:])


def targo_lock_metadata_equal(old, new, old_raw, new_raw):
    """Keep metadata exact except for a permutation of complete unused rows."""
    from collections import Counter
    before = {key: value for key, value in old.items() if key != "package"}
    after = {key: value for key, value in new.items() if key != "package"}
    if not any(isinstance(value.get("patch"), dict) and "unused" in value["patch"]
               for value in (before, after)):
        return before == after
    old_blocks, new_blocks = targo_unused_patch_blocks(old_raw), targo_unused_patch_blocks(new_raw)
    for metadata in (before, after):
        patch = metadata["patch"]
        metadata["patch"] = {key: value for key, value in patch.items() if key != "unused"}
    return before == after and Counter(old_blocks[1]) == Counter(new_blocks[1])


def targo_unused_patch_order_restoration(graph, base):
    """Own only a writer-row permutation; every other input byte stays exact."""
    from collections import Counter
    import land_select as ls
    manifests = ("Cargo.toml", TARGO_MANIFEST, LOCAL_GIT_CORE + "/Cargo.toml")
    try:
        before = ls.Graph(ls.TreeIndex.load(graph.index.repo, base), {}, {}, [], {}, {})
        if any(not safe_regular(tree, path) for tree in (before, graph) for path in (TARGO_LOCK, *manifests)):
            return False
        if any(graph.opaque_owner(path) or before.index.entries[path] != graph.index.entries[path]
               for path in manifests):
            return False
        docs = {path: ls.tomllib.loads(raw.decode("utf-8"))
                for path, raw in graph.index.read_blobs(manifests).items()}
        if (docs[TARGO_MANIFEST]["package"]["name"] != "targo"
                or docs[LOCAL_GIT_CORE + "/Cargo.toml"]["package"]["name"] != "targo-core"):
            return False
        old_raw = before.index.read_blobs([TARGO_LOCK])[TARGO_LOCK]
        new_raw = graph.index.read_blobs([TARGO_LOCK])[TARGO_LOCK]
        old_blocks, new_blocks = targo_unused_patch_blocks(old_raw), targo_unused_patch_blocks(new_raw)
        return (old_blocks[0] == new_blocks[0] and old_blocks[1] != new_blocks[1]
                and Counter(old_blocks[1]) == Counter(new_blocks[1]))
    except (OSError, RuntimeError, UnicodeError, ValueError, TypeError, KeyError):
        return False


def targo_lock_restoration(graph, base):
    """Only restore the existing unix path dependency's missing lock edge.

    This supplies focused development ownership, never a diagnostic Cargo
    waiver. Identities, versions, sources, checksums, metadata, every other
    edge and the manifests declaring this already-existing edge stay exact.
    """
    import land_select as ls
    try:
        before = ls.Graph(ls.TreeIndex.load(graph.index.repo, base), {}, {}, [], {}, {})
        owner, target = "crates/trust-certify", "crates/trust-resource-provenance"
        manifests = ("Cargo.toml", LOCAL_GIT_WORKSPACE + "/Cargo.toml", owner + "/Cargo.toml", target + "/Cargo.toml")
        if any(not safe_regular(tree, path) for tree in (before, graph) for path in (TARGO_LOCK, *manifests)):
            return False
        if any(graph.opaque_owner(path) for path in manifests):
            return False
        if any(before.index.entries[path] != graph.index.entries[path] for path in manifests):
            return False
        docs = {path: ls.tomllib.loads(raw.decode("utf-8"))
                for path, raw in graph.index.read_blobs(manifests).items()}
        package = docs[owner + "/Cargo.toml"]["package"]
        dependency = docs[target + "/Cargo.toml"]["package"]
        if (package["name"] != "trust-certify" or dependency["name"] != "trust-resource-provenance"
                or docs[owner + "/Cargo.toml"]["target"]["cfg(unix)"]["dependencies"].get(
                    "trust-resource-provenance") != {"path": "../trust-resource-provenance"}):
            return False
        old_raw = before.index.read_blobs([TARGO_LOCK])[TARGO_LOCK]
        new_raw = graph.index.read_blobs([TARGO_LOCK])[TARGO_LOCK]
        old = ls.tomllib.loads(old_raw.decode("utf-8"))
        new = ls.tomllib.loads(new_raw.decode("utf-8"))
        def rows(lock):
            result = {}
            for row in lock["package"]:
                key = (row["name"], row["version"], row.get("source", ""))
                edges = row.get("dependencies", [])
                if key in result or not isinstance(edges, list) or len(edges) != len(set(edges)):
                    raise ValueError("ambiguous lock package/edges")
                result[key] = row
            return result
        old_rows, new_rows = rows(old), rows(new)
        if old_rows.keys() != new_rows.keys() or not targo_lock_metadata_equal(old, new, old_raw, new_raw):
            return False
        def version(package):
            value = package["version"]
            if value == {"workspace": True}:
                value = docs["Cargo.toml"]["workspace"]["package"]["version"]
            if not isinstance(value, str):
                raise ValueError("unknown package version inheritance")
            return value
        source_key = (package["name"], version(package), "")
        target_key = (dependency["name"], version(dependency), "")
        # A bare lock edge must resolve uniquely, not to a second registry/git
        # package with the same name or an unrelated source/version.
        if ([key for key in old_rows if key[0] == source_key[0]] != [source_key]
                or [key for key in old_rows if key[0] == target_key[0]] != [target_key]):
            return False
        expected = old_rows[source_key].copy()
        edges = expected.get("dependencies", [])
        if "trust-resource-provenance" in edges:
            return False
        expected["dependencies"] = sorted([*edges, "trust-resource-provenance"])
        return all(new_rows[key] == (expected if key == source_key else value) for key, value in old_rows.items())
    except (OSError, RuntimeError, UnicodeError, ValueError, TypeError, KeyError):
        return False


def targo_sha2_lock_restoration(graph, base):
    """Repair only core's dangling edge to the already locked SHA256 crate.

    Main declared the inherited 0.11.0 requirement but recorded a nonexistent
    0.11.0 package instead of the existing 0.11.1 identity. No package version,
    source, checksum, metadata, other edge or declaring manifest may change.
    """
    import land_select as ls
    manifests = (LOCAL_GIT_WORKSPACE + "/Cargo.toml", LOCAL_GIT_CORE + "/Cargo.toml")
    try:
        before = ls.Graph(ls.TreeIndex.load(graph.index.repo, base), {}, {}, [], {}, {})
        if any(not safe_regular(tree, path) for tree in (before, graph) for path in (TARGO_LOCK, *manifests)):
            return False
        if any(graph.opaque_owner(path) or before.index.entries[path] != graph.index.entries[path]
               for path in manifests):
            return False
        docs = {path: ls.tomllib.loads(raw.decode("utf-8"))
                for path, raw in graph.index.read_blobs(manifests).items()}
        workspace, core = (docs[path] for path in manifests)
        package = core["package"]
        if (package["name"] != "targo-core"
                or core["dependencies"].get("sha2") != {"workspace": True}
                or workspace["workspace"]["dependencies"].get("sha2") != "0.11.0"):
            return False
        version = package["version"]
        if version == {"workspace": True}:
            version = workspace["workspace"]["package"]["version"]
        if not isinstance(version, str):
            return False
        old_raw = before.index.read_blobs([TARGO_LOCK])[TARGO_LOCK]
        new_raw = graph.index.read_blobs([TARGO_LOCK])[TARGO_LOCK]
        old = ls.tomllib.loads(old_raw.decode("utf-8"))
        new = ls.tomllib.loads(new_raw.decode("utf-8"))
        def rows(lock):
            result = {}
            for row in lock["package"]:
                key = (row["name"], row["version"], row.get("source", ""))
                edges = row.get("dependencies", [])
                if key in result or not isinstance(edges, list) or len(edges) != len(set(edges)):
                    raise ValueError("ambiguous lock package/edges")
                result[key] = row
            return result
        old_rows, new_rows = rows(old), rows(new)
        source_key = ("targo-core", version, "")
        target_key = ("sha2", "0.11.1", "registry+https://github.com/rust-lang/crates.io-index")
        if (old_rows.keys() != new_rows.keys() or target_key not in old_rows
                or [key for key in old_rows if key[0] == "targo-core"] != [source_key]
                or [key for key in old_rows if key[:2] == ("sha2", "0.11.1")] != [target_key]
                or any(key[:2] == ("sha2", "0.11.0") for key in old_rows)
                or not targo_lock_metadata_equal(old, new, old_raw, new_raw)):
            return False
        expected = old_rows[source_key].copy()
        edges = expected.get("dependencies", [])
        if "sha2 0.11.0" not in edges or "sha2 0.11.1" in edges:
            return False
        expected["dependencies"] = sorted("sha2 0.11.1" if edge == "sha2 0.11.0" else edge for edge in edges)
        return all(new_rows[key] == (expected if key == source_key else value) for key, value in old_rows.items())
    except (OSError, RuntimeError, UnicodeError, ValueError, TypeError, KeyError):
        return False


def targo_build_rs_manifest_addition(old, new):
    """One exact inherited local build dependency; every other byte stays put."""
    import land_select as ls
    header = b"[build-dependencies]\n"
    try:
        before = ls.tomllib.loads(old.decode("utf-8"))
        after = ls.tomllib.loads(new.decode("utf-8"))
        return (old.count(header) == 1
                and new == old.replace(header, header + b"build-rs.workspace = true\n", 1)
                and before["package"]["name"] == "targo"
                and before["workspace"]["dependencies"]["build-rs"] == {
                    "version": "0.3.6", "path": "crates/build-rs"}
                and "build-rs" not in before["build-dependencies"]
                and after["build-dependencies"]["build-rs"] == {"workspace": True})
    except (UnicodeError, ValueError, TypeError, KeyError):
        return False


def targo_build_rs_repair(graph, base):
    """Only this compiler getter/lint repair and its already-existing local edge.

    The preexisting, separately typed dangling SHA2 edge may compose with this
    repair. No package identity/checksum, other edge, local dependency input or
    manifest byte is thereby granted general development ownership.
    """
    import land_select as ls
    core_manifest = LOCAL_GIT_CORE + "/Cargo.toml"
    declaration = TARGO_BUILD_RS + "/Cargo.toml"
    input_source = TARGO_BUILD_RS + "/src/input.rs"
    paths = (TARGO_LOCK, TARGO_MANIFEST, TARGO_BUILD_SCRIPT, core_manifest, declaration, input_source)
    try:
        before = ls.Graph(ls.TreeIndex.load(graph.index.repo, base), {}, {}, [], {}, {})
        if any(not safe_regular(tree, path) for tree in (before, graph) for path in paths):
            return False
        if any(graph.opaque_owner(path) for path in paths[1:]):
            return False
        old_bytes, new_bytes = before.index.read_blobs(paths), graph.index.read_blobs(paths)
        if not targo_build_rs_manifest_addition(old_bytes[TARGO_MANIFEST], new_bytes[TARGO_MANIFEST]):
            return False
        old_script = old_bytes[TARGO_BUILD_SCRIPT]
        function = b"fn trust_std() {\n"
        if old_script.count(function) != 1 or old_script.count(TARGO_RUSTC_INPUT_BEFORE) != 1:
            return False
        start, change = old_script.index(function), old_script.index(TARGO_RUSTC_INPUT_BEFORE)
        end = old_script.find(b"\n}\n", start)
        if not start < change < end or new_bytes[TARGO_BUILD_SCRIPT] != old_script.replace(
                TARGO_RUSTC_INPUT_BEFORE, TARGO_RUSTC_INPUT_AFTER, 1):
            return False
        if old_bytes[core_manifest] != new_bytes[core_manifest]:
            return False
        prefix = TARGO_BUILD_RS + "/"
        if {p: v for p, v in before.index.entries.items() if p.startswith(prefix)} != {
                p: v for p, v in graph.index.entries.items() if p.startswith(prefix)}:
            return False
        workspace = ls.tomllib.loads(old_bytes[TARGO_MANIFEST].decode("utf-8"))
        dependency = ls.tomllib.loads(old_bytes[declaration].decode("utf-8"))["package"]
        core = ls.tomllib.loads(old_bytes[core_manifest].decode("utf-8"))
        if (dependency["name"] != "build-rs" or dependency["version"] != "0.3.7"
                or core["package"]["name"] != "targo-core"):
            return False
        def version(package):
            value = package["version"]
            if value == {"workspace": True}:
                value = workspace["workspace"]["package"]["version"]
            if not isinstance(value, str):
                raise ValueError("unknown local package version")
            return value
        old = ls.tomllib.loads(old_bytes[TARGO_LOCK].decode("utf-8"))
        new = ls.tomllib.loads(new_bytes[TARGO_LOCK].decode("utf-8"))
        def rows(lock):
            result = {}
            for row in lock["package"]:
                key = (row["name"], row["version"], row.get("source", ""))
                edges = row.get("dependencies", [])
                if key in result or not isinstance(edges, list) or len(edges) != len(set(edges)):
                    raise ValueError("ambiguous lock package/edges")
                result[key] = row
            return result
        old_rows, new_rows = rows(old), rows(new)
        if old_rows.keys() != new_rows.keys() or not targo_lock_metadata_equal(
                old, new, old_bytes[TARGO_LOCK], new_bytes[TARGO_LOCK]):
            return False
        source_key = ("targo", version(workspace["package"]), "")
        target_key = ("build-rs", "0.3.7", "")
        if ([key for key in old_rows if key[0] == "targo"] != [source_key]
                or [key for key in old_rows if key[0] == "build-rs"] != [target_key]):
            return False
        expected = dict(old_rows)
        source = expected[source_key].copy()
        if "build-rs" in source.get("dependencies", []):
            return False
        source["dependencies"] = sorted([*source.get("dependencies", []), "build-rs"])
        expected[source_key] = source
        core_key = ("targo-core", version(core["package"]), "")
        if [key for key in old_rows if key[0] == "targo-core"] != [core_key]:
            return False
        if "sha2 0.11.0" in old_rows[core_key].get("dependencies", []):
            sha2 = ("sha2", "0.11.1", "registry+https://github.com/rust-lang/crates.io-index")
            if (core["package"]["name"] != "targo-core"
                    or core["dependencies"].get("sha2") != {"workspace": True}
                    or workspace["workspace"]["dependencies"].get("sha2") != "0.11.0"
                    or [key for key in old_rows if key[:2] == ("sha2", "0.11.1")] != [sha2]
                    or any(key[:2] == ("sha2", "0.11.0") for key in old_rows)
                    or "sha2 0.11.1" in old_rows[core_key]["dependencies"]):
                return False
            expected[core_key] = dict(old_rows[core_key], dependencies=sorted(
                "sha2 0.11.1" if edge == "sha2 0.11.0" else edge
                for edge in old_rows[core_key]["dependencies"]))
        return new_rows == expected
    except (OSError, RuntimeError, UnicodeError, ValueError, TypeError, KeyError):
        return False


def targo_vendor_trigger_move(graph, base):
    import land_select as ls
    path = TARGO_TRIAGEBOT
    source = LOCAL_GIT_CORE + "/src/ops/cargo_vendor.rs"
    try:
        before = ls.Graph(ls.TreeIndex.load(graph.index.repo, base), {}, {}, [], {}, {})
        if not safe_regular(before, path) or not safe_regular(graph, path) or not targo_layout_move(graph, base, source):
            return False
        old = before.index.read_blobs([path])[path]
        new = graph.index.read_blobs([path])[path]
        old_path = b"src/ops/cargo_vendor.rs"
        new_path = TARGO_NATIVE_MODULE_MOVES[source].removeprefix(LOCAL_GIT_WORKSPACE + "/").encode()
        # Exactly the actual module trigger, with every other policy byte
        # unchanged; parsing also rejects a malformed/duplicate declaration.
        old_doc = ls.tomllib.loads(old.decode("utf-8"))
        new_doc = ls.tomllib.loads(new.decode("utf-8"))
        triggers = old_doc["autolabel"]["Command-vendor"]["trigger_files"]
        if (not isinstance(triggers, list) or triggers.count(old_path.decode()) != 1
                or new_doc["autolabel"]["Command-vendor"]["trigger_files"] != [
                    new_path.decode() if item == old_path.decode() else item for item in triggers]):
            return False
        return old.count(old_path) == 1 and old.replace(old_path, new_path, 1) == new
    except (OSError, RuntimeError, UnicodeError, ValueError, KeyError, TypeError):
        return False


def oracle_citation_repair(index, base):
    """Own locator repairs only; every actual oracle row still executes.

    An old Rust module locator can name its unchanged owning source file.
    No waiver identity, pin, date, rationale, claim or function name changes.
    The real oracle reader, not this eligibility check, judges executable
    citations. New waivers and every other ledger edit retain refusal.
    """
    import land_select as ls
    citation = re.compile(r"(?<![A-Za-z0-9_/])((?:crates|compiler|src|tests)/[A-Za-z0-9_/-]+\.rs)::([A-Za-z_][A-Za-z0-9_]*)")
    try:
        before = ls.TreeIndex.load(index.repo, base)
        if any(tree.entries.get(ORACLE_WAIVERS, (None,))[0] != "100644"
               for tree in (before, index)):
            return False
        old = before.read_blobs([ORACLE_WAIVERS])[ORACLE_WAIVERS].decode("utf-8").splitlines(keepends=True)
        new = index.read_blobs([ORACLE_WAIVERS])[ORACLE_WAIVERS].decode("utf-8").splitlines(keepends=True)
        if len(old) != len(new):
            return False
        changed = False
        for original, current in zip(old, new):
            if original == current:
                continue
            left, right = original.split("|", 4), current.split("|", 4)
            if len(left) != 5 or len(right) != 5 or left[:4] != right[:4]:
                return False
            if (before.entries.get(left[0], (None,))[0] != "100644"
                    or before.entries.get(left[0]) != index.entries.get(left[0])):
                return False
            normalized, repairs = right[4], 0
            for match in list(citation.finditer(right[4])):
                source, function = match.groups()
                if any(part in ("", ".", "..") for part in source.split("/")):
                    return False
                module = posixpath.basename(source)[:-3]
                previous = module + "::tests::" + function
                if previous not in left[4]:
                    continue
                if source != posixpath.join(posixpath.dirname(left[0]), module + ".rs"):
                    return False
                if (before.entries.get(source, (None,))[0] != "100644"
                        or before.entries.get(source) != index.entries.get(source)):
                    return False
                body = index.read_blobs([source])[source]
                if len(re.findall(rb"\bfn\s+" + re.escape(function.encode("ascii")) + rb"\s*\(", body)) != 1:
                    return False
                normalized = normalized.replace(match.group(), previous)
                repairs += 1
            if not repairs or normalized != left[4]:
                return False
            changed = True
        return changed
    except (OSError, RuntimeError, UnicodeError, ValueError, KeyError, TypeError, AttributeError):
        return False


def local_git_owner(path, index=None, base=None):
    if path.startswith(LOCAL_GIT_IMPORT):
        return LOCAL_GIT_CORE
    if path == LOCAL_GIT_FIXTURE:
        return LOCAL_GIT_WORKSPACE
    if index is not None:
        return local_git_bridge_owner(index, base, path)
    return None


def local_git_bridge_owner(index, base, path):
    """Bind only additive DATA API plumbing, never a registry implementation.

    Whole native library/CLI cohorts still execute afresh. This syntactic
    boundary selects their owner; it supplies no compiler/source attestation.
    """
    import land_select as ls
    if path not in LOCAL_GIT_BRIDGES or not base:
        return None
    try:
        before = ls.TreeIndex.load(index.repo, base)
        if any(tree.entries.get(path, (None,))[0] != "100644" for tree in (before, index)):
            return None
        old = before.read_blobs([path])[path]
        new = index.read_blobs([path])[path]
        if path == LOCAL_GIT_EXPORT:
            if old.count(LOCAL_GIT_SNAPSHOT_EXPORT) or new.count(LOCAL_GIT_SNAPSHOT_EXPORT) != 1:
                return None
            stripped = new.replace(LOCAL_GIT_SNAPSHOT_EXPORT, b"", 1)
        elif path == LOCAL_GIT_REGISTRY:
            public = b"pub(crate) " + LOCAL_GIT_REGISTRY_DECL
            if old.count(LOCAL_GIT_REGISTRY_DECL) != 1 or new.count(public) != 1:
                return None
            stripped = new.replace(public, LOCAL_GIT_REGISTRY_DECL, 1)
        else:
            if not LOCAL_GIT_FETCH_ADDITIONS:
                return None
            stripped = new
            for addition in LOCAL_GIT_FETCH_ADDITIONS:
                if old.count(addition) or stripped.count(addition) != 1:
                    return None
                stripped = stripped.replace(addition, b"", 1)
        if stripped != old:
            return None
        return LOCAL_GIT_WORKSPACE if path == LOCAL_GIT_FETCH else LOCAL_GIT_CORE
    except (OSError, RuntimeError, UnicodeError, ValueError, KeyError, TypeError, AttributeError):
        return None


def bootstrap_library_source(path):
    import land_select as ls
    folded = ls.fold(path)
    return (path.startswith(BOOTSTRAP_COMPONENT + "/src/")
            and not folded.startswith(BOOTSTRAP_COMPONENT + "/src/bin/")
            and folded != BOOTSTRAP_COMPONENT + "/src/main.rs"
            and path.endswith((".rs", ".snap")))


def build_tree_admission_source(path):
    """The library admission module, excluding CLI and manifest inputs."""
    return (path.endswith(".rs") and
            (path == BUILD_TREE_COMPONENT + "/src/admission.rs"
             or path.startswith(BUILD_TREE_COMPONENT + "/src/admission/")))


def may_have_scope(paths):
    """Negative-only fast filter. True never supplies eligibility or a SKIP."""
    import land_select as ls
    return all(path in ("Cargo.lock", ORACLE_WAIVERS, TARGO_LOCK, TARGO_TRIAGEBOT)
               or path in TARGO_BUILD_INPUT_SOURCES or path in TARGO_CHECKOUT_LAYOUT_PATHS
               or path in PROGRAM_TESTS or path in ls.VALIDATION_PROGRAM_TESTS
               or any(path.startswith(owner + "/") for owner in COMPONENTS - {BOOTSTRAP_COMPONENT})
               or bootstrap_library_source(path)
               or local_git_owner(path) is not None or path in LOCAL_GIT_BRIDGES
               or targo_source_owner(path) is not None
               or path in CONTROLLER_DESCRIPTOR_SOURCES
               or path == TOOL_NAME_TEST
               or path.startswith(TARGO_TRUST_COMPONENT + "/")
               or path.startswith("tests/run-make/") or ls.is_prose(path) for path in paths)


def controller_feature_extension(index, base):
    """Prove unchanged package/dependency inputs and legacy feature activations.

    Only the registered receiver cohort may be newly exposed. This is not a
    source/readset attestation; its complete native cohorts still run afresh.
    """
    import land_select as ls
    if not base:
        return False
    path = CONTROLLER_COMPONENT + "/Cargo.toml"
    try:
        before = ls.TreeIndex.load(index.repo, base)
        if any(tree.entries.get(path, (None,))[0] != "100644" for tree in (before, index)):
            return False
        old = ls.tomllib.loads(before.read_blobs([path])[path].decode("utf-8"))
        new = ls.tomllib.loads(index.read_blobs([path])[path].decode("utf-8"))
        old_features, new_features = old.pop("features", {}), new.pop("features", {})
        def identical(left, right):
            if type(left) is not type(right):
                return False
            if isinstance(left, dict):
                return left.keys() == right.keys() and all(identical(v, right[k]) for k, v in left.items())
            if isinstance(left, list):
                return len(left) == len(right) and all(identical(a, b) for a, b in zip(left, right))
            return left == right

        package = old.get("package", {})
        if (not identical(old, new) or not isinstance(package, dict)
                or package.get("name") != "trust-resource-controller"
                or package.get("build") is not None
                or old.get("lib", {}).get("path", "src/lib.rs") != "src/lib.rs"):
            return False
        build_script = CONTROLLER_COMPONENT + "/build.rs"
        if any(build_script in tree.entries for tree in (before, index)):
            for tree in (before, index):
                if tree.entries.get(build_script, (None,))[0] != "100644":
                    return False
                raw = tree.read_blobs([build_script])[build_script]
                if hashlib.sha256(raw).hexdigest() != CONTROLLER_BUILD_SCRIPT_SHA256:
                    return False
        if (not isinstance(old_features, dict) or not isinstance(new_features, dict)
                or not old_features.keys() <= new_features.keys()
                or not (new_features.keys() - old_features.keys()) <= {"bootstrap-receiver"}
                or old_features.get("default", []) != new_features.get("default", [])):
            return False
        for features in (old_features, new_features):
            if any(not isinstance(values, list) or any(not isinstance(v, str) for v in values)
                   for values in features.values()):
                return False
        added = new_features.keys() - old_features.keys()

        def implicit_features(features):
            result = dict(features)
            tables = [old.get("dependencies", {}), old.get("build-dependencies", {})]
            for target in old.get("target", {}).values():
                tables.extend((target.get("dependencies", {}), target.get("build-dependencies", {})))
            suppressed = {value[4:] for values in features.values() for value in values if value.startswith("dep:")}
            for table in tables:
                for name, dependency in table.items():
                    if (isinstance(dependency, dict) and dependency.get("optional") is True
                            and name not in result and name not in suppressed):
                        result[name] = ["dep:" + name]
            return result

        old_activations = implicit_features(old_features)
        new_activations = implicit_features(new_features)
        if not old_activations.keys() <= new_activations.keys():
            return False
        new_nodes = new_activations.keys() - old_activations.keys()

        def activation(features, name, visiting=frozenset()):
            if name not in features:
                return {name}
            if name in visiting:
                raise ValueError("cyclic feature activation")
            result = {name}
            for value in features[name]:
                result.update(activation(features, value, visiting | {name}))
            return result

        if any(activation(old_activations, name) != activation(new_activations, name) - new_nodes
               for name in old_activations):
            return False
        # Reject literal dormant cfg/environment reads in original component sources.
        rust = [p for p in before.entries if p.startswith(CONTROLLER_COMPONENT + "/") and p.endswith(".rs")]
        if any(before.entries[path][0] not in ("100644", "100755") for path in rust):
            return False
        needles = {spelling.encode() for feature in added for spelling in
                   (feature, feature.replace("-", "_"), feature.replace("-", "_").upper())}
        if needles and any(needle in raw for raw in before.read_blobs(rust).values() for needle in needles):
            return False
        return True
    except (OSError, RuntimeError, UnicodeError, ValueError, KeyError, TypeError, AttributeError):
        return False


def has_declared_source_ownership(index, paths, base=None):
    """Only registered execution sources, never arbitrary reader/data reach.

    Cargo declarations, prose, links and recipes retain ordinary discovery,
    except the exact Targo build-input/lock/trigger transformations checked by scope().
    A positive result selects fresh tests, never full diagnostic coverage.
    """
    import land_select as ls
    receiver_manifest = (CONTROLLER_COMPONENT + "/Cargo.toml" in paths
                         and controller_feature_extension(index, base))
    for path in paths:
        moved = TARGO_CHECKOUT_LAYOUT_NEW if path == TARGO_CHECKOUT_LAYOUT_OLD else TARGO_NATIVE_MODULE_MOVES.get(path)
        if (index.entries.get(path, (None,))[0] not in ("100644", "100755")
                and not (path not in index.entries and moved in index.entries
                         and index.entries[moved][0] in ("100644", "100755"))):
            return False
        ancestors = path.split("/")[:-1]
        if any(index.entries.get("/".join(ancestors[:n]), (None,))[0] in ("120000", "160000")
               for n in range(1, len(ancestors) + 1)):
            return False
        if not (path in PROGRAM_TESTS or path == TEST_BODY_PROGRAM
                or path in ls.VALIDATION_PROGRAM_TESTS
                or path == TOOL_NAME_TEST
                or path in CONTROLLER_DESCRIPTOR_SOURCES
                or targo_source_owner(path) is not None or path in (TARGO_LOCK, TARGO_TRIAGEBOT)
                or path.startswith("crates/trust-build-cpu/src/")
                or path.startswith(CONTROLLER_COMPONENT + "/src/")
                or (path.startswith(PROVENANCE_COMPONENT + "/src/") and path.endswith(".rs"))
                or (receiver_manifest and path == CONTROLLER_COMPONENT + "/Cargo.toml")
                or bootstrap_library_source(path)
                or build_tree_admission_source(path)
                or path in TARGO_BUILD_INPUT_SOURCES
                or path in TARGO_CHECKOUT_LAYOUT_PATHS):
            return False
    return bool(paths)


def native_domain_owner(graph, selection):
    """Recognize this isolated module change without narrowing other CPU APIs."""
    import land_select as ls
    cpu = [path for path in selection.changed if path.startswith("crates/trust-build-cpu/")]
    if not cpu or not set(cpu) <= NATIVE_DOMAIN_SOURCES:
        return False
    debt = "crates/trust-build-cpu/src/external_debt.rs"
    if debt not in cpu:
        return True
    before = ls.TreeIndex.load(graph.index.repo, selection.base)
    if (before.entries.get(debt, (None,))[0] != "100644"
            or graph.index.entries.get(debt, (None,))[0] != "100644"):
        return False
    old = before.read_blobs([debt])[debt]
    new = graph.index.read_blobs([debt])[debt]
    return new.count(RETAINED_IDENTITY_ACCESSOR) == 1 and new.replace(RETAINED_IDENTITY_ACCESSOR, b"", 1) == old


def direct_reads(graph, selection, path):
    """(package, read) for each read that needs a focused check of `path`.

    Exact content/compile readers need a focused check. Broad runtime
    directory/walk/potential consumers remain in the FULL diagnostic
    readsets; this profile does not claim to test them.
    """
    import land_select as ls

    def required(read):
        if read.listing and path in selection.in_place:
            return False
        if not ls._reads(graph, path, ls._InputSet({read.target})):
            return False
        if read.cls == "compile":
            return True
        if read.cls != "runtime":
            return False
        if ls.fold(read.target) == ls.fold(path) or any(ch in read.target for ch in "*?["):
            return True
        resolved = ls._realpath(graph, "", read.target)
        return graph.index.entries.get(resolved, (None,))[0] in ("100644", "100755")
    return [(package, read) for package in graph.packages.values() for read in package.reads if required(read)]


def scope(graph, selection):
    import land_select as ls

    result = Scope()
    import land_manifest
    repaired_lock = (LOCAL_GIT_LOCK in selection.changed and
                     land_manifest.existing_local_lock_repair(graph, selection.base, LOCAL_GIT_LOCK))
    repaired_citations = (ORACLE_WAIVERS in selection.changed and
                          oracle_citation_repair(graph.index, selection.base))
    build_input_owned = targo_build_rs_repair(graph, selection.base) if set(selection.changed) & (
        TARGO_BUILD_INPUT_SOURCES | {TARGO_LOCK}) else False
    lock_owned = TARGO_LOCK in selection.changed and (
        build_input_owned or targo_lock_restoration(graph, selection.base)
        or targo_sha2_lock_restoration(graph, selection.base)
        or targo_unused_patch_order_restoration(graph, selection.base))
    trigger_owned = TARGO_TRIAGEBOT in selection.changed and targo_vendor_trigger_move(graph, selection.base)
    checkout_layout_owned = bool(set(selection.changed) & TARGO_CHECKOUT_LAYOUT_PATHS) and targo_checkout_layout_move(graph, selection.base)
    if selection.everything:
        # Full diagnostics conservatively classify scripts as global. This
        # development profile has explicit test ownership for these inputs.
        # Discharge only that exact path reason, retaining unresolved/global
        # graph facts and every unowned path.
        owned_reasons = set()
        for path in selection.changed:
            if (path in PROGRAM_TESTS or (path == LOCAL_GIT_LOCK and repaired_lock)
                    or (path in TARGO_BUILD_INPUT_SOURCES and build_input_owned)
                    or (path in TARGO_CHECKOUT_LAYOUT_PATHS and checkout_layout_owned)
                    or (path == TARGO_LOCK and lock_owned) or (path == TARGO_TRIAGEBOT and trigger_owned)
                    or (path == ORACLE_WAIVERS and repaired_citations)
                    or (bootstrap_library_source(path)
                        and graph.owner(path) == BOOTSTRAP_COMPONENT
                        and not graph.opaque_owner(path) and safe_regular(graph, path))
                    or (path == CONTROLLER_COMPONENT + "/Cargo.toml"
                        and graph.owner(path) == CONTROLLER_COMPONENT
                        and not graph.opaque_owner(path))):
                kind, why = ls.classify(graph, path)
                if kind == "everything":
                    owned_reasons.add(f"{path}: {why}")
        result.errors.extend(reason for reason in selection.everything if reason not in owned_reasons)
    owners, recipes, tests = set(), set(), set()
    for path in selection.changed:
        if path == TOOL_NAME_TEST:
            if tool_name_inputs_available(graph):
                result.tool_name_guide = True
            else:
                result.errors.append(f"{path}: actual tool-name reader/input custody unavailable")
            continue
        if path in TARGO_BUILD_INPUT_SOURCES:
            if build_input_owned and graph.owner(path) == LOCAL_GIT_WORKSPACE:
                result.targo_native_core = result.targo_cleanup = True
            else:
                result.errors.append(f"{path}: unsupported native Targo build input delta")
            continue
        if path in TARGO_CHECKOUT_LAYOUT_PATHS:
            if not checkout_layout_owned:
                result.errors.append(f"{path}: unsupported Targo module-layout/locator delta")
            else:
                result.targo_native_core = True
                tests.add(TARGO_CHECKOUT_LAYOUT_TEST)
            continue
        targo_owner = targo_source_owner(path)
        if targo_owner is not None:
            layout_only = path in TARGO_LAYOUT_ONLY_MOVES or path in TARGO_LAYOUT_ONLY_MOVES.values()
            if (graph.owner(path) != targo_owner or graph.opaque_owner(path)
                    or not (safe_regular(graph, path) or targo_module_move(graph, selection.base, path))
                    or layout_only and not targo_layout_move(graph, selection.base, path)
                    or path == TARGO_COMPILER_CONTEXT_VISIBILITY
                    and not targo_context_visibility_only(graph, selection.base)):
                result.errors.append(f"{path}: cannot establish declared native Targo source owner")
            else:
                result.targo_cleanup |= path in TARGO_CLEANUP_SOURCES
                result.targo_native_core |= path in TARGO_NATIVE_CORE_SOURCES or path in TARGO_CLEANUP_CORE_SOURCES
                result.targo_core_example |= path == TARGO_CORE_EXAMPLE
            continue
        if path in (TARGO_LOCK, TARGO_TRIAGEBOT):
            if path == TARGO_LOCK and lock_owned:
                result.targo_native_core = result.targo_cleanup = True
            elif path == TARGO_LOCK and repaired_lock:
                result.local_git_import = True
            elif path == TARGO_TRIAGEBOT and trigger_owned:
                result.targo_native_core = True
            else:
                result.errors.append(f"{path}: unsupported native Targo Cargo/policy delta")
            continue
        if graph.index.entries.get(path, ("100644",))[0] not in ("100644", "100755"):
            result.errors.append(f"{path}: changed source input is not a regular file")
            continue
        if path == TEST_BODY_PROGRAM:
            owned_tests, error = changed_test_classes(graph, selection.base, path)
            if error:
                result.errors.append(error)
            tests.update(owned_tests)
            continue
        if path == ORACLE_WAIVERS and repaired_citations:
            result.oracle_citations = True
            tests.add("scripts.tests.land_development_test.OracleCitationOwnershipTests")
            continue
        if path in selection.cargo_impacts:
            # Eligibility is changed input ownership. The full conservative
            # activation/consumer impact set stays in diagnostic selection;
            # this profile does not claim to test every possible consumer.
            if path != "Cargo.lock":
                owner = graph.owner(path)
                if (path == TARGO_TRUST_MANIFEST and owner == TARGO_TRUST_COMPONENT
                        and not graph.opaque_owner(path)):
                    # Only land_manifest.scoped_inputs' proven bounded case
                    # reaches here: added local path dependencies with their
                    # exact lock edges, every other manifest table unchanged.
                    # Any other targo-trust manifest edit keeps its global
                    # classification and refuses this profile. Its readers
                    # are classified as a source file's are; the declared
                    # checker that reads it (workspace inheritance) runs too.
                    checks, named_tests, readers, refused = targo_trust_reader_scope(graph, selection, path)
                    if refused:
                        result.errors.extend(refused)
                        continue
                    result.targo_trust = True
                    result.reader_checks = sorted(set(result.reader_checks) | checks
                                                  | {"development-reader-toolchain-coherence"})
                    tests.update(named_tests)
                    result.reader_tests = sorted(set(result.reader_tests) | readers)
                elif owner not in COMPONENTS or owner in (BOOTSTRAP_COMPONENT, BUILD_TREE_COMPONENT):
                    result.errors.append(f"{path}: unsupported changed Cargo owner")
                else:
                    owners.add(owner)
            continue
        if path in PROGRAM_TESTS:
            tests.update(PROGRAM_TESTS[path])
            continue
        if path in ls.VALIDATION_PROGRAM_TESTS:
            tests.update(ls.VALIDATION_PROGRAM_TESTS[path])
            continue
        owner = graph.owner(path)
        if path in CONTROLLER_DESCRIPTOR_SOURCES:
            if owner != CONTROLLER_DESCRIPTORS or graph.opaque_owner(path):
                result.errors.append(f"{path}: cannot establish declared controller descriptor owner")
            else:
                result.controller_descriptors = True
            continue
        local_git = local_git_owner(path, graph.index, selection.base)
        if local_git is not None:
            if owner != local_git or graph.opaque_owner(path):
                result.errors.append(f"{path}: cannot establish declared local Git importer owner")
            else:
                result.local_git_import = True
            continue
        if owner in COMPONENTS:
            if owner == PROVENANCE_COMPONENT and not (
                    path.endswith(".rs") and path.startswith((owner + "/src/", owner + "/tests/"))):
                result.errors.append(f"{path}: no native provenance Rust target owner")
                continue
            if owner == BOOTSTRAP_COMPONENT and not bootstrap_library_source(path):
                result.errors.append(f"{path}: no Bootstrap library-only source owner")
                continue
            if (owner == BUILD_TREE_COMPONENT and not build_tree_admission_source(path)
                    and path != BUILD_TREE_COMPONENT + "/README.md"):
                result.errors.append(f"{path}: no build-tree admission-library source owner")
                continue
            if graph.opaque_owner(path):
                result.errors.append(f"{path}: unknown component manifest")
            owners.add(owner)
            continue
        if owner == TARGO_TRUST_COMPONENT:
            # A build input with a global classification (manifest, build
            # script, Cargo configuration, lock, toolchain pin) is no source
            # file of this package; its full selection already refuses too.
            # Nor is anything outside src/ and tests/ (benches/ is not built
            # by the suite), or a formatter, linter or attribute file.
            reason = ls.everything_reason(path) or targo_trust_source(path)
            if reason:
                result.errors.append(f"{path}: {reason}: no targo-trust development owner")
                continue
            if graph.opaque_owner(path):
                result.errors.append(f"{path}: unknown targo-trust manifest")
                continue
            if path in graph.index.entries and not safe_regular(graph, path):
                result.errors.append(f"{path}: cannot establish targo-trust source owner")
                continue
            checks, named_tests, readers, refused = targo_trust_reader_scope(graph, selection, path)
            if refused:
                result.errors.extend(refused)
                continue
            result.reader_checks = sorted(set(result.reader_checks) | checks)
            tests.update(named_tests)
            result.reader_tests = sorted(set(result.reader_tests) | readers)
            result.targo_trust = True
            continue
        if path.startswith("tests/run-make/"):
            moved = trust_recipe_move(graph, selection.base, path)
            if moved is not None:
                recipes.add(moved)
                continue
            recipe = posixpath.dirname(path)
            while recipe.startswith("tests/run-make/"):
                if recipe + "/rmake.rs" in graph.index.entries:
                    break
                recipe = posixpath.dirname(recipe)
            if recipe.startswith("tests/run-make/"):
                recipes.add(recipe)
                continue
            result.errors.append(f"{path}: no actual recipe owns changed input")
            continue
        if ls.is_prose(path):
            if path == TOOL_NAME_GUIDE:
                # Discovery losing a read must never remove this actual-input
                # check. Still inspect every read below for unowned consumers.
                if tool_name_inputs_available(graph):
                    result.tool_name_guide = True
                else:
                    result.errors.append(f"{path}: actual tool-name reader/input custody unavailable")
            for package, read in direct_reads(graph, selection, path):
                if tool_name_reader_owned(graph, package, read, path):
                    result.tool_name_guide = True
                    continue
                if package.dir in COMPONENTS:
                    owners.add(package.dir)
                else:
                    result.errors.append(f"{path}: direct reader {package.dir} has no development check")
            continue
        result.errors.append(f"{path}: no declared development component/test owner")
    if owners:
        # Test changed packages and execution components that consume them;
        # normal library tests execute, rather than a scheduler-only filter.
        execution_components = ({"crates/trust-build-cpu"} if native_domain_owner(graph, selection)
                                else COMPONENTS)
        for component in execution_components:
            if graph.closure({component}) & owners:
                result.packages.append(component)
        if set(result.packages) & SCHEDULER_COMPONENTS:
            recipes.update(INTEGRATION_RECIPES)
        # The exit regression is introduced with the real scheduler repair.
        # Earlier public trees get the existing controls, never a fictitious
        # passing case. Once either real input exists, retain the requirement.
        if (set(result.packages) & SCHEDULER_COMPONENTS
                and (EXIT_RECIPE + "/rmake.rs" in graph.index.entries or SCHEDULER_MODULE in graph.index.entries)):
            recipes.add(EXIT_RECIPE)
    for recipe in recipes:
        if graph.index.entries.get(recipe + "/rmake.rs", (None,))[0] not in ("100644", "100755"):
            result.errors.append(f"{recipe}: required normal recipe missing or not regular")
    if result.local_git_import:
        for owner, name in ((LOCAL_GIT_CORE, "targo-core"), (LOCAL_GIT_WORKSPACE, "targo")):
            manifest = owner + "/Cargo.toml"
            package = graph.packages.get(owner)
            if (package is None or package.name != name or graph.opaque_owner(manifest)
                    or graph.index.entries.get(manifest, (None,))[0] not in ("100644", "100755")):
                result.errors.append(f"{manifest}: required local Git importer manifest missing or unknown")
        if graph.index.entries.get(LOCAL_GIT_FIXTURE, (None,))[0] not in ("100644", "100755"):
            result.errors.append(f"{LOCAL_GIT_FIXTURE}: required native fixture missing or not regular")
    if result.controller_descriptors:
        manifest = CONTROLLER_DESCRIPTORS + "/Cargo.toml"
        package = graph.packages.get(CONTROLLER_DESCRIPTORS)
        if (package is None or package.name != "trust-resource-controller" or graph.opaque_owner(manifest)
                or graph.index.entries.get(manifest, (None,))[0] not in ("100644", "100755")):
            result.errors.append(f"{manifest}: required controller descriptor manifest missing or unknown")
        for source in sorted(CONTROLLER_DESCRIPTOR_SOURCES):
            if graph.index.entries.get(source, (None,))[0] not in ("100644", "100755"):
                result.errors.append(f"{source}: required controller descriptor source missing or not regular")
    if result.targo_native_core or result.targo_cleanup or result.targo_core_example:
        for owner, name in ((LOCAL_GIT_CORE, "targo-core"), (LOCAL_GIT_WORKSPACE, "targo")):
            manifest = owner + "/Cargo.toml"
            package = graph.packages.get(owner)
            if (package is None or package.name != name or graph.opaque_owner(manifest)
                    or not safe_regular(graph, manifest)):
                result.errors.append(f"{manifest}: required native Targo manifest missing or unknown")
        required = set()
        if result.targo_cleanup:
            required.update(TARGO_CLEANUP_SOURCES)
        if result.targo_native_core:
            required.update(TARGO_NATIVE_TEST_SOURCES)
            for source in (LOCAL_GIT_CORE + "/src/compiler/candidate_dependencies.rs",
                           LOCAL_GIT_CORE + "/src/compiler/native_job.rs"):
                required.add(source if source in graph.index.entries else TARGO_NATIVE_MODULE_MOVES[source])
        for path in sorted(required):
            owner = targo_source_owner(path) or LOCAL_GIT_CORE
            if not safe_regular(graph, path) or graph.owner(path) != owner or graph.opaque_owner(path):
                result.errors.append(f"{path}: required native Targo test/source input missing, foreign or unsafe")
    result.packages.sort()
    result.recipes = sorted(recipes)
    result.tests = sorted(tests)
    return result


def trust_recipe_move(graph, base, path):
    """Recognize only a complete byte-identical move into the Trust namespace."""
    import land_select as ls
    prefix = "tests/run-make/"
    if not path.startswith(prefix) or path in graph.index.entries:
        return None
    parts = path[len(prefix):].split("/")
    if len(parts) < 2 or parts[0].startswith("trust"):
        return None
    old = prefix + parts[0] + "/"
    new = prefix + "trust-" + parts[0] + "/"
    try:
        before = ls.Graph(ls.TreeIndex.load(graph.index.repo, base), {}, {}, [], {}, {})
        old_files = {p[len(old):]: entry for p, entry in before.index.entries.items()
                     if p.startswith(old)}
        new_files = {p[len(new):]: entry for p, entry in graph.index.entries.items()
                     if p.startswith(new)}
        if ("rmake.rs" not in old_files or old_files != new_files
                or any(p.startswith(old) for p in graph.index.entries)
                or any(p.startswith(new) for p in before.index.entries)
                or any(not safe_regular(before, old + name)
                       or not safe_regular(graph, new + name) for name in old_files)):
            return None
        return new.rstrip("/")
    except (OSError, RuntimeError, ValueError):
        return None


def recipe_result(directory, targets, log, exit_code, source_root, host, stage=1):
    """Check the existing normal bootstrap case streams against caller targets.

    Counts/labels alone grant nothing: every actual selected case must have
    one start and one successful terminal, in every started normal target.
    The executor creates this directory fresh; stale files are never reused.
    """
    if exit_code:
        return exit_code, "normal recipe command failed"
    expected = {"[run-make] " + target for target in targets}
    if not expected or len(expected) != len(targets):
        return 2, "invalid/empty expected normal recipe population"

    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate case event key")
            result[key] = value
        return result

    try:
        files = sorted(directory.glob("compiletest-events-*.jsonl"))
        clean = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", log)
        starts = re.findall(r"^Testing stage(\d+) with compiletest suite=(\S+) mode=(\S+) \(([^\n()]+)\)", clean, re.M)
        identities = {(int(s), suite, mode, target) for s, suite, mode, target in starts}
        if (not files or len(starts) != len(files) or len(identities) != len(starts)
                or any(s != stage or suite != "run-make" or mode != "run-make" for s, suite, mode, _ in identities)):
            raise ValueError("normal target starts and retained case streams differ or are empty")
        source_root = Path(source_root).resolve()
        # Resolve the sanctioned build -> build.noindex layout while keeping
        # foreign, chained and arbitrary build roots outside this source claim.
        build_root = source_root / "build"
        if build_root.is_symlink():
            physical = source_root / "build.noindex"
            if (physical.is_symlink() or not physical.is_dir()
                    or build_root.resolve(strict=True) != physical):
                raise ValueError("normal build alias is not the sanctioned checkout layout")
            build_root = physical
        observed = set()
        if sum(path.stat().st_size for path in files) > 64 * 1024 * 1024:
            raise ValueError("normal case population exceeds bounded carrier")
        for path in files:
            rows = [json.loads(line, object_pairs_hook=unique) for line in path.read_text().splitlines()]
            if len(rows) < 3 or any(not isinstance(row, dict) or row.get("schema") != "trust.compiletest.case-events/v1" for row in rows):
                raise ValueError("missing/unknown normal case event schema")
            header = rows[0]
            argv = header.get("argv")
            if header.get("type") != "invocation" or not isinstance(argv, list) or not all(isinstance(arg, str) for arg in argv):
                raise ValueError("missing actual normal compiletest invocation")
            def argument(flag):
                if argv.count(flag) != 1:
                    raise ValueError(f"missing/duplicate normal invocation {flag}")
                return argv[argv.index(flag) + 1]
            target = argument("--target")
            identity = (stage, argument("--suite"), argument("--mode"), target)
            if (identity not in identities or identity in observed
                    or argument("--stage-id") != f"stage{stage}-{target}"
                    or argument("--host") != host
                    or Path(argument("--src-root")).resolve() != source_root):
                raise ValueError("normal invocation has wrong source/stage/host/target identity")
            # Bind checkout ownership without guessing the bootstrap's tool
            # layout. In particular support may live in bootstrap-seed-tools,
            # not the historical stage1-tools-bin location.
            for flag in ("--rustc-path", "--compile-lib-path", "--run-lib-path",
                         "--run-make-support-rlib", "--run-make-support-rmeta"):
                value = Path(argument(flag))
                if not value.is_absolute() or not value.resolve().is_relative_to(build_root):
                    raise ValueError(f"normal invocation {flag} belongs to another checkout/layout")
            observed.add(identity)
            first, last = rows[1], rows[-1]
            if (first.get("type") != "suite" or first.get("event") != "started"
                    or type(first.get("selected_count")) is not int or type(first.get("test_count")) is not int
                    or first.get("selected_count") != len(expected) or first.get("test_count") != len(expected)):
                raise ValueError("normal selected case count differs from caller population")
            begun, terminal = set(), set()
            for row in rows[2:-1]:
                name = row.get("name")
                if row.get("type") != "test" or name not in expected:
                    raise ValueError("unexpected normal case")
                if row.get("event") == "started" and name not in begun and name not in terminal:
                    begun.add(name)
                elif row.get("event") == "ok" and name in begun and name not in terminal:
                    terminal.add(name)
                else:
                    raise ValueError("missing/duplicate/ignored/failed normal case terminal")
            if begun != expected or terminal != expected:
                raise ValueError("not every expected normal recipe executed successfully")
            required = {"type": "suite", "event": "ok", "selected_count": len(expected),
                        "executed_count": len(expected), "terminal_count": len(expected),
                        "passed": len(expected), "failed": 0, "ignored": 0,
                        "protocol_valid": True, "protocol_error": None}
            if any(type(last.get(key)) is not type(value) or last.get(key) != value for key, value in required.items()):
                raise ValueError("normal terminal counts/protocol contradict actual case population")
        if observed != identities:
            raise ValueError("normal target identity population is incomplete")
        return 0, f"every expected normal recipe passed in {len(files)} actual target stream(s)"
    except (OSError, ValueError, KeyError, IndexError, TypeError, RuntimeError) as error:
        return 2, f"normal recipe population NOT JUDGED: {error}"
