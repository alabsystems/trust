//! Exact dependency trust-base accounting from Targo's authenticated Unit graph.
//!
//! Cargo.lock is a resolution cache, not an execution inventory: it contains
//! inactive optionals, loses Unit mode/target distinctions, and a package name
//! cannot distinguish versions or sources. Targo therefore declares every
//! active resolved Unit before compilation. This module turns only the exact
//! excluded partition into dependency assumptions, while retaining the
//! verifier's explicit core/alloc/std trust boundary.

use trust_proof_cert::AssumptionSet;

#[cfg(test)]
use crate::pipeline::transport::CargoTargetIdentity;
use crate::pipeline::transport::{
    CargoProofInventory, TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION,
    TARGO_TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED, TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST,
    TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY, TARGO_TRUST_EXCLUSION_DOCUMENTATION,
    TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST,
};

#[derive(Debug, Clone)]
struct ExactTcbRow {
    level: String,
    subject: String,
    reason: String,
    tag: &'static str,
}

fn one_line(detail: &str) -> String {
    detail.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// One dependency-TCB scope: an authenticated closed-set exclusion reason, the
/// graph roles under which the ledger records that exclusion as an explicit
/// trust assumption, the tag the report carries, what the proof is then
/// conditional on (or leaves out), and whether the whole-crate verification
/// gate admits the Unit.
#[derive(Debug)]
struct DepTcbScope {
    tag: &'static str,
    exclusion_reason: &'static str,
    graph_roles: &'static [&'static str],
    /// The exclusion is a recorded assumption only when the run did not ask
    /// to verify dependencies (`include_dependencies` false). Under
    /// include-dependencies a Unit carrying this reason contradicts the policy
    /// and stays unresolved.
    only_when_dependencies_excluded: bool,
    whole_crate_gate_admits: bool,
    detail: &'static str,
}

/// Every scope `resolved_exclusion_scope` can resolve an exclusion to, stated
/// once: the classification is a lookup in this slice, so it can return no
/// tag that is not written here, and the whole-crate gate reads its admission
/// from the same entry. `docs/TCB.md` ("Dependency-TCB scopes") has one row
/// per entry; `crates/trust-integration-tests/tests/tcb_document_exhaustiveness.rs`
/// parses this slice and fails when a row is missing or disagrees with it.
///
/// The whole-crate gate is DELIBERATELY NARROWER than "resolves to any entry":
/// it admits only the classes that are unambiguously NOT the crate's own
/// verifiable compiler output — a dependency library the explicit dependency
/// policy kept outside the proof frontier (the crate's own code is verified
/// and merely calls into it), a build-script execution (a Cargo control job
/// outside the compiler proof channel), and (D2d) a doctest Unit whose
/// authenticated census found zero doctests. Deferred doctests that do (or may)
/// hold a doctest, documentation, and `--compile-time-deps` filtering (which can
/// drop a PRIMARY crate unit) keep the gate fail-closed, even though the ledger
/// still records each as a `Conditional` assumption.
const DEP_TCB_SCOPES: &[DepTcbScope] = &[
    DepTcbScope {
        tag: "dependency-scope",
        exclusion_reason: TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY,
        graph_roles: &["dependency"],
        only_when_dependencies_excluded: true,
        whole_crate_gate_admits: true,
        detail: "active compiler-capable Cargo unit was excluded by the explicit dependency policy; proof is conditional on this exact unit's correctness",
    },
    DepTcbScope {
        tag: "build-execution-scope",
        exclusion_reason: TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION,
        graph_roles: &["control"],
        only_when_dependencies_excluded: false,
        whole_crate_gate_admits: true,
        detail: "active build-script execution is a Cargo control job outside the compiler proof channel; proof is conditional on this exact execution unit's correctness",
    },
    DepTcbScope {
        tag: "deferred-doctest-scope",
        exclusion_reason: TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST,
        graph_roles: &["primary", "dependency"],
        only_when_dependencies_excluded: false,
        whole_crate_gate_admits: false,
        detail: "active doctest execution is deferred outside the compiler job-queue proof channel; proof does not cover this exact doctest unit",
    },
    // Trust (D2d, 2026-09-28): the same Cargo doctest Unit after Targo's
    // authenticated census counted ZERO doctests in it. `targo trust test`
    // executes no doctests (phase B selects `--tests`), and this Unit holds
    // none to defer, so the frontier matches what phase B executes. The row
    // stays disclosed; it is conditional on the census, not on any code.
    DepTcbScope {
        tag: "empty-doctest-scope",
        exclusion_reason: TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST,
        graph_roles: &["primary", "dependency"],
        only_when_dependencies_excluded: false,
        whole_crate_gate_admits: true,
        detail: "active doctest unit contains zero doctests per Targo's authenticated trustdoc census; there is no doctest to execute or defer, conditional on that census",
    },
    DepTcbScope {
        tag: "documentation-scope",
        exclusion_reason: TARGO_TRUST_EXCLUSION_DOCUMENTATION,
        graph_roles: &["primary", "dependency"],
        only_when_dependencies_excluded: false,
        whole_crate_gate_admits: false,
        detail: "active rustdoc generation lacks the authenticated per-Unit proof protocol; proof does not cover this exact documentation unit",
    },
    DepTcbScope {
        tag: "compile-time-deps-scope",
        exclusion_reason: TARGO_TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED,
        graph_roles: &["primary", "test-execution", "dependency"],
        only_when_dependencies_excluded: false,
        whole_crate_gate_admits: false,
        detail: "active Cargo Unit was filtered from the executable job graph by --compile-time-deps; proof does not cover this exact filtered unit",
    },
];

/// The tag of every ledger row whose exclusion resolves to no
/// `DEP_TCB_SCOPES` entry, or whose inventory is incomplete. Never admitted.
const UNRESOLVED_SCOPE_TAG: &str = "dependency-scope-unresolved";

/// The tag of the foundational sysroot rows (`core`, `alloc`, `std`, and
/// libtest for a test-harness unit): the dependency-policy entry's own tag,
/// read from the slice so the two can never be spelled apart.
fn foundational_scope_tag() -> &'static str {
    DEP_TCB_SCOPES
        .iter()
        .find(|scope| scope.exclusion_reason == TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY)
        .expect("DEP_TCB_SCOPES has a dependency-policy entry")
        .tag
}

/// Pure, single-source-of-truth classification of an active Cargo exclusion
/// into a resolved dependency-TCB trust scope: a lookup in `DEP_TCB_SCOPES`.
///
/// Returns the entry for every `(reason, graph_role, include_dependencies)`
/// combination that the dependency-TCB ledger admits as an explicit, recorded
/// trust assumption. Returns `None` for any unsupported or policy-inconsistent
/// combination — those are recorded by the ledger as `UNRESOLVED_SCOPE_TAG`,
/// and the whole-crate verification gate treats them as genuinely unresolved
/// (fail-closed).
///
/// Both the ledger renderer (`exact_tcb_rows`) and the verification gate
/// (`report_unit_is_dep_tcb_admitted`) route through this one function so they
/// can never disagree about which exclusions are admitted assumptions.
fn resolved_exclusion_scope(
    exclusion_reason: &str,
    graph_role: &str,
    include_dependencies: bool,
) -> Option<&'static DepTcbScope> {
    DEP_TCB_SCOPES.iter().find(|scope| {
        scope.exclusion_reason == exclusion_reason
            && scope.graph_roles.contains(&graph_role)
            && !(scope.only_when_dependencies_excluded && include_dependencies)
    })
}

/// Whether an excluded active Cargo Unit from the report inventory is admitted
/// as a dependency-TCB trust assumption for the purpose of the whole-crate
/// verification gate: its exclusion resolves to a `DEP_TCB_SCOPES` entry whose
/// `whole_crate_gate_admits` is set (the slice says which classes, and why the
/// set is narrower than the ledger's). Any unresolved or policy-inconsistent
/// exclusion keeps the gate fail-closed.
///
/// An admitted Unit here always emits its matching `Conditional` row from
/// `exact_tcb_rows` (both route through `resolved_exclusion_scope`), so passing
/// the gate for it claims trusted-assumed, never proved; the assumption is
/// present in the report ledger the user sees.
pub(crate) fn report_unit_is_dep_tcb_admitted(
    include_dependencies: bool,
    unit: &trust_types::CargoProofUnitReport,
) -> bool {
    let Some(reason) = unit.exclusion_reason.as_deref() else {
        return false;
    };
    resolved_exclusion_scope(reason, unit.graph_role.as_str(), include_dependencies)
        .is_some_and(|scope| scope.whole_crate_gate_admits)
}

fn exact_tcb_rows(inventory: Option<&CargoProofInventory>) -> Vec<ExactTcbRow> {
    let mut rows = AssumptionSet::from_scoped_out_deps(None, std::iter::empty::<&str>())
        .trust_levels
        .into_iter()
        .map(|assumption| ExactTcbRow {
            level: assumption.level.label().to_string(),
            subject: assumption.path,
            reason: assumption.reason,
            tag: foundational_scope_tag(),
        })
        .collect::<Vec<_>>();

    let Some(inventory) = inventory else {
        rows.push(ExactTcbRow {
            level: "Conditional".to_string(),
            subject: "<unresolved active Cargo unit inventory>".to_string(),
            reason: "authenticated Targo proof inventory was absent; proof is conditional on every unenumerated active dependency unit"
                .to_string(),
            tag: UNRESOLVED_SCOPE_TAG,
        });
        rows.sort_by(|left, right| left.subject.cmp(&right.subject));
        return rows;
    };

    // Trust (CB4): a proof unit compiled as a libtest harness (`test`,
    // `check-test`) links the sysroot `test` crate, and the compiler EXCLUDES the
    // code rustc synthesizes around each `#[test]` (the runner closure and the
    // harness `main`) from the proof inventory. Test EXECUTION is therefore
    // conditional on libtest exactly as every proof is conditional on std: list
    // it beside core/alloc/std, and only when such a unit is in the frontier.
    if inventory.proof_targets.iter().any(|target| {
        trust_types::exclusion::test_harness_exclusion_admits_unit_mode(&target.proof_unit_mode)
    }) {
        rows.push(ExactTcbRow {
            level: "Conditional".to_string(),
            subject: "test".to_string(),
            reason: "the sysroot libtest crate `test` runs every test of a --test proof unit; the \
                     harness code rustc synthesizes around each #[test]/#[bench] (runner closure, \
                     harness main) is excluded from the proof inventory \
                     (excluded:test-harness-synthesized), so test execution is conditional on \
                     libtest; each user test function is still verified as its own body"
                .to_string(),
            tag: foundational_scope_tag(),
        });
    }

    for target in &inventory.excluded_targets {
        let Some(exclusion_reason) = inventory.excluded_reasons.get(target) else {
            rows.push(ExactTcbRow {
                level: "Conditional".to_string(),
                subject: target.report_label(),
                reason: "active Cargo unit was excluded without an authenticated closed-set reason; proof scope is unresolved"
                    .to_string(),
                tag: UNRESOLVED_SCOPE_TAG,
            });
            continue;
        };
        let Some(graph_role) = inventory.excluded_graph_roles.get(target) else {
            rows.push(ExactTcbRow {
                level: "Conditional".to_string(),
                subject: target.report_label(),
                reason: "active Cargo unit was excluded without its authenticated graph role; proof scope is unresolved"
                    .to_string(),
                tag: UNRESOLVED_SCOPE_TAG,
            });
            continue;
        };
        let (tag, reason) = match resolved_exclusion_scope(
            exclusion_reason.as_str(),
            graph_role.as_str(),
            inventory.include_dependencies,
        ) {
            Some(scope) => (scope.tag, scope.detail.to_string()),
            None => (
                UNRESOLVED_SCOPE_TAG,
                format!(
                    "active Cargo unit carried an unsupported or policy-inconsistent exclusion reason {exclusion_reason:?}; proof scope is unresolved"
                ),
            ),
        };
        rows.push(ExactTcbRow {
            level: "Conditional".to_string(),
            subject: format!("{};graph_role={graph_role:?}", target.report_label()),
            reason: format!(
                "graph_role={graph_role:?}; exclusion_reason={exclusion_reason:?}; {reason}"
            ),
            tag,
        });
    }
    for (target, reason) in &inventory.excluded_reasons {
        if !inventory.excluded_targets.contains(target) {
            rows.push(ExactTcbRow {
                level: "Conditional".to_string(),
                subject: target.report_label(),
                reason: format!(
                    "an exclusion reason {reason:?} named a Unit absent from the excluded partition; proof scope is unresolved"
                ),
                tag: UNRESOLVED_SCOPE_TAG,
            });
        }
    }
    for (target, graph_role) in &inventory.excluded_graph_roles {
        if !inventory.excluded_targets.contains(target) {
            rows.push(ExactTcbRow {
                level: "Conditional".to_string(),
                subject: target.report_label(),
                reason: format!(
                    "a graph role {graph_role:?} named a Unit absent from the excluded partition; proof scope is unresolved"
                ),
                tag: UNRESOLVED_SCOPE_TAG,
            });
        }
    }
    rows.sort_by(|left, right| left.subject.cmp(&right.subject));
    rows
}

/// Human-readable dependency-TCB ledger derived from the same exact inventory
/// used by the machine-readable report.
pub(crate) fn dep_tcb_ledger_lines(inventory: Option<&CargoProofInventory>) -> Vec<String> {
    exact_tcb_rows(inventory)
        .into_iter()
        .map(|row| format!("{:<12} {}  ({})", row.level, row.subject, one_line(&row.reason)))
        .collect()
}

/// Machine-readable crate-scope assumptions for exactly the active Units that
/// Targo declared outside the proof frontier, plus core/alloc/std.
pub(crate) fn dep_tcb_assumption_entries(
    inventory: Option<&CargoProofInventory>,
) -> Vec<trust_types::AssumptionEntry> {
    exact_tcb_rows(inventory)
        .into_iter()
        .map(|row| trust_types::AssumptionEntry {
            scope: "crate".to_string(),
            subject: row.subject,
            tag: row.tag.to_string(),
            detail: format!("{}: {}", row.level, one_line(&row.reason)),
            location: None,
            source: "dep-tcb-cargo-unit-inventory".to_string(),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;

    fn target(index: u64, package_id: &str, package_name: &str) -> CargoTargetIdentity {
        CargoTargetIdentity {
            package_id: package_id.to_string(),
            package_name: package_name.to_string(),
            target_name: package_name.to_string(),
            target_kinds: vec!["lib".to_string()],
            compile_target: "x86_64-unknown-linux-gnu".to_string(),
            compile_mode: "build".to_string(),
            compile_kind: "target".to_string(),
            unit_identity_sha256: "c".repeat(64),
            compile_target_spec_sha256: None,
            proof_unit_index: index,
            proof_unit_mode: "build".to_string(),
            proof_unit_role: "excluded".to_string(),
            semantics_sha256: "a".repeat(64),
        }
    }

    fn inventory(excluded: impl IntoIterator<Item = CargoTargetIdentity>) -> CargoProofInventory {
        let excluded_targets = excluded.into_iter().collect::<BTreeSet<_>>();
        CargoProofInventory {
            include_dependencies: false,
            proof_targets: BTreeSet::new(),
            excluded_reasons: excluded_targets
                .iter()
                .cloned()
                .map(|target| (target, TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY.to_string()))
                .collect(),
            excluded_graph_roles: excluded_targets
                .iter()
                .cloned()
                .map(|target| (target, "dependency".to_string()))
                .collect(),
            excluded_targets,
            unit_semantics: BTreeMap::new(),
        }
    }

    #[test]
    fn missing_inventory_is_explicit_and_std_is_never_silent() {
        let entries = dep_tcb_assumption_entries(None);
        assert!(entries.iter().any(|entry| entry.subject == "core"));
        assert!(entries.iter().any(|entry| entry.subject == "std"));
        assert!(entries.iter().any(|entry| entry.tag == "dependency-scope-unresolved"));
    }

    #[test]
    fn exact_active_exclusions_replace_lockfile_name_guessing() {
        let inventory =
            inventory([target(1, "registry+https://example.invalid/index#serde@1.0.0", "serde")]);
        let entries = dep_tcb_assumption_entries(Some(&inventory));
        let serde = entries
            .iter()
            .find(|entry| entry.subject.contains("serde@1.0.0"))
            .expect("active excluded dependency is reported by exact package ID");
        assert!(serde.subject.contains("proof_unit_index=1"), "{serde:?}");
        assert!(serde.detail.contains(TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY));
        assert!(!entries.iter().any(|entry| entry.tag == "dependency-scope-unresolved"));
        assert!(!entries.iter().any(|entry| entry.subject.contains("inactive")));
    }

    /// Trust (CB4): libtest joins the foundational trust base exactly when a
    /// libtest-harness unit (`test`, `check-test`) is in the proof frontier.
    #[test]
    fn libtest_is_conditional_trust_base_only_for_test_harness_units() {
        let libtest = |entries: &[trust_types::AssumptionEntry]| {
            entries.iter().find(|entry| entry.subject == "test").cloned()
        };
        assert!(libtest(&dep_tcb_assumption_entries(None)).is_none());
        for (mode, expected) in
            [("test", true), ("check-test", true), ("build", false), ("check", false)]
        {
            let mut unit = target(0, "path+file:///w/fixture#0.1.0", "fixture");
            unit.compile_mode = mode.to_string();
            unit.proof_unit_mode = mode.to_string();
            unit.proof_unit_role = "primary".to_string();
            let mut inventory = inventory(std::iter::empty::<CargoTargetIdentity>());
            inventory.proof_targets.insert(unit);
            let entries = dep_tcb_assumption_entries(Some(&inventory));
            let row = libtest(&entries);
            assert_eq!(row.is_some(), expected, "{mode}: {entries:?}");
            if let Some(row) = row {
                assert!(row.detail.starts_with("Conditional: "), "{row:?}");
                assert!(row.detail.contains("excluded:test-harness-synthesized"), "{row:?}");
            }
            // std stays whatever the mode.
            assert!(entries.iter().any(|entry| entry.subject == "std"), "{mode}");
        }
    }

    #[test]
    fn verified_dependencies_disappear_while_std_remains() {
        let inventory = CargoProofInventory {
            include_dependencies: true,
            proof_targets: [target(
                0,
                "registry+https://example.invalid/index#verified@2.0.0",
                "verified",
            )]
            .into_iter()
            .map(|mut target| {
                target.proof_unit_role = "dependency".to_string();
                target
            })
            .collect(),
            excluded_targets: BTreeSet::new(),
            excluded_reasons: BTreeMap::new(),
            excluded_graph_roles: BTreeMap::new(),
            unit_semantics: BTreeMap::new(),
        };
        let entries = dep_tcb_assumption_entries(Some(&inventory));
        assert!(!entries.iter().any(|entry| entry.subject.contains("verified@2.0.0")));
        assert!(entries.iter().any(|entry| entry.subject == "core"));
        assert!(entries.iter().any(|entry| entry.subject == "std"));
    }

    #[test]
    fn same_name_multi_version_packages_remain_distinct() {
        let inventory = inventory([
            target(0, "registry+https://example.invalid/index#same@1.0.0", "same"),
            target(1, "registry+https://example.invalid/index#same@2.0.0", "same"),
        ]);
        let entries = dep_tcb_assumption_entries(Some(&inventory));
        assert_eq!(entries.iter().filter(|entry| entry.subject.contains("#same@")).count(), 2);
    }

    #[test]
    fn exact_cargo_unit_named_std_is_not_suppressed_by_curated_sysroot_row() {
        let inventory =
            inventory([target(0, "registry+https://example.invalid/index#std@99.0.0", "std")]);
        let entries = dep_tcb_assumption_entries(Some(&inventory));
        assert!(entries.iter().any(|entry| entry.subject == "std"));
        assert!(
            entries.iter().any(|entry| entry.subject.contains("#std@99.0.0")),
            "a package-name alias cannot impersonate the curated sysroot assumption: {entries:?}"
        );
    }

    /// `DEP_TCB_SCOPES` replaced a `match` on 2026-10-01. Every cell of the
    /// classification is pinned here as that match stated it (the closure
    /// below is its text, arm for arm), so the slice is the same rule; each
    /// tag and each exclusion reason is declared once, so the lookup's order
    /// cannot decide a row; and every declared scope is reachable.
    #[test]
    fn dep_tcb_scope_slice_is_the_classification_cell_by_cell() {
        let tags = DEP_TCB_SCOPES.iter().map(|scope| scope.tag).collect::<BTreeSet<_>>();
        let reasons =
            DEP_TCB_SCOPES.iter().map(|scope| scope.exclusion_reason).collect::<BTreeSet<_>>();
        assert_eq!(tags.len(), DEP_TCB_SCOPES.len(), "a tag is declared twice");
        assert_eq!(reasons.len(), DEP_TCB_SCOPES.len(), "an exclusion reason is declared twice");
        assert!(!tags.contains(UNRESOLVED_SCOPE_TAG), "the unresolved tag is never a scope");

        let pre_slice_match = |reason: &str, role: &str, include_dependencies: bool| match reason {
            TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY
                if !include_dependencies && role == "dependency" =>
            {
                Some(("dependency-scope", true))
            }
            TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION if role == "control" => {
                Some(("build-execution-scope", true))
            }
            TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST if matches!(role, "primary" | "dependency") => {
                Some(("deferred-doctest-scope", false))
            }
            TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST if matches!(role, "primary" | "dependency") => {
                Some(("empty-doctest-scope", true))
            }
            TARGO_TRUST_EXCLUSION_DOCUMENTATION if matches!(role, "primary" | "dependency") => {
                Some(("documentation-scope", false))
            }
            TARGO_TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED
                if matches!(role, "primary" | "test-execution" | "dependency") =>
            {
                Some(("compile-time-deps-scope", false))
            }
            _ => None,
        };
        let mut reached = BTreeSet::new();
        for reason in [
            TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY,
            TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION,
            TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST,
            TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST,
            TARGO_TRUST_EXCLUSION_DOCUMENTATION,
            TARGO_TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED,
            crate::pipeline::transport::TARGO_TRUST_EXCLUSION_BUILD_SUPPORT_ONLY,
            crate::pipeline::transport::TARGO_TRUST_EXCLUSION_AUDITED_TRUST_SPEC,
            "unknown-exclusion-reason",
        ] {
            for role in ["primary", "dependency", "test-execution", "control", "unknown-role"] {
                for include_dependencies in [false, true] {
                    let got = resolved_exclusion_scope(reason, role, include_dependencies)
                        .map(|scope| (scope.tag, scope.whole_crate_gate_admits));
                    assert_eq!(
                        got,
                        pre_slice_match(reason, role, include_dependencies),
                        "reason={reason:?} role={role:?} include_dependencies={include_dependencies}"
                    );
                    reached.extend(got.map(|(tag, _)| tag));
                }
            }
        }
        assert_eq!(reached, tags, "every declared scope must be reachable");
        assert_eq!(foundational_scope_tag(), "dependency-scope");
    }

    #[test]
    fn execution_exclusions_retain_distinct_reasons_and_tags() {
        let mut build_script =
            target(0, "path+file:///workspace#build-helper@0.1.0", "build-helper");
        build_script.target_name = "build-script-build".to_string();
        build_script.target_kinds = vec!["custom-build".to_string()];
        build_script.proof_unit_mode = "run-custom-build".to_string();
        let mut doctest = target(1, "path+file:///workspace#docs@0.1.0", "docs");
        doctest.proof_unit_mode = "doctest".to_string();
        let excluded_targets = [build_script.clone(), doctest.clone()].into_iter().collect();
        let inventory = CargoProofInventory {
            include_dependencies: true,
            proof_targets: BTreeSet::new(),
            excluded_targets,
            excluded_reasons: BTreeMap::from([
                (build_script.clone(), TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION.to_string()),
                (doctest.clone(), TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST.to_string()),
            ]),
            excluded_graph_roles: BTreeMap::from([
                (build_script, "control".to_string()),
                (doctest, "primary".to_string()),
            ]),
            unit_semantics: BTreeMap::new(),
        };
        let entries = dep_tcb_assumption_entries(Some(&inventory));
        assert!(entries.iter().any(|entry| {
            entry.tag == "build-execution-scope"
                && entry.detail.contains(TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION)
        }));
        assert!(entries.iter().any(|entry| {
            entry.tag == "deferred-doctest-scope"
                && entry.detail.contains(TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST)
        }));
        assert!(!entries.iter().any(|entry| entry.tag == "dependency-scope-unresolved"));
    }

    fn doctest_unit_report(reason: &str, graph_role: &str) -> trust_types::CargoProofUnitReport {
        trust_types::CargoProofUnitReport {
            package_id: "path+file:///workspace#docs@0.1.0".to_string(),
            package_name: "docs".to_string(),
            target_name: "docs".to_string(),
            target_kinds: vec!["lib".to_string()],
            compile_target: "x86_64-unknown-linux-gnu".to_string(),
            compile_target_spec_sha256: None,
            proof_unit_index: 1,
            proof_unit_mode: "doctest".to_string(),
            proof_unit_role: "excluded".to_string(),
            graph_role: graph_role.to_string(),
            exclusion_reason: Some(reason.to_string()),
            semantics_sha256: None,
            semantics: None,
        }
    }

    /// D2d (2026-09-28): the proof frontier of `targo trust test` must match
    /// what phase B executes. A doctest Unit whose authenticated census found
    /// ZERO doctests executes nothing and defers nothing, so it is admitted
    /// (and still disclosed as a conditional row); a doctest Unit that holds —
    /// or may hold — a doctest stays `deferred-doctest-execution`, disclosed
    /// and gate-failing, so a real doctest never silently leaves the frontier.
    #[test]
    fn empty_doctest_unit_is_admitted_while_a_deferred_one_still_fails_the_gate() {
        for include_dependencies in [false, true] {
            assert!(report_unit_is_dep_tcb_admitted(
                include_dependencies,
                &doctest_unit_report(TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST, "primary"),
            ));
            assert!(report_unit_is_dep_tcb_admitted(
                include_dependencies,
                &doctest_unit_report(TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST, "dependency"),
            ));
            assert!(
                !report_unit_is_dep_tcb_admitted(
                    include_dependencies,
                    &doctest_unit_report(TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST, "primary"),
                ),
                "a doctest Unit with real (or uncounted) doctests must keep the gate fail-closed"
            );
            assert!(
                !report_unit_is_dep_tcb_admitted(
                    include_dependencies,
                    &doctest_unit_report(TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST, "control"),
                ),
                "the census-only reason is bound to the doctest graph roles"
            );
        }

        let mut empty = target(1, "path+file:///workspace#docs@0.1.0", "docs");
        empty.proof_unit_mode = "doctest".to_string();
        let mut deferred = target(2, "path+file:///workspace#more-docs@0.1.0", "more-docs");
        deferred.proof_unit_mode = "doctest".to_string();
        let inventory = CargoProofInventory {
            include_dependencies: false,
            proof_targets: BTreeSet::new(),
            excluded_targets: [empty.clone(), deferred.clone()].into_iter().collect(),
            excluded_reasons: BTreeMap::from([
                (empty.clone(), TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST.to_string()),
                (deferred.clone(), TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST.to_string()),
            ]),
            excluded_graph_roles: BTreeMap::from([
                (empty, "primary".to_string()),
                (deferred, "primary".to_string()),
            ]),
            unit_semantics: BTreeMap::new(),
        };
        let entries = dep_tcb_assumption_entries(Some(&inventory));
        assert!(
            entries.iter().any(|entry| entry.tag == "empty-doctest-scope"
                && entry.detail.contains(TARGO_TRUST_EXCLUSION_EMPTY_DOCTEST)
                && entry.subject.contains("#docs@0.1.0")),
            "the empty doctest Unit stays disclosed: {entries:?}"
        );
        assert!(
            entries.iter().any(|entry| entry.tag == "deferred-doctest-scope"
                && entry.subject.contains("#more-docs@0.1.0")),
            "the deferred doctest Unit stays disclosed: {entries:?}"
        );
        assert!(!entries.iter().any(|entry| entry.tag == "dependency-scope-unresolved"));
    }
}
