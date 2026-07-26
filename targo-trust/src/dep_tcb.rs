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

/// Pure, single-source-of-truth classification of an active Cargo exclusion
/// into a resolved dependency-TCB trust scope.
///
/// Returns `Some((tag, detail))` for every `(reason, graph_role,
/// include_dependencies)` combination that the dependency-TCB ledger admits as
/// an explicit, recorded trust assumption. Returns `None` for any unsupported
/// or policy-inconsistent combination — those are recorded by the ledger as
/// `dependency-scope-unresolved`, and the whole-crate verification gate treats
/// them as genuinely unresolved (fail-closed).
///
/// Both the ledger renderer (`exact_tcb_rows`) and the verification gate
/// (`report_unit_is_dep_tcb_admitted`) route through this one function so they
/// can never disagree about which exclusions are admitted assumptions.
fn resolved_exclusion_scope(
    exclusion_reason: &str,
    graph_role: &str,
    include_dependencies: bool,
) -> Option<(&'static str, &'static str)> {
    match exclusion_reason {
        TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY
            if !include_dependencies && graph_role == "dependency" =>
        {
            Some((
                "dependency-scope",
                "active compiler-capable Cargo unit was excluded by the explicit dependency policy; proof is conditional on this exact unit's correctness",
            ))
        }
        TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION if graph_role == "control" => Some((
            "build-execution-scope",
            "active build-script execution is a Cargo control job outside the compiler proof channel; proof is conditional on this exact execution unit's correctness",
        )),
        TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST
            if matches!(graph_role, "primary" | "dependency") =>
        {
            Some((
                "deferred-doctest-scope",
                "active doctest execution is deferred outside the compiler job-queue proof channel; proof does not cover this exact doctest unit",
            ))
        }
        TARGO_TRUST_EXCLUSION_DOCUMENTATION if matches!(graph_role, "primary" | "dependency") => {
            Some((
                "documentation-scope",
                "active rustdoc generation lacks the authenticated per-Unit proof protocol; proof does not cover this exact documentation unit",
            ))
        }
        TARGO_TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED
            if matches!(graph_role, "primary" | "test-execution" | "dependency") =>
        {
            Some((
                "compile-time-deps-scope",
                "active Cargo Unit was filtered from the executable job graph by --compile-time-deps; proof does not cover this exact filtered unit",
            ))
        }
        _ => None,
    }
}

/// Whether an excluded active Cargo Unit from the report inventory is admitted
/// as a dependency-TCB trust assumption for the purpose of the whole-crate
/// verification gate.
///
/// This is DELIBERATELY NARROWER than "resolves to any dep-TCB ledger scope":
/// only the two classes that are unambiguously NOT the crate's own verifiable
/// compiler output are blessed here —
///   * `dependency-scope` — a third-party dependency library the explicit
///     dependency policy kept outside the proof frontier; the crate's own code
///     is verified and merely calls into this trusted, un-verified dependency;
///   * `build-execution-scope` — a build-script execution, a Cargo *control*
///     job (`build.rs`) that runs outside the compiler proof channel.
///
/// Every other exclusion — deferred doctests, documentation, `--compile-time-deps`
/// filtering (which can drop a PRIMARY crate unit), and any unresolved or
/// policy-inconsistent exclusion — is NOT blessed and keeps the gate fail-closed,
/// even though the ledger still records each as a `Conditional` assumption.
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
    matches!(
        resolved_exclusion_scope(reason, unit.graph_role.as_str(), include_dependencies),
        Some(("dependency-scope" | "build-execution-scope", _))
    )
}

fn exact_tcb_rows(inventory: Option<&CargoProofInventory>) -> Vec<ExactTcbRow> {
    let mut rows = AssumptionSet::from_scoped_out_deps(None, std::iter::empty::<&str>())
        .trust_levels
        .into_iter()
        .map(|assumption| ExactTcbRow {
            level: assumption.level.label().to_string(),
            subject: assumption.path,
            reason: assumption.reason,
            tag: "dependency-scope",
        })
        .collect::<Vec<_>>();

    let Some(inventory) = inventory else {
        rows.push(ExactTcbRow {
            level: "Conditional".to_string(),
            subject: "<unresolved active Cargo unit inventory>".to_string(),
            reason: "authenticated Targo proof inventory was absent; proof is conditional on every unenumerated active dependency unit"
                .to_string(),
            tag: "dependency-scope-unresolved",
        });
        rows.sort_by(|left, right| left.subject.cmp(&right.subject));
        return rows;
    };

    for target in &inventory.excluded_targets {
        let Some(exclusion_reason) = inventory.excluded_reasons.get(target) else {
            rows.push(ExactTcbRow {
                level: "Conditional".to_string(),
                subject: target.report_label(),
                reason: "active Cargo unit was excluded without an authenticated closed-set reason; proof scope is unresolved"
                    .to_string(),
                tag: "dependency-scope-unresolved",
            });
            continue;
        };
        let Some(graph_role) = inventory.excluded_graph_roles.get(target) else {
            rows.push(ExactTcbRow {
                level: "Conditional".to_string(),
                subject: target.report_label(),
                reason: "active Cargo unit was excluded without its authenticated graph role; proof scope is unresolved"
                    .to_string(),
                tag: "dependency-scope-unresolved",
            });
            continue;
        };
        let (tag, reason) = match resolved_exclusion_scope(
            exclusion_reason.as_str(),
            graph_role.as_str(),
            inventory.include_dependencies,
        ) {
            Some((tag, detail)) => (tag, detail.to_string()),
            None => (
                "dependency-scope-unresolved",
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
                tag: "dependency-scope-unresolved",
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
                tag: "dependency-scope-unresolved",
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
}
