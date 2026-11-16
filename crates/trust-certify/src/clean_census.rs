//! Independent, diagnostic Lean kernel roster. This is deliberately NOT a
//! producer coverage denominator: kernel constants are not the executable body
//! universe after erasure, specialization, closure conversion and ABI lowering.
//!
//! The owned environment is enumerated before and after elaboration, without
//! consulting producer admission. In particular, generated helpers omitted by
//! the elaborator's `introduces` list still appear, with unknown ownership when
//! the public kernel metadata cannot establish it. Lazy/import enumeration is
//! explicitly unverified: `ConstantSource::names` may legally return no names.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use clean_elab::module_batch::{DeclStatus, ModuleOutcome};
use clean_kernel::{Environment, Expr, ExprKind, Name, TypeChecker};
use serde_json::{Value, json};
use trust_types::digest::{canonical_json_sha256, stable_sha256_hex};

use crate::clean_island::CleanIslandOutcome;

/// Versioned measurement only; never citation, producer or product authority.
#[derive(Debug, Clone)]
pub struct LeanKernelRoster {
    /// Canonical-name identities, input hashes, provenance and limitations.
    pub report: Value,
}

/// A type-based diagnostic, not a producer admission or a runtime/erasure
/// decision. In particular, returning a proposition is different from proving
/// one, and a primitive may compute without `ConstantInfo::value`.
#[derive(Debug, Clone, PartialEq, Eq)]
enum KernelClassification {
    ProofOnly,
    TypeFamily,
    ComputationalCandidate,
    PrimitiveCandidate,
    Unknown { reason: String },
}

impl KernelClassification {
    fn diagnostic_json(&self) -> Value {
        match self {
            Self::ProofOnly => json!({ "kind": "proof-only" }),
            Self::TypeFamily => json!({ "kind": "type-family" }),
            Self::ComputationalCandidate => json!({ "kind": "computational-candidate" }),
            Self::PrimitiveCandidate => json!({ "kind": "primitive-candidate" }),
            Self::Unknown { reason } => json!({ "kind": "unknown", "reason": reason }),
        }
    }
}

#[derive(Clone, Copy)]
struct ClassificationLimits {
    type_nodes: usize,
    type_depth: usize,
    telescope_binders: usize,
    kernel_heartbeats: u32,
}

const CLASSIFICATION_LIMITS: ClassificationLimits = ClassificationLimits {
    type_nodes: 16_384,
    type_depth: 128,
    telescope_binders: 128,
    kernel_heartbeats: 100_000,
};

fn bounded_type(expr: &Expr, limits: ClassificationLimits) -> Result<(), String> {
    let mut pending = vec![(expr, 0usize)];
    let mut nodes = 0usize;
    while let Some((expr, depth)) = pending.pop() {
        nodes += 1;
        if nodes > limits.type_nodes || depth > limits.type_depth {
            return Err("kernel classification type-size/depth bound exceeded".into());
        }
        let child_depth = depth + 1;
        match expr.kind() {
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Const(..)
            | ExprKind::Lit(_) => {}
            ExprKind::App(left, right)
            | ExprKind::Lam(_, left, right)
            | ExprKind::Pi(_, left, right) => {
                pending.push((left, child_depth));
                pending.push((right, child_depth));
            }
            ExprKind::Let(_, ty, value, body, _) => {
                pending.push((ty, child_depth));
                pending.push((value, child_depth));
                pending.push((body, child_depth));
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                pending.push((inner, child_depth));
            }
            // Alternative kernel modes need an explicit classification model;
            // never infer erasure from an unfamiliar syntax node.
            _ => return Err("kernel classification does not model this expression form".into()),
        }
    }
    Ok(())
}

fn classify_kernel_type(
    env: &Environment,
    name: &Name,
    limits: ClassificationLimits,
) -> KernelClassification {
    let classify = || -> Result<KernelClassification, String> {
        let info = env.get_const(name).ok_or("kernel classification constant is absent")?;
        bounded_type(&info.type_, limits)?;
        // Zero means UNLIMITED to the kernel, not no work. Never turn an
        // accidentally empty diagnostic budget into an unbounded query.
        if limits.kernel_heartbeats == 0 {
            return Err("kernel classification requires a nonzero heartbeat bound".into());
        }
        let mut checker = TypeChecker::new(env);
        checker.set_heartbeat_limit(limits.kernel_heartbeats);
        let sort = checker.infer_sort(&info.type_).map_err(|error| {
            if checker.heartbeat_spent() {
                format!("kernel classification heartbeat bound exceeded: {error:?}")
            } else {
                format!("kernel classification type check: {error:?}")
            }
        })?;
        if checker.heartbeat_spent() {
            return Err("kernel classification heartbeat bound exceeded".into());
        }
        if sort.is_zero() {
            return Ok(KernelClassification::ProofOnly);
        }

        // A definition `P : Prop` returns a proposition, not a proof. Likewise
        // `T : Type` and `F : Nat -> Type` return types. Open the actual typed
        // telescope rather than testing kind/name/body presence or stripping
        // binders without instantiating their dependent variables.
        let mut current = info.type_.clone();
        let mut pushed = 0usize;
        let result = (|| {
            loop {
                bounded_type(&current, limits)?;
                let reduced = checker.whnf(&current);
                if checker.heartbeat_spent() {
                    return Err("kernel classification heartbeat bound exceeded".into());
                }
                bounded_type(&reduced, limits)?;
                match reduced.kind() {
                    ExprKind::Pi(binder, domain, body) => {
                        if pushed >= limits.telescope_binders {
                            return Err("kernel classification telescope bound exceeded".into());
                        }
                        let id = checker.push_binder_local(
                            Name::anon(),
                            domain.as_ref().clone(),
                            *binder,
                        );
                        pushed += 1;
                        current = body.instantiate(&Expr::fvar(id));
                    }
                    ExprKind::Sort(_) => return Ok(KernelClassification::TypeFamily),
                    _ => {
                        return Ok(
                            if env.get_constructor(name).is_some()
                                || env.get_recursor(name).is_some()
                                || env.quotients().any(|val| &val.name == name)
                            {
                                KernelClassification::PrimitiveCandidate
                            } else {
                                KernelClassification::ComputationalCandidate
                            },
                        );
                    }
                }
            }
        })();
        for _ in 0..pushed {
            checker.pop_binder_local();
        }
        result
    };
    classify().unwrap_or_else(|reason| KernelClassification::Unknown { reason })
}

/// Snapshot of eager identities, taken before parsing or producer admission.
pub(crate) fn owned_names(env: &Environment) -> BTreeSet<Name> {
    env.constants().map(|info| info.name.clone()).collect()
}

/// The checker that actually ran. A sequential island has no module transaction
/// or complete source-declaration metadata; `module: None` alone cannot express
/// that distinction from a batch which failed before producing a module.
enum CheckExecution<'a> {
    HeaderFirst { module: Option<&'a ModuleOutcome>, rejected: bool },
    Sequential(&'a CleanIslandOutcome),
}

impl LeanKernelRoster {
    /// Account for earlier rejected checks in a stateful session as well.
    pub(crate) fn mark_session_tainted(&mut self, tainted: bool) {
        self.report["session_tainted"] = json!(tainted);
    }

    pub(crate) fn capture(
        before: &BTreeSet<Name>,
        env: &Environment,
        sources: &[&str],
        module: Option<&ModuleOutcome>,
        rejected: bool,
    ) -> Self {
        Self::capture_execution(
            before,
            env,
            sources,
            CheckExecution::HeaderFirst { module, rejected },
        )
    }

    pub(crate) fn capture_sequential(
        before: &BTreeSet<Name>,
        env: &Environment,
        source: &str,
        outcome: &CleanIslandOutcome,
    ) -> Self {
        Self::capture_execution(before, env, &[source], CheckExecution::Sequential(outcome))
    }

    fn capture_execution(
        before: &BTreeSet<Name>,
        env: &Environment,
        sources: &[&str],
        execution: CheckExecution<'_>,
    ) -> Self {
        let (module, rejected) = match &execution {
            CheckExecution::HeaderFirst { module, rejected } => (*module, *rejected),
            CheckExecution::Sequential(outcome) => (None, outcome.is_rejected()),
        };
        let (
            check_mode,
            registration_semantics,
            batch_committed,
            batch_rejected,
            sequential_outcome,
        ) = match execution {
            CheckExecution::HeaderFirst { .. } => (
                "header-first-batch",
                "transactional-module",
                Some(module.is_some_and(|module| module.committed)),
                Some(rejected),
                Value::Null,
            ),
            CheckExecution::Sequential(outcome) => (
                "sequential-island",
                "nontransactional-per-declaration",
                None,
                None,
                json!({
                    // Observation only: this list is not the kernel roster
                    // or a complete source ownership map.
                    "registered": outcome.registered,
                    "errors": outcome.errors.iter().map(|error| json!({
                        "start": error.start,
                        "end": error.end,
                        "message": error.message,
                    })).collect::<Vec<_>>(),
                }),
            ),
        };
        let after = owned_names(env);
        let mut errors = Vec::new();
        let mut owners: BTreeMap<Name, Vec<usize>> = BTreeMap::new();
        let mut source_declarations = Vec::new();
        if let Some(module) = module {
            for (index, decl) in module.decls.iter().enumerate() {
                for name in &decl.introduces {
                    owners.entry(name.clone()).or_default().push(index);
                }
                let status = match &decl.status {
                    DeclStatus::Registered => "registered",
                    DeclStatus::Refused(_) => "refused",
                    DeclStatus::NoHeader { .. } => "no-header",
                    DeclStatus::LexicalOrCommand => "lexical-or-command",
                };
                source_declarations.push(json!({
                    "source_declaration": index,
                    "unit": decl.unit.0,
                    "start": decl.span.start,
                    "end": decl.span.end,
                    "identity": decl.name,
                    "name": decl.name.as_ref().map(ToString::to_string),
                    "status": status,
                    "introduced_identities": decl.introduces,
                    "resolved_type_and_value_dependencies": decl.depends_on,
                }));
            }
        }

        // Walk the environment, not `registered`/`introduces`/producer rows.
        let declarations: Vec<Value> = after
            .difference(before)
            .map(|name| {
                let info = env.get_const(name).expect("owned identity must have a constant");
                let (owner_indices, ownership) = if let Some(indices) = owners.get(name) {
                    (indices.clone(), "elaborator-introduces")
                } else {
                    let parent = env
                        .get_constructor(name)
                        .map(|val| &val.inductive_name)
                        .or_else(|| env.get_recursor(name).map(|val| &val.inductive_name));
                    match parent.and_then(|parent| owners.get(parent)) {
                        Some(indices) => (indices.clone(), "kernel-inductive-owner"),
                        None => (Vec::new(), "unattributed"),
                    }
                };
                let role = if env.get_inductive(name).is_some() {
                    "inductive"
                } else if env.get_constructor(name).is_some() {
                    "constructor"
                } else if env.get_recursor(name).is_some() {
                    "recursor"
                } else if env.quotients().any(|val| &val.name == name) {
                    "quotient-primitive"
                } else {
                    "constant"
                };
                let mut dependencies = HashSet::new();
                info.type_.collect_constants_into(&mut dependencies);
                if let Some(value) = &info.value {
                    value.collect_constants_into(&mut dependencies);
                }
                if let Some(recursor) = env.get_recursor(name) {
                    for rule in &recursor.rules {
                        dependencies.insert(rule.constructor_name.clone());
                        rule.rhs.collect_constants_into(&mut dependencies);
                    }
                }
                let dependencies: BTreeSet<_> = dependencies.into_iter().collect();
                let missing: Vec<_> = dependencies
                    .iter()
                    .filter(|dependency| env.get_const(dependency).is_none())
                    .collect();
                // Bind the actual constant plus primitive metadata. A recursor
                // can have no ConstantInfo.value but executable reduction rules.
                // Failure to serialize remains an explicit hole, never a fake hash.
                let payload_sha256 = match canonical_json_sha256(&(
                    info,
                    env.get_inductive(name),
                    env.get_constructor(name),
                    env.get_recursor(name),
                    env.quotients().find(|val| &val.name == name),
                )) {
                    Ok(hash) => Some(hash),
                    Err(error) => {
                        errors.push(format!("kernel payload {name}: {error}"));
                        None
                    }
                };
                json!({
                    "identity": name,
                    "name": name.to_string(),
                    "kernel_role": role,
                    "constant_kind": info.kind,
                    "has_value": info.value.is_some(),
                    "noncomputable": env.is_noncomputable(name),
                    "kernel_payload_sha256": payload_sha256,
                    "ownership": ownership,
                    "source_declarations": owner_indices,
                    "type_value_and_recursor_dependencies": dependencies,
                    "unresolved_dependencies": missing,
                    "kernel_classification": classify_kernel_type(env, name, CLASSIFICATION_LIMITS).diagnostic_json(),
                    "runtime_classification": "unmeasured",
                })
            })
            .collect();
        let unattributed =
            declarations.iter().filter(|row| row["ownership"] == "unattributed").count();
        let lazy_names: BTreeSet<_> = env.lazy_source_names().into_iter().collect();
        let input_rows: Vec<_> = sources
            .iter()
            .enumerate()
            .map(|(unit, source)| {
                json!({
                    "unit": unit,
                    "bytes": source.len(),
                    "sha256": stable_sha256_hex(source.as_bytes()),
                })
            })
            .collect();
        let before_hash =
            canonical_json_sha256(before).map_err(|error| errors.push(error.to_string())).ok();
        let after_hash =
            canonical_json_sha256(&after).map_err(|error| errors.push(error.to_string())).ok();
        Self {
            report: json!({
                "schema": "trust.lean.kernel-roster/v1",
                "authority": "diagnostic-only",
                "scope": "new-owned-kernel-identities",
                "kernel_payload_hash_format": "canonical-json tuple [ConstantInfo, InductiveVal?, ConstructorVal?, RecursorVal?, QuotVal?]",
                // Additive diagnostic extension: legacy v1 consumers may ignore
                // it, but must never interpret absence as a measured class.
                "kernel_classification_schema": "trust.lean.kernel-classification/v1",
                "kernel_classification_limits": {
                    "type_nodes": CLASSIFICATION_LIMITS.type_nodes,
                    "type_depth": CLASSIFICATION_LIMITS.type_depth,
                    "telescope_binders": CLASSIFICATION_LIMITS.telescope_binders,
                    "kernel_heartbeats": CLASSIFICATION_LIMITS.kernel_heartbeats,
                },
                "inputs": input_rows,
                // Additive mode schema. Batch booleans retain their meaning;
                // null explicitly means no batch transaction ran, not false.
                "check_execution_schema": "trust.lean.kernel-check-execution/v1",
                "check_mode": check_mode,
                "registration_semantics": registration_semantics,
                "check_rejected": rejected,
                "batch_committed": batch_committed,
                "batch_rejected": batch_rejected,
                "sequential_outcome": sequential_outcome,
                "source_declaration_metadata": if check_mode == "sequential-island" {
                    "unavailable-sequential-checker"
                } else if module.is_some() {
                    "elaborator-module-outcome"
                } else {
                    "unavailable-before-module-outcome"
                },
                "session_tainted": rejected,
                "owned_before": { "count": before.len(), "identities_sha256": before_hash },
                "owned_after": { "count": after.len(), "identities_sha256": after_hash },
                "removed_owned_identities": before.difference(&after).collect::<Vec<_>>(),
                "source_declarations": source_declarations,
                "declarations": declarations,
                "unattributed_declarations": unattributed,
                "has_lazy_constant_source": env.has_constant_source(),
                "discovered_lazy_identities": lazy_names,
                "lazy_import_enumeration": "unverified",
                "runtime_body_universe": "unmeasured",
                "denominator_status": "denominator_unverified",
                "limitations": [
                    "Owned identity delta does not measure changed payloads of preexisting identities.",
                    "Source ownership is incomplete where public elaboration/kernel metadata omits generated owners.",
                    "Sequential checks retain partial registrations on rejection; their registered-name list does not establish source ownership or completeness, and batch transaction fields are inapplicable.",
                    "Lazy names are advisory; the kernel source API does not certify exhaustive enumeration.",
                    "Dependencies include types and proofs; they are not executable reachability.",
                    "Kernel classification describes declaration types only: proof-only/type-family are erasure candidates, never exclusions from this roster or runtime-completeness evidence.",
                    "Kernel classification does not check declaration values or grant axiom-policy/source acceptance.",
                    "Noncomputable, bodyless and primitive declarations retain their flags/roles independently of kernel classification; an unknown classification remains unmeasured.",
                    "Erasure, closure conversion, specialization and runtime/ABI helpers require a separate body census."
                ],
                "errors": errors,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clean_island::CleanIslandSession;

    fn row<'a>(report: &'a Value, name: &str) -> &'a Value {
        report["declarations"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["name"] == name)
            .unwrap_or_else(|| panic!("missing census row {name}: {report}"))
    }

    fn assert_same_outcome(actual: &CleanIslandOutcome, expected: &CleanIslandOutcome) {
        assert_eq!(actual.registered, expected.registered);
        let errors = |outcome: &CleanIslandOutcome| {
            outcome
                .errors
                .iter()
                .map(|error| (error.start, error.end, error.message.clone()))
                .collect::<Vec<_>>()
        };
        assert_eq!(errors(actual), errors(expected));
        assert_eq!(actual.is_rejected(), expected.is_rejected());
    }

    fn assert_sequential_report(report: &Value, source: &str, outcome: &CleanIslandOutcome) {
        assert_eq!(report["check_execution_schema"], "trust.lean.kernel-check-execution/v1");
        assert_eq!(report["check_mode"], "sequential-island");
        assert_eq!(report["registration_semantics"], "nontransactional-per-declaration");
        assert!(report["batch_committed"].is_null());
        assert!(report["batch_rejected"].is_null());
        assert_eq!(report["check_rejected"], outcome.is_rejected());
        assert_eq!(
            report["inputs"],
            json!([{
                "unit": 0,
                "bytes": source.len(),
                "sha256": stable_sha256_hex(source.as_bytes()),
            }])
        );
        assert_eq!(report["sequential_outcome"]["registered"], json!(outcome.registered));
        let errors: Vec<_> = outcome
            .errors
            .iter()
            .map(|error| {
                json!({
                    "start": error.start,
                    "end": error.end,
                    "message": error.message,
                })
            })
            .collect();
        assert_eq!(report["sequential_outcome"]["errors"], json!(errors));
        assert_eq!(report["source_declaration_metadata"], "unavailable-sequential-checker");
        assert_eq!(report["source_declarations"], json!([]));
        let rows = report["declarations"].as_array().unwrap();
        assert!(rows.iter().all(|row| row["ownership"] == "unattributed"));
        assert_eq!(report["unattributed_declarations"], rows.len());
        assert!(rows.iter().all(|row| row["runtime_classification"] == "unmeasured"));
        assert_eq!(report["runtime_body_universe"], "unmeasured");
        assert_eq!(report["denominator_status"], "denominator_unverified");
    }

    #[test]
    fn sequential_observer_preserves_exact_outcomes_environment_and_file_context() {
        let mut plain = CleanIslandSession::new();
        let mut measured = CleanIslandSession::new();
        for source in [
            "namespace Shared\ntheorem zero_eq : 0 = 0 := rfl\nend Shared",
            "open Shared\ntheorem reused : 0 = 0 := zero_eq",
            "theorem reusedAgain : 0 = 0 := zero_eq",
        ] {
            let before = owned_names(plain.environment().unwrap());
            let expected = plain.check(source);
            let (actual, census) = measured.check_with_census(source);
            assert!(!expected.is_rejected(), "{expected:?}");
            assert_same_outcome(&actual, &expected);
            assert_sequential_report(&census.report, source, &actual);
            let expected_report = LeanKernelRoster::capture_sequential(
                &before,
                plain.environment().unwrap(),
                source,
                &expected,
            );
            assert_eq!(census.report, expected_report.report);
            let constants = |session: &CleanIslandSession| {
                let constants: BTreeMap<_, _> = session
                    .environment()
                    .unwrap()
                    .constants()
                    .map(|info| (info.name.clone(), info))
                    .collect();
                // Names have structural JSON identities, not string map keys.
                // Sort by Name, then hash the exact complete constant records.
                canonical_json_sha256(&constants.into_values().collect::<Vec<_>>()).unwrap()
            };
            assert_eq!(constants(&plain), constants(&measured));
            assert!(!measured.is_tainted());
        }
    }

    #[test]
    fn sequential_forward_reference_is_not_silently_changed_to_batch_semantics() {
        let source = "def earlier : Nat := later\ndef later : Nat := 1";
        let expected = CleanIslandSession::new().check(source);
        let mut measured = CleanIslandSession::new();
        let (actual, census) = measured.check_with_census(source);
        assert_same_outcome(&actual, &expected);
        assert!(actual.is_rejected());
        assert!(actual.registered.iter().any(|name| name == "later"));
        assert_sequential_report(&census.report, source, &actual);
        row(&census.report, "later");
        assert_eq!(census.report["session_tainted"], true);
        assert!(measured.environment().is_none());
        let batch = CleanIslandSession::new().check_all_with_census(&[source]);
        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        let report = batch.census.unwrap().report;
        assert_eq!(report["check_mode"], "header-first-batch");
        assert_eq!(report["registration_semantics"], "transactional-module");
        assert_eq!(report["batch_committed"], true);
        assert_eq!(report["batch_rejected"], false);
        assert_eq!(report["check_rejected"], false);
        assert!(report["sequential_outcome"].is_null());
        assert_eq!(report["source_declaration_metadata"], "elaborator-module-outcome");
    }

    #[test]
    fn sequential_rejection_retains_all_partial_and_generated_identities_without_owners() {
        let source = "inductive SequentialChoice where\n| first : SequentialChoice\n| second : SequentialChoice\n\
            def rejectedProof : False := True.intro\n\
            def retainedAfterFailure : Nat := 7";
        let expected = CleanIslandSession::new().check(source);
        let mut measured = CleanIslandSession::new();
        let (actual, census) = measured.check_with_census(source);
        assert_same_outcome(&actual, &expected);
        assert!(actual.is_rejected());
        assert_sequential_report(&census.report, source, &actual);
        for name in [
            "SequentialChoice",
            "SequentialChoice.first",
            "SequentialChoice.second",
            "SequentialChoice.rec",
            "SequentialChoice.recOn",
            "retainedAfterFailure",
        ] {
            row(&census.report, name);
        }
        assert!(!actual.registered.iter().any(|name| name == "SequentialChoice.recOn"));
        assert!(census.report["declarations"].as_array().unwrap().len() > actual.registered.len());
        assert_eq!(census.report["session_tainted"], true);
        assert!(measured.environment().is_none());
    }

    #[test]
    fn sequential_prior_taint_and_parse_failure_are_not_fabricated_batch_rejections() {
        let mut plain = CleanIslandSession::new();
        let mut measured = CleanIslandSession::new();
        for source in ["def :", "def afterParseFailure : Nat := 3", ""] {
            let expected = plain.check(source);
            let (actual, census) = measured.check_with_census(source);
            assert_same_outcome(&actual, &expected);
            assert_sequential_report(&census.report, source, &actual);
            assert_eq!(actual.is_rejected(), source == "def :");
            assert_eq!(census.report["session_tainted"], true);
            assert!(plain.environment().is_none());
            assert!(measured.environment().is_none());
            if source == "def :" || source.is_empty() {
                assert_eq!(census.report["declarations"], json!([]));
                assert_eq!(census.report["owned_before"], census.report["owned_after"]);
            } else {
                row(&census.report, "afterParseFailure");
            }
        }
        let failed_batch = CleanIslandSession::new().check_all_with_census(&["def :"]);
        let report = failed_batch.census.unwrap().report;
        assert_eq!(report["check_mode"], "header-first-batch");
        assert_eq!(report["batch_committed"], false);
        assert_eq!(report["batch_rejected"], true);
        assert_eq!(report["check_rejected"], true);
        assert_eq!(report["source_declaration_metadata"], "unavailable-before-module-outcome");
    }

    #[test]
    fn sequential_missing_import_preserves_refusal_and_observes_actual_builtin_materialization() {
        let source = "import MissingSequentialCensusModule\ndef afterMissingImport : Nat := 4";
        let expected = CleanIslandSession::new().check(source);
        let mut measured = CleanIslandSession::new();
        let (actual, census) = measured.check_with_census(source);
        assert_same_outcome(&actual, &expected);
        assert!(actual.is_rejected());
        assert!(
            actual
                .errors
                .iter()
                .any(|error| error.message.contains("MissingSequentialCensusModule"))
        );
        assert_sequential_report(&census.report, source, &actual);
        row(&census.report, "afterMissingImport");
        // Ordinary island semantics initialize PProd on this lexical path. The
        // observer does not move that initialization or mislabel the builtins
        // as authored source; every real delta identity remains unattributed.
        row(&census.report, "PProd");
        assert_eq!(census.report["session_tainted"], true);
        assert!(measured.environment().is_none());
    }

    #[test]
    fn sequential_delta_excludes_prior_state_without_discarding_its_usable_context() {
        let mut plain = CleanIslandSession::new();
        let mut measured = CleanIslandSession::new();
        let seed = "def previouslyChecked : Nat := 7";
        assert!(!plain.check(seed).is_rejected());
        assert!(!measured.check(seed).is_rejected());
        let source = "def newUse : Nat := previouslyChecked";
        let expected = plain.check(source);
        let (actual, census) = measured.check_with_census(source);
        assert!(!actual.is_rejected(), "{actual:?}");
        assert_same_outcome(&actual, &expected);
        assert_sequential_report(&census.report, source, &actual);
        assert_eq!(census.report["declarations"].as_array().unwrap().len(), 1);
        row(&census.report, "newUse");
        assert!(
            measured
                .environment()
                .unwrap()
                .get_const(&Name::from_string("previouslyChecked"))
                .is_some()
        );
        assert_eq!(census.report["session_tainted"], false);
    }

    #[test]
    fn classification_distinguishes_proofs_from_propositions_and_type_families() {
        let source = "def propositionValue : Prop := True\n\
            def proofValue : True := True.intro\n\
            theorem provedTheorem : True := True.intro\n\
            def typeValue : Type := Nat\n\
            def typeFamily (n : Nat) : Type := Nat\n\
            def propositionFamily (n : Nat) : Prop := n = n\n\
            def dependentProof (p : Prop) (h : p) : p := h\n\
            def dependentTypeFamily (a : Type) : Type := a\n\
            def dependentIdentity (a : Type) (x : a) : a := x\n\
            def ordinaryValue (n : Nat) : Nat := n";
        let batch = CleanIslandSession::new().check_all_with_census(&[source]);
        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        let report = batch.census.unwrap().report;
        for name in ["proofValue", "provedTheorem", "dependentProof"] {
            assert_eq!(row(&report, name)["kernel_classification"]["kind"], "proof-only", "{name}");
        }
        for name in [
            "propositionValue",
            "typeValue",
            "typeFamily",
            "propositionFamily",
            "dependentTypeFamily",
        ] {
            assert_eq!(
                row(&report, name)["kernel_classification"]["kind"],
                "type-family",
                "{name}"
            );
        }
        assert_eq!(
            row(&report, "ordinaryValue")["kernel_classification"]["kind"],
            "computational-candidate"
        );
        assert_eq!(
            row(&report, "dependentIdentity")["kernel_classification"]["kind"],
            "computational-candidate"
        );
        assert_eq!(row(&report, "proofValue")["constant_kind"], "Definition");
        assert_eq!(row(&report, "propositionValue")["constant_kind"], "Definition");
        assert_eq!(report["declarations"].as_array().unwrap().len(), 10);
        assert!(
            report["declarations"]
                .as_array()
                .unwrap()
                .iter()
                .all(|row| row["runtime_classification"] == "unmeasured")
        );
        assert_eq!(report["denominator_status"], "denominator_unverified");
        assert_eq!(report["kernel_classification_schema"], "trust.lean.kernel-classification/v1");
    }

    #[test]
    fn classification_retains_generated_primitive_roster_and_ownership() {
        let batch = CleanIslandSession::new().check_all_with_census(&[
            "inductive ClassifiedChoice where\n| first : ClassifiedChoice\n| second : ClassifiedChoice",
            "inductive ClassifiedProof : Prop where\n| intro : ClassifiedProof",
        ]);
        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        let registered = batch.outcomes[0].registered.len();
        let report = batch.census.unwrap().report;
        assert_eq!(
            row(&report, "ClassifiedChoice")["kernel_classification"]["kind"],
            "type-family"
        );
        for name in [
            "ClassifiedChoice.first",
            "ClassifiedChoice.second",
            "ClassifiedChoice.rec",
            "ClassifiedChoice.recOn",
        ] {
            let row = row(&report, name);
            assert_eq!(
                row["kernel_classification"]["kind"], "primitive-candidate",
                "{name}: {row}"
            );
            assert_eq!(row["runtime_classification"], "unmeasured");
        }
        let helper = row(&report, "ClassifiedChoice.recOn");
        assert_eq!(helper["ownership"], "kernel-inductive-owner");
        assert_eq!(
            helper["has_value"], true,
            "this generated recOn helper retains its definition too"
        );
        assert_eq!(
            row(&report, "ClassifiedChoice.rec")["has_value"],
            false,
            "recursor rules are retained without an ordinary body"
        );
        assert_eq!(
            row(&report, "ClassifiedProof.intro")["kernel_classification"]["kind"],
            "proof-only",
            "primitive metadata does not override an actual Prop result"
        );
        assert!(report["declarations"].as_array().unwrap().len() > registered);
    }

    #[test]
    fn noncomputable_is_an_independent_flag_not_proof_or_runtime_erasure() {
        let batch = CleanIslandSession::new()
            .check_all_with_census(&["noncomputable def classifiedNoncomputable : Nat := 7"]);
        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        let report = batch.census.unwrap().report;
        let row = row(&report, "classifiedNoncomputable");
        assert_eq!(row["noncomputable"], true);
        assert_eq!(row["kernel_classification"]["kind"], "computational-candidate");
        assert_eq!(row["runtime_classification"], "unmeasured");
        assert_eq!(report["denominator_status"], "denominator_unverified");
    }

    #[test]
    fn classification_errors_and_each_resource_bound_remain_unknown() {
        let mut session = CleanIslandSession::new();
        assert!(!session.check("def boundedTypeFamily (n : Nat) : Type := Nat").is_rejected());
        let env = session.environment().unwrap();
        let name = Name::from_string("boundedTypeFamily");
        let unknown = |result: KernelClassification, expected: &str| match result {
            KernelClassification::Unknown { reason } => {
                assert!(reason.contains(expected), "{reason}")
            }
            other => panic!("resource/error case acquired a classification: {other:?}"),
        };
        unknown(
            classify_kernel_type(env, &Name::from_string("absent"), CLASSIFICATION_LIMITS),
            "absent",
        );
        for limits in [
            ClassificationLimits { type_nodes: 1, ..CLASSIFICATION_LIMITS },
            ClassificationLimits { type_depth: 0, ..CLASSIFICATION_LIMITS },
            ClassificationLimits { telescope_binders: 0, ..CLASSIFICATION_LIMITS },
            ClassificationLimits { kernel_heartbeats: 1, ..CLASSIFICATION_LIMITS },
        ] {
            unknown(classify_kernel_type(env, &name, limits), "bound");
        }
        unknown(
            classify_kernel_type(
                env,
                &name,
                ClassificationLimits { kernel_heartbeats: 0, ..CLASSIFICATION_LIMITS },
            ),
            "nonzero",
        );
        // These are diagnostic-only malformed dependency bytes, not a kernel
        // registration or an accepted source context.
        #[derive(Debug)]
        struct BrokenSource(clean_kernel::ConstantInfo);
        impl clean_kernel::env::ConstantSource for BrokenSource {
            fn get(&self, name: &Name) -> Option<&clean_kernel::ConstantInfo> {
                (&self.0.name == name).then_some(&self.0)
            }
            fn contains(&self, name: &Name) -> bool {
                &self.0.name == name
            }
        }
        let mut broken = env.get_const(&name).unwrap().clone();
        broken.type_ = Expr::const_str("MissingClassificationType");
        let mut broken_env = Environment::with_prelude();
        broken_env.set_constant_source(std::sync::Arc::new(BrokenSource(broken)));
        unknown(classify_kernel_type(&broken_env, &name, CLASSIFICATION_LIMITS), "type check");
        assert_eq!(
            classify_kernel_type(env, &name, CLASSIFICATION_LIMITS),
            KernelClassification::TypeFamily
        );
    }

    #[test]
    fn classification_does_not_change_checked_identity_or_failed_batch_state() {
        use crate::lean_source_batch::{CheckedLeanSourceBatch, LeanSourceInput};
        let sources = vec![LeanSourceInput {
            module: "Classified".into(),
            path: "Classified.lean".into(),
            source: "def value : Nat := 7\ndef proof : True := True.intro".into(),
        }];
        let plain = CheckedLeanSourceBatch::check(sources.clone(), false);
        let measured = CheckedLeanSourceBatch::check(sources, true);
        let plain = plain.accepted_context().unwrap();
        let measured_context = measured.accepted_context().unwrap();
        assert_eq!(plain.source_closure_sha256(), measured_context.source_closure_sha256());
        assert_eq!(plain.owned_declarations_sha256(), measured_context.owned_declarations_sha256());
        let report = &measured.attempt().unwrap().census.as_ref().unwrap().report;
        assert_eq!(report["declarations"].as_array().unwrap().len(), 2);
        let failed = CleanIslandSession::new()
            .check_all_with_census(&["def good : Nat := 1\ndef bad : False := True.intro"]);
        assert!(failed.is_rejected());
        let report = failed.census.unwrap().report;
        assert_eq!(report["batch_rejected"], true);
        assert_eq!(report["session_tainted"], true);
        assert_eq!(report["denominator_status"], "denominator_unverified");
        assert!(!report["source_declarations"].as_array().unwrap().is_empty());
    }

    #[test]
    fn oversized_classification_retains_the_row_and_measures_the_next_declaration() {
        let binders = (0..130).map(|index| format!(" (n{index} : Nat)")).collect::<String>();
        let source = format!("def tooDeep{binders} : Nat := 0\ndef afterDeep : Nat := 1");
        let batch = CleanIslandSession::new().check_all_with_census(&[&source]);
        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        let report = batch.census.unwrap().report;
        assert_eq!(report["declarations"].as_array().unwrap().len(), 2);
        let unknown = &row(&report, "tooDeep")["kernel_classification"];
        assert_eq!(unknown["kind"], "unknown");
        assert!(unknown["reason"].as_str().unwrap().contains("bound"));
        assert_eq!(
            row(&report, "afterDeep")["kernel_classification"]["kind"],
            "computational-candidate"
        );
        assert_eq!(row(&report, "tooDeep")["runtime_classification"], "unmeasured");
        assert_eq!(report["denominator_status"], "denominator_unverified");
    }

    #[test]
    fn records_sources_and_all_kernel_delta_without_producer_admission() {
        let source = "def censusId (n : Nat) : Nat := n\ndef censusUse : Nat := censusId 3";
        let batch = CleanIslandSession::new().check_all_with_census(&[source]);
        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        let report = &batch.census.unwrap().report;
        assert_eq!(report["inputs"][0]["sha256"], stable_sha256_hex(source.as_bytes()));
        let rows = report["declarations"].as_array().unwrap();
        assert!(rows.iter().any(|row| row["name"] == "censusId"));
        assert!(rows.iter().any(|row| row["name"] == "censusUse"));
        assert!(rows.iter().all(|row| row["kernel_payload_sha256"].as_str().unwrap().len() == 64));
        assert_eq!(report["denominator_status"], "denominator_unverified");
        assert_eq!(report["runtime_body_universe"], "unmeasured");
    }

    #[test]
    fn generated_inductive_entries_are_not_lost_with_primary_registration() {
        let batch = CleanIslandSession::new().check_all_with_census(&[
            "inductive CensusChoice where\n| first : CensusChoice\n| second : CensusChoice",
        ]);
        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        let report = &batch.census.unwrap().report;
        let rows = report["declarations"].as_array().unwrap();
        assert!(rows.len() > batch.outcomes[0].registered.len());
        assert!(rows.iter().any(|row| row["kernel_role"] == "constructor"));
        assert!(rows.iter().any(|row| row["kernel_role"] == "recursor"));
        let rec_on = rows.iter().find(|row| row["name"] == "CensusChoice.recOn").expect(
            "kernel-generated helper absent from the synthetic introduces list is retained",
        );
        assert_eq!(rec_on["ownership"], "kernel-inductive-owner");
        assert_eq!(
            report["owned_before"]["count"].as_u64().unwrap() + rows.len() as u64,
            report["owned_after"]["count"].as_u64().unwrap()
        );
    }

    #[test]
    fn no_census_on_ordinary_check_and_no_complete_census_on_refusal() {
        assert!(CleanIslandSession::new().check_all(&["def x : Nat := 1"]).census.is_none());
        let batch = CleanIslandSession::new().check_all_with_census(&["def x : Nat := missing"]);
        assert!(batch.is_rejected());
        let report = batch.census.unwrap().report;
        assert_eq!(report["batch_rejected"], true);
        assert_eq!(report["session_tainted"], true);
        assert_eq!(report["denominator_status"], "denominator_unverified");
        assert!(!report["source_declarations"].as_array().unwrap().is_empty());
    }

    #[test]
    fn parse_failure_and_prior_taint_remain_visible() {
        let mut session = CleanIslandSession::new();
        assert!(session.check("def :").is_rejected());
        let batch = session.check_all_with_census(&["def afterFailure : Nat := 3"]);
        assert_eq!(batch.census.unwrap().report["session_tainted"], true);
        let batch = CleanIslandSession::new().check_all_with_census(&["def :"]);
        let report = batch.census.unwrap().report;
        assert_eq!(report["batch_committed"], false);
        assert_eq!(report["inputs"].as_array().unwrap().len(), 1);
    }

    #[test]
    fn missing_elaborator_metadata_does_not_drop_or_guess_ownership() {
        let mut session = CleanIslandSession::new();
        assert!(!session.check("def M.untracked : Nat := 1").is_rejected());
        let env = session.environment().unwrap();
        // Deliberately omit the ownership channel; never infer it from `M.`.
        let before = env
            .constants()
            .filter(|info| info.name.to_string() != "M.untracked")
            .map(|info| info.name.clone())
            .collect();
        let roster = LeanKernelRoster::capture(&before, env, &[], None, false);
        assert_eq!(roster.report["declarations"][0]["ownership"], "unattributed");
        assert_eq!(roster.report["unattributed_declarations"], 1);
    }

    #[test]
    fn input_and_payload_mutations_change_their_hashes() {
        let first = CleanIslandSession::new().check_all_with_census(&["def changed : Nat := 1"]);
        let second = CleanIslandSession::new().check_all_with_census(&["def changed : Nat := 2"]);
        let first = first.census.unwrap().report;
        let second = second.census.unwrap().report;
        assert_ne!(first["inputs"][0]["sha256"], second["inputs"][0]["sha256"]);
        assert_ne!(
            first["declarations"][0]["kernel_payload_sha256"],
            second["declarations"][0]["kernel_payload_sha256"]
        );
    }

    #[test]
    fn empty_lazy_enumeration_is_not_evidence_of_an_empty_import_closure() {
        #[derive(Debug)]
        struct HiddenSource(clean_kernel::ConstantInfo);
        impl clean_kernel::env::ConstantSource for HiddenSource {
            fn get(&self, name: &Name) -> Option<&clean_kernel::ConstantInfo> {
                (&self.0.name == name).then_some(&self.0)
            }
            fn contains(&self, name: &Name) -> bool {
                &self.0.name == name
            }
            // Intentionally use the default, incomplete names() implementation.
        }
        let mut checked = CleanIslandSession::new();
        assert!(!checked.check("def hiddenImported : Nat := 7").is_rejected());
        let hidden_name = Name::from_string("hiddenImported");
        let hidden = checked.environment().unwrap().get_const(&hidden_name).unwrap().clone();
        let mut env = Environment::new();
        env.set_constant_source(std::sync::Arc::new(HiddenSource(hidden)));
        assert!(env.get_const(&hidden_name).is_some());
        let report = LeanKernelRoster::capture(&BTreeSet::new(), &env, &[], None, false).report;
        assert_eq!(report["has_lazy_constant_source"], true);
        assert_eq!(report["discovered_lazy_identities"], json!([]));
        assert_eq!(report["lazy_import_enumeration"], "unverified");
        assert_eq!(report["denominator_status"], "denominator_unverified");
    }

    #[test]
    fn proof_valued_definition_is_not_mislabeled_as_a_runtime_body() {
        let batch = CleanIslandSession::new().check_all_with_census(&[
            "def proofDefinition : 0 = 0 := rfl\ntheorem proofTheorem : 0 = 0 := rfl",
        ]);
        assert!(!batch.is_rejected(), "{:?}", batch.outcomes);
        let report = batch.census.unwrap().report;
        let rows = report["declarations"].as_array().unwrap();
        assert_eq!(rows.len(), 2);
        assert!(rows.iter().all(|row| row["runtime_classification"] == "unmeasured"));
        assert!(rows.iter().any(|row| row["constant_kind"] == "Definition"));
        assert!(rows.iter().any(|row| row["constant_kind"] == "Theorem"));
    }

    #[test]
    fn dropping_an_input_changes_roster_even_when_other_inputs_still_check() {
        let first = "def keep : Nat := 1";
        let second = "def drop : Nat := 2";
        let full = CleanIslandSession::new().check_all_with_census(&[first, second]);
        let missing = CleanIslandSession::new().check_all_with_census(&[first]);
        assert!(!full.is_rejected() && !missing.is_rejected());
        let full = full.census.unwrap().report;
        let missing = missing.census.unwrap().report;
        assert_eq!(full["inputs"].as_array().unwrap().len(), 2);
        assert_eq!(missing["inputs"].as_array().unwrap().len(), 1);
        assert_ne!(
            full["owned_after"]["identities_sha256"],
            missing["owned_after"]["identities_sha256"]
        );
    }
}
