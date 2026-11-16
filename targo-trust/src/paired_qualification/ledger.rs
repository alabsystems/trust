//! Complete native AY observations. Serialized outcomes and certificate
//! descriptions remain DATA; the actual compiler's current-kernel checks and
//! original live action/input binding are required independently.
use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;
use trust_qualification::{Refusal, Result};
use trust_resource_controller::paired_qualification::PairedInvocation;
use trust_resource_controller::paired_qualification::service::Node;
use trust_types::{FunctionTransportResult, TransportObligationResult};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum Class {
    ProvedSolver,
    ProvedStructural,
    Failed,
    Unknown,
    Timeout,
    RuntimeChecked,
    Skipped,
    Unsupported,
    Canceled,
    Rejected,
}
#[derive(Serialize)]
pub(super) struct Entry {
    pub class: Class,
    /// Source line is retained in the original row; never in the ledger key.
    pub original: TransportObligationResult,
    pub conservative_outcome: crate::types::VerificationOutcome,
    pub vcgen_truncated_function: bool,
    pub absent_callee: Option<String>,
    agreement: Vec<u8>,
}
#[derive(Serialize)]
pub(super) struct Ledger {
    pub claim_scope: &'static str,
    pub source_commit: String,
    pub crate_tree: String,
    pub policy: &'static str,
    pub verification_session: String,
    pub denominator_complete: bool,
    pub classes: BTreeMap<Class, usize>,
    pub entries: BTreeMap<String, Entry>,
    pub truncated_functions: BTreeSet<String>,
    pub coverage: trust_types::CoverageTransportSummary,
    pub terminal: trust_types::CrateTransportSummary,
    pub functions: Vec<FunctionTransportResult>,
    pub conservative_results: Vec<crate::types::VerificationResult>,
}
impl Ledger {
    /// Scope authentication here concerns observed consistency. No constructor
    /// from saved bytes can establish actual execution or proof authority.
    pub fn parse(plan: &PairedInvocation, node: Node, stderr: &[u8]) -> Result<Self> {
        let policy = match node {
            Node::Advisory => "advisory",
            Node::Strict => "strict",
            _ => {
                return Err(Refusal("AY ledger requires its own verification action index".into()));
            }
        };
        plan.validate()?;
        let verification_session =
            format!("native-ay-{}-{policy}", super::hex(&plan.consumer.invocation));
        let parsed = crate::pipeline::transport::paired::parse(stderr, &verification_session)
            .map_err(Refusal)?;
        let mut entries = BTreeMap::new();
        let mut classes = BTreeMap::new();
        let mut truncated_functions = BTreeSet::new();
        let mut normalized = parsed.parsed.verification_results.iter();
        for function in &parsed.functions {
            let mut occurrences = BTreeMap::<String, usize>::new();
            for (index, row) in function.results.iter().enumerate() {
                let projected = normalized.next().ok_or_else(|| {
                    Refusal("native AY row projection omitted an original obligation".into())
                })?;
                let file = row.location.as_ref().map_or("?", |location| location.file.as_str());
                let prefix = format!("{}|{}|{file}", function.function, row.kind);
                let occurrence = occurrences.entry(prefix.clone()).or_default();
                let identity = format!("{prefix}#{occurrence}");
                *occurrence += 1;
                let class = classify(row)?;
                *classes.entry(class).or_default() += 1;
                // The marker stands for a discarded whole-function set. It
                // is a missing denominator, never merely one Unknown row.
                let exact_row = serde_json::to_vec(row).map_err(|error| {
                    Refusal(format!("cannot retain exact native AY row: {error}"))
                })?;
                let vcgen_truncated_function = exact_row
                    .windows(b"TrustVcGenWorkBudgetExceeded".len())
                    .any(|bytes| bytes == b"TrustVcGenWorkBudgetExceeded");
                if vcgen_truncated_function {
                    truncated_functions.insert(function.function.clone());
                }
                let absent_callee = absent_callee(&row.description)
                    .or_else(|| row.reason.as_deref().and_then(absent_callee));
                // Policy-specific artifact locators, timing and independent
                // counterexample choices need not be byte-identical. Exact
                // claims, grades, assumptions and every ledger class must be.
                let agreement = serde_json::to_vec(&(
                    class,
                    projected.outcome,
                    &row.claim_digest_sha256,
                    &row.typed_kind,
                    &row.assumes,
                    &row.grade,
                    &function.modeled_facts,
                    function.runtime_checks,
                    &row.solver,
                    &function.source_sha256,
                    function.stable_ids.get(index),
                    &absent_callee,
                ))
                .map_err(|error| Refusal(format!("cannot bind native AY agreement: {error}")))?;
                if entries
                    .insert(
                        identity,
                        Entry {
                            class,
                            original: row.clone(),
                            conservative_outcome: projected.outcome,
                            vcgen_truncated_function,
                            absent_callee,
                            agreement,
                        },
                    )
                    .is_some()
                {
                    return Err(Refusal("native AY obligation identity was repeated".into()));
                }
            }
        }
        if normalized.next().is_some() || entries.len() != parsed.summary.total_obligations {
            return Err(Refusal(
                "native AY normalized ledger differs from complete compiler denominator".into(),
            ));
        }
        let denominator_complete = truncated_functions.is_empty();
        Ok(Self {
            claim_scope: "complete observed original compiler transport; no execution, source authentication or proof grant from serialized rows",
            source_commit: super::hex(&plan.ay.source_commit),
            crate_tree: super::hex(&plan.ay.crate_tree),
            policy,
            verification_session,
            denominator_complete,
            entries,
            classes,
            truncated_functions,
            coverage: parsed.coverage,
            terminal: parsed.summary,
            functions: parsed.functions,
            conservative_results: parsed.parsed.verification_results,
        })
    }
    pub fn agrees_with(&self, other: &Self) -> Result<()> {
        if self.policy != "advisory"
            || other.policy != "strict"
            || self.source_commit != other.source_commit
            || self.crate_tree != other.crate_tree
            || !self.denominator_complete
            || !other.denominator_complete
            || self.classes != other.classes
            || self.entries.len() != other.entries.len()
            || self.coverage.function_identities != other.coverage.function_identities
            || self.entries.iter().any(|(identity, row)| {
                other.entries.get(identity).is_none_or(|other| row.agreement != other.agreement)
            })
        {
            Err(Refusal(
                "independent advisory/strict complete obligation ledgers do not agree".into(),
            ))
        } else {
            Ok(())
        }
    }
}
fn classify(row: &TransportObligationResult) -> Result<Class> {
    use trust_types::Outcome;
    // An instance discharge is a callee assumption, never a second proof of
    // the caller's obligation; use the same maintained compiler predicate.
    if row.outcome == Outcome::Proved
        && trust_types::assumption::is_instance_hypothesis_discharge_row(&row.kind, &row.solver)
    {
        return Ok(Class::Skipped);
    }
    Ok(match row.outcome {
        Outcome::Proved if row.kind == "no_obligations" => Class::ProvedStructural,
        Outcome::Proved => Class::ProvedSolver,
        Outcome::Failed => Class::Failed,
        Outcome::Unknown => Class::Unknown,
        Outcome::Timeout => Class::Timeout,
        Outcome::RuntimeChecked => Class::RuntimeChecked,
        Outcome::Skipped => Class::Skipped,
        Outcome::Unsupported => Class::Unsupported,
        Outcome::Canceled => Class::Canceled,
        Outcome::Rejected => Class::Rejected,
        _ => {
            return Err(Refusal(
                "native AY obligation has an unsupported outcome vocabulary".into(),
            ));
        }
    })
}
fn absent_callee(text: &str) -> Option<String> {
    let after = text.split_once("call to absent callee `")?.1;
    let value = after.split_once('`')?.0;
    (!value.is_empty()).then(|| value.into())
}

#[cfg(test)]
pub(super) mod tests;
