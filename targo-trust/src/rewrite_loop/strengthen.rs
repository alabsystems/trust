// Strengthen pass: analyze verification failures, build proposals via
// trust-strengthen, and emit RepairFailure records summarizing each failure
// with optional source context.

use std::collections::BTreeMap;

use trust_strengthen::{
    FailureAnalysis, Proposal, analyze_failure, read_function, strengthen, strengthen_with_context,
};

use super::backprop_gate::source_backed_location_path_for_backprop;
use super::proposal::{
    extract_function_name, failure_pattern_label, proposal_kind_tag, summarize_proposal,
    to_failure_analysis, to_trust_pair,
};
use super::provenance::RuntimeBinarySourceProvenance;
use super::types::{RepairFailure, RepairProposalRecord, RepairSourceContext, RewriteProposal};
use crate::types::{VerificationOutcome, VerificationResult};

#[derive(Debug, Clone)]
pub(crate) struct StrengthenIteration {
    pub(crate) proposals: Vec<Proposal>,
    pub(crate) failures: Vec<RepairFailure>,
}

impl StrengthenIteration {
    pub(crate) fn summaries(&self) -> Vec<RewriteProposal> {
        self.proposals.iter().map(summarize_proposal).collect()
    }

    pub(crate) fn proposal_records(&self) -> Vec<RepairProposalRecord> {
        self.proposals
            .iter()
            .map(|proposal| RepairProposalRecord {
                source_file: proposal.function_path.clone(),
                function_name: proposal.function_name.clone(),
                kind: proposal_kind_tag(&proposal.kind).to_string(),
                confidence: proposal.confidence,
                rationale: proposal.rationale.clone(),
            })
            .collect()
    }
}

#[cfg(test)]
pub(crate) fn strengthen_failures(
    failures: &[VerificationResult],
    _default_source_file: Option<&str>,
) -> StrengthenIteration {
    strengthen_failures_with_binary_source_provenance(failures, None)
}

pub(crate) fn strengthen_failures_with_binary_source_provenance(
    failures: &[VerificationResult],
    source_provenance: Option<&RuntimeBinarySourceProvenance>,
) -> StrengthenIteration {
    // Only a REFUTED obligation drives a proposal. An `Unknown`/timeout row
    // would classify just as well — `analyze_failure` reads the VC kind, not
    // the counterexample — but its proposals would flow to the same place, and
    // one proposal kind per pattern (the runtime check) is auto-applied. That
    // makes "the solver ran out of time" a reason to write a panicking
    // `assert!` into a program whose property may well hold, which is the same
    // mistake as rejecting valid Rust because we could not model it.
    // Inconclusive rows already reach the operator as repair prompts.
    // Widening this filter is a capability worth having, but it needs the
    // approval tier to know which verdict a rewrite came from first, so that an
    // inconclusive-derived rewrite can never classify as Auto.
    let mut by_function: BTreeMap<String, Vec<&VerificationResult>> = BTreeMap::new();
    for failure in failures.iter().filter(|r| r.outcome == VerificationOutcome::Failed) {
        let key = if failure.function.is_empty() {
            extract_function_name(&failure.raw_line)
        } else {
            failure.function.clone()
        };
        by_function.entry(key).or_default().push(failure);
    }

    let mut proposals = Vec::new();
    let mut repair_failures = Vec::new();

    for (function_path, function_failures) in by_function {
        let function_name = function_path.rsplit("::").next().unwrap_or(&function_path).to_string();
        let source_backed_failures: Vec<&VerificationResult> = function_failures
            .iter()
            .copied()
            .filter(|failure| {
                source_backed_location_path_for_backprop(failure, source_provenance).is_some()
            })
            .collect();
        let source_file = source_backed_failures
            .iter()
            .find_map(|failure| {
                source_backed_location_path_for_backprop(failure, source_provenance)
            })
            .map(str::to_string);
        let source_ctx =
            source_file.as_deref().and_then(|file| read_function(file, &function_name));

        let analyses: Vec<FailureAnalysis> = source_backed_failures
            .iter()
            .map(|failure| {
                let (vc, result) = to_trust_pair(failure);
                analyze_failure(&vc, &result)
            })
            .collect();

        if !analyses.is_empty() {
            if let Some(ctx) = source_ctx.as_ref() {
                let source_path = source_file.as_deref().unwrap_or(&function_path);
                proposals.extend(strengthen_with_context(
                    source_path,
                    &function_name,
                    &analyses,
                    ctx,
                ));
            } else {
                let source_path = source_file.as_deref().unwrap_or(&function_path);
                proposals.extend(strengthen(source_path, &function_name, &analyses));
            }
        }

        repair_failures.extend(function_failures.into_iter().map(|failure| {
            let source_context =
                if source_backed_location_path_for_backprop(failure, source_provenance).is_none() {
                    None
                } else {
                    source_ctx.as_ref().map(|ctx| RepairSourceContext {
                        source_file: source_file.clone().unwrap_or_default(),
                        signature: ctx.signature.clone(),
                        params: ctx.params.clone(),
                        return_type: ctx.return_type.clone(),
                    })
                };

            RepairFailure {
                function_path: function_path.clone(),
                function_name: function_name.clone(),
                kind: failure.kind.clone(),
                pattern: failure_pattern_label(&to_failure_analysis(failure).pattern).to_string(),
                description: failure.message.clone(),
                location: failure.location.clone(),
                solver: failure.backend.clone(),
                time_ms: failure.time_ms,
                counterexample: failure.counterexample.clone(),
                reason: failure.reason.clone(),
                source_context,
            }
        }));
    }

    StrengthenIteration { proposals, failures: repair_failures }
}
