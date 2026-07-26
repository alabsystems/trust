// Rewrite loop orchestration for `targo trust build --rewrite`.
//
// Implements the prove-strengthen-backprop convergence loop as a CLI
// orchestrator. Each iteration:
//   1. Invoke trustc (prove) and parse verification results
//   2. Analyze failures and propose rewrites (strengthen)
//   3. Check convergence
//   4. Accept or undo the previous iteration's edits against that verdict
//   5. Apply new rewrites to source via trust-backprop (backprop)
//
// Convergence is judged before anything new is written, because the run that
// judges iteration N's edits is the run at the top of iteration N+1: applying
// first would stack an unjudged generation on top of one already known to be
// bad, and there would be no verdict at all for the last iteration's edits.
// `safety` holds the outstanding generation and its undo path.
//
// Uses trust-backprop for AST-aware source rewriting with governance controls.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod artifact;
mod backprop;
mod backprop_gate;
mod convergence;
mod digests;
mod display;
mod identity;
mod mapping;
mod ownership;
mod proposal;
mod provenance;
mod safety;
mod strengthen;
mod types;

#[cfg(test)]
mod tests;

pub(crate) use artifact::{
    append_audit_entries, build_rewrite_records, decision_label, write_repair_artifact,
    write_repair_markdown,
};
pub(crate) use backprop::{BackpropEngine, BackpropResult};
pub(crate) use backprop_gate::binary_source_backpropagation_blockers;
pub(crate) use convergence::{ConvergenceTracker, LoopDecision, ProofFrontier};
pub(crate) use display::{
    print_ai_repair_prompts_for_results, print_iteration_header, print_iteration_summary,
    print_loop_summary,
};
pub(crate) use identity::RuntimeBinarySourceIdentity;
pub(crate) use mapping::{RuntimeBinarySourceMapping, RuntimeBinarySourceProofEvidence};
pub(crate) use ownership::RuntimeExactSourceTypeOwnershipArtifact;
pub(crate) use provenance::RuntimeBinarySourceProvenance;
pub(crate) use safety::{UnverifiedRewrites, describe_restore, rewrite_rejection};
#[cfg(test)]
pub(crate) use strengthen::strengthen_failures;
pub(crate) use strengthen::strengthen_failures_with_binary_source_provenance;
#[cfg(test)]
pub(crate) use types::RewriteProposal;
pub(crate) use types::{
    BinarySourceBackpropagationBlocker, RepairArtifact, RepairIteration, RepairRunSummary,
};
