// Backprop engine: applies trust-backprop rewrites to source files with
// governance controls (protected/test-function immutability, per-function
// rewrite limits).

use std::path::PathBuf;

use trust_backprop::file_io::{FileRewriteResult, apply_plan_to_files};
use trust_backprop::{
    ApprovalPolicy, ApprovalQueue, GovernancePolicy, PendingRewrite, RewriteCheckpoint, RewritePlan,
    RewriteTracker, SourceRewrite, apply_plan, classify_rewrite, create_checkpoint, default_rules,
};
use trust_strengthen::Proposal;

use super::backprop_gate::is_binary_only_path;
#[cfg(test)]
use super::provenance::RuntimeBinarySourceProvenance;
#[cfg(test)]
use super::types::RewriteProposal;
#[cfg(test)]
use crate::types::VerificationResult;

/// Orchestrates applying rewrite proposals to source files via `trust-backprop`.
///
/// Respects governance controls:
/// - Protected functions cannot be rewritten (except spec-only when allowed)
/// - Test functions are immutable
/// - Per-function rewrite limit enforced across iterations
pub(crate) struct BackpropEngine {
    policy: GovernancePolicy,
    tracker: RewriteTracker,
    /// Default source file path to use when the verification result does not
    /// contain an extractable file path. Set from the CLI `--file` argument in
    /// single-file mode.
    default_source_file: Option<String>,
    #[cfg(test)]
    /// Exact source provenance recovered from binary debug/source mappings.
    /// Binary-derived rewrites stay closed unless this gate is effectively open.
    binary_source_provenance: Option<RuntimeBinarySourceProvenance>,
}

/// Result of applying a single backprop iteration.
#[derive(Debug)]
pub(crate) struct BackpropResult {
    /// Number of files modified.
    pub(crate) files_modified: usize,
    /// Number of rewrites applied.
    pub(crate) rewrites_applied: usize,
    /// Number of proposals skipped due to governance.
    pub(crate) governance_skips: usize,
    /// Number of proposals skipped due to rewrite limit.
    pub(crate) limit_skips: usize,
    /// Rewrites that were applied automatically.
    pub(crate) applied_rewrites: Vec<SourceRewrite>,
    /// Rewrites that require review or were blocked.
    pub(crate) pending_rewrites: Vec<PendingRewrite>,
    /// File-level before/after snapshots for applied rewrites.
    pub(crate) file_results: Vec<FileRewriteResult>,
    /// The exact pre-apply content of every file this iteration wrote to.
    ///
    /// `apply_plan_to_files` already unwinds a *partially* written plan, but a
    /// fully written one is only as good as the verdict the next compiler run
    /// gives it. This snapshot is what lets the loop take that edit back.
    pub(crate) pre_apply_checkpoint: Option<RewriteCheckpoint>,
}

impl BackpropResult {
    /// An iteration that reached no file.
    pub(crate) fn nothing_applied(governance_skips: usize, limit_skips: usize) -> Self {
        Self {
            files_modified: 0,
            rewrites_applied: 0,
            governance_skips,
            limit_skips,
            applied_rewrites: Vec::new(),
            pending_rewrites: Vec::new(),
            file_results: Vec::new(),
            pre_apply_checkpoint: None,
        }
    }
}

impl BackpropEngine {
    /// Create a new backprop engine with default governance policy.
    #[cfg(test)]
    pub(crate) fn new() -> Self {
        Self {
            policy: GovernancePolicy::default(),
            tracker: RewriteTracker::new(),
            default_source_file: None,
            #[cfg(test)]
            binary_source_provenance: None,
        }
    }

    /// Create a new backprop engine with protected functions.
    ///
    /// Functions in `skip_functions` will be treated as protected and will not
    /// be rewritten (except for spec-only changes if policy allows).
    pub(crate) fn with_protected(skip_functions: &[String]) -> Self {
        Self {
            policy: GovernancePolicy {
                protected_functions: skip_functions.to_vec(),
                ..GovernancePolicy::default()
            },
            tracker: RewriteTracker::new(),
            default_source_file: None,
            #[cfg(test)]
            binary_source_provenance: None,
        }
    }

    /// Set the default source file path used when verification results lack
    /// file path information. Typically the CLI `--file` target.
    pub(crate) fn set_default_source_file(&mut self, path: String) {
        self.default_source_file = Some(path);
    }

    #[cfg(test)]
    pub(crate) fn set_binary_source_provenance(
        &mut self,
        source_provenance: RuntimeBinarySourceProvenance,
    ) {
        self.binary_source_provenance = Some(source_provenance);
    }

    #[cfg(test)]
    fn binary_source_provenance(&self) -> Option<&RuntimeBinarySourceProvenance> {
        self.binary_source_provenance.as_ref()
    }

    /// Apply rewrite proposals to source files.
    ///
    /// Converts CLI-level `RewriteProposal`s into `trust_strengthen::Proposal`s,
    /// checks governance, generates a rewrite plan, and applies it to disk.
    ///
    /// Returns a summary of what was applied and what was skipped.
    #[cfg(test)]
    pub(crate) fn apply(
        &mut self,
        proposals: &[RewriteProposal],
        verification_results: &[VerificationResult],
    ) -> BackpropResult {
        use super::proposal::{
            proposal_has_binary_only_span, proposal_has_rejected_binary_source_span,
            to_strengthen_proposal,
        };

        let mut governance_skips = 0usize;
        let mut limit_skips = 0usize;

        // Convert CLI proposals to trust-strengthen Proposals, filtering by
        // governance and rewrite-limit.
        let mut strengthen_proposals = Vec::new();
        for proposal in proposals {
            if proposal_has_binary_only_span(proposal, verification_results) {
                governance_skips += 1;
                eprintln!(
                    "    Backprop: skipping `{}` (binary-only span has no source file)",
                    proposal.function
                );
                continue;
            }
            if proposal_has_rejected_binary_source_span(
                proposal,
                verification_results,
                self.binary_source_provenance(),
            ) {
                governance_skips += 1;
                eprintln!(
                    "    Backprop: skipping `{}` (binary-derived span lacks exact source provenance)",
                    proposal.function
                );
                continue;
            }

            // Check per-function rewrite limit before conversion
            if self.tracker.exceeds_limit(&proposal.function, self.policy.max_rewrites_per_function)
            {
                limit_skips += 1;
                eprintln!(
                    "    Backprop: skipping `{}` (rewrite limit {} exceeded)",
                    proposal.function, self.policy.max_rewrites_per_function
                );
                continue;
            }

            let sp = to_strengthen_proposal(
                proposal,
                verification_results,
                self.default_source_file.as_deref(),
                self.binary_source_provenance(),
            );

            // Check governance
            let violations = self.policy.check(&sp);
            if !violations.is_empty() {
                governance_skips += 1;
                eprintln!(
                    "    Backprop: skipping `{}` (governance: {:?})",
                    proposal.function, violations
                );
                continue;
            }

            strengthen_proposals.push(sp);
        }

        self.apply_strengthen_proposals(&strengthen_proposals, governance_skips, limit_skips)
    }

    pub(crate) fn apply_strengthen_proposals(
        &mut self,
        proposals: &[Proposal],
        mut governance_skips: usize,
        mut limit_skips: usize,
    ) -> BackpropResult {
        if proposals.is_empty() {
            return BackpropResult::nothing_applied(governance_skips, limit_skips);
        }

        let mut filtered_proposals = Vec::new();
        for proposal in proposals {
            if is_binary_only_path(&proposal.function_path) {
                governance_skips += 1;
                eprintln!(
                    "    Backprop: skipping `{}` (binary-only span has no source file)",
                    proposal.function_name
                );
                continue;
            }

            if self
                .tracker
                .exceeds_limit(&proposal.function_name, self.policy.max_rewrites_per_function)
            {
                limit_skips += 1;
                eprintln!(
                    "    Backprop: skipping `{}` (rewrite limit {} exceeded)",
                    proposal.function_name, self.policy.max_rewrites_per_function
                );
                continue;
            }

            let violations = self.policy.check(proposal);
            if !violations.is_empty() {
                governance_skips += 1;
                eprintln!(
                    "    Backprop: skipping `{}` (governance: {:?})",
                    proposal.function_name, violations
                );
                continue;
            }

            filtered_proposals.push(proposal.clone());
        }

        if filtered_proposals.is_empty() {
            return BackpropResult::nothing_applied(governance_skips, limit_skips);
        }

        // Generate rewrite plan through trust-backprop (non-strict: skip violations)
        let plan = match apply_plan(&filtered_proposals, &self.policy) {
            Ok(plan) => plan,
            Err(e) => {
                eprintln!("    Backprop: plan generation failed: {e}");
                return BackpropResult::nothing_applied(governance_skips, limit_skips);
            }
        };

        if plan.is_empty() {
            return BackpropResult::nothing_applied(governance_skips, limit_skips);
        }

        let mut auto_plan = RewritePlan::new(plan.summary.clone());
        let mut queue = ApprovalQueue::new();
        let rules = default_rules();

        for rewrite in plan.rewrites {
            match classify_rewrite(&rewrite, &rules) {
                ApprovalPolicy::Auto => auto_plan.rewrites.push(rewrite),
                policy => queue.enqueue(rewrite, policy),
            }
        }

        auto_plan.sort_for_application();
        let applied_rewrites = auto_plan.rewrites.clone();
        let pending_rewrites = queue.drain_all();
        let rewrites_applied = applied_rewrites.len();

        if auto_plan.is_empty() {
            return BackpropResult {
                applied_rewrites,
                pending_rewrites,
                ..BackpropResult::nothing_applied(governance_skips, limit_skips)
            };
        }

        // Nothing reaches the user's files until their current content is
        // captured: an edit that cannot be taken back is worse than an edit not
        // made, and the verdict that judges this generation only arrives on the
        // next compiler run.
        let checkpoint = match create_checkpoint(&auto_plan_target_files(&auto_plan)) {
            Ok(checkpoint) => checkpoint,
            Err(error) => {
                eprintln!(
                    "    Backprop: refusing to rewrite source without a restorable checkpoint: {error}"
                );
                return BackpropResult {
                    applied_rewrites: Vec::new(),
                    pending_rewrites,
                    ..BackpropResult::nothing_applied(governance_skips, limit_skips)
                };
            }
        };

        // Apply the plan to actual files on disk
        match apply_plan_to_files(&auto_plan) {
            Ok(results) => {
                let files_modified = results.len();

                // Record applied rewrites in the tracker
                for rewrite in &applied_rewrites {
                    self.tracker.record(&rewrite.function_name);
                }

                for result in &results {
                    eprintln!(
                        "    Backprop: modified {} ({} rewrites)",
                        result.path, result.rewrite_count
                    );
                }

                BackpropResult {
                    files_modified,
                    rewrites_applied,
                    governance_skips,
                    limit_skips,
                    applied_rewrites,
                    pending_rewrites,
                    file_results: results,
                    pre_apply_checkpoint: Some(checkpoint),
                }
            }
            Err(e) => {
                // The commit owns unwinding its own partial writes, and says so
                // in `rollback_error` when it refused — which it does when
                // another writer reached the file first. Forcing our snapshot
                // over that refusal would clobber whoever that was, so this
                // generation is reported, not silently repaired.
                eprintln!("    Backprop: file rewrite failed: {e}");
                BackpropResult {
                    applied_rewrites: Vec::new(),
                    pending_rewrites,
                    ..BackpropResult::nothing_applied(governance_skips, limit_skips)
                }
            }
        }
    }
}

/// The distinct files an approved plan will write, in plan order.
///
/// A plan routinely carries several rewrites per file, and the same file can be
/// spelled two ways across proposals, while `create_checkpoint` rejects a repeat
/// of the same canonical path outright. Collapsing aliases here keeps that
/// refusal for what it is meant to catch.
fn auto_plan_target_files(plan: &RewritePlan) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = Vec::new();
    let mut identities: Vec<PathBuf> = Vec::new();
    for rewrite in &plan.rewrites {
        let path = PathBuf::from(&rewrite.file_path);
        let identity = path.canonicalize().unwrap_or_else(|_| path.clone());
        if !identities.contains(&identity) {
            identities.push(identity);
            files.push(path);
        }
    }
    files
}
