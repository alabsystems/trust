// Repair artifact I/O: write the JSON/Markdown reports, build per-rewrite
// records, and append audit-trail entries.

use std::collections::BTreeMap;
use std::path::Path;

use trust_backprop::file_io::FileRewriteResult;
use trust_backprop::{
    ApprovalPolicy, ApprovalStatus, AuditAction, AuditEntryBuilder, AuditTrail, PendingRewrite,
    ReverificationResult, RewriteEngine, SourceRewrite, format_github, format_unified,
    generate_diff,
};

use super::convergence::LoopDecision;
use super::proposal::rewrite_spec_delta;
use super::types::{RepairArtifact, RepairRewriteRecord};
use crate::durable_io::atomic_write_private;
use crate::input_limits::{MAX_SAVED_PROOF_REPORT_BYTES, read_bounded_utf8_file};

pub(crate) fn write_repair_artifact(
    output_dir: &Path,
    artifact: &RepairArtifact,
) -> std::io::Result<()> {
    let json = serde_json::to_string_pretty(artifact)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    atomic_write_private(&output_dir.join("repair.json"), json.as_bytes())
}

pub(crate) fn write_repair_markdown(
    output_dir: &Path,
    artifact: &RepairArtifact,
) -> std::io::Result<()> {
    let markdown = render_repair_markdown(artifact);
    atomic_write_private(&output_dir.join("repair.md"), markdown.as_bytes())
}

pub(crate) fn build_rewrite_records(
    applied_rewrites: &[SourceRewrite],
    pending_rewrites: &[PendingRewrite],
    file_results: &[FileRewriteResult],
) -> Vec<RepairRewriteRecord> {
    let engine = RewriteEngine::new();
    let mut current_sources: BTreeMap<String, String> =
        file_results.iter().map(|result| (result.path.clone(), result.original.clone())).collect();
    let mut records = Vec::new();

    for rewrite in applied_rewrites {
        let Some(current_source) = current_sources.get_mut(&rewrite.file_path) else {
            records.push(RepairRewriteRecord {
                status: "applied".to_string(),
                policy: Some("auto".to_string()),
                reviewer_notes: None,
                rewrite: rewrite.clone(),
                diff: None,
                preview_error: Some(
                    "original source snapshot is unavailable; refusing to fabricate an applied diff from an empty or post-rewrite file"
                        .to_string(),
                ),
            });
            continue;
        };

        match engine.apply_rewrite(current_source, rewrite) {
            Ok(updated_source) => {
                let diff = generate_diff(current_source, &updated_source, &rewrite.file_path);
                *current_source = updated_source;
                records.push(RepairRewriteRecord {
                    status: "applied".to_string(),
                    policy: Some("auto".to_string()),
                    reviewer_notes: None,
                    rewrite: rewrite.clone(),
                    diff: Some(diff),
                    preview_error: None,
                });
            }
            Err(err) => records.push(RepairRewriteRecord {
                status: "applied".to_string(),
                policy: Some("auto".to_string()),
                reviewer_notes: None,
                rewrite: rewrite.clone(),
                diff: None,
                preview_error: Some(err.to_string()),
            }),
        }
    }

    for pending in pending_rewrites {
        match read_bounded_utf8_file(
            Path::new(&pending.rewrite.file_path),
            MAX_SAVED_PROOF_REPORT_BYTES,
        ) {
            Ok(source) => match engine.apply_rewrite(&source, &pending.rewrite) {
                Ok(updated_source) => records.push(RepairRewriteRecord {
                    status: pending_status_label(pending.policy).to_string(),
                    policy: Some(approval_policy_label(pending.policy).to_string()),
                    reviewer_notes: pending.reviewer_notes.clone(),
                    rewrite: pending.rewrite.clone(),
                    diff: Some(generate_diff(&source, &updated_source, &pending.rewrite.file_path)),
                    preview_error: None,
                }),
                Err(err) => records.push(RepairRewriteRecord {
                    status: pending_status_label(pending.policy).to_string(),
                    policy: Some(approval_policy_label(pending.policy).to_string()),
                    reviewer_notes: pending.reviewer_notes.clone(),
                    rewrite: pending.rewrite.clone(),
                    diff: None,
                    preview_error: Some(err.to_string()),
                }),
            },
            Err(err) => records.push(RepairRewriteRecord {
                status: pending_status_label(pending.policy).to_string(),
                policy: Some(approval_policy_label(pending.policy).to_string()),
                reviewer_notes: pending.reviewer_notes.clone(),
                rewrite: pending.rewrite.clone(),
                diff: None,
                preview_error: Some(err.to_string()),
            }),
        }
    }

    records
}

pub(crate) fn append_audit_entries(
    trail: &mut AuditTrail,
    iteration: usize,
    rewrite_records: &[RepairRewriteRecord],
) {
    for record in rewrite_records.iter().filter(|record| record.status == "applied") {
        let (old_spec, new_spec, rollback_safe) = rewrite_spec_delta(&record.rewrite);
        let approval_status = match record.policy.as_deref() {
            Some("auto") => ApprovalStatus::Auto,
            Some("review") => ApprovalStatus::Reviewed,
            Some("block") => ApprovalStatus::Rejected,
            _ => ApprovalStatus::Pending,
        };
        let mut entry = AuditEntryBuilder::new(
            AuditAction::RewriteApplied,
            record.rewrite.file_path.clone(),
            record.rewrite.function_name.clone(),
        )
        .iteration(iteration as u32)
        .approval_status(approval_status)
        .reverification_result(ReverificationResult::NotRun)
        .rollback_safe(rollback_safe);

        if let Some(old_spec) = old_spec {
            entry = entry.old_spec(old_spec);
        }
        if let Some(new_spec) = new_spec {
            entry = entry.new_spec(new_spec);
        }
        if let Some(diff) = &record.diff {
            entry = entry.before_after_diff(format_unified(diff));
        }

        trail.append(entry);
    }
}

fn render_repair_markdown(artifact: &RepairArtifact) -> String {
    let mut out = String::new();
    out.push_str("# Trust Repair Report\n\n");
    out.push_str(&format!(
        "- Iterations: {}\n- Final frontier: {} proved, {} failed, {} unknown\n- Outcome: {}\n- Total duration: {}ms\n- Audit entries: {}\n\n",
        artifact.summary.iterations,
        artifact.summary.final_frontier.proved,
        artifact.summary.final_frontier.failed,
        artifact.summary.final_frontier.unknown,
        artifact.summary.final_decision,
        artifact.summary.total_duration_ms,
        artifact.audit_trail.entries().len(),
    ));

    for iteration in &artifact.iterations {
        out.push_str(&format!("## Iteration {}\n\n", iteration.iteration));
        out.push_str(&format!(
            "- Command: `{}`\n- Exit code: `{}`\n- Frontier: {} proved, {} failed, {} unknown\n- Diagnostics: {}\n\n",
            iteration.command.join(" "),
            iteration.exit_code,
            iteration.frontier.proved,
            iteration.frontier.failed,
            iteration.frontier.unknown,
            iteration.compiler_diagnostics.len(),
        ));

        if !iteration.failures.is_empty() {
            out.push_str("### Failures\n\n");
            for failure in &iteration.failures {
                out.push_str(&format!(
                    "- `{}` `{}` at `{}`: {}",
                    failure.function_path,
                    failure.kind,
                    failure
                        .location
                        .as_ref()
                        .map(|span| {
                            format!("{}:{}:{}", span.file, span.line_start, span.col_start)
                        })
                        .unwrap_or_else(|| "unknown".to_string()),
                    failure.description,
                ));
                if let Some(counterexample) = &failure.counterexample {
                    out.push_str(&format!(" | counterexample: `{:?}`", counterexample));
                }
                if let Some(reason) = &failure.reason {
                    out.push_str(&format!(" | reason: `{reason}`"));
                }
                out.push('\n');
            }
            out.push('\n');
        }

        if !iteration.proposals.is_empty() {
            out.push_str("### Proposals\n\n");
            for proposal in &iteration.proposals {
                out.push_str(&format!(
                    "- `{}` `{}` ({:.2}): {}\n",
                    proposal.function_name, proposal.kind, proposal.confidence, proposal.rationale,
                ));
            }
            out.push('\n');
        }

        if !iteration.rewrite_records.is_empty() {
            out.push_str("### Rewrite Details\n\n");
            for record in &iteration.rewrite_records {
                out.push_str(&format!(
                    "- `{}` `{}` [{}] {}\n",
                    record.rewrite.function_name,
                    record.rewrite.file_path,
                    record.status,
                    record.rewrite.rationale,
                ));
                if let Some(policy) = &record.policy {
                    out.push_str(&format!("  Policy: `{policy}`\n"));
                }
                if let Some(error) = &record.preview_error {
                    out.push_str(&format!("  Preview error: `{error}`\n"));
                }
                if let Some(diff) = &record.diff {
                    out.push_str(&format!("{}\n", format_github(diff)));
                }
            }
        }
    }

    out
}

#[cfg(test)]
mod tests {
    use super::super::convergence::ProofFrontier;
    use super::super::types::RepairRunSummary;
    use super::*;

    fn empty_artifact() -> RepairArtifact {
        RepairArtifact {
            schema_version: "test",
            summary: RepairRunSummary {
                iterations: 0,
                succeeded: false,
                final_frontier: ProofFrontier { proved: 0, failed: 0, unknown: 0 },
                final_decision: "test".to_string(),
                total_duration_ms: 0,
                exact_source_type_ownership_artifact_digest: None,
            },
            iterations: Vec::new(),
            audit_trail: AuditTrail::new(),
        }
    }

    #[cfg(unix)]
    #[test]
    fn repair_artifact_writer_rejects_symlink_leaf_without_clobbering_target() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().expect("repair artifact fixture");
        let output = root.path().join("reports");
        std::fs::create_dir_all(&output).expect("create report directory");
        let victim = root.path().join("victim.json");
        std::fs::write(&victim, b"keep me").expect("write victim");
        symlink(&victim, output.join("repair.json")).expect("link report leaf");

        write_repair_artifact(&output, &empty_artifact())
            .expect_err("symlinked repair artifact must fail closed");
        assert_eq!(std::fs::read(&victim).expect("read victim"), b"keep me");
    }

    #[test]
    fn applied_rewrite_without_original_snapshot_never_fabricates_a_diff() {
        let rewrite = SourceRewrite {
            file_path: "/definitely/not/read.rs".to_string(),
            offset: 0,
            kind: trust_backprop::RewriteKind::InsertContractClause {
                clause: trust_backprop::ContractClauseKind::Requires,
                expression: "true".to_string(),
            },
            function_name: "f".to_string(),
            rationale: "fixture".to_string(),
            expected_source_hash: None,
            provenance: trust_backprop::ClaimProvenance::Authoritative,
        };

        let records = build_rewrite_records(&[rewrite], &[], &[]);
        assert_eq!(records.len(), 1);
        assert!(records[0].diff.is_none());
        assert!(
            records[0]
                .preview_error
                .as_deref()
                .is_some_and(|error| error.contains("original source snapshot is unavailable"))
        );
    }
}

pub(super) fn approval_policy_label(policy: ApprovalPolicy) -> &'static str {
    match policy {
        ApprovalPolicy::Auto => "auto",
        ApprovalPolicy::Review => "review",
        ApprovalPolicy::Block => "block",
        _ => "other",
    }
}

pub(super) fn pending_status_label(policy: ApprovalPolicy) -> &'static str {
    match policy {
        ApprovalPolicy::Auto => "pending_auto",
        ApprovalPolicy::Review => "pending_review",
        ApprovalPolicy::Block => "blocked",
        _ => "pending_other",
    }
}

pub(crate) fn decision_label(decision: &LoopDecision) -> String {
    match decision {
        LoopDecision::Continue { verdict } => format!("continue:{verdict}"),
        LoopDecision::Converged { stable_rounds } => format!("converged:{stable_rounds}"),
        LoopDecision::Regressed { reason } => format!("regressed:{reason}"),
        LoopDecision::IterationLimitReached => "iteration_limit".to_string(),
    }
}
