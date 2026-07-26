// Terminal display for the rewrite loop: iteration headers, summaries, and
// AI-targeted repair prompts.

use trust_backprop::{RepairPromptContext, print_ai_repair_prompt};
use trust_strengthen::read_function;

use super::backprop_gate::is_binary_only_path;
use super::convergence::{ConvergenceTracker, LoopDecision, ProofFrontier};
use super::proposal::{extract_function_name, failure_pattern_label, to_failure_analysis};
use super::types::RewriteProposal;
use crate::types::{VerificationOutcome, VerificationResult};

/// Print iteration progress to the terminal.
pub(crate) fn print_iteration_header(iteration: usize, max: usize) {
    eprintln!();
    eprintln!("=== Trust Rewrite Loop: Iteration {}/{} ===", iteration + 1, max);
}

/// Print iteration summary after verification.
pub(crate) fn print_iteration_summary(
    frontier: &ProofFrontier,
    proposals: &[RewriteProposal],
    decision: &LoopDecision,
    elapsed: &std::time::Duration,
) {
    eprintln!();
    eprintln!(
        "  Frontier: {} proved, {} failed, {} unknown ({} total)",
        frontier.proved,
        frontier.failed,
        frontier.unknown,
        frontier.total()
    );

    if !proposals.is_empty() {
        eprintln!("  Proposals: {} rewrites suggested", proposals.len());
        for (i, p) in proposals.iter().enumerate().take(5) {
            eprintln!("    {}: [{}] {}", i + 1, p.kind, p.description);
        }
        if proposals.len() > 5 {
            eprintln!("    ... and {} more", proposals.len() - 5);
        }
    }

    let decision_str = match decision {
        LoopDecision::Continue { verdict } => format!("CONTINUE ({verdict})"),
        LoopDecision::Converged { stable_rounds } => {
            format!("CONVERGED (stable for {stable_rounds} rounds)")
        }
        LoopDecision::Regressed { reason } => format!("REGRESSED ({reason})"),
        LoopDecision::IterationLimitReached => "ITERATION LIMIT REACHED".to_string(),
    };
    eprintln!("  Decision: {decision_str}");
    eprintln!("  Elapsed: {}ms", elapsed.as_millis());
}

/// Emit AI repair prompts for every failure or inconclusive result.
///
/// For each `Failed` or `Unknown` verification result the loop produces, prints
/// an AI-targeted prompt (via `trust_backprop::ai_prompt`) asking the assistant
/// to add the strongest native `requires` / `ensures` signature clauses to the failing
/// function, along with a ready-to-run `claude --dangerously-skip-permissions`
/// invocation. Returns the number of prompts printed.
///
/// This is the "backprop" side-channel: even when the AST-rewriting backprop
/// engine cannot autonomously discharge an obligation, the operator gets a
/// concrete, copy-pasteable AI prompt that targets exactly the failing function.
pub(crate) fn print_ai_repair_prompts_for_results(
    results: &[VerificationResult],
    default_source_file: Option<&str>,
    intent: Option<&str>,
) -> usize {
    let mut printed = 0;
    for result in results
        .iter()
        .filter(|r| matches!(r.outcome, VerificationOutcome::Failed | VerificationOutcome::Unknown))
    {
        let function = if result.function.is_empty() {
            extract_function_name(&result.raw_line)
        } else {
            result.function.clone()
        };
        let function_short = function.rsplit("::").next().unwrap_or(&function).to_string();

        let source_file = result
            .location
            .as_ref()
            .map(|s| s.file.as_str())
            .filter(|p| !p.is_empty() && !is_binary_only_path(p))
            .map(str::to_string)
            .or_else(|| default_source_file.map(str::to_string));

        let source_ctx =
            source_file.as_deref().and_then(|file| read_function(file, &function_short));

        let pattern = failure_pattern_label(&to_failure_analysis(result).pattern);
        let outcome_label = match result.outcome {
            VerificationOutcome::Failed => "FAILED",
            VerificationOutcome::Unknown => "UNKNOWN",
            _ => "UNCHECKED",
        };

        let params: Vec<(String, String)> =
            source_ctx.as_ref().map(|ctx| ctx.params.clone()).unwrap_or_default();
        let signature = source_ctx.as_ref().map(|ctx| ctx.signature.clone());
        let return_type = source_ctx.as_ref().and_then(|ctx| ctx.return_type.clone());

        let ctx = RepairPromptContext {
            function: &function,
            source_file: source_file.as_deref(),
            signature: signature.as_deref(),
            params: &params,
            return_type: return_type.as_deref(),
            vc_kind: &result.kind,
            pattern,
            solver: if result.backend.is_empty() { "verifier" } else { &result.backend },
            outcome: outcome_label,
            solver_reason: result.reason.as_deref(),
            counterexample: result.counterexample.as_ref(),
            location: result.location.as_ref(),
            intent,
        };

        print_ai_repair_prompt(&ctx);
        printed += 1;
    }
    printed
}

/// Print final loop summary.
pub(crate) fn print_loop_summary(
    tracker: &ConvergenceTracker,
    final_frontier: &ProofFrontier,
    total_elapsed: &std::time::Duration,
    final_decision: &LoopDecision,
) {
    eprintln!();
    eprintln!("=== Trust Rewrite Loop Summary ===");
    eprintln!("  Iterations: {}", tracker.iteration_count());
    eprintln!(
        "  Final frontier: {} proved, {} failed, {} unknown",
        final_frontier.proved, final_frontier.failed, final_frontier.unknown
    );

    let score = if final_frontier.total() > 0 {
        final_frontier.proved as f64 / final_frontier.total() as f64
    } else {
        0.0
    };
    eprintln!("  Convergence score: {:.1}%", score * 100.0);

    let outcome = match final_decision {
        LoopDecision::Converged { .. } => "CONVERGED",
        LoopDecision::IterationLimitReached => "ITERATION LIMIT",
        LoopDecision::Regressed { .. } => "REGRESSED",
        LoopDecision::Continue { .. } => "IN PROGRESS",
    };
    eprintln!("  Outcome: {outcome}");
    eprintln!("  Total time: {}ms", total_elapsed.as_millis());
    eprintln!("==================================");
}
