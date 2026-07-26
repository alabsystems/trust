//! AI repair-prompt generation for the prove-strengthen-backprop loop.
//!
//! When a verification obligation fails (`Failed`) or comes back inconclusive
//! (`Unknown`, e.g. trust_wp reports `UNKNOWN` or trust-mc/trust-vc give up), the loop
//! emits an explicit prompt that an AI assistant can act on: propose native
//! `requires` and `ensures` signature clauses that truthfully address the
//! failed VC. The prompt is paired with a ready-to-run
//! `claude --dangerously-skip-permissions` invocation so the operator can pipe
//! it straight in without further confirmation prompts.
//!
//! This module is pure formatting — no I/O beyond writing to `stderr` in the
//! convenience printers. Callers (`targo-trust/src/rewrite_loop.rs`) gather
//! the failure context and invoke [`build_ai_repair_prompt`] /
//! [`print_ai_repair_prompt`].
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt::Write as _;

use trust_types::{Counterexample, SourceSpan};

/// CLI command emitted to drive the AI assistant on the rendered prompt.
pub const AI_REPAIR_CLI: &str = "claude --dangerously-skip-permissions";

/// Context required to render an AI repair prompt for one failed obligation.
#[derive(Debug, Clone)]
pub struct RepairPromptContext<'a> {
    /// Fully-qualified function path, e.g. `crate::math::div`.
    pub function: &'a str,
    /// Source file containing the function, if known.
    pub source_file: Option<&'a str>,
    /// Function signature line, e.g. `fn div(a: u32, b: u32) -> u32`.
    pub signature: Option<&'a str>,
    /// Parameter list `(name, type)` so the prompt can name them precisely.
    pub params: &'a [(String, String)],
    /// Return type (used to hint that `result` may appear in `ensures`).
    pub return_type: Option<&'a str>,
    /// Verification-condition kind, e.g. `arithmetic_overflow`, `div_by_zero`.
    pub vc_kind: &'a str,
    /// Classified failure pattern label.
    pub pattern: &'a str,
    /// Solver that produced the result: `trust-wp`, `trust-mc`, `trust-vc`, ...
    pub solver: &'a str,
    /// Outcome label, typically `UNKNOWN` or `FAILED`.
    pub outcome: &'a str,
    /// Optional solver-supplied reason text.
    pub solver_reason: Option<&'a str>,
    /// Optional structured counterexample (assignment list).
    pub counterexample: Option<&'a Counterexample>,
    /// Optional source span (file + line/column).
    pub location: Option<&'a SourceSpan>,
    /// Optional author intent (a design-doc excerpt or chat conversation) that
    /// guides *what to aim for*. On the authority ladder this sits below a
    /// formal contract but above code-abduced guesses; it never enters the TCB
    /// — the proof still decides whether the repair discharges the obligation.
    pub intent: Option<&'a str>,
}

/// Render the natural-language prompt body for one failure.
///
/// The prompt asks the AI assistant for first-class native signature clauses,
/// with no compatibility attributes or helper surface.
#[must_use]
pub fn build_ai_repair_prompt(ctx: &RepairPromptContext<'_>) -> String {
    let mut s = String::new();

    let _ =
        writeln!(s, "The Trust verifier could not discharge an obligation in `{}`.", ctx.function);

    match (ctx.source_file, ctx.location) {
        (Some(file), Some(loc)) => {
            let _ = writeln!(s, "Location: {}:{}:{}", file, loc.line_start, loc.col_start);
        }
        (Some(file), None) => {
            let _ = writeln!(s, "Location: {file}");
        }
        (None, Some(loc)) if !loc.file.is_empty() => {
            let _ = writeln!(s, "Location: {}:{}:{}", loc.file, loc.line_start, loc.col_start);
        }
        _ => {}
    }

    let _ = writeln!(s, "Solver: {} returned {}.", ctx.solver, ctx.outcome);
    let _ = writeln!(s, "Failed VC: {} (pattern: {}).", ctx.vc_kind, ctx.pattern);

    if let Some(reason) = ctx.solver_reason.filter(|r| !r.trim().is_empty()) {
        let _ = writeln!(s, "Solver reason: {reason}");
    }

    if let Some(sig) = ctx.signature.filter(|s| !s.trim().is_empty()) {
        let _ = writeln!(s, "Signature: {sig}");
    }

    if !ctx.params.is_empty() {
        let params: Vec<String> = ctx.params.iter().map(|(n, t)| format!("{n}: {t}")).collect();
        let _ = writeln!(s, "Parameters: {}", params.join(", "));
    }

    if let Some(ret) = ctx.return_type.filter(|r| !r.trim().is_empty()) {
        let _ = writeln!(s, "Return type: {ret}");
    }

    if let Some(cex) = ctx.counterexample.filter(|c| !c.assignments.is_empty()) {
        s.push_str("Counterexample:\n");
        for (name, val) in &cex.assignments {
            let _ = writeln!(s, "  {name} = {val}");
        }
    }

    let intent = ctx.intent.map(str::trim).filter(|i| !i.is_empty());
    if let Some(intent) = intent {
        s.push('\n');
        s.push_str(
            "Author intent (authority: design-doc/chat — below a formal contract, \
            above any code-abduced guess; guidance only, never trusted as proof):\n",
        );
        for line in intent.lines() {
            let _ = writeln!(s, "  {line}");
        }
    }

    s.push('\n');
    s.push_str(
        "Task: propose precise first-class `requires P` and `ensures Q` \
        signature clauses for `",
    );
    s.push_str(ctx.function);
    s.push_str("` so the failed verification condition above is discharged.\n");
    if intent.is_some() {
        s.push_str(
            "Align the spec with the author's stated intent above: choose the \
            predicates that capture what the author meant. Never contradict an \
            explicitly stated contract. The proof, not the intent, decides \
            whether the obligation is discharged.\n",
        );
    }
    s.push_str(
        "Constraints:\n\
        - Edit ONLY native signature clauses on the failing function. Place \
        them after the return type and before `where` or the body `{`. Do not touch \
        the function body, callers, tests, imports, or any other file.\n\
        - No comments, no docstrings, no helper functions, no other \
        boilerplate. Each clause is one precise, unquoted predicate.\n\
        - Never emit attributes, quoted attribute payloads, imports, shim-crate \
        paths, or `old(...)`. Parameter names denote entry values; use `result`, \
        `out`, or primed outputs for post-state. Use Lean-shaped quantifiers such \
        as `forall i: usize, P`, never closure binders.\n\
        - Reference parameters by the names listed above; use `result` inside \
        `ensures` to refer to the return value.\n\
        - Use total mathematical expressions over those names. Do not call \
        other functions inside the spec.\n\
        - A proposed `requires` is an assumption, not a proof. Use the weakest \
        precondition justified by the intended caller domain; never exclude a \
        real caller merely to silence the VC. Use the strongest postcondition \
        actually established by the body. Every proposal remains review-gated.\n\
        - Output the edited function with only the new clauses added. No \
        explanation text.\n",
    );

    s
}

/// Wrap a prompt body into a ready-to-run `claude` invocation.
///
/// The emitted command uses `--dangerously-skip-permissions` so the assistant
/// can act on the rewrite without per-tool confirmation, matching the
/// autonomous repair loop's contract.
#[must_use]
pub fn build_ai_repair_command(prompt_body: &str) -> String {
    let mut s = String::new();
    s.push_str(AI_REPAIR_CLI);
    s.push_str(" <<'TRUST_AI_PROMPT_EOF'\n");
    s.push_str(prompt_body);
    if !prompt_body.ends_with('\n') {
        s.push('\n');
    }
    s.push_str("TRUST_AI_PROMPT_EOF\n");
    s
}

/// Print one prompt and its companion command to stderr.
pub fn print_ai_repair_prompt(ctx: &RepairPromptContext<'_>) {
    let body = build_ai_repair_prompt(ctx);
    let cmd = build_ai_repair_command(&body);
    eprintln!();
    eprintln!("--- Trust AI repair prompt for `{}` ---", ctx.function);
    eprint!("{body}");
    eprintln!("--- run with: ---");
    eprint!("{cmd}");
    eprintln!("--- end Trust AI repair prompt ---");
}

/// Print prompts for every context in `contexts` to stderr in order.
pub fn print_ai_repair_prompts(contexts: &[RepairPromptContext<'_>]) {
    for ctx in contexts {
        print_ai_repair_prompt(ctx);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{Counterexample, CounterexampleValue, SourceSpan};

    fn span(file: &str, line: u32, col: u32) -> SourceSpan {
        SourceSpan {
            file: file.to_string(),
            line_start: line,
            col_start: col,
            line_end: line,
            col_end: col,
        }
    }

    #[test]
    fn prompt_names_function_and_solver_outcome() {
        let ctx = RepairPromptContext {
            function: "math::div",
            source_file: Some("src/math.rs"),
            signature: Some("fn div(a: u32, b: u32) -> u32"),
            params: &[("a".to_string(), "u32".to_string()), ("b".to_string(), "u32".to_string())],
            return_type: Some("u32"),
            vc_kind: "div_by_zero",
            pattern: "division_by_zero",
            solver: "trust-wp",
            outcome: "UNKNOWN",
            solver_reason: Some("could not discharge: b may be 0"),
            counterexample: None,
            location: Some(&span("src/math.rs", 12, 5)),
            intent: None,
        };

        let body = build_ai_repair_prompt(&ctx);

        assert!(body.contains("`math::div`"));
        assert!(body.contains("trust-wp returned UNKNOWN"));
        assert!(body.contains("div_by_zero"));
        assert!(body.contains("division_by_zero"));
        assert!(body.contains("src/math.rs:12:5"));
        assert!(body.contains("Parameters: a: u32, b: u32"));
        assert!(body.contains("Return type: u32"));
        assert!(body.contains("`requires P`"));
        assert!(body.contains("`ensures Q`"));
        assert!(body.contains("weakest"));
        assert!(body.contains("Never emit attributes"));
        assert!(body.contains("No comments"));
    }

    #[test]
    fn command_uses_dangerously_skip_permissions() {
        let cmd = build_ai_repair_command("hello\n");
        assert!(cmd.starts_with("claude --dangerously-skip-permissions"));
        assert!(cmd.contains("<<'TRUST_AI_PROMPT_EOF'"));
        assert!(cmd.contains("\nhello\n"));
        assert!(cmd.trim_end().ends_with("TRUST_AI_PROMPT_EOF"));
    }

    #[test]
    fn command_appends_trailing_newline_when_missing() {
        let cmd = build_ai_repair_command("hello");
        assert!(cmd.contains("hello\nTRUST_AI_PROMPT_EOF"));
    }

    #[test]
    fn prompt_renders_counterexample_assignments() {
        let cex = Counterexample::new(vec![
            ("a".to_string(), CounterexampleValue::Uint(5)),
            ("b".to_string(), CounterexampleValue::Uint(0)),
        ]);
        let ctx = RepairPromptContext {
            function: "math::div",
            source_file: None,
            signature: None,
            params: &[],
            return_type: None,
            vc_kind: "div_by_zero",
            pattern: "division_by_zero",
            solver: "trust-mc",
            outcome: "FAILED",
            solver_reason: None,
            counterexample: Some(&cex),
            location: None,
            intent: None,
        };

        let body = build_ai_repair_prompt(&ctx);
        assert!(body.contains("Counterexample:"));
        assert!(body.contains("a = 5"));
        assert!(body.contains("b = 0"));
    }

    #[test]
    fn prompt_includes_author_intent_when_present() {
        let ctx = RepairPromptContext {
            function: "checkout::total",
            source_file: Some("src/checkout.rs"),
            signature: Some("fn total(items: &[Item]) -> u64"),
            params: &[("items".to_string(), "&[Item]".to_string())],
            return_type: Some("u64"),
            vc_kind: "arithmetic_overflow",
            pattern: "addition_overflow",
            solver: "trust-wp",
            outcome: "UNKNOWN",
            solver_reason: None,
            counterexample: None,
            location: None,
            intent: Some(
                "Totals must saturate, never wrap: an overpriced cart\nis clamped to u64::MAX, not silently overflowed.",
            ),
        };

        let body = build_ai_repair_prompt(&ctx);
        assert!(body.contains("Author intent"));
        assert!(body.contains("Totals must saturate"));
        assert!(body.contains("clamped to u64::MAX"));
        assert!(body.contains("Align the spec with the author's stated intent"));
        assert!(body.contains("The proof, not the intent, decides"));
    }

    #[test]
    fn prompt_omits_intent_section_when_absent_or_blank() {
        let ctx = RepairPromptContext {
            function: "checkout::total",
            source_file: None,
            signature: None,
            params: &[],
            return_type: None,
            vc_kind: "arithmetic_overflow",
            pattern: "addition_overflow",
            solver: "trust-wp",
            outcome: "UNKNOWN",
            solver_reason: None,
            counterexample: None,
            location: None,
            intent: Some("   \n  "),
        };

        let body = build_ai_repair_prompt(&ctx);
        assert!(!body.contains("Author intent"));
        assert!(!body.contains("Align the spec with the author's stated intent"));
    }
}
