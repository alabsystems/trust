// targo trust report-query: focused inspection of saved verification reports
//
// This is intentionally read-only. It does not claim to restrict compiler work;
// it gives focused UX over reports that check/report already produced.

use std::collections::BTreeSet;
use std::path::Path;
use std::process::ExitCode;

use serde::Serialize;
use trust_types::{FunctionProofReport, JsonProofReport, ObligationOutcome, ObligationReport};

use crate::diff::load_report;
use crate::report::LiveCanonicalReport;
use crate::types::OutputFormat;

#[derive(Debug, Clone)]
struct ReportQueryArgs {
    format: ReportQueryFormat,
    report: String,
    function: Option<String>,
    require: QueryRequirement,
}

/// Output formats supported by `report-query`. Extends the shared
/// [`OutputFormat`] set with `repair`, the stable `trust.repair.v1`
/// machine-readable repair report consumed by AI repair agents
/// (see `trust_report::build_repair_report`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReportQueryFormat {
    Terminal,
    Json,
    Repair,
}

#[derive(Debug, Clone, Default, Serialize, PartialEq, Eq)]
struct QuerySummary {
    functions: usize,
    total_obligations: usize,
    proved: usize,
    runtime_checked: usize,
    failed: usize,
    unknown: usize,
    timed_out: usize,
    skipped: usize,
    unattributed_failed: usize,
    unattributed_unknown: usize,
    unattributed_proved: usize,
    total_time_ms: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QueryRequirement {
    FullyProved,
}

#[derive(Debug, Serialize)]
struct QuerySelector<'a> {
    #[serde(skip_serializing_if = "Option::is_none")]
    function: Option<&'a str>,
}

#[derive(Debug, Serialize)]
struct QueryJsonReport<'a> {
    report_path: &'a str,
    crate_name: &'a str,
    query: QuerySelector<'a>,
    matches: usize,
    summary: QuerySummary,
    focused_summary: QuerySummary,
    focused_exit_code: u8,
    functions: Vec<&'a FunctionProofReport>,
}

pub(crate) fn run_report_query_subcommand(args: &[String]) -> ExitCode {
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        print!("{}", report_query_usage_text());
        return ExitCode::SUCCESS;
    }

    let query_args = match parse_report_query_args(args) {
        Ok(args) => args,
        Err(error) => {
            eprintln!("targo trust report-query: {error}");
            eprintln!("Try `targo trust report-query --help`.");
            return ExitCode::from(2);
        }
    };

    ExitCode::from(run_query(query_args, "targo trust report-query"))
}

/// Query the canonical report while its opaque same-process publication
/// capability is still live. Saved `report.json` must continue through
/// [`run_query`]'s replay-authority rejection and can never call this entry.
pub(crate) fn run_live_focused_check_query(
    live_report: &LiveCanonicalReport,
    function: &str,
    format: OutputFormat,
) -> u8 {
    // Preserve the historical behavior: HTML falls back to terminal rendering.
    let format = match format {
        OutputFormat::Json => ReportQueryFormat::Json,
        OutputFormat::Terminal | OutputFormat::Html => ReportQueryFormat::Terminal,
    };
    let query_args = ReportQueryArgs {
        format,
        report: "<live sealed compiler report>".to_string(),
        function: Some(function.to_string()),
        require: QueryRequirement::FullyProved,
    };
    run_query_on_report(
        live_report.for_focused_query(),
        &query_args,
        "targo trust check --function",
    )
}

fn run_query(query_args: ReportQueryArgs, command_label: &str) -> u8 {
    let report_path = Path::new(&query_args.report);
    let loaded = match load_report(report_path) {
        Ok(report) => report,
        Err(error) => {
            eprintln!("{command_label}: {error}");
            return 2;
        }
    };
    if let Err(error) = loaded.reject_unreplayed_proved_claims(report_path) {
        eprintln!("{command_label}: {error}");
        return 2;
    }
    let report = loaded.report;
    run_query_on_report(&report, &query_args, command_label)
}

fn run_query_on_report(
    report: &JsonProofReport,
    query_args: &ReportQueryArgs,
    command_label: &str,
) -> u8 {
    if let Some(defect) = report_identity_defect(report) {
        eprintln!(
            "{command_label}: saved report has ambiguous identities: {}",
            crate::solver_detect::terminal_safe(&defect)
        );
        return 2;
    }

    let matches = select_functions(report, query_args.function.as_deref());
    if matches.is_empty() {
        let selector = query_args.function.as_deref().unwrap_or("<all>");
        eprintln!(
            "{command_label}: no functions matched `{}` in {}",
            crate::solver_detect::terminal_safe(selector),
            crate::solver_detect::terminal_safe(&query_args.report)
        );
        return 2;
    }

    let summary = summarize_functions(&matches);
    let focused_exit_code = query_requirement_exit_code(query_args.require, &summary);
    match query_args.format {
        ReportQueryFormat::Json => {
            let json_report = QueryJsonReport {
                report_path: &query_args.report,
                crate_name: &report.crate_name,
                query: QuerySelector { function: query_args.function.as_deref() },
                matches: matches.len(),
                summary: summary.clone(),
                focused_summary: summary.clone(),
                focused_exit_code,
                functions: matches,
            };
            match serde_json::to_string_pretty(&json_report) {
                Ok(json) => println!("{json}"),
                Err(error) => {
                    eprintln!("{command_label}: failed to serialize query: {error}");
                    return 2;
                }
            }
        }
        ReportQueryFormat::Repair => {
            let repair_report = repair_report_for_functions(report, &matches);
            match serde_json::to_string_pretty(&repair_report) {
                Ok(json) => println!("{json}"),
                Err(error) => {
                    eprintln!("{command_label}: failed to serialize repair report: {error}");
                    return 2;
                }
            }
        }
        ReportQueryFormat::Terminal => {
            render_terminal(&query_args.report, report, query_args.function.as_deref(), &matches);
        }
    }

    focused_exit_code
}

/// Build the stable `trust.repair.v1` repair report over the selected
/// functions. When a `--function` selector filtered the report, the repair
/// view is restricted to the matched functions so both formats answer the
/// same query; the builder itself never invents, drops, or reclassifies an
/// obligation relative to the canonical report.
fn repair_report_for_functions(
    report: &JsonProofReport,
    functions: &[&FunctionProofReport],
) -> trust_report::RepairReport {
    if functions.len() == report.functions.len() {
        return trust_report::build_repair_report(report);
    }
    let filtered = JsonProofReport {
        functions: functions.iter().map(|function| (*function).clone()).collect(),
        ..report.clone()
    };
    trust_report::build_repair_report(&filtered)
}

fn report_query_usage_text() -> String {
    [
        "targo trust report-query: focused inspection of saved verification reports",
        "",
        "Usage:",
        "  targo trust report-query --report <report.json> [--function <name>] [--format json]",
        "  targo trust report-query <report.json> [function]",
        "",
        "Options:",
        "  --report <path>       Saved JsonProofReport or legacy report JSON",
        "  --function <name>     Function selector; exact, ::suffix, or bare final segment",
        "  --require proved      Require at least one selected obligation and all selected obligations to be proved",
        "  --format <fmt>        Output format: terminal (default), json, or repair",
        "                        (repair = stable trust.repair.v1 machine-readable report",
        "                        of non-proved obligations for AI repair agents)",
        "  --json                Alias for --format json",
        "",
        "Exit codes:",
        "  0  Matching functions have at least one selected obligation and all selected obligations are proved",
        "  1  Matching functions have no selected obligations or still have failed, runtime-checked, or inconclusive obligations",
        "  2  Bad arguments, unreadable report, or no matching functions",
    ]
    .join("\n")
        + "\n"
}

fn parse_report_query_args(args: &[String]) -> Result<ReportQueryArgs, String> {
    let mut format = ReportQueryFormat::Terminal;
    let mut report = None;
    let mut function = None;
    let mut require = QueryRequirement::FullyProved;
    let mut positionals = Vec::new();
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "--json" => {
                format = ReportQueryFormat::Json;
            }
            "--format" => {
                i += 1;
                let value = args.get(i).ok_or("--format requires a value (terminal or json)")?;
                format = parse_output_format(value)?;
            }
            value if value.starts_with("--format=") => {
                let value = value.strip_prefix("--format=").expect("prefix checked");
                format = parse_output_format(value)?;
            }
            "--report" => {
                i += 1;
                let value = args.get(i).ok_or("--report requires a file path")?;
                report = Some(value.clone());
            }
            value if value.starts_with("--report=") => {
                let value = value.strip_prefix("--report=").expect("prefix checked");
                report = Some(value.to_string());
            }
            "--function" => {
                i += 1;
                let value = args.get(i).ok_or("--function requires a function name")?;
                function = Some(value.clone());
            }
            value if value.starts_with("--function=") => {
                let value = value.strip_prefix("--function=").expect("prefix checked");
                function = Some(value.to_string());
            }
            "--require" => {
                i += 1;
                let value = args.get(i).ok_or("--require requires a value (proved)")?;
                require = parse_query_requirement(value)?;
            }
            value if value.starts_with("--require=") => {
                let value = value.strip_prefix("--require=").expect("prefix checked");
                require = parse_query_requirement(value)?;
            }
            value if value.starts_with('-') => {
                return Err(format!("unknown option `{value}`"));
            }
            value => positionals.push(value.to_string()),
        }

        i += 1;
    }

    let mut consumed_positionals = 0;
    if report.is_none() {
        report = positionals.first().cloned();
        consumed_positionals = usize::from(report.is_some());
    }
    if function.is_none() {
        function = positionals.get(consumed_positionals).cloned();
        consumed_positionals += usize::from(function.is_some());
    }

    if let Some(unexpected) = positionals.get(consumed_positionals) {
        return Err(format!("unexpected positional argument `{unexpected}`"));
    }

    let report = report.ok_or("missing report path; pass --report <report.json>")?;

    Ok(ReportQueryArgs { format, report, function, require })
}

fn parse_output_format(value: &str) -> Result<ReportQueryFormat, String> {
    if value == "repair" {
        return Ok(ReportQueryFormat::Repair);
    }
    let format = OutputFormat::from_str(value).map_err(|error| error.to_string())?;
    match format {
        OutputFormat::Terminal => Ok(ReportQueryFormat::Terminal),
        OutputFormat::Json => Ok(ReportQueryFormat::Json),
        OutputFormat::Html => {
            Err("report-query supports terminal, json, or repair output, not html".to_string())
        }
    }
}

fn parse_query_requirement(value: &str) -> Result<QueryRequirement, String> {
    match value {
        "proved" => Ok(QueryRequirement::FullyProved),
        other => Err(format!("unsupported --require value `{other}`; expected `proved`")),
    }
}

fn select_functions<'a>(
    report: &'a JsonProofReport,
    function: Option<&str>,
) -> Vec<&'a FunctionProofReport> {
    let Some(function) = function.map(str::trim).filter(|function| !function.is_empty()) else {
        return report.functions.iter().collect();
    };

    report
        .functions
        .iter()
        .filter(|entry| function_selector_matches(&entry.function, function))
        .collect()
}

fn report_identity_defect(report: &JsonProofReport) -> Option<String> {
    let mut functions = BTreeSet::new();
    let mut obligations = BTreeSet::new();
    for function in &report.functions {
        if !functions.insert(function.function.as_str()) {
            return Some(format!("duplicate function `{}`", function.function));
        }
        for obligation in &function.obligations {
            if let Some(id) = obligation.obligation_id.as_deref() {
                if id.trim().is_empty() {
                    return Some(format!(
                        "function `{}` contains an empty obligation_id",
                        function.function
                    ));
                }
                if !obligations.insert(id) {
                    return Some(format!("duplicate obligation_id `{id}`"));
                }
            }
        }
    }
    None
}

fn function_selector_matches(candidate: &str, selector: &str) -> bool {
    if candidate == selector {
        return true;
    }

    if selector.contains("::") {
        return candidate.ends_with(selector);
    }

    candidate.rsplit("::").next().is_some_and(|name| name == selector)
}

fn summarize_functions(functions: &[&FunctionProofReport]) -> QuerySummary {
    functions.iter().fold(
        QuerySummary { functions: functions.len(), ..QuerySummary::default() },
        |mut summary, function| {
            summary.total_obligations =
                summary.total_obligations.saturating_add(function.summary.total_obligations);
            summary.proved = summary.proved.saturating_add(function.summary.proved);
            summary.runtime_checked =
                summary.runtime_checked.saturating_add(function.summary.runtime_checked);
            summary.failed = summary.failed.saturating_add(function.summary.failed);
            let inconclusive = obligation_inconclusive_counts(function);
            summary.unknown = summary.unknown.saturating_add(inconclusive.unknown);
            summary.timed_out = summary.timed_out.saturating_add(inconclusive.timed_out);
            summary.skipped = summary.skipped.saturating_add(inconclusive.skipped);
            summary.unattributed_failed =
                summary.unattributed_failed.saturating_add(function.summary.unattributed_failed);
            summary.unattributed_unknown =
                summary.unattributed_unknown.saturating_add(function.summary.unattributed_unknown);
            summary.unattributed_proved =
                summary.unattributed_proved.saturating_add(function.summary.unattributed_proved);
            summary.total_time_ms =
                summary.total_time_ms.saturating_add(function.summary.total_time_ms);
            summary
        },
    )
}

fn query_is_fully_proved(summary: &QuerySummary) -> bool {
    summary.total_obligations > 0
        && summary.proved == summary.total_obligations
        && summary.failed == 0
        && summary.unknown == 0
        && summary.timed_out == 0
        && summary.skipped == 0
        && summary.runtime_checked == 0
        && summary.unattributed_failed == 0
        && summary.unattributed_unknown == 0
        && summary.unattributed_proved == 0
}

fn query_result_label(summary: &QuerySummary) -> &'static str {
    if query_is_fully_proved(summary) {
        "PASS"
    } else if summary.total_obligations == 0 {
        "NO OBLIGATIONS"
    } else {
        "FAIL"
    }
}

fn query_requirement_passes(requirement: QueryRequirement, summary: &QuerySummary) -> bool {
    match requirement {
        QueryRequirement::FullyProved => query_is_fully_proved(summary),
    }
}

fn query_requirement_exit_code(requirement: QueryRequirement, summary: &QuerySummary) -> u8 {
    if query_requirement_passes(requirement, summary) { 0 } else { 1 }
}

fn render_terminal(
    report_path: &str,
    report: &JsonProofReport,
    function_query: Option<&str>,
    functions: &[&FunctionProofReport],
) {
    let summary = summarize_functions(functions);
    println!("Trust report query");
    println!("  report: {}", crate::solver_detect::terminal_safe(report_path));
    println!("  crate: {}", crate::solver_detect::terminal_safe(&report.crate_name));
    if let Some(function_query) = function_query {
        println!("  function: {}", crate::solver_detect::terminal_safe(function_query));
    }
    println!("  matches: {}", functions.len());
    println!(
        "  summary: {} proved, {} failed, {} runtime-checked, {} ({} obligations)",
        summary.proved,
        summary.failed,
        summary.runtime_checked,
        inconclusive_summary(summary.unknown, summary.timed_out, summary.skipped),
        summary.total_obligations
    );
    println!("  result: {}", query_result_label(&summary));
    if summary.unattributed_failed > 0
        || summary.unattributed_unknown > 0
        || summary.unattributed_proved > 0
    {
        println!(
            "  unattributed backend rows: {} proved, {} failed, {} inconclusive",
            summary.unattributed_proved, summary.unattributed_failed, summary.unattributed_unknown
        );
    }

    for function in functions {
        let inconclusive = obligation_inconclusive_counts(function);
        println!();
        println!(
            "{}: {:?}; {} proved / {} failed / {} runtime-checked / {} ({} obligations, {}ms)",
            crate::solver_detect::terminal_safe(&function.function),
            function.summary.verdict,
            function.summary.proved,
            function.summary.failed,
            function.summary.runtime_checked,
            inconclusive_summary(
                inconclusive.unknown,
                inconclusive.timed_out,
                inconclusive.skipped
            ),
            function.summary.total_obligations,
            function.summary.total_time_ms,
        );

        for obligation in &function.obligations {
            let location = obligation
                .location
                .as_ref()
                .map(|span| {
                    format!(
                        " {}:{}:{}",
                        crate::solver_detect::terminal_safe(&span.file),
                        span.line_start,
                        span.col_start
                    )
                })
                .unwrap_or_default();
            println!(
                "  [{}] {}: {} ({}, {}ms){}",
                obligation_status_label(obligation),
                crate::solver_detect::terminal_safe(&obligation.kind),
                crate::solver_detect::terminal_safe(&obligation.description),
                crate::solver_detect::terminal_safe(&obligation.solver),
                obligation.time_ms,
                location
            );
        }
    }
}

fn inconclusive_summary(unknown: usize, timed_out: usize, skipped: usize) -> String {
    let mut parts = vec![format!("{unknown} unknown")];
    if timed_out > 0 {
        parts.push(format!("{timed_out} {}", timeout_word(timed_out)));
    }
    if skipped > 0 {
        parts.push(format!("{skipped} {}", skipped_word(skipped)));
    }
    parts.join(", ")
}

fn timeout_word(count: usize) -> &'static str {
    if count == 1 { "timeout" } else { "timeouts" }
}

fn skipped_word(_count: usize) -> &'static str {
    "skipped"
}

fn obligation_status_label(obligation: &ObligationReport) -> &'static str {
    if is_skipped_obligation(obligation) {
        return "skipped";
    }

    match &obligation.outcome {
        ObligationOutcome::Proved { .. } => "proved",
        ObligationOutcome::Failed { .. } => "failed",
        ObligationOutcome::Unknown { .. } => "unknown",
        ObligationOutcome::Timeout { .. } => "timeout",
        ObligationOutcome::RuntimeChecked { .. } => "runtime_checked",
        _ => "unknown",
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct InconclusiveCounts {
    unknown: usize,
    timed_out: usize,
    skipped: usize,
}

fn obligation_inconclusive_counts(function: &FunctionProofReport) -> InconclusiveCounts {
    let mut explicit_counts = InconclusiveCounts::default();
    for obligation in &function.obligations {
        if is_skipped_obligation(obligation) {
            explicit_counts.skipped += 1;
            continue;
        }

        match &obligation.outcome {
            ObligationOutcome::Unknown { .. } => explicit_counts.unknown += 1,
            ObligationOutcome::Timeout { .. } => explicit_counts.timed_out += 1,
            _ => {}
        }
    }

    let timed_out = function.summary.timed_out.max(explicit_counts.timed_out);
    let skipped = explicit_counts.skipped;
    let mut counts = InconclusiveCounts {
        unknown: function.summary.unknown.saturating_sub(timed_out).saturating_sub(skipped),
        timed_out,
        skipped,
    };

    counts.unknown = counts.unknown.max(explicit_counts.unknown);
    counts
}

fn is_skipped_obligation(obligation: &ObligationReport) -> bool {
    let ObligationOutcome::Unknown { reason } = &obligation.outcome else {
        return false;
    };

    let kind = obligation.kind.to_ascii_lowercase();
    let reason = reason.to_ascii_lowercase();
    kind.contains("skipped")
        || kind == "memory_guard_resource_proof_gap"
        || reason.contains("skipped solver dispatch")
        || reason.contains("skipping solver dispatch")
        || reason.contains("memory guard skipped solver dispatch")
}

#[cfg(test)]
mod tests {
    use trust_types::{
        CrateSummary, CrateVerdict, FunctionSummary, FunctionVerdict, ObligationReport, ProofLevel,
        ReportMetadata, summarize_proof_grade_engine_statuses,
    };

    use super::*;

    fn function(
        name: &str,
        verdict: FunctionVerdict,
        proved: usize,
        failed: usize,
    ) -> FunctionProofReport {
        function_with_counts(name, verdict, proved + failed, proved, 0, failed, 0)
    }

    fn function_with_counts(
        name: &str,
        verdict: FunctionVerdict,
        total_obligations: usize,
        proved: usize,
        runtime_checked: usize,
        failed: usize,
        unknown: usize,
    ) -> FunctionProofReport {
        FunctionProofReport {
            function: name.to_string(),
            summary: FunctionSummary {
                total_obligations,
                proved,
                runtime_checked,
                failed,
                unknown,
                timed_out: 0,
                design_requirements: 0,
                unattributed_failed: 0,
                unattributed_unknown: 0,
                unattributed_proved: 0,
                total_time_ms: 7,
                max_proof_level: Some(ProofLevel::L0Safety),
                verdict,
            },
            obligations: Vec::<ObligationReport>::new(),
        }
    }

    fn obligation(kind: &str, description: &str, outcome: ObligationOutcome) -> ObligationReport {
        ObligationReport {
            obligation_id: None,
            description: description.to_string(),
            kind: kind.to_string(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome,
            solver: "ay".into(),
            time_ms: 7,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        }
    }

    fn report() -> JsonProofReport {
        JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "1.0".into(),
                trust_version: "test".into(),
                timestamp: String::new(),
                total_time_ms: 14,
                timeout_ms: None,
                function_budget_ms: None,
            },
            crate_name: "demo".into(),
            summary: CrateSummary {
                functions_analyzed: 3,
                functions_verified: 1,
                functions_runtime_checked: 0,
                functions_with_violations: 1,
                functions_inconclusive: 0,
                total_obligations: 2,
                total_proved: 1,
                total_runtime_checked: 0,
                total_failed: 1,
                total_unknown: 0,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                proof_grade_engine_statuses: summarize_proof_grade_engine_statuses(&[]),
                verdict: CrateVerdict::HasViolations,
            },
            functions: vec![
                function("crate::math::midpoint", FunctionVerdict::Verified, 1, 0),
                function("crate::math::divide", FunctionVerdict::HasViolations, 0, 1),
                function_with_counts(
                    "crate::math::noop",
                    FunctionVerdict::NoObligations,
                    0,
                    0,
                    0,
                    0,
                    0,
                ),
            ],
            hardened: None,
            assumptions: Vec::new(),
            cargo_proof_inventory: None,
            verification_gate: None,
        }
    }

    #[test]
    fn parse_report_query_accepts_report_and_function_flags() {
        let args = vec![
            "--report".to_string(),
            "target/trust/report.json".to_string(),
            "--function=crate::math::midpoint".to_string(),
            "--require".to_string(),
            "proved".to_string(),
            "--json".to_string(),
        ];

        let parsed = parse_report_query_args(&args).expect("report-query args should parse");

        assert_eq!(parsed.report, "target/trust/report.json");
        assert_eq!(parsed.function.as_deref(), Some("crate::math::midpoint"));
        assert_eq!(parsed.require, QueryRequirement::FullyProved);
        assert_eq!(parsed.format, ReportQueryFormat::Json);
    }

    #[test]
    fn parse_report_query_accepts_repair_format() {
        let parsed = parse_report_query_args(&[
            "--report".to_string(),
            "target/trust/report.json".to_string(),
            "--format".to_string(),
            "repair".to_string(),
        ])
        .expect("report-query args should parse");
        assert_eq!(parsed.format, ReportQueryFormat::Repair);

        let parsed = parse_report_query_args(&[
            "--report=target/trust/report.json".to_string(),
            "--format=repair".to_string(),
        ])
        .expect("report-query args should parse");
        assert_eq!(parsed.format, ReportQueryFormat::Repair);

        let error = parse_output_format("html").expect_err("html must stay rejected");
        assert!(error.contains("repair"), "error should advertise the repair format: {error}");
    }

    #[test]
    fn repair_format_restricts_to_selected_functions_without_reclassifying() {
        let mut report = report();
        report.functions[1].obligations = vec![
            obligation(
                "division_by_zero",
                "denominator may be zero",
                ObligationOutcome::Failed { counterexample: None },
            ),
            obligation(
                "postcondition",
                "quotient bound unproven",
                ObligationOutcome::Unknown { reason: "x * y nonlinear".into() },
            ),
            obligation(
                "hardened_boundary",
                "raw process call",
                ObligationOutcome::DesignRequirement { detail: "move off raw exec".into() },
            ),
        ];

        // Selected subset: only `divide`'s obligations may appear.
        let selected = select_functions(&report, Some("divide"));
        let repair = repair_report_for_functions(&report, &selected);
        assert_eq!(repair.schema_version, trust_report::REPAIR_SCHEMA_VERSION);
        assert_eq!(repair.obligations.len(), 3);
        assert!(repair.obligations.iter().all(|o| o.function == "crate::math::divide"));
        assert_eq!(repair.summary.failed, 1);
        assert_eq!(repair.summary.unknown, 1);
        assert_eq!(
            repair.summary.design_requirements, 1,
            "design requirement lands in its own bucket"
        );
        assert_eq!(repair.summary.timeout, 0);

        // Unfiltered: identical to building straight from the canonical report
        // (bucket identity of the CLI path vs the library builder).
        let all = select_functions(&report, None);
        let via_cli = repair_report_for_functions(&report, &all);
        let via_lib = trust_report::build_repair_report(&report);
        assert_eq!(
            serde_json::to_value(&via_cli).expect("serialize"),
            serde_json::to_value(&via_lib).expect("serialize"),
        );
    }

    #[test]
    fn parse_report_query_accepts_report_flag_with_positional_function() {
        let args = vec![
            "--report".to_string(),
            "target/trust/report.json".to_string(),
            "midpoint".to_string(),
        ];

        let parsed = parse_report_query_args(&args).expect("report-query args should parse");

        assert_eq!(parsed.report, "target/trust/report.json");
        assert_eq!(parsed.function.as_deref(), Some("midpoint"));
    }

    #[test]
    fn select_functions_accepts_exact_suffix_and_bare_name() {
        let report = report();

        assert_eq!(select_functions(&report, Some("crate::math::midpoint")).len(), 1);
        assert_eq!(select_functions(&report, Some("math::midpoint")).len(), 1);
        let selected = select_functions(&report, Some("midpoint"));
        assert_eq!(selected.len(), 1);
        assert_eq!(selected[0].function, "crate::math::midpoint");
    }

    #[test]
    fn focused_summary_fails_when_selected_function_has_violations() {
        let report = report();
        let selected = select_functions(&report, Some("divide"));
        let summary = summarize_functions(&selected);

        assert_eq!(
            summary,
            QuerySummary {
                functions: 1,
                total_obligations: 1,
                proved: 0,
                runtime_checked: 0,
                failed: 1,
                unknown: 0,
                timed_out: 0,
                skipped: 0,
                unattributed_failed: 0,
                unattributed_unknown: 0,
                unattributed_proved: 0,
                total_time_ms: 7,
            }
        );
        assert!(!query_is_fully_proved(&summary));
    }

    #[test]
    fn focused_summary_never_credits_unattributed_proof_rows() {
        let summary = QuerySummary {
            functions: 1,
            total_obligations: 1,
            proved: 1,
            unattributed_proved: 1,
            ..QuerySummary::default()
        };
        assert!(
            !query_is_fully_proved(&summary),
            "proof rows without a stable obligation identity cannot satisfy --require proved"
        );
    }

    #[test]
    fn report_query_rejects_duplicate_function_identities() {
        let mut report = report();
        report.functions.push(report.functions[0].clone());
        assert_eq!(
            report_identity_defect(&report).as_deref(),
            Some("duplicate function `crate::math::midpoint`")
        );
    }

    #[test]
    fn focused_summary_fails_when_selected_function_has_zero_obligations() {
        let report = report();
        let selected = select_functions(&report, Some("noop"));
        let summary = summarize_functions(&selected);

        assert_eq!(summary.functions, 1);
        assert_eq!(summary.total_obligations, 0);
        assert_eq!(query_result_label(&summary), "NO OBLIGATIONS");
        assert!(
            !query_is_fully_proved(&summary),
            "zero selected obligations must not satisfy --require proved"
        );
    }

    #[test]
    fn focused_summary_requires_all_selected_obligations_to_be_accounted_as_proved() {
        let inconsistent = function_with_counts(
            "crate::math::partial",
            FunctionVerdict::Inconclusive,
            2,
            1,
            0,
            0,
            0,
        );
        let summary = summarize_functions(&[&inconsistent]);

        assert_eq!(summary.total_obligations, 2);
        assert_eq!(summary.proved, 1);
        assert!(
            !query_is_fully_proved(&summary),
            "a missing obligation outcome must not satisfy --require proved"
        );
    }

    #[test]
    fn focused_summary_counts_runtime_checked_separately_from_unknowns() {
        let mut runtime = function_with_counts(
            "crate::math::runtime",
            FunctionVerdict::Inconclusive,
            2,
            0,
            1,
            0,
            1,
        );
        runtime.obligations = vec![
            obligation(
                "arithmetic_overflow_add",
                "overflow is checked dynamically",
                ObligationOutcome::RuntimeChecked { note: Some("overflow-checks enabled".into()) },
            ),
            obligation(
                "postcondition",
                "static proof remains incomplete",
                ObligationOutcome::Unknown { reason: "unknown".into() },
            ),
        ];

        let summary = summarize_functions(&[&runtime]);

        assert_eq!(summary.runtime_checked, 1);
        assert_eq!(summary.unknown, 1);
        assert_eq!(summary.timed_out, 0);
        assert_eq!(summary.skipped, 0);
        assert_eq!(obligation_status_label(&runtime.obligations[0]), "runtime_checked");
        assert!(
            !query_is_fully_proved(&summary),
            "runtime-checked obligations do not satisfy --require proved"
        );
    }

    #[test]
    fn focused_summary_distinguishes_solver_timeouts_from_unknowns() {
        let mut timed_out =
            function_with_counts("crate::math::slow", FunctionVerdict::Inconclusive, 2, 0, 0, 0, 2);
        timed_out.obligations = vec![
            ObligationReport {
                obligation_id: None,
                description: "solver timed out".to_string(),
                kind: "solver_timeout".to_string(),
                proof_level: ProofLevel::L0Safety,
                location: None,
                outcome: ObligationOutcome::Timeout { timeout_ms: 30_000 },
                solver: "ay".into(),
                time_ms: 30_000,
                evidence: None,
                proof_evidence: None,
                transport_evidence: None,
            },
            ObligationReport {
                obligation_id: None,
                description: "incomplete quantifier reasoning".to_string(),
                kind: "postcondition".to_string(),
                proof_level: ProofLevel::L0Safety,
                location: None,
                outcome: ObligationOutcome::Unknown { reason: "unknown".into() },
                solver: "ay".into(),
                time_ms: 3,
                evidence: None,
                proof_evidence: None,
                transport_evidence: None,
            },
        ];

        let summary = summarize_functions(&[&timed_out]);

        assert_eq!(summary.unknown, 1);
        assert_eq!(summary.timed_out, 1);
        assert_eq!(summary.skipped, 0);
        assert_eq!(obligation_status_label(&timed_out.obligations[0]), "timeout");
        assert!(
            !query_is_fully_proved(&summary),
            "timeouts remain release-blocking even when separated from unknowns"
        );
    }

    #[test]
    fn focused_summary_distinguishes_skipped_from_unknowns_and_timeouts() {
        let mut skipped = function_with_counts(
            "crate::math::resource_limited",
            FunctionVerdict::Inconclusive,
            3,
            0,
            0,
            0,
            3,
        );
        skipped.summary.timed_out = 1;
        skipped.obligations = vec![
            obligation(
                "solver_timeout",
                "solver timed out before proving bound",
                ObligationOutcome::Timeout { timeout_ms: 30_000 },
            ),
            obligation(
                "memory_guard_resource_proof_gap",
                "solver dispatch was skipped",
                ObligationOutcome::Unknown {
                    reason: "release-blocking proof gap: memory guard skipped solver dispatch"
                        .into(),
                },
            ),
            obligation(
                "postcondition",
                "incomplete quantifier reasoning",
                ObligationOutcome::Unknown { reason: "unknown".into() },
            ),
        ];

        let summary = summarize_functions(&[&skipped]);

        assert_eq!(summary.unknown, 1);
        assert_eq!(summary.timed_out, 1);
        assert_eq!(summary.skipped, 1);
        assert_eq!(obligation_status_label(&skipped.obligations[1]), "skipped");
        assert_eq!(
            inconclusive_summary(summary.unknown, summary.timed_out, summary.skipped),
            "1 unknown, 1 timeout, 1 skipped"
        );
        assert!(
            !query_is_fully_proved(&summary),
            "skipped obligations remain release-blocking and are not plain unknowns"
        );
    }

    #[test]
    fn focused_summary_preserves_legacy_unknown_summary_without_obligation_rows() {
        let legacy = function_with_counts(
            "crate::math::legacy",
            FunctionVerdict::Inconclusive,
            1,
            0,
            0,
            0,
            1,
        );
        let summary = summarize_functions(&[&legacy]);

        assert_eq!(summary.unknown, 1);
        assert_eq!(summary.timed_out, 0);
        assert_eq!(summary.skipped, 0);
    }

    #[test]
    fn focused_summary_uses_summary_timeout_when_rows_are_absent() {
        let mut summary_only = function_with_counts(
            "crate::math::summary_only",
            FunctionVerdict::Inconclusive,
            2,
            0,
            0,
            0,
            2,
        );
        summary_only.summary.timed_out = 1;

        let summary = summarize_functions(&[&summary_only]);

        assert_eq!(summary.unknown, 1);
        assert_eq!(summary.timed_out, 1);
        assert_eq!(summary.skipped, 0);
    }

    #[test]
    fn focused_summary_reconciles_summary_timeout_when_rows_are_partial() {
        let mut partial = function_with_counts(
            "crate::math::partial",
            FunctionVerdict::Inconclusive,
            3,
            0,
            0,
            0,
            3,
        );
        partial.summary.timed_out = 2;
        partial.obligations = vec![
            ObligationReport {
                obligation_id: None,
                description: "solver timed out".to_string(),
                kind: "solver_timeout".to_string(),
                proof_level: ProofLevel::L0Safety,
                location: None,
                outcome: ObligationOutcome::Timeout { timeout_ms: 30_000 },
                solver: "ay".into(),
                time_ms: 30_000,
                evidence: None,
                proof_evidence: None,
                transport_evidence: None,
            },
            ObligationReport {
                obligation_id: None,
                description: "incomplete quantifier reasoning".to_string(),
                kind: "postcondition".to_string(),
                proof_level: ProofLevel::L0Safety,
                location: None,
                outcome: ObligationOutcome::Unknown { reason: "unknown".into() },
                solver: "ay".into(),
                time_ms: 3,
                evidence: None,
                proof_evidence: None,
                transport_evidence: None,
            },
        ];

        let summary = summarize_functions(&[&partial]);

        assert_eq!(summary.unknown, 1);
        assert_eq!(summary.timed_out, 2);
        assert_eq!(summary.skipped, 0);
    }
}
