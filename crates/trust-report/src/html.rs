// trust-report/html.rs: Interactive HTML proof report dashboard
//
// Renders a JsonProofReport as a complete, self-contained interactive HTML
// dashboard with inline CSS and JavaScript. Features:
// - Collapsible function sections (HTML <details> elements + JS enhancement)
// - Color-coded status indicators (green/red/yellow/blue)
// - Summary statistics with progress bars
// - Filter controls to show/hide by obligation status
// - Embedded proof evidence (solver output, counterexamples)
//
// No external dependencies — all CSS and JS are inline.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt::Write;
use std::path::Path;

use trust_types::{
    CrateVerdict, FunctionVerdict, JsonProofReport, ObligationOutcome, ObligationReport,
    VerificationCondition, VerificationResult,
};

use crate::{
    build_json_report, function_verdict_label, monitor_executability_label,
    proof_evidence_label_with_monitor, proof_level_label,
};

/// Build a complete HTML proof report from raw verification results.
///
/// This is the primary entry point for HTML report generation. It takes a crate
/// name and raw `(VerificationCondition, VerificationResult)` pairs, builds the
/// canonical JSON report internally, and renders it as a self-contained HTML page.
///
/// The HTML includes:
/// - Summary header: total VCs, proved count, failed count, unknown count
/// - Per-function table with color-coded status (green=proved, red=failed, yellow=unknown)
/// - Counterexample display for failed VCs (variable assignments)
/// - Proof strength indicators
/// - Interactive filter bar and collapsible sections
#[must_use]
pub fn build_html_report(
    name: &str,
    results: &[(VerificationCondition, VerificationResult)],
) -> String {
    let json_report = build_json_report(name, results);
    format_html_report(&json_report)
}

/// Write an HTML proof report to a file in the output directory.
///
/// Creates `report.html` in the given directory, building the report from raw
/// verification results. The directory is created if it does not exist.
pub fn write_html_report(
    name: &str,
    results: &[(VerificationCondition, VerificationResult)],
    output_dir: &Path,
) -> std::io::Result<()> {
    std::fs::create_dir_all(output_dir)?;
    let html = build_html_report(name, results);
    std::fs::write(output_dir.join("report.html"), html)?;
    Ok(())
}

/// Format a `JsonProofReport` as a complete, self-contained interactive HTML page.
///
/// The output includes:
/// - A header with crate name, Trust version, and timestamp
/// - Summary statistics with progress bars (proved/runtime-checked/failed/pending)
/// - Filter bar to show/hide functions by verdict status
/// - Per-function collapsible sections with obligation detail tables
/// - Color coding: green=proved, blue=runtime-checked, red=failed, yellow=pending
/// - Counterexample display for failed obligations
/// - Footer with solver and version info
///
/// The HTML uses inline CSS (dark theme) and inline JavaScript for interactivity.
/// It degrades gracefully with JS disabled (sections are expanded by default).
pub fn format_html_report(report: &JsonProofReport) -> String {
    let mut html = String::with_capacity(8192);

    html.push_str(&html_head(&report.crate_name));
    html.push_str("<body>\n");
    html.push_str(&html_header(report));
    html.push_str(&html_summary(report));
    html.push_str(&html_filters(report));
    html.push_str(&html_functions(report));
    html.push_str(&html_footer(report));
    html.push_str(&html_script());
    html.push_str("</body>\n</html>\n");

    html
}

/// Emit the `<!DOCTYPE>`, `<html>`, `<head>`, and inline `<style>` block.
fn html_head(crate_name: &str) -> String {
    format!(
        r#"<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Trust Proof Report: {crate_name}</title>
<style>
:root {{
  --bg: #1a1b26;
  --surface: #24283b;
  --surface2: #2f3349;
  --text: #c0caf5;
  --text-dim: #565f89;
  --green: #9ece6a;
  --red: #f7768e;
  --yellow: #e0af68;
  --blue: #7aa2f7;
  --border: #3b4261;
}}
* {{ margin: 0; padding: 0; box-sizing: border-box; }}
body {{
  font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial, monospace;
  background: var(--bg);
  color: var(--text);
  line-height: 1.6;
  padding: 2rem;
  max-width: 960px;
  margin: 0 auto;
}}
h1 {{ font-size: 1.5rem; margin-bottom: 0.25rem; }}
h2 {{ font-size: 1.15rem; margin: 1.5rem 0 0.5rem; }}
.header {{ margin-bottom: 1.5rem; border-bottom: 1px solid var(--border); padding-bottom: 1rem; }}
.header .meta {{ color: var(--text-dim); font-size: 0.85rem; }}
.summary {{ background: var(--surface); border-radius: 8px; padding: 1rem 1.25rem; margin-bottom: 1.5rem; }}
.summary-grid {{ display: flex; gap: 1.5rem; flex-wrap: wrap; }}
.stat {{ text-align: center; min-width: 80px; }}
.stat .value {{ font-size: 1.75rem; font-weight: bold; }}
.stat .label {{ font-size: 0.75rem; color: var(--text-dim); text-transform: uppercase; letter-spacing: 0.05em; }}
.progress-bar {{ width: 100%; height: 8px; background: var(--surface2); border-radius: 4px; margin-top: 0.75rem; overflow: hidden; display: flex; }}
.progress-bar .segment {{ height: 100%; transition: width 0.3s ease; }}
.progress-bar .seg-proved {{ background: var(--green); }}
.progress-bar .seg-runtime {{ background: var(--blue); }}
.progress-bar .seg-failed {{ background: var(--red); }}
.progress-bar .seg-unknown {{ background: var(--yellow); }}
.progress-bar .seg-timeout {{ background: var(--yellow); opacity: 0.7; }}
.verdict {{ display: inline-block; padding: 0.2rem 0.6rem; border-radius: 4px; font-weight: bold; font-size: 0.85rem; text-transform: uppercase; }}
.verdict-verified {{ background: rgba(158,206,106,0.15); color: var(--green); }}
.verdict-runtime-checked {{ background: rgba(122,162,247,0.15); color: var(--blue); }}
.verdict-violations {{ background: rgba(247,118,142,0.15); color: var(--red); }}
.verdict-inconclusive {{ background: rgba(224,175,104,0.15); color: var(--yellow); }}
.verdict-none {{ background: rgba(86,95,137,0.15); color: var(--text-dim); }}
.filter-bar {{ background: var(--surface); border-radius: 8px; padding: 0.75rem 1.25rem; margin-bottom: 1.5rem; display: flex; gap: 0.75rem; flex-wrap: wrap; align-items: center; }}
.filter-bar .filter-label {{ color: var(--text-dim); font-size: 0.8rem; font-weight: 600; text-transform: uppercase; letter-spacing: 0.05em; }}
.filter-btn {{ background: var(--surface2); border: 1px solid var(--border); color: var(--text); padding: 0.3rem 0.75rem; border-radius: 4px; font-size: 0.8rem; cursor: pointer; transition: all 0.15s ease; }}
.filter-btn:hover {{ border-color: var(--text-dim); }}
.filter-btn.active {{ border-color: var(--text); font-weight: bold; }}
.filter-btn.active[data-filter="verified"] {{ border-color: var(--green); color: var(--green); }}
.filter-btn.active[data-filter="runtime-checked"] {{ border-color: var(--blue); color: var(--blue); }}
.filter-btn.active[data-filter="violations"] {{ border-color: var(--red); color: var(--red); }}
.filter-btn.active[data-filter="inconclusive"] {{ border-color: var(--yellow); color: var(--yellow); }}
.expand-controls {{ margin-left: auto; display: flex; gap: 0.5rem; }}
.func-section {{ background: var(--surface); border-radius: 8px; margin-bottom: 1rem; }}
.func-section[hidden] {{ display: none; }}
details.func-details {{ }}
details.func-details summary {{ cursor: pointer; list-style: none; padding: 1rem 1.25rem; }}
details.func-details summary::-webkit-details-marker {{ display: none; }}
details.func-details summary::marker {{ display: none; }}
.func-header {{ display: flex; align-items: center; justify-content: space-between; flex-wrap: wrap; gap: 0.5rem; }}
.func-name {{ font-family: monospace; font-weight: bold; font-size: 1rem; }}
.func-toggle {{ color: var(--text-dim); font-size: 0.85rem; margin-right: 0.5rem; transition: transform 0.2s ease; display: inline-block; }}
details.func-details[open] .func-toggle {{ transform: rotate(90deg); }}
.func-meta {{ color: var(--text-dim); font-size: 0.8rem; }}
.func-summary {{ color: var(--text-dim); font-size: 0.8rem; margin-top: 0.35rem; display: flex; flex-wrap: wrap; gap: 0.5rem; }}
.pill {{ display: inline-block; padding: 0.12rem 0.45rem; border-radius: 999px; background: var(--surface2); border: 1px solid var(--border); }}
.func-body {{ padding: 0 1.25rem 1rem; }}
table {{ width: 100%; border-collapse: collapse; font-size: 0.85rem; }}
th {{ text-align: left; padding: 0.4rem 0.6rem; border-bottom: 1px solid var(--border); color: var(--text-dim); font-weight: 600; font-size: 0.75rem; text-transform: uppercase; letter-spacing: 0.05em; }}
td {{ padding: 0.4rem 0.6rem; border-bottom: 1px solid var(--surface2); vertical-align: top; }}
tr:last-child td {{ border-bottom: none; }}
.status-proved {{ color: var(--green); font-weight: bold; }}
.status-runtime-checked {{ color: var(--blue); font-weight: bold; }}
.status-failed {{ color: var(--red); font-weight: bold; }}
.status-unknown {{ color: var(--yellow); font-weight: bold; }}
.status-timeout {{ color: var(--yellow); font-weight: bold; }}
.counterexample {{ background: var(--surface2); border-left: 3px solid var(--red); padding: 0.5rem 0.75rem; margin-top: 0.3rem; border-radius: 0 4px 4px 0; font-family: monospace; font-size: 0.8rem; }}
.cex-label {{ color: var(--red); font-weight: bold; margin-bottom: 0.2rem; }}
.reason {{ color: var(--text-dim); font-style: italic; margin-top: 0.2rem; font-size: 0.8rem; }}
.footer {{ margin-top: 2rem; padding-top: 1rem; border-top: 1px solid var(--border); color: var(--text-dim); font-size: 0.75rem; text-align: center; }}
</style>
</head>
"#
    )
}

/// Emit the page header with crate name, version, and timestamp.
fn html_header(report: &JsonProofReport) -> String {
    format!(
        r#"<div class="header">
<h1>Trust Proof Report</h1>
<div class="meta">Crate: <strong>{crate_name}</strong> | Trust v{version} | Schema v{schema} | Generated: {ts} | Total time: {time}ms</div>
</div>
"#,
        crate_name = escape(&report.crate_name),
        version = escape(&report.metadata.trust_version),
        schema = escape(&report.metadata.schema_version),
        ts = escape(&report.metadata.timestamp),
        time = report.metadata.total_time_ms,
    )
}

/// Emit the summary statistics section with progress bar.
fn html_summary(report: &JsonProofReport) -> String {
    let s = &report.summary;
    let verdict_class = verdict_class_crate(s.verdict);
    let verdict_label = verdict_label_crate(s.verdict);

    // Compute progress bar segment widths as percentages.
    let total = s.total_obligations.max(1) as f64;
    let pure_unknown = s.total_unknown.saturating_sub(s.total_timed_out);
    let pct_proved = (s.total_proved as f64 / total) * 100.0;
    let pct_runtime = (s.total_runtime_checked as f64 / total) * 100.0;
    let pct_failed = (s.total_failed as f64 / total) * 100.0;
    let pct_unknown = (pure_unknown as f64 / total) * 100.0;
    let pct_timeout = (s.total_timed_out as f64 / total) * 100.0;
    let pending_label = pending_summary(s.total_unknown, s.total_timed_out);
    let timeout_segment = if s.total_timed_out > 0 {
        format!(r#"<div class="segment seg-timeout" style="width:{pct_timeout:.1}%"></div>"#)
    } else {
        String::new()
    };
    let timeout_stat = if s.total_timed_out > 0 {
        format!(
            r#"<div class="stat"><div class="value" style="color:var(--yellow)">{}</div><div class="label">Timeout</div></div>"#,
            s.total_timed_out
        )
    } else {
        String::new()
    };

    // Trust: per-kind composition of the blended totals above — the report must
    // never present a single `proved` number without showing WHICH kinds it is
    // made of, so admissions and lowering-gap markers cannot hide inside it.
    let mut crate_breakdown = crate::formatting::KindBreakdown::default();
    for func in &report.functions {
        crate_breakdown.add(&func.obligations);
    }
    let kind_lines = crate_breakdown.lines("");
    let kind_breakdown = if kind_lines.is_empty() {
        String::new()
    } else {
        format!(
            r#"<div class="kind-breakdown" style="margin-top:0.5rem;font-size:0.85rem;color:#888">{}</div>"#,
            kind_lines.iter().map(|line| escape(line)).collect::<Vec<_>>().join("<br>")
        )
    };

    format!(
        r#"<div class="summary">
<h2>Summary</h2>
<div class="summary-grid">
<div class="stat"><div class="value">{functions}</div><div class="label">Functions</div></div>
<div class="stat"><div class="value" style="color:var(--green)">{proved}</div><div class="label">Proved</div></div>
<div class="stat"><div class="value" style="color:var(--blue)">{runtime_checked}</div><div class="label">Runtime-checked</div></div>
<div class="stat"><div class="value" style="color:var(--red)">{failed}</div><div class="label">Failed</div></div>
<div class="stat"><div class="value" style="color:var(--yellow)">{unknown}</div><div class="label">Unknown</div></div>
{timeout_stat}
<div class="stat"><div class="value">{obligations}</div><div class="label">Obligations</div></div>
</div>
<div class="progress-bar" title="{proved} proved, {runtime_checked} runtime-checked, {failed} failed, {pending_label}">
<div class="segment seg-proved" style="width:{pct_proved:.1}%"></div>
<div class="segment seg-runtime" style="width:{pct_runtime:.1}%"></div>
<div class="segment seg-failed" style="width:{pct_failed:.1}%"></div>
<div class="segment seg-unknown" style="width:{pct_unknown:.1}%"></div>
{timeout_segment}
</div>
<div style="margin-top:0.75rem">Verdict: <span class="verdict {verdict_class}">{verdict_label}</span></div>
{kind_breakdown}
</div>
"#,
        functions = s.functions_analyzed,
        kind_breakdown = kind_breakdown,
        proved = s.total_proved,
        runtime_checked = s.total_runtime_checked,
        failed = s.total_failed,
        unknown = pure_unknown,
        timeout_stat = timeout_stat,
        timeout_segment = timeout_segment,
        pending_label = pending_label,
        obligations = s.total_obligations,
    )
}

/// Emit the filter bar for showing/hiding functions by verdict.
fn html_filters(report: &JsonProofReport) -> String {
    let s = &report.summary;

    // Only show filter bar if there are functions.
    if s.functions_analyzed == 0 {
        return String::new();
    }

    format!(
        r#"<div class="filter-bar" id="filter-bar">
<span class="filter-label">Filter:</span>
<button class="filter-btn active" data-filter="all" onclick="filterFunctions('all')">All ({all})</button>
<button class="filter-btn active" data-filter="verified" onclick="filterFunctions('verified')">Verified ({verified})</button>
<button class="filter-btn active" data-filter="runtime-checked" onclick="filterFunctions('runtime-checked')">Runtime ({runtime})</button>
<button class="filter-btn active" data-filter="violations" onclick="filterFunctions('violations')">Failed ({failed})</button>
<button class="filter-btn active" data-filter="inconclusive" onclick="filterFunctions('inconclusive')">Pending ({pending})</button>
<span class="expand-controls">
<button class="filter-btn" onclick="expandAll()">Expand All</button>
<button class="filter-btn" onclick="collapseAll()">Collapse All</button>
</span>
</div>
"#,
        all = s.functions_analyzed,
        verified = s.functions_verified,
        runtime = s.functions_runtime_checked,
        failed = s.functions_with_violations,
        pending = s.functions_inconclusive,
    )
}

/// Emit per-function collapsible sections with obligation tables.
fn html_functions(report: &JsonProofReport) -> String {
    let mut out = String::new();

    for func in &report.functions {
        let verdict_class = verdict_class_func(func.summary.verdict);
        let verdict_label = function_verdict_label(func.summary.verdict);
        let data_verdict = func_verdict_data_attr(func.summary.verdict);

        let _ = write!(
            out,
            r#"<div class="func-section" data-verdict="{data_verdict}">
<details class="func-details" open>
<summary>
<div class="func-header">
<span><span class="func-toggle">&#9654;</span><span class="func-name">{name}</span></span>
<span><span class="verdict {vc}">{vl}</span> <span class="func-meta">{proved}/{total} proved, {runtime_checked} runtime-checked, {failed} failed, {pending}, {time}ms</span></span>
</div>
<div class="func-summary">
<span class="pill">Max level: {level}</span>
<span class="pill">Proved: {proved}</span>
<span class="pill">Runtime-checked: {runtime_checked}</span>
<span class="pill">Failed: {failed}</span>
<span class="pill">Unknown: {unknown}</span>
{timeout_pill}
</div>
</summary>
<div class="func-body">
"#,
            name = escape(&func.function),
            vc = verdict_class,
            vl = verdict_label,
            data_verdict = data_verdict,
            proved = func.summary.proved,
            total = func.summary.total_obligations,
            runtime_checked = func.summary.runtime_checked,
            failed = func.summary.failed,
            unknown = func.summary.unknown.saturating_sub(func.summary.timed_out),
            pending = pending_summary(func.summary.unknown, func.summary.timed_out),
            timeout_pill = timeout_pill(func.summary.timed_out),
            time = func.summary.total_time_ms,
            level = proof_level_label(func.summary.max_proof_level),
        );

        if !func.obligations.is_empty() {
            out.push_str("<table>\n<tr><th>Status</th><th>Strength</th><th>Obligation</th><th>Solver</th><th>Time</th><th>Location</th></tr>\n");

            for ob in &func.obligations {
                out.push_str(&format_obligation_row(ob));
            }

            out.push_str("</table>\n");
        }

        out.push_str("</div>\n</details>\n</div>\n");
    }

    out
}

fn pending_summary(pending: usize, timed_out: usize) -> String {
    let unknown = pending.saturating_sub(timed_out);
    if timed_out > 0 {
        format!("{unknown} unknown, {timed_out} {}", timeout_word(timed_out))
    } else {
        format!("{unknown} unknown")
    }
}

fn timeout_word(count: usize) -> &'static str {
    if count == 1 { "timeout" } else { "timeouts" }
}

fn timeout_pill(timed_out: usize) -> String {
    if timed_out > 0 {
        format!(r#"<span class="pill">Timed out: {timed_out}</span>"#)
    } else {
        String::new()
    }
}

/// Emit a single table row for an obligation, plus any counterexample detail.
fn format_obligation_row(ob: &ObligationReport) -> String {
    let monitor = ob.transport_evidence.as_ref().and_then(|transport| transport.monitor.as_ref());
    let (status_class, status_label) = match &ob.outcome {
        ObligationOutcome::Proved { .. } => ("status-proved", "PROVED"),
        ObligationOutcome::RuntimeChecked { .. } => ("status-runtime-checked", "RUNTIME-CHECKED"),
        ObligationOutcome::Failed { .. } => ("status-failed", "FAILED"),
        ObligationOutcome::Unknown { .. } => ("status-unknown", "UNKNOWN"),
        ObligationOutcome::Timeout { .. } => ("status-timeout", "TIMEOUT"),
        ObligationOutcome::DesignRequirement { .. } => {
            ("status-design-required", "DESIGN-REQUIRED")
        }
        _ => ("status-unknown", "UNKNOWN"),
    };
    let strength_cell = match &ob.outcome {
        ObligationOutcome::Proved { strength } => {
            escape(&proof_evidence_label_with_monitor(strength, monitor))
        }
        ObligationOutcome::RuntimeChecked { .. } => monitor.map_or_else(
            || "runtime-checked".to_string(),
            |monitor| {
                format!("runtime-checked; execution={}", monitor_executability_label(monitor))
            },
        ),
        _ => monitor.map_or_else(
            || "&mdash;".to_string(),
            |monitor| format!("execution={}", monitor_executability_label(monitor)),
        ),
    };

    let location_str = ob
        .location
        .as_ref()
        .map(|loc| format!("{}:{}", escape(&loc.file), loc.line_start))
        .unwrap_or_else(|| "&mdash;".to_string());

    let mut row = format!(
        "<tr><td class=\"{sc}\">{sl}</td><td>{strength}</td><td>{desc}</td><td>{solver}</td><td>{time}ms</td><td>{loc}</td></tr>\n",
        sc = status_class,
        sl = status_label,
        strength = strength_cell,
        desc = escape(&ob.description),
        solver = escape(&ob.solver),
        time = ob.time_ms,
        loc = location_str,
    );

    // Counterexample detail row
    if let ObligationOutcome::Failed { counterexample: Some(cex) } = &ob.outcome {
        let vars: Vec<String> = cex
            .variables
            .iter()
            .map(|v| format!("{} = {}", escape(&v.name), escape(&v.display)))
            .collect();
        let _ = writeln!(
            row,
            "<tr><td colspan=\"6\"><div class=\"counterexample\"><div class=\"cex-label\">Counterexample</div>{vars}</div></td></tr>",
            vars = vars.join(", "),
        );
    }

    // Unknown reason detail row
    if let ObligationOutcome::Unknown { reason } = &ob.outcome {
        let _ = writeln!(
            row,
            "<tr><td colspan=\"6\"><div class=\"reason\">Reason: {reason}</div></td></tr>",
            reason = escape(reason),
        );
    }

    // Runtime-check detail row
    if let ObligationOutcome::RuntimeChecked { note: Some(note) } = &ob.outcome {
        let _ = writeln!(
            row,
            "<tr><td colspan=\"6\"><div class=\"reason\">Runtime check: {note}</div></td></tr>",
            note = escape(note),
        );
    }

    // Timeout detail row
    if let ObligationOutcome::Timeout { timeout_ms } = &ob.outcome {
        let _ = writeln!(
            row,
            "<tr><td colspan=\"6\"><div class=\"reason\">Timed out after {timeout_ms}ms</div></td></tr>",
        );
    }

    row
}

/// Emit the page footer.
fn html_footer(report: &JsonProofReport) -> String {
    // Collect unique solver names across all obligations.
    let mut solvers: Vec<String> = report
        .functions
        .iter()
        .flat_map(|f| f.obligations.iter().map(|o| o.solver.clone()))
        .collect();
    solvers.sort();
    solvers.dedup();

    let solver_list = if solvers.is_empty() { "none".to_string() } else { solvers.join(", ") };

    format!(
        "<div class=\"footer\">Generated by Trust v{version} | Solvers: {solvers} | Schema v{schema}</div>\n",
        version = escape(&report.metadata.trust_version),
        solvers = escape(&solver_list),
        schema = escape(&report.metadata.schema_version),
    )
}

/// Emit the inline JavaScript for interactive features.
///
/// Provides:
/// - `filterFunctions(verdict)`: toggle visibility of function sections by verdict
/// - `expandAll()` / `collapseAll()`: bulk open/close all `<details>` elements
fn html_script() -> String {
    r#"<script>
function filterFunctions(verdict) {
  var btn = document.querySelector('.filter-btn[data-filter="' + verdict + '"]');
  if (!btn) return;
  if (verdict === 'all') {
    var allBtn = btn;
    var isActive = allBtn.classList.contains('active');
    var buttons = document.querySelectorAll('.filter-btn[data-filter]');
    for (var i = 0; i < buttons.length; i++) {
      if (isActive) { buttons[i].classList.remove('active'); }
      else { buttons[i].classList.add('active'); }
    }
  } else {
    btn.classList.toggle('active');
    syncAllButton();
  }
  applyFilters();
}
function syncAllButton() {
  var filterBtns = document.querySelectorAll('.filter-btn[data-filter]:not([data-filter="all"])');
  var allActive = true;
  for (var i = 0; i < filterBtns.length; i++) {
    if (!filterBtns[i].classList.contains('active')) { allActive = false; break; }
  }
  var allBtn = document.querySelector('.filter-btn[data-filter="all"]');
  if (allBtn) {
    if (allActive) { allBtn.classList.add('active'); }
    else { allBtn.classList.remove('active'); }
  }
}
function applyFilters() {
  var activeFilters = [];
  var buttons = document.querySelectorAll('.filter-btn[data-filter]:not([data-filter="all"])');
  for (var i = 0; i < buttons.length; i++) {
    if (buttons[i].classList.contains('active')) {
      activeFilters.push(buttons[i].getAttribute('data-filter'));
    }
  }
  var sections = document.querySelectorAll('.func-section[data-verdict]');
  for (var j = 0; j < sections.length; j++) {
    var v = sections[j].getAttribute('data-verdict');
    if (activeFilters.indexOf(v) >= 0) { sections[j].removeAttribute('hidden'); }
    else { sections[j].setAttribute('hidden', ''); }
  }
}
function expandAll() {
  var details = document.querySelectorAll('details.func-details');
  for (var i = 0; i < details.length; i++) { details[i].setAttribute('open', ''); }
}
function collapseAll() {
  var details = document.querySelectorAll('details.func-details');
  for (var i = 0; i < details.length; i++) { details[i].removeAttribute('open'); }
}
</script>
"#
    .to_string()
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Verdict CSS class for crate-level verdicts.
fn verdict_class_crate(verdict: CrateVerdict) -> &'static str {
    match verdict {
        CrateVerdict::Verified => "verdict-verified",
        CrateVerdict::RuntimeChecked => "verdict-runtime-checked",
        CrateVerdict::HasViolations => "verdict-violations",
        CrateVerdict::Inconclusive => "verdict-inconclusive",
        CrateVerdict::NoObligations => "verdict-none",
        _ => "unknown",
    }
}

/// Human-readable label for crate-level verdicts.
fn verdict_label_crate(verdict: CrateVerdict) -> &'static str {
    match verdict {
        CrateVerdict::Verified => "VERIFIED",
        CrateVerdict::RuntimeChecked => "RUNTIME CHECKED",
        CrateVerdict::HasViolations => "HAS VIOLATIONS",
        CrateVerdict::Inconclusive => "INCONCLUSIVE",
        CrateVerdict::NoObligations => "NO OBLIGATIONS",
        _ => "unknown",
    }
}

/// Verdict CSS class for function-level verdicts.
fn verdict_class_func(verdict: FunctionVerdict) -> &'static str {
    match verdict {
        FunctionVerdict::Verified => "verdict-verified",
        FunctionVerdict::RuntimeChecked => "verdict-runtime-checked",
        FunctionVerdict::HasViolations => "verdict-violations",
        FunctionVerdict::Inconclusive => "verdict-inconclusive",
        FunctionVerdict::NoObligations => "verdict-none",
        _ => "unknown",
    }
}

/// Data attribute value for function-level verdicts (used by JS filter).
fn func_verdict_data_attr(verdict: FunctionVerdict) -> &'static str {
    match verdict {
        FunctionVerdict::Verified => "verified",
        FunctionVerdict::RuntimeChecked => "runtime-checked",
        FunctionVerdict::HasViolations => "violations",
        FunctionVerdict::Inconclusive => "inconclusive",
        FunctionVerdict::NoObligations => "verified",
        _ => "unknown",
    }
}

/// Minimal HTML entity escaping for user-controlled strings.
fn escape(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;").replace('"', "&quot;")
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;
    use crate::{SCHEMA_VERSION, TRUST_VERSION, build_json_report};

    /// Helper: build a report with mixed results for get_midpoint.
    fn mixed_report() -> JsonProofReport {
        let results = vec![
            (
                VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::usize(), Ty::usize()),
                    },
                    function: "get_midpoint".into(),
                    location: SourceSpan {
                        file: "src/midpoint.rs".to_string(),
                        line_start: 5,
                        col_start: 5,
                        line_end: 5,
                        col_end: 10,
                    },
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 3,
                    counterexample: Some(Counterexample::new(vec![
                        ("a".to_string(), CounterexampleValue::Uint(u64::MAX as u128)),
                        ("b".to_string(), CounterexampleValue::Uint(1)),
                    ])),
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "get_midpoint".into(),
                    location: SourceSpan {
                        file: "src/midpoint.rs".to_string(),
                        line_start: 5,
                        col_start: 18,
                        line_end: 5,
                        col_end: 23,
                    },
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Proved {
                    solver: "ay".into(),
                    time_ms: 1,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            ),
        ];
        build_json_report("midpoint", &results)
    }

    /// Multi-function report with all outcome types.
    fn multi_function_report() -> JsonProofReport {
        let results = vec![
            (
                VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::usize(), Ty::usize()),
                    },
                    function: "get_midpoint".into(),
                    location: SourceSpan {
                        file: "src/midpoint.rs".to_string(),
                        line_start: 5,
                        col_start: 5,
                        line_end: 5,
                        col_end: 10,
                    },
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 3,
                    counterexample: Some(Counterexample::new(vec![
                        ("a".to_string(), CounterexampleValue::Uint(u64::MAX as u128)),
                        ("b".to_string(), CounterexampleValue::Uint(1)),
                    ])),
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "get_midpoint".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Proved {
                    solver: "ay".into(),
                    time_ms: 1,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::IndexOutOfBounds,
                    function: "lookup".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Unknown {
                    solver: "ay".into(),
                    time_ms: 50,
                    reason: "nonlinear arithmetic".to_string(),
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::Postcondition,
                    function: "compute".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 5000 },
            ),
        ];
        build_json_report("multi_crate", &results)
    }

    fn runtime_checked_report() -> JsonProofReport {
        JsonProofReport {
            metadata: ReportMetadata {
                schema_version: SCHEMA_VERSION.to_string(),
                trust_version: TRUST_VERSION.to_string(),
                timestamp: "0".to_string(),
                total_time_ms: 11,
                timeout_ms: None,
                function_budget_ms: None,
            },
            crate_name: "runtime_checked".to_string(),
            summary: CrateSummary {
                proof_grade_engine_statuses: Vec::new(),
                functions_analyzed: 1,
                functions_verified: 0,
                functions_runtime_checked: 1,
                functions_with_violations: 0,
                functions_inconclusive: 0,
                total_obligations: 1,
                total_proved: 0,
                total_runtime_checked: 1,
                total_failed: 0,
                total_unknown: 0,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                verdict: CrateVerdict::RuntimeChecked,
            },
            functions: vec![FunctionProofReport {
                function: "dynamic_check".into(),
                summary: FunctionSummary {
                    total_obligations: 1,
                    proved: 0,
                    runtime_checked: 1,
                    failed: 0,
                    unknown: 0,
                    timed_out: 0,
                    design_requirements: 0,
                    unattributed_failed: 0,
                    unattributed_unknown: 0,
                    unattributed_proved: 0,
                    total_time_ms: 11,
                    max_proof_level: Some(ProofLevel::L0Safety),
                    verdict: FunctionVerdict::RuntimeChecked,
                },
                obligations: vec![ObligationReport {
                    obligation_id: None,
                    description: "runtime safety check".to_string(),
                    kind: "postcondition".to_string(),
                    proof_level: ProofLevel::L0Safety,
                    location: Some(SourceSpan {
                        file: "src/runtime.rs".to_string(),
                        line_start: 10,
                        col_start: 1,
                        line_end: 10,
                        col_end: 12,
                    }),
                    outcome: ObligationOutcome::RuntimeChecked {
                        note: Some("validated by runtime instrumentation".to_string()),
                    },
                    solver: "runtime".into(),
                    time_ms: 11,
                    evidence: None,
                    proof_evidence: None,
                    transport_evidence: None,
                }],
            }],
            hardened: None,
            assumptions: Vec::new(),
            verification_gate: None,
            cargo_proof_inventory: None,
        }
    }

    // -------------------------------------------------------------------
    // Basic structure tests (existing, updated for interactive features)
    // -------------------------------------------------------------------

    #[test]
    fn test_html_report_basic() {
        let report = mixed_report();
        let html = format_html_report(&report);

        // Valid HTML structure
        assert!(html.starts_with("<!DOCTYPE html>"));
        assert!(html.contains("<html lang=\"en\">"));
        assert!(html.contains("<head>"));
        assert!(html.contains("</head>"));
        assert!(html.contains("<body>"));
        assert!(html.contains("</body>"));
        assert!(html.contains("</html>"));

        // Contains inline CSS
        assert!(html.contains("<style>"));
        assert!(html.contains("</style>"));

        // Contains the page title
        assert!(html.contains("<title>Trust Proof Report: midpoint</title>"));

        // Contains key structural elements
        assert!(html.contains("Trust Proof Report"));
        assert!(html.contains("UNKNOWN"));
        assert!(html.contains("proof_evidence is missing"));
        assert!(html.contains("FAILED"));
        assert!(html.contains("Counterexample"));
        assert!(html.contains("Strength"));
    }

    #[test]
    fn test_html_contains_function_names() {
        let report = multi_function_report();
        let html = format_html_report(&report);

        // All function names present
        assert!(html.contains("get_midpoint"), "HTML should contain function name 'get_midpoint'");
        assert!(html.contains("lookup"), "HTML should contain function name 'lookup'");
        assert!(html.contains("compute"), "HTML should contain function name 'compute'");
    }

    #[test]
    fn test_html_summary() {
        let report = multi_function_report();
        let html = format_html_report(&report);

        // Summary section exists
        assert!(html.contains("Summary"));

        // Contains the crate name
        assert!(html.contains("multi_crate"));

        // Verdict badge present
        assert!(html.contains("HAS VIOLATIONS"));

        // The summary grid should show numeric stats.
        assert!(html.contains("Functions"));
        assert!(html.contains("Proved"));
        assert!(html.contains("Failed"));
        assert!(html.contains("Pending"));
        assert!(html.contains("Obligations"));
        assert!(html.contains("Max level"));
    }

    #[test]
    fn test_html_counterexample_display() {
        let report = mixed_report();
        let html = format_html_report(&report);

        // Counterexample section present
        assert!(html.contains("Counterexample"));
        assert!(html.contains("a = 18446744073709551615"));
        assert!(html.contains("b = 1"));
    }

    #[test]
    fn test_html_unknown_reason_display() {
        let results = vec![(
            VerificationCondition {
                kind: VcKind::Postcondition,
                function: "lookup".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Unknown {
                solver: "ay".into(),
                time_ms: 50,
                reason: "nonlinear arithmetic".to_string(),
            },
        )];
        let report = build_json_report("unknown_reason", &results);
        let html = format_html_report(&report);

        // Unknown reason displayed
        assert!(html.contains("UNKNOWN"));
        assert!(html.contains("nonlinear arithmetic"));
    }

    #[test]
    fn test_html_timeout_display() {
        let report = multi_function_report();
        let html = format_html_report(&report);

        // Timeout info displayed
        assert!(html.contains("TIMEOUT"));
        assert!(html.contains("5000ms"));
        assert!(html.contains("0 unknown, 1 timeout"));
    }

    #[test]
    fn test_html_runtime_checked_rendering() {
        let report = runtime_checked_report();
        let html = format_html_report(&report);

        assert!(html.contains("status-runtime-checked"));
        assert!(html.contains("RUNTIME-CHECKED"));
        assert!(html.contains("Runtime-checked"));
        assert!(html.contains("validated by runtime instrumentation"));
        assert!(html.contains("verdict-runtime-checked"));
        assert!(html.contains("RUNTIME CHECKED"));
    }

    #[test]
    fn test_html_footer_solver_info() {
        let report = mixed_report();
        let html = format_html_report(&report);

        // Footer with solver info
        assert!(html.contains("Solvers: ay"));
        assert!(html.contains(&format!("Schema v{}", report.metadata.schema_version)));
        assert!(html.contains("proof_evidence is missing"));
    }

    #[test]
    fn test_html_escapes_special_chars() {
        // Build a report with HTML-special characters in a function name
        let results = vec![(
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "fn<T>(&self)".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let report = build_json_report("escape_test", &results);
        let html = format_html_report(&report);

        // Angle brackets must be escaped
        assert!(html.contains("fn&lt;T&gt;(&amp;self)"));
        assert!(!html.contains("fn<T>(&self)"));
    }

    #[test]
    fn test_html_empty_report() {
        let report = build_json_report("empty", &[]);
        let html = format_html_report(&report);

        // Still valid HTML
        assert!(html.starts_with("<!DOCTYPE html>"));
        assert!(html.contains("</html>"));
        assert!(html.contains("empty"));
        assert!(html.contains("NO OBLIGATIONS"));
    }

    #[test]
    fn test_html_location_display() {
        let report = mixed_report();
        let html = format_html_report(&report);

        // Location for the overflow obligation
        assert!(html.contains("src/midpoint.rs:5"));
    }

    #[test]
    fn test_html_raw_proved_status_is_inconclusive() {
        let results = vec![(
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "safe_fn".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let report = build_json_report("safe", &results);
        let html = format_html_report(&report);

        assert!(html.contains("verdict-inconclusive"));
        assert!(html.contains("INCONCLUSIVE"));
        assert!(html.contains("proof_evidence is missing"));
    }

    // -------------------------------------------------------------------
    // Interactive dashboard tests (NEW for #61)
    // -------------------------------------------------------------------

    #[test]
    fn test_html_contains_javascript() {
        let report = mixed_report();
        let html = format_html_report(&report);

        assert!(html.contains("<script>"), "HTML must contain inline JavaScript");
        assert!(html.contains("</script>"), "HTML must close script tag");
        assert!(html.contains("filterFunctions"), "HTML must contain filterFunctions JS function");
        assert!(html.contains("expandAll"), "HTML must contain expandAll JS function");
        assert!(html.contains("collapseAll"), "HTML must contain collapseAll JS function");
    }

    #[test]
    fn test_html_collapsible_sections() {
        let report = mixed_report();
        let html = format_html_report(&report);

        // Function sections use <details> for collapsibility
        assert!(
            html.contains("<details class=\"func-details\""),
            "Function sections must use <details> elements"
        );
        assert!(html.contains("</details>"), "Function sections must close <details> elements");
        assert!(html.contains("<summary>"), "Function sections must have <summary> elements");
        // Default open
        assert!(html.contains("open"), "Function details should be open by default");
        // Toggle arrow
        assert!(
            html.contains("func-toggle"),
            "Function sections must have a toggle arrow indicator"
        );
    }

    #[test]
    fn test_html_filter_bar() {
        let report = multi_function_report();
        let html = format_html_report(&report);

        // Filter bar present with controls
        assert!(html.contains("id=\"filter-bar\""), "HTML must contain filter bar");
        assert!(html.contains("filter-btn"), "Filter bar must contain filter buttons");
        assert!(html.contains("data-filter=\"verified\""), "Must have verified filter");
        assert!(html.contains("data-filter=\"violations\""), "Must have violations filter");
        assert!(html.contains("data-filter=\"inconclusive\""), "Must have inconclusive filter");
        assert!(
            html.contains("data-filter=\"runtime-checked\""),
            "Must have runtime-checked filter"
        );
        assert!(html.contains("data-filter=\"all\""), "Must have all filter");

        // Expand/Collapse controls
        assert!(html.contains("Expand All"), "Must have Expand All button");
        assert!(html.contains("Collapse All"), "Must have Collapse All button");
    }

    #[test]
    fn test_html_filter_bar_hidden_for_empty_report() {
        let report = build_json_report("empty", &[]);
        let html = format_html_report(&report);

        // Filter bar should NOT be present for empty reports
        assert!(!html.contains("id=\"filter-bar\""), "Empty report must not have filter bar");
    }

    #[test]
    fn test_html_data_verdict_attributes() {
        let report = multi_function_report();
        let html = format_html_report(&report);

        // Each function section has data-verdict for JS filtering
        assert!(
            html.contains("data-verdict=\"violations\""),
            "Failed functions must have data-verdict=violations"
        );
        assert!(
            html.contains("data-verdict=\"inconclusive\""),
            "Inconclusive functions must have data-verdict=inconclusive"
        );
    }

    #[test]
    fn test_html_progress_bar() {
        let report = multi_function_report();
        let html = format_html_report(&report);

        // Progress bar present with segment classes
        assert!(html.contains("progress-bar"), "HTML must contain a progress bar");
        assert!(html.contains("seg-proved"), "Progress bar must have proved segment");
        assert!(html.contains("seg-runtime"), "Progress bar must have runtime segment");
        assert!(html.contains("seg-failed"), "Progress bar must have failed segment");
        assert!(html.contains("seg-unknown"), "Progress bar must have unknown segment");
    }

    #[test]
    fn test_html_progress_bar_percentages() {
        // Build a report with known counts to verify percentages
        let results = vec![
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "f1".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Proved {
                    solver: "ay".into(),
                    time_ms: 1,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::Postcondition,
                    function: "f2".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 1,
                    counterexample: None,
                },
            ),
        ];
        let report = build_json_report("pct", &results);
        let html = format_html_report(&report);

        // 1 proved out of 2 = 50.0%, 1 failed = 50.0%
        assert!(
            html.contains("width:50.0%"),
            "Progress bar segments should show 50.0% for 1/2 split"
        );
    }

    #[test]
    fn test_html_filter_counts_in_buttons() {
        let report = multi_function_report();
        let html = format_html_report(&report);

        // Filter buttons show counts in parentheses
        // multi_function_report has 3 functions analyzed
        assert!(html.contains("All (3)"), "All filter button must show total function count");
    }

    #[test]
    fn test_html_func_body_wrapper() {
        let report = mixed_report();
        let html = format_html_report(&report);

        // The obligation table is wrapped in func-body div inside details
        assert!(
            html.contains("class=\"func-body\""),
            "Obligation tables must be wrapped in func-body div"
        );
    }

    #[test]
    fn test_html_runtime_checked_data_verdict() {
        let report = runtime_checked_report();
        let html = format_html_report(&report);

        assert!(
            html.contains("data-verdict=\"runtime-checked\""),
            "Runtime-checked functions must have correct data-verdict"
        );
    }

    #[test]
    fn test_html_raw_proved_status_has_unknown_data_verdict() {
        let results = vec![(
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "safe_fn".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let report = build_json_report("verified", &results);
        let html = format_html_report(&report);

        assert!(
            html.contains("data-verdict=\"inconclusive\""),
            "raw proof statuses without structured evidence must be inconclusive"
        );
    }

    #[test]
    fn test_html_self_contained() {
        let report = multi_function_report();
        let html = format_html_report(&report);

        // Must not reference external resources
        assert!(!html.contains("src=\"http"), "HTML must not reference external scripts");
        assert!(!html.contains("href=\"http"), "HTML must not reference external stylesheets");

        // Must have all CSS inline
        assert!(html.contains("<style>"));
        assert!(html.contains("</style>"));

        // Must have all JS inline
        assert!(html.contains("<script>"));
        assert!(html.contains("</script>"));
    }

    // -------------------------------------------------------------------
    // build_html_report convenience API tests
    // -------------------------------------------------------------------

    #[test]
    fn test_build_html_report_from_raw_results() {
        let results = vec![
            (
                VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::usize(), Ty::usize()),
                    },
                    function: "get_midpoint".into(),
                    location: SourceSpan {
                        file: "src/midpoint.rs".to_string(),
                        line_start: 5,
                        col_start: 5,
                        line_end: 5,
                        col_end: 10,
                    },
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 3,
                    counterexample: Some(Counterexample::new(vec![
                        ("a".to_string(), CounterexampleValue::Uint(u64::MAX as u128)),
                        ("b".to_string(), CounterexampleValue::Uint(1)),
                    ])),
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "get_midpoint".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Proved {
                    solver: "ay".into(),
                    time_ms: 1,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            ),
        ];

        let html = build_html_report("midpoint", &results);

        // Valid HTML
        assert!(html.starts_with("<!DOCTYPE html>"));
        assert!(html.contains("</html>"));

        // Crate name in title
        assert!(html.contains("<title>Trust Proof Report: midpoint</title>"));

        // Summary counts
        assert!(html.contains("Proved"));
        assert!(html.contains("Failed"));
        assert!(html.contains("HAS VIOLATIONS"));

        // Function name
        assert!(html.contains("get_midpoint"));

        // Counterexample
        assert!(html.contains("Counterexample"));
        assert!(html.contains("a = 18446744073709551615"));

        // The raw status is visible as a fail-closed proof gap.
        assert!(html.contains("proof_evidence is missing"));

        // Color-coded status classes
        assert!(html.contains("status-unknown"));
        assert!(html.contains("status-failed"));
    }

    #[test]
    fn test_build_html_report_empty() {
        let html = build_html_report("empty_crate", &[]);

        assert!(html.starts_with("<!DOCTYPE html>"));
        assert!(html.contains("empty_crate"));
        assert!(html.contains("NO OBLIGATIONS"));
    }

    #[test]
    fn test_write_html_report_file() {
        let results = vec![(
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "safe_div".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];

        let dir = std::env::temp_dir().join("trust_report_test_html_218");
        let _ = std::fs::remove_dir_all(&dir);

        write_html_report("file_test", &results, &dir).expect("write html report");

        let content = std::fs::read_to_string(dir.join("report.html")).expect("read html");
        assert!(content.starts_with("<!DOCTYPE html>"));
        assert!(content.contains("file_test"));
        assert!(content.contains("safe_div"));
        assert!(content.contains("INCONCLUSIVE"));
        assert!(content.contains("proof_evidence is missing"));

        let _ = std::fs::remove_dir_all(&dir);
    }
}
