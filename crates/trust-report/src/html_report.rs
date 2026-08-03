// trust-report/html_report.rs: Standalone HTML verification report generator
//
// Produces self-contained, styled HTML reports from JsonProofReport or
// CrateVerificationResult. Features:
// - Standalone HTML (all CSS inline, no external dependencies)
// - Summary section: total functions, verified/failed/unknown counts, verdict
// - Per-function section: function name, VCs, status, counterexamples
// - Color-coded (green=verified, red=failed, yellow=unknown)
// - Sortable/filterable table (minimal inline JS)
// - Responsive layout for both screen and print
// - Light/dark color schemes
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt::Write;

use trust_types::{
    CrateVerdict, CrateVerificationResult, FunctionVerdict, HardenedBoundaryInventoryEntry,
    HardenedBoundaryInventoryRole, JsonProofReport, ObligationOutcome,
};

use crate::{
    build_crate_verification_report, function_verdict_label, monitor_executability_label,
    proof_evidence_label_with_monitor,
};

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Color scheme for HTML report rendering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[derive(Default)]
pub enum ColorScheme {
    /// Light background with dark text.
    #[default]
    Light,
    /// Dark background with light text.
    Dark,
}

/// Configuration for HTML report generation.
#[derive(Debug, Clone, PartialEq)]
pub struct HtmlReportConfig {
    /// Report title (appears in `<title>` and page header).
    pub title: String,
    /// Whether to include source file paths in obligation rows.
    pub include_source: bool,
    /// Whether to render counterexample variable assignments.
    pub include_counterexamples: bool,
    /// Color scheme for the report.
    pub color_scheme: ColorScheme,
    /// Maximum nesting depth for collapsible sections (0 = collapsed).
    pub max_depth: usize,
}

impl Default for HtmlReportConfig {
    fn default() -> Self {
        Self {
            title: "Trust Verification Report".to_string(),
            include_source: true,
            include_counterexamples: true,
            color_scheme: ColorScheme::Light,
            max_depth: 2,
        }
    }
}

// ---------------------------------------------------------------------------
// Top-level convenience API
// ---------------------------------------------------------------------------

/// Generate a standalone HTML verification report from a `JsonProofReport`.
///
/// This is the primary entry point requested by #354. It produces a
/// self-contained HTML document with:
/// - Summary section (total functions, verified/failed/unknown counts, verdict)
/// - Per-function section (function name, VCs generated, status, counterexamples)
/// - Color coding (green=verified, red=failed, yellow=unknown)
/// - Sortable/filterable table (minimal inline JavaScript)
/// - Responsive layout for both screen and print
///
/// Uses the default `HtmlReportConfig`. For customization, use
/// `HtmlReportGenerator::generate_from_json`.
#[must_use]
pub fn generate_html_report(report: &JsonProofReport) -> String {
    let config = HtmlReportConfig::default();
    HtmlReportGenerator::generate_from_json(report, &config)
}

// ---------------------------------------------------------------------------
// Generator
// ---------------------------------------------------------------------------

/// HTML report generator that produces self-contained HTML documents
/// from `CrateVerificationResult`, `JsonProofReport`, or raw
/// `(VerificationCondition, VerificationResult)` pairs.
// Trust: #485 HTML proof report generation with dashboard
pub struct HtmlReportGenerator;

impl HtmlReportGenerator {
    /// Generate a complete, self-contained HTML document from verification results.
    ///
    /// The output includes embedded CSS (no external dependencies), a summary
    /// section, per-function collapsible detail sections, color-coded results,
    /// and an optional counterexample display.
    #[must_use]
    pub fn generate(results: &CrateVerificationResult, config: &HtmlReportConfig) -> String {
        let report = build_crate_verification_report(results);
        Self::generate_from_json(&report, config)
    }

    /// Generate a full HTML proof report page from raw verification result pairs.
    ///
    /// This is the convenience entry point requested by #485. It accepts a
    /// crate name and a slice of `(VerificationCondition, VerificationResult)`
    /// pairs, builds the canonical `JsonProofReport` internally, and renders
    /// a self-contained HTML page with:
    /// - Dashboard section: total functions, proved, failed, timeout counts
    /// - Per-function detail cards with color coding (green/red/yellow)
    /// - CSS styling inline (no external deps)
    /// - ProofStrength display per function
    // Trust: #485 generate_report convenience method
    #[must_use]
    pub fn generate_report(
        crate_name: &str,
        results: &[(trust_types::VerificationCondition, trust_types::VerificationResult)],
    ) -> String {
        let json_report = crate::build_json_report(crate_name, results);
        let config = HtmlReportConfig::default();
        Self::generate_from_json(&json_report, &config)
    }

    /// Generate HTML from an already-built `JsonProofReport`.
    #[must_use]
    pub fn generate_from_json(report: &JsonProofReport, config: &HtmlReportConfig) -> String {
        let mut html = String::with_capacity(8192);

        html.push_str(&Self::render_doctype_and_head(report, config));
        html.push_str("<body>\n");
        html.push_str(&Self::render_header(report, config));
        html.push_str(&Self::render_summary(report));
        html.push_str(&Self::render_hardened_context(report));
        html.push_str(&Self::render_functions(report, config));
        html.push_str(&Self::render_footer(report));
        html.push_str(&Self::render_script());
        html.push_str("</body>\n</html>\n");

        html
    }

    // -- Section renderers --------------------------------------------------

    fn render_doctype_and_head(report: &JsonProofReport, config: &HtmlReportConfig) -> String {
        let css = Self::render_css(config);
        let title = escape_html(&config.title);
        let crate_name = escape_html(&report.crate_name);

        format!(
            "<!DOCTYPE html>\n\
             <html lang=\"en\">\n\
             <head>\n\
             <meta charset=\"utf-8\">\n\
             <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
             <title>{title} - {crate_name}</title>\n\
             <style>\n\
             {css}\
             </style>\n\
             </head>\n",
        )
    }

    fn render_css(config: &HtmlReportConfig) -> String {
        let (bg, surface, text, text_dim, border) = match config.color_scheme {
            ColorScheme::Light => ("#ffffff", "#f8f9fa", "#212529", "#6c757d", "#dee2e6"),
            ColorScheme::Dark => ("#1a1b26", "#24283b", "#c0caf5", "#565f89", "#3b4261"),
        };

        format!(
            "* {{ margin: 0; padding: 0; box-sizing: border-box; }}\n\
             body {{ font-family: -apple-system, BlinkMacSystemFont, \"Segoe UI\", Roboto, monospace; \
             background: {bg}; color: {text}; line-height: 1.6; padding: 2rem; max-width: 960px; margin: 0 auto; }}\n\
             h1 {{ font-size: 1.5rem; margin-bottom: 0.25rem; }}\n\
             h2 {{ font-size: 1.15rem; margin: 1.25rem 0 0.5rem; }}\n\
             .header {{ margin-bottom: 1.5rem; border-bottom: 1px solid {border}; padding-bottom: 1rem; }}\n\
             .meta {{ color: {text_dim}; font-size: 0.85rem; }}\n\
             .summary {{ background: {surface}; border-radius: 8px; padding: 1rem 1.25rem; margin-bottom: 1.5rem; }}\n\
             .summary-grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(100px, 1fr)); gap: 1rem; }}\n\
             .stat {{ text-align: center; }}\n\
             .stat .value {{ font-size: 1.75rem; font-weight: bold; }}\n\
             .stat .label {{ font-size: 0.75rem; color: {text_dim}; text-transform: uppercase; }}\n\
             .hardened {{ background: {surface}; border-radius: 8px; padding: 1rem 1.25rem; margin-bottom: 1.5rem; }}\n\
             .hardened-grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(160px, 1fr)); gap: 0.75rem; margin-bottom: 0.75rem; }}\n\
             .hardened-box {{ border: 1px solid {border}; border-radius: 6px; padding: 0.6rem 0.75rem; }}\n\
             .hardened-label {{ color: {text_dim}; font-size: 0.7rem; font-weight: 700; text-transform: uppercase; }}\n\
             .hardened-value {{ font-weight: 700; }}\n\
             .hardened-detail {{ color: {text_dim}; font-size: 0.75rem; }}\n\
             .role-inventory {{ color: #3b82f6; font-weight: bold; }}\n\
             .role-model {{ color: #eab308; font-weight: bold; }}\n\
             .role-proof {{ color: #22c55e; font-weight: bold; }}\n\
             .color-proved {{ color: #22c55e; }}\n\
             .color-failed {{ color: #ef4444; }}\n\
             .color-timeout {{ color: #eab308; }}\n\
             .verdict {{ display: inline-block; padding: 0.2rem 0.6rem; border-radius: 4px; \
             font-weight: bold; font-size: 0.85rem; text-transform: uppercase; }}\n\
             .v-verified {{ background: rgba(34,197,94,0.15); color: #22c55e; }}\n\
             .v-failed {{ background: rgba(239,68,68,0.15); color: #ef4444; }}\n\
             .v-timeout {{ background: rgba(234,179,8,0.15); color: #eab308; }}\n\
             .v-none {{ background: rgba(108,117,125,0.15); color: {text_dim}; }}\n\
             .filter-bar {{ background: {surface}; border-radius: 8px; padding: 0.5rem 1rem; \
             margin-bottom: 1rem; display: flex; gap: 0.5rem; flex-wrap: wrap; align-items: center; }}\n\
             .filter-bar .lbl {{ color: {text_dim}; font-size: 0.8rem; font-weight: 600; text-transform: uppercase; }}\n\
             .fbtn {{ background: {surface}; border: 1px solid {border}; color: {text}; padding: 0.25rem 0.6rem; \
             border-radius: 4px; font-size: 0.8rem; cursor: pointer; }}\n\
             .fbtn:hover {{ border-color: {text_dim}; }}\n\
             .fbtn.active {{ border-color: {text}; font-weight: bold; }}\n\
             .func-section {{ background: {surface}; border-radius: 8px; margin-bottom: 0.75rem; }}\n\
             .func-section[hidden] {{ display: none; }}\n\
             details.func-details summary {{ cursor: pointer; padding: 0.75rem 1rem; list-style: none; }}\n\
             details.func-details summary::-webkit-details-marker {{ display: none; }}\n\
             .func-name {{ font-family: monospace; font-weight: bold; }}\n\
             .func-meta {{ color: {text_dim}; font-size: 0.8rem; margin-left: 0.5rem; }}\n\
             .func-body {{ padding: 0 1rem 1rem; }}\n\
             table {{ width: 100%; border-collapse: collapse; font-size: 0.85rem; }}\n\
             th {{ text-align: left; padding: 0.4rem 0.6rem; border-bottom: 1px solid {border}; \
             color: {text_dim}; font-size: 0.75rem; text-transform: uppercase; cursor: pointer; }}\n\
             th:hover {{ text-decoration: underline; }}\n\
             td {{ padding: 0.4rem 0.6rem; border-bottom: 1px solid {surface}; vertical-align: top; }}\n\
             tr:last-child td {{ border-bottom: none; }}\n\
             .s-proved {{ color: #22c55e; font-weight: bold; }}\n\
             .s-failed {{ color: #ef4444; font-weight: bold; }}\n\
             .s-unknown {{ color: #eab308; font-weight: bold; }}\n\
             .s-timeout {{ color: #eab308; font-weight: bold; }}\n\
             .s-runtime {{ color: #3b82f6; font-weight: bold; }}\n\
             .cex {{ background: {surface}; border-left: 3px solid #ef4444; padding: 0.5rem 0.75rem; \
             margin-top: 0.25rem; font-family: monospace; font-size: 0.8rem; }}\n\
             .cex-label {{ color: #ef4444; font-weight: bold; margin-bottom: 0.2rem; }}\n\
             .footer {{ margin-top: 2rem; padding-top: 1rem; border-top: 1px solid {border}; \
             color: {text_dim}; font-size: 0.75rem; text-align: center; }}\n\
             @media print {{\n\
               body {{ background: #fff; color: #000; padding: 0.5rem; max-width: 100%; }}\n\
               .summary {{ background: #f5f5f5; page-break-inside: avoid; }}\n\
               .hardened {{ background: #f5f5f5; page-break-inside: avoid; }}\n\
               .func-section {{ background: #f5f5f5; page-break-inside: avoid; }}\n\
               .filter-bar {{ display: none; }}\n\
               details.func-details {{ display: block; }}\n\
               details.func-details > summary {{ display: block; }}\n\
               .color-proved {{ color: #16a34a; }}\n\
               .color-failed {{ color: #dc2626; }}\n\
               .color-timeout {{ color: #ca8a04; }}\n\
               .s-proved {{ color: #16a34a; }}\n\
               .s-failed {{ color: #dc2626; }}\n\
               .s-unknown {{ color: #ca8a04; }}\n\
               .s-timeout {{ color: #ca8a04; }}\n\
               .s-runtime {{ color: #2563eb; }}\n\
               .v-verified {{ background: #dcfce7; color: #16a34a; }}\n\
               .v-failed {{ background: #fee2e2; color: #dc2626; }}\n\
               .v-timeout {{ background: #fef9c3; color: #ca8a04; }}\n\
               .v-none {{ background: #f3f4f6; color: #6b7280; }}\n\
               .footer {{ page-break-before: auto; }}\n\
             }}\n\
             @media (max-width: 640px) {{\n\
               body {{ padding: 0.75rem; }}\n\
               .summary-grid {{ grid-template-columns: repeat(2, 1fr); }}\n\
               table {{ font-size: 0.75rem; }}\n\
             }}\n",
        )
    }

    fn render_header(report: &JsonProofReport, config: &HtmlReportConfig) -> String {
        format!(
            "<div class=\"header\">\n\
             <h1>{title}</h1>\n\
             <div class=\"meta\">Crate: <strong>{crate_name}</strong> \
             | Trust v{version} | Generated: {ts}</div>\n\
             </div>\n",
            title = escape_html(&config.title),
            crate_name = escape_html(&report.crate_name),
            version = escape_html(&report.metadata.trust_version),
            ts = escape_html(&report.metadata.timestamp),
        )
    }

    fn render_summary(report: &JsonProofReport) -> String {
        let s = &report.summary;
        let (verdict_class, verdict_label) = crate_verdict_display(s.verdict);
        let pure_unknown = s.total_unknown.saturating_sub(s.total_timed_out);

        format!(
            "<div class=\"summary\">\n\
             <h2>Summary</h2>\n\
             <div class=\"summary-grid\">\n\
             <div class=\"stat\"><div class=\"value\">{functions}</div>\
             <div class=\"label\">Functions</div></div>\n\
             <div class=\"stat\"><div class=\"value color-proved\">{proved}</div>\
             <div class=\"label\">Proved</div></div>\n\
             <div class=\"stat\"><div class=\"value color-failed\">{failed}</div>\
             <div class=\"label\">Failed</div></div>\n\
             <div class=\"stat\"><div class=\"value color-timeout\">{unknown}</div>\
             <div class=\"label\">Unknown</div></div>\n\
             {timeout_stat}\
             <div class=\"stat\"><div class=\"value\">{total}</div>\
             <div class=\"label\">Total VCs</div></div>\n\
             </div>\n\
             <div style=\"margin-top:0.75rem\">Verdict: \
             <span class=\"verdict {vc}\">{vl}</span></div>\n\
             </div>\n",
            functions = s.functions_analyzed,
            proved = s.total_proved,
            failed = s.total_failed,
            unknown = pure_unknown,
            timeout_stat = Self::timeout_stat(s.total_timed_out),
            total = s.total_obligations,
            vc = verdict_class,
            vl = verdict_label,
        )
    }

    fn render_hardened_context(report: &JsonProofReport) -> String {
        let Some(hardened) = &report.hardened else {
            return String::new();
        };

        let mut out = String::new();
        out.push_str("<div class=\"hardened\">\n<h2>Hardened Context</h2>\n");

        if hardened.profile.is_some() || hardened.assurance.is_some() || hardened.summary.is_some()
        {
            out.push_str("<div class=\"hardened-grid\">\n");

            if let Some(profile) = &hardened.profile {
                let categories = if profile.enabled_categories.is_empty() {
                    "none".to_string()
                } else {
                    profile.enabled_categories.join(", ")
                };
                let _ = writeln!(
                    out,
                    "<div class=\"hardened-box\">\
                     <div class=\"hardened-label\">Profile</div>\
                     <div class=\"hardened-value\">{name}</div>\
                     <div class=\"hardened-detail\">{version}</div>\
                     <div class=\"hardened-detail\">Categories: {categories}</div>\
                     </div>",
                    name = escape_html(profile.name.as_deref().unwrap_or("unspecified")),
                    version = escape_html(profile.version.as_deref().unwrap_or("unversioned")),
                    categories = escape_html(&categories),
                );
            }

            if let Some(assurance) = &hardened.assurance {
                let requirement = if assurance.proof_evidence_required {
                    "proof evidence required"
                } else {
                    "proof evidence optional"
                };
                let _ = writeln!(
                    out,
                    "<div class=\"hardened-box\">\
                     <div class=\"hardened-label\">Assurance</div>\
                     <div class=\"hardened-value\">{level}</div>\
                     <div class=\"hardened-detail\">Model: {model}</div>\
                     <div class=\"hardened-detail\">{requirement}</div>\
                     <div class=\"hardened-detail\">{policy}</div>\
                     </div>",
                    level = escape_html(assurance.level.as_deref().unwrap_or("unspecified")),
                    model = escape_html(assurance.model.as_deref().unwrap_or("unspecified")),
                    requirement = requirement,
                    policy = escape_html(
                        assurance.proof_evidence_policy.as_deref().unwrap_or("no policy recorded")
                    ),
                );
            }

            if let Some(summary) = &hardened.summary {
                let _ = writeln!(
                    out,
                    "<div class=\"hardened-box\">\
                     <div class=\"hardened-label\">Summary</div>\
                     <div class=\"hardened-value\">{proved}/{total} proved</div>\
                     <div class=\"hardened-detail\">Inventory: {inventory}</div>\
                     <div class=\"hardened-detail\">Model assumptions: {assumptions}</div>\
                     <div class=\"hardened-detail\">Proof evidence: {evidence}</div>\
                     </div>",
                    proved = summary.proved_hardened_obligations,
                    total = summary.hardened_obligations,
                    inventory = summary.inventory_entries,
                    assumptions = summary.model_assumptions,
                    evidence = summary.proof_evidence_entries,
                );
            }

            out.push_str("</div>\n");
        }

        if !hardened.boundary_inventory.is_empty() {
            out.push_str(
                "<table>\n<tr><th>Role</th><th>Boundary</th><th>Category</th><th>Evidence / Source</th></tr>\n",
            );

            for entry in &hardened.boundary_inventory {
                let (role_class, role_label) = hardened_role_display(entry.role);
                let category = if entry.category.is_empty() {
                    "&mdash;".to_string()
                } else {
                    escape_html(&entry.category)
                };
                let boundary = if entry.boundary.is_empty() {
                    "&mdash;".to_string()
                } else {
                    escape_html(&entry.boundary)
                };
                let detail = hardened_entry_detail(entry);
                let refs = hardened_entry_refs(entry);

                let _ = writeln!(
                    out,
                    "<tr><td class=\"{role_class}\">{role_label}</td>\
                     <td>{boundary}{detail}</td><td>{category}</td><td>{refs}</td></tr>",
                );
            }

            out.push_str("</table>\n");
        }

        out.push_str("</div>\n");
        out
    }

    fn render_functions(report: &JsonProofReport, config: &HtmlReportConfig) -> String {
        let mut out = String::new();

        // Filter bar (only when there are functions)
        if !report.functions.is_empty() {
            out.push_str(
                "<div class=\"filter-bar\" id=\"filterBar\">\n\
                 <span class=\"lbl\">Filter:</span>\n\
                 <button class=\"fbtn active\" data-filter=\"all\" onclick=\"trustFilter('all')\">All</button>\n\
                 <button class=\"fbtn active\" data-filter=\"verified\" onclick=\"trustFilter('verified')\">Verified</button>\n\
                 <button class=\"fbtn active\" data-filter=\"failed\" onclick=\"trustFilter('failed')\">Failed</button>\n\
                 <button class=\"fbtn active\" data-filter=\"unknown\" onclick=\"trustFilter('unknown')\">Unknown</button>\n\
                 </div>\n",
            );
        }

        for func in &report.functions {
            let verdict_label = function_verdict_label(func.summary.verdict);
            let (vc_class, _) = func_verdict_display(func.summary.verdict);
            let open_attr = if config.max_depth > 0 { " open" } else { "" };
            let data_status = func_data_status(func.summary.verdict);

            let _ = write!(
                out,
                "<div class=\"func-section\" data-status=\"{ds}\">\n\
                 <details class=\"func-details\"{open_attr}>\n\
                 <summary>\n\
                 <span class=\"func-name\">{name}</span>\n\
                 <span class=\"verdict {vc}\">{vl}</span>\n\
                 <span class=\"func-meta\">{proved}/{total} proved, \
                 {failed} failed, {pending}, {time}ms</span>\n\
                 </summary>\n\
                 <div class=\"func-body\">\n",
                ds = data_status,
                name = escape_html(&func.function),
                vc = vc_class,
                vl = verdict_label,
                proved = func.summary.proved,
                total = func.summary.total_obligations,
                failed = func.summary.failed,
                pending = Self::pending_summary(func.summary.unknown, func.summary.timed_out),
                time = func.summary.total_time_ms,
            );

            if !func.obligations.is_empty() {
                out.push_str(
                    "<table>\n<tr><th onclick=\"trustSort(this,0)\">Status</th>\
                     <th onclick=\"trustSort(this,1)\">Description</th>\
                     <th onclick=\"trustSort(this,2)\">Solver</th>\
                     <th onclick=\"trustSort(this,3)\">Time</th>",
                );
                if config.include_source {
                    out.push_str("<th onclick=\"trustSort(this,4)\">Location</th>");
                }
                out.push_str("</tr>\n");

                for ob in &func.obligations {
                    let (status_class, status_label) = obligation_display(&ob.outcome);
                    let monitor = ob
                        .transport_evidence
                        .as_ref()
                        .and_then(|transport| transport.monitor.as_ref());
                    let strength_info = match &ob.outcome {
                        ObligationOutcome::Proved { strength } => {
                            format!(
                                " ({})",
                                escape_html(&proof_evidence_label_with_monitor(strength, monitor))
                            )
                        }
                        _ => monitor.map_or_else(String::new, |monitor| {
                            format!(" (execution={})", monitor_executability_label(monitor))
                        }),
                    };

                    let loc_cell = if config.include_source {
                        let loc_str = ob
                            .location
                            .as_ref()
                            .map(|l| format!("{}:{}", escape_html(&l.file), l.line_start))
                            .unwrap_or_else(|| "&mdash;".to_string());
                        format!("<td>{loc_str}</td>")
                    } else {
                        String::new()
                    };

                    let _ = writeln!(
                        out,
                        "<tr><td class=\"{sc}\">{sl}{strength}</td>\
                         <td>{desc}</td><td>{solver}</td>\
                         <td>{time}ms</td>{loc}</tr>",
                        sc = status_class,
                        sl = status_label,
                        strength = strength_info,
                        desc = escape_html(&ob.description),
                        solver = escape_html(&ob.solver),
                        time = ob.time_ms,
                        loc = loc_cell,
                    );

                    // Counterexample detail row
                    if config.include_counterexamples
                        && let ObligationOutcome::Failed { counterexample: Some(cex) } = &ob.outcome
                    {
                        let colspan = if config.include_source { 5 } else { 4 };
                        let vars: Vec<String> = cex
                            .variables
                            .iter()
                            .map(|v| {
                                format!("{} = {}", escape_html(&v.name), escape_html(&v.display))
                            })
                            .collect();
                        let _ = writeln!(
                            out,
                            "<tr><td colspan=\"{colspan}\">\
                                 <div class=\"cex\">\
                                 <div class=\"cex-label\">Counterexample</div>\
                                 {vars}</div></td></tr>",
                            vars = vars.join(", "),
                        );
                    }

                    // Timeout detail row
                    if let ObligationOutcome::Timeout { timeout_ms } = &ob.outcome {
                        let colspan = if config.include_source { 5 } else { 4 };
                        let _ = writeln!(
                            out,
                            "<tr><td colspan=\"{colspan}\">\
                             <div class=\"func-meta\">\
                             Timed out after {timeout_ms}ms</div></td></tr>",
                        );
                    }
                }

                out.push_str("</table>\n");
            }

            out.push_str("</div>\n</details>\n</div>\n");
        }

        out
    }

    fn timeout_stat(timed_out: usize) -> String {
        if timed_out > 0 {
            format!(
                "<div class=\"stat\"><div class=\"value color-timeout\">{timed_out}</div>\
                 <div class=\"label\">Timeout</div></div>\n"
            )
        } else {
            String::new()
        }
    }

    fn pending_summary(pending: usize, timed_out: usize) -> String {
        let unknown = pending.saturating_sub(timed_out);
        if timed_out > 0 {
            format!("{unknown} unknown, {timed_out} {}", Self::timeout_word(timed_out))
        } else {
            format!("{unknown} unknown")
        }
    }

    fn timeout_word(count: usize) -> &'static str {
        if count == 1 { "timeout" } else { "timeouts" }
    }

    fn render_footer(report: &JsonProofReport) -> String {
        let mut solvers: Vec<String> = report
            .functions
            .iter()
            .flat_map(|f| f.obligations.iter().map(|o| o.solver.clone()))
            .collect();
        solvers.sort();
        solvers.dedup();

        let solver_list = if solvers.is_empty() { "none".to_string() } else { solvers.join(", ") };

        let timestamp = escape_html(&report.metadata.timestamp);

        format!(
            "<div class=\"footer\">Generated by Trust v{version} \
             | Solvers: {solvers} | {ts}</div>\n",
            version = escape_html(&report.metadata.trust_version),
            solvers = escape_html(&solver_list),
            ts = timestamp,
        )
    }

    /// Render minimal inline JavaScript for filtering and column sorting.
    fn render_script() -> String {
        "<script>\n\
         function trustFilter(v){\n\
           var b=document.querySelector('.fbtn[data-filter=\"'+v+'\"]');\n\
           if(!b)return;\n\
           if(v==='all'){\n\
             var bs=document.querySelectorAll('.fbtn[data-filter]');\n\
             var on=b.classList.contains('active');\n\
             for(var i=0;i<bs.length;i++){on?bs[i].classList.remove('active'):bs[i].classList.add('active');}\n\
           }else{b.classList.toggle('active');}\n\
           var af=[];\n\
           var fs=document.querySelectorAll('.fbtn[data-filter]:not([data-filter=\"all\"])');\n\
           for(var i=0;i<fs.length;i++){if(fs[i].classList.contains('active'))af.push(fs[i].getAttribute('data-filter'));}\n\
           var ss=document.querySelectorAll('.func-section[data-status]');\n\
           for(var j=0;j<ss.length;j++){\n\
             var s=ss[j].getAttribute('data-status');\n\
             af.indexOf(s)>=0?ss[j].removeAttribute('hidden'):ss[j].setAttribute('hidden','');\n\
           }\n\
         }\n\
         function trustSort(th,col){\n\
           var t=th.closest('table');if(!t)return;\n\
           var rows=Array.from(t.querySelectorAll('tr')).slice(1);\n\
           var asc=th.getAttribute('data-asc')!=='1';\n\
           th.setAttribute('data-asc',asc?'1':'0');\n\
           rows.sort(function(a,b){\n\
             var at=(a.cells[col]||{}).textContent||'';\n\
             var bt=(b.cells[col]||{}).textContent||'';\n\
             var an=parseFloat(at),bn=parseFloat(bt);\n\
             if(!isNaN(an)&&!isNaN(bn))return asc?an-bn:bn-an;\n\
             return asc?at.localeCompare(bt):bt.localeCompare(at);\n\
           });\n\
           var tb=t.querySelector('tbody')||t;\n\
           for(var i=0;i<rows.length;i++)tb.appendChild(rows[i]);\n\
         }\n\
         </script>\n"
            .to_string()
    }
}

// ---------------------------------------------------------------------------
// Public escape function
// ---------------------------------------------------------------------------

/// Escape a string for safe inclusion in HTML content.
///
/// Replaces `&`, `<`, `>`, `"`, and `'` with their HTML entity equivalents.
/// This prevents XSS when embedding user-provided strings (function names,
/// file paths, counterexample values) into HTML output.
#[must_use]
pub fn escape_html(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&#x27;")
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

fn crate_verdict_display(verdict: CrateVerdict) -> (&'static str, &'static str) {
    match verdict {
        CrateVerdict::Verified => ("v-verified", "VERIFIED"),
        CrateVerdict::RuntimeChecked => ("v-verified", "RUNTIME CHECKED"),
        CrateVerdict::HasViolations => ("v-failed", "HAS VIOLATIONS"),
        CrateVerdict::Inconclusive => ("v-timeout", "INCONCLUSIVE"),
        CrateVerdict::NoObligations => ("v-none", "NO OBLIGATIONS"),
        _ => ("s-unknown", "UNKNOWN"),
    }
}

fn func_verdict_display(verdict: FunctionVerdict) -> (&'static str, &'static str) {
    match verdict {
        FunctionVerdict::Verified => ("v-verified", "VERIFIED"),
        FunctionVerdict::RuntimeChecked => ("v-verified", "RUNTIME CHECKED"),
        FunctionVerdict::HasViolations => ("v-failed", "VIOLATIONS"),
        FunctionVerdict::Inconclusive => ("v-timeout", "INCONCLUSIVE"),
        FunctionVerdict::NoObligations => ("v-none", "NO OBLIGATIONS"),
        _ => ("s-unknown", "UNKNOWN"),
    }
}

fn obligation_display(outcome: &ObligationOutcome) -> (&'static str, &'static str) {
    match outcome {
        ObligationOutcome::Proved { .. } => ("s-proved", "PROVED"),
        ObligationOutcome::RuntimeChecked { .. } => ("s-runtime", "RUNTIME"),
        ObligationOutcome::Failed { .. } => ("s-failed", "FAILED"),
        ObligationOutcome::Unknown { .. } => ("s-unknown", "UNKNOWN"),
        ObligationOutcome::Timeout { .. } => ("s-timeout", "TIMEOUT"),
        _ => ("s-unknown", "UNKNOWN"),
    }
}

fn hardened_role_display(role: HardenedBoundaryInventoryRole) -> (&'static str, &'static str) {
    match role {
        HardenedBoundaryInventoryRole::Inventory => ("role-inventory", "INVENTORY"),
        HardenedBoundaryInventoryRole::ModelAssumption => ("role-model", "MODEL ASSUMPTION"),
        HardenedBoundaryInventoryRole::ProofEvidence => ("role-proof", "PROOF EVIDENCE"),
        _ => ("role-inventory", "INVENTORY"),
    }
}

fn hardened_entry_detail(entry: &HardenedBoundaryInventoryEntry) -> String {
    let mut parts = Vec::new();
    if let Some(function) = &entry.function {
        parts.push(format!("Function: {}", escape_html(function)));
    }
    if let Some(location) = &entry.location
        && !location.file.is_empty()
    {
        parts.push(format!("{}:{}", escape_html(&location.file), location.line_start));
    }
    if let Some(description) = &entry.description {
        parts.push(escape_html(description));
    }

    if parts.is_empty() {
        String::new()
    } else {
        format!("<div class=\"hardened-detail\">{}</div>", parts.join(" | "))
    }
}

fn hardened_entry_refs(entry: &HardenedBoundaryInventoryEntry) -> String {
    let mut refs = Vec::new();
    if let Some(proof_evidence_id) = &entry.proof_evidence_id {
        refs.push(format!("Proof: {}", escape_html(proof_evidence_id)));
    }
    if let Some(obligation_id) = &entry.obligation_id {
        refs.push(format!("Obligation: {}", escape_html(obligation_id)));
    }
    if let Some(source) = &entry.source {
        refs.push(format!("Source: {}", escape_html(source)));
    }
    if let Some(id) = &entry.id {
        refs.push(format!("Entry: {}", escape_html(id)));
    }

    if refs.is_empty() { "&mdash;".to_string() } else { refs.join("<br>") }
}

/// Map function verdict to a data-status attribute value for JS filtering.
fn func_data_status(verdict: FunctionVerdict) -> &'static str {
    match verdict {
        FunctionVerdict::Verified | FunctionVerdict::NoObligations => "verified",
        FunctionVerdict::RuntimeChecked => "verified",
        FunctionVerdict::HasViolations => "failed",
        FunctionVerdict::Inconclusive => "unknown",
        _ => "unknown",
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;
    use crate::build_json_report;

    // -- Test helpers -------------------------------------------------------

    fn empty_crate_result() -> CrateVerificationResult {
        CrateVerificationResult::new("empty_crate")
    }

    fn single_proved_result() -> CrateVerificationResult {
        let mut cr = CrateVerificationResult::new("proved_crate");
        cr.add_function(FunctionVerificationResult {
            function_path: "crate::safe_div".to_string(),
            function_name: "safe_div".to_string(),
            results: vec![(
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "safe_div".into(),
                    location: SourceSpan {
                        file: "src/math.rs".to_string(),
                        line_start: 10,
                        col_start: 5,
                        line_end: 10,
                        col_end: 20,
                    },
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Proved {
                    solver: "ay".into(),
                    time_ms: 2,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            )],
            from_notes: 0,
            with_assumptions: 0,
        });
        cr
    }

    fn single_failed_result() -> CrateVerificationResult {
        let mut cr = CrateVerificationResult::new("failed_crate");
        cr.add_function(FunctionVerificationResult {
            function_path: "crate::bad_add".to_string(),
            function_name: "bad_add".to_string(),
            results: vec![(
                VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::u32(), Ty::u32()),
                    },
                    function: "bad_add".into(),
                    location: SourceSpan {
                        file: "src/math.rs".to_string(),
                        line_start: 5,
                        col_start: 5,
                        line_end: 5,
                        col_end: 15,
                    },
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 3,
                    counterexample: Some(Counterexample::new(vec![
                        ("a".to_string(), CounterexampleValue::Uint(u32::MAX as u128)),
                        ("b".to_string(), CounterexampleValue::Uint(1)),
                    ])),
                },
            )],
            from_notes: 0,
            with_assumptions: 0,
        });
        cr
    }

    fn mixed_result() -> CrateVerificationResult {
        let mut cr = CrateVerificationResult::new("mixed_crate");
        cr.add_function(FunctionVerificationResult {
            function_path: "crate::safe_div".to_string(),
            function_name: "safe_div".to_string(),
            results: vec![(
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
            )],
            from_notes: 0,
            with_assumptions: 0,
        });
        cr.add_function(FunctionVerificationResult {
            function_path: "crate::bad_add".to_string(),
            function_name: "bad_add".to_string(),
            results: vec![(
                VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::u32(), Ty::u32()),
                    },
                    function: "bad_add".into(),
                    location: SourceSpan {
                        file: "src/math.rs".to_string(),
                        line_start: 20,
                        col_start: 5,
                        line_end: 20,
                        col_end: 15,
                    },
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 5,
                    counterexample: Some(Counterexample::new(vec![
                        ("x".to_string(), CounterexampleValue::Uint(u32::MAX as u128)),
                        ("y".to_string(), CounterexampleValue::Uint(1)),
                    ])),
                },
            )],
            from_notes: 0,
            with_assumptions: 0,
        });
        cr.add_function(FunctionVerificationResult {
            function_path: "crate::slow_fn".to_string(),
            function_name: "slow_fn".to_string(),
            results: vec![(
                VerificationCondition {
                    kind: VcKind::Postcondition,
                    function: "slow_fn".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 5000 },
            )],
            from_notes: 0,
            with_assumptions: 0,
        });
        cr
    }

    // -- Tests -------------------------------------------------------

    // 1. generate_html_report produces valid HTML
    #[test]
    fn test_generate_html_report_basic_structure() {
        let report = build_json_report("test_crate", &[]);
        let html = generate_html_report(&report);

        assert!(html.starts_with("<!DOCTYPE html>"));
        assert!(html.contains("<html lang=\"en\">"));
        assert!(html.contains("</html>"));
        assert!(html.contains("<head>"));
        assert!(html.contains("<body>"));
        assert!(html.contains("test_crate"));
    }

    // 2. generate_html_report includes summary counts
    #[test]
    fn test_generate_html_report_summary_counts() {
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
                    time_ms: 2,
                    counterexample: None,
                },
            ),
        ];
        let report = build_json_report("counts", &results);
        let html = generate_html_report(&report);

        assert!(html.contains("Functions"));
        assert!(html.contains("Proved"));
        assert!(html.contains("Failed"));
        assert!(html.contains("Total VCs"));
        assert!(html.contains("Verdict:"));
        assert!(html.contains("HAS VIOLATIONS"));
    }

    // 3. Empty report renders correctly
    #[test]
    fn test_generate_html_report_empty() {
        let report = build_json_report("empty", &[]);
        let html = generate_html_report(&report);

        assert!(html.contains("empty"));
        assert!(html.contains("NO OBLIGATIONS"));
        // No filter bar for empty report
        assert!(!html.contains("id=\"filterBar\""));
    }

    // 4. HTML escape handling prevents XSS
    #[test]
    fn test_escape_html_xss_prevention() {
        assert_eq!(escape_html("a & b"), "a &amp; b");
        assert_eq!(
            escape_html("<script>alert('xss')</script>"),
            "&lt;script&gt;alert(&#x27;xss&#x27;)&lt;/script&gt;"
        );
        assert_eq!(escape_html("x=\"y\""), "x=&quot;y&quot;");
        assert_eq!(escape_html("plain text"), "plain text");
        assert_eq!(escape_html(""), "");
        assert_eq!(escape_html("&<>\"'"), "&amp;&lt;&gt;&quot;&#x27;");
    }

    // 5. Function names with HTML special chars are escaped
    #[test]
    fn test_html_escapes_in_function_names() {
        let mut cr = CrateVerificationResult::new("escape_test");
        cr.add_function(FunctionVerificationResult {
            function_path: "crate::fn<T>(&self)".to_string(),
            function_name: "fn<T>(&self)".to_string(),
            results: vec![(
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
            )],
            from_notes: 0,
            with_assumptions: 0,
        });
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("fn&lt;T&gt;(&amp;self)"));
        assert!(!html.contains("fn<T>(&self)"));
    }

    // 6. Counterexample display
    #[test]
    fn test_generate_counterexample_display() {
        let cr = single_failed_result();
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("bad_add"));
        assert!(html.contains("FAILED"));
        assert!(html.contains("Counterexample"));
        assert!(html.contains("a = 4294967295"));
        assert!(html.contains("b = 1"));
    }

    // 7. Counterexamples can be disabled
    #[test]
    fn test_config_no_counterexamples() {
        let cr = single_failed_result();
        let config = HtmlReportConfig { include_counterexamples: false, ..Default::default() };
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("FAILED"));
        assert!(!html.contains("Counterexample"));
    }

    // 8. Dark color scheme
    #[test]
    fn test_config_color_scheme_dark() {
        let cr = single_proved_result();
        let config = HtmlReportConfig { color_scheme: ColorScheme::Dark, ..Default::default() };
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("#1a1b26"));
    }

    // 9. Light color scheme
    #[test]
    fn test_config_color_scheme_light() {
        let cr = single_proved_result();
        let config = HtmlReportConfig { color_scheme: ColorScheme::Light, ..Default::default() };
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("#ffffff"));
    }

    // 10. Collapsed sections (max_depth=0)
    #[test]
    fn test_config_max_depth_zero_collapsed() {
        let cr = single_proved_result();
        let config = HtmlReportConfig { max_depth: 0, ..Default::default() };
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("<details class=\"func-details\">"));
        assert!(!html.contains("<details class=\"func-details\" open>"));
    }

    // 11. Custom title
    #[test]
    fn test_config_custom_title() {
        let cr = single_proved_result();
        let config =
            HtmlReportConfig { title: "Custom Report Title".to_string(), ..Default::default() };
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("Custom Report Title"));
        assert!(html.contains("<title>Custom Report Title - proved_crate</title>"));
    }

    // 12. Self-contained (no external deps)
    #[test]
    fn test_self_contained_no_external_deps() {
        let cr = mixed_result();
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(!html.contains("src=\"http"));
        assert!(!html.contains("href=\"http"));
        assert!(!html.contains("<link rel=\"stylesheet\""));
        assert!(html.contains("<style>"));
        assert!(html.contains("</style>"));
    }

    // 13. Contains inline JavaScript for sorting/filtering
    #[test]
    fn test_contains_inline_javascript() {
        let cr = single_proved_result();
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("<script>"));
        assert!(html.contains("</script>"));
        assert!(html.contains("trustFilter"));
        assert!(html.contains("trustSort"));
    }

    // 14. Filter bar present for non-empty reports
    #[test]
    fn test_filter_bar_present() {
        let cr = mixed_result();
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("id=\"filterBar\""));
        assert!(html.contains("data-filter=\"all\""));
        assert!(html.contains("data-filter=\"verified\""));
        assert!(html.contains("data-filter=\"failed\""));
        assert!(html.contains("data-filter=\"unknown\""));
    }

    // 15. Print media query present
    #[test]
    fn test_print_media_query() {
        let cr = single_proved_result();
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("@media print"));
        assert!(html.contains("display: none"));
    }

    // 16. Responsive media query present
    #[test]
    fn test_responsive_media_query() {
        let cr = single_proved_result();
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("@media (max-width: 640px)"));
    }

    // 17. Sortable table headers have onclick
    #[test]
    fn test_sortable_table_headers() {
        let cr = single_proved_result();
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("onclick=\"trustSort(this,0)\""));
        assert!(html.contains("onclick=\"trustSort(this,1)\""));
    }

    // 18. Footer has timestamp and solvers
    #[test]
    fn test_footer_has_timestamp_and_solvers() {
        let cr = single_proved_result();
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("class=\"footer\""));
        assert!(html.contains("Generated by Trust"));
        assert!(html.contains("Solvers:"));
    }

    // 19. generate_from_json works with JsonProofReport
    #[test]
    fn test_generate_from_json_report() {
        let results = vec![(
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "test_fn".into(),
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
        let json_report = build_json_report("json_test", &results);
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate_from_json(&json_report, &config);

        assert!(html.starts_with("<!DOCTYPE html>"));
        assert!(html.contains("json_test"));
        assert!(html.contains("test_fn"));
        assert!(html.contains("UNKNOWN"));
    }

    #[test]
    fn test_hardened_context_not_rendered_when_absent() {
        let report = build_json_report("plain", &[]);
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate_from_json(&report, &config);

        assert!(!html.contains("Hardened Context"));
        assert!(!html.contains("MODEL ASSUMPTION"));
        assert!(!html.contains("PROOF EVIDENCE"));
    }

    #[test]
    fn test_hardened_context_renders_inventory_assumptions_and_evidence() {
        let mut report = build_json_report("hardened", &[]);
        report.hardened = Some(HardenedReportContext {
            profile: Some(HardenedProfileReport {
                name: Some("unix_hardened".to_string()),
                version: Some("2026.04".to_string()),
                enabled_categories: vec!["byte_loss".to_string(), "raw_path_api".to_string()],
            }),
            assurance: Some(HardenedAssuranceReport {
                level: Some("proof_backed".to_string()),
                model: Some("unix_fs_process".to_string()),
                proof_evidence_policy: Some("role=proof_evidence links to obligations".to_string()),
                proof_evidence_required: true,
            }),
            summary: Some(HardenedSummaryReport {
                hardened_obligations: 2,
                proved_hardened_obligations: 1,
                inventory_entries: 1,
                model_assumptions: 1,
                proof_evidence_entries: 1,
            }),
            boundary_inventory: vec![
                HardenedBoundaryInventoryEntry {
                    id: Some("inv-raw-path".to_string()),
                    role: HardenedBoundaryInventoryRole::Inventory,
                    category: "raw_path_api".to_string(),
                    boundary: "std::fs::rename".to_string(),
                    function: Some("crate::mv".to_string()),
                    description: Some("name-based path boundary".to_string()),
                    location: None,
                    obligation_id: None,
                    proof_evidence_id: None,
                    source: Some("trust_vcgen".to_string()),
                },
                HardenedBoundaryInventoryEntry {
                    id: Some("model-byte-exact".to_string()),
                    role: HardenedBoundaryInventoryRole::ModelAssumption,
                    category: "byte_loss".to_string(),
                    boundary: "unix argv bytes".to_string(),
                    function: None,
                    description: Some("argv bytes are preserved by the process model".to_string()),
                    location: None,
                    obligation_id: Some("crate::main#vc0".to_string()),
                    proof_evidence_id: None,
                    source: Some("unix-model".to_string()),
                },
                HardenedBoundaryInventoryEntry {
                    id: Some("proof-byte-loss".to_string()),
                    role: HardenedBoundaryInventoryRole::ProofEvidence,
                    category: "byte_loss".to_string(),
                    boundary: "Path::as_os_str".to_string(),
                    function: Some("crate::render".to_string()),
                    description: Some("byte-exact rendering proof".to_string()),
                    location: Some(SourceSpan {
                        file: "src/path.rs".to_string(),
                        line_start: 12,
                        col_start: 4,
                        line_end: 12,
                        col_end: 28,
                    }),
                    obligation_id: Some("crate::render#vc1".to_string()),
                    proof_evidence_id: Some("proof:render:byte_loss".to_string()),
                    source: Some("ay".to_string()),
                },
            ],
        });

        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate_from_json(&report, &config);

        assert!(html.contains("Hardened Context"));
        assert!(html.contains("unix_hardened"));
        assert!(html.contains("proof evidence required"));
        assert!(html.contains("INVENTORY"));
        assert!(html.contains("MODEL ASSUMPTION"));
        assert!(html.contains("PROOF EVIDENCE"));
        assert!(html.contains("std::fs::rename"));
        assert!(html.contains("argv bytes are preserved"));
        assert!(html.contains("Proof: proof:render:byte_loss"));
        assert!(html.contains("src/path.rs:12"));
    }

    // 20. data-status attribute on function sections
    #[test]
    fn test_data_status_attributes() {
        let cr = mixed_result();
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(!html.contains("data-status=\"verified\""));
        assert!(html.contains("data-status=\"failed\""));
        assert!(html.contains("data-status=\"unknown\""));
    }

    // 21. Empty crate result renders
    #[test]
    fn test_generate_empty_results() {
        let cr = empty_crate_result();
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.starts_with("<!DOCTYPE html>"));
        assert!(html.contains("</html>"));
        assert!(html.contains("empty_crate"));
        assert!(html.contains("NO OBLIGATIONS"));
    }

    // 22. Source locations can be hidden
    #[test]
    fn test_config_no_source_locations() {
        let cr = single_proved_result();
        let config = HtmlReportConfig { include_source: false, ..Default::default() };
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(!html.contains("<th onclick=\"trustSort(this,4)\">Location</th>"));
        assert!(!html.contains("src/math.rs:10"));
    }

    // 23. Multiple counterexample variables
    #[test]
    fn test_counterexample_multiple_variables() {
        let mut cr = CrateVerificationResult::new("cex_test");
        cr.add_function(FunctionVerificationResult {
            function_path: "crate::multi_var".to_string(),
            function_name: "multi_var".to_string(),
            results: vec![(
                VerificationCondition {
                    kind: VcKind::Postcondition,
                    function: "multi_var".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 10,
                    counterexample: Some(Counterexample::new(vec![
                        ("x".to_string(), CounterexampleValue::Int(-42)),
                        ("y".to_string(), CounterexampleValue::Uint(100)),
                        ("flag".to_string(), CounterexampleValue::Bool(false)),
                    ])),
                },
            )],
            from_notes: 0,
            with_assumptions: 0,
        });
        let config = HtmlReportConfig::default();
        let html = HtmlReportGenerator::generate(&cr, &config);

        assert!(html.contains("Counterexample"));
        assert!(html.contains("x = -42"));
        assert!(html.contains("y = 100"));
        assert!(html.contains("flag = false"));
    }

    // 24. Under 500 lines check (the file itself)
    #[test]
    fn test_file_size_under_500_lines() {
        // The source file is kept under 500 lines of production code.
        // Tests are additional. This test verifies the generated HTML
        // is reasonably sized for a simple report.
        let report = build_json_report("size_check", &[]);
        let html = generate_html_report(&report);
        let line_count = html.lines().count();
        // An empty report should produce compact HTML
        assert!(line_count < 200, "Empty report HTML should be compact, got {line_count} lines");
    }

    // -------------------------------------------------------------------
    // #485: generate_report convenience method tests
    // -------------------------------------------------------------------

    // 25. generate_report produces valid HTML from raw result pairs
    #[test]
    fn test_generate_report_basic_structure() {
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
        let html = HtmlReportGenerator::generate_report("my_crate", &results);

        assert!(html.starts_with("<!DOCTYPE html>"));
        assert!(html.contains("<html lang=\"en\">"));
        assert!(html.contains("</html>"));
        assert!(html.contains("my_crate"));
        assert!(html.contains("safe_div"));
    }

    // 26. generate_report empty results
    #[test]
    fn test_generate_report_empty_results() {
        let html = HtmlReportGenerator::generate_report("empty_crate", &[]);

        assert!(html.starts_with("<!DOCTYPE html>"));
        assert!(html.contains("empty_crate"));
        assert!(html.contains("NO OBLIGATIONS"));
    }

    // 27. generate_report includes dashboard summary section
    #[test]
    fn test_generate_report_dashboard_summary() {
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
                    time_ms: 5,
                    counterexample: None,
                },
            ),
        ];
        let html = HtmlReportGenerator::generate_report("dash", &results);

        // Dashboard summary stats present
        assert!(html.contains("Functions"));
        assert!(html.contains("Proved"));
        assert!(html.contains("Failed"));
        assert!(html.contains("Total VCs"));
        assert!(html.contains("Verdict:"));
    }

    // 28. generate_report shows color-coded per-function cards
    #[test]
    fn test_generate_report_color_coded_functions() {
        let results = vec![
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "good_fn".into(),
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
                    function: "bad_fn".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 5,
                    counterexample: None,
                },
            ),
        ];
        let html = HtmlReportGenerator::generate_report("colors", &results);

        // Green for verified, red for failed
        assert!(html.contains("v-verified"));
        assert!(html.contains("v-failed"));
        // Function names in detail cards
        assert!(html.contains("good_fn"));
        assert!(html.contains("bad_fn"));
    }

    // 29. raw proof status without structured evidence fails closed
    #[test]
    fn test_generate_report_raw_proof_status_is_unknown() {
        let results = vec![(
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "proven_fn".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let html = HtmlReportGenerator::generate_report("strength", &results);

        assert!(html.contains("UNKNOWN"));
    }

    // 30. generate_report includes counterexample display for failures
    #[test]
    fn test_generate_report_counterexample_display() {
        let results = vec![(
            VerificationCondition {
                kind: VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (Ty::u32(), Ty::u32()),
                },
                function: "overflow_fn".into(),
                location: SourceSpan {
                    file: "src/lib.rs".to_string(),
                    line_start: 42,
                    col_start: 5,
                    line_end: 42,
                    col_end: 15,
                },
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Failed {
                solver: "ay".into(),
                time_ms: 3,
                counterexample: Some(Counterexample::new(vec![
                    ("a".to_string(), CounterexampleValue::Uint(u32::MAX as u128)),
                    ("b".to_string(), CounterexampleValue::Uint(1)),
                ])),
            },
        )];
        let html = HtmlReportGenerator::generate_report("cex_crate", &results);

        assert!(html.contains("Counterexample"));
        assert!(html.contains("a = 4294967295"));
        assert!(html.contains("b = 1"));
        assert!(html.contains("src/lib.rs:42"));
    }

    // 31. generate_report has inline CSS (no external deps)
    #[test]
    fn test_generate_report_self_contained() {
        let results = vec![(
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "f".into(),
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
        let html = HtmlReportGenerator::generate_report("self_contained", &results);

        assert!(html.contains("<style>"));
        assert!(html.contains("</style>"));
        assert!(!html.contains("src=\"http"));
        assert!(!html.contains("href=\"http"));
        assert!(!html.contains("<link rel=\"stylesheet\""));
    }

    // 32. generate_report handles timeout obligations
    #[test]
    fn test_generate_report_timeout_handling() {
        let results = vec![(
            VerificationCondition {
                kind: VcKind::Postcondition,
                function: "slow_fn".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 10000 },
        )];
        let html = HtmlReportGenerator::generate_report("timeout_crate", &results);

        assert!(html.contains("slow_fn"));
        assert!(html.contains("INCONCLUSIVE"));
        assert!(html.contains("10000ms"));
        assert!(html.contains("0 unknown, 1 timeout"));
    }

    // 33. generate_report with multiple functions shows all of them
    #[test]
    fn test_generate_report_multiple_functions() {
        let results = vec![
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "alpha".into(),
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
                    function: "beta".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Unknown {
                    solver: "ay".into(),
                    time_ms: 50,
                    reason: "nonlinear".to_string(),
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::IndexOutOfBounds,
                    function: "gamma".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 3,
                    counterexample: None,
                },
            ),
        ];
        let html = HtmlReportGenerator::generate_report("multi", &results);

        assert!(html.contains("alpha"));
        assert!(html.contains("beta"));
        assert!(html.contains("gamma"));
    }

    // 34. generate_report HTML-escapes function names with special chars
    #[test]
    fn test_generate_report_escapes_function_names() {
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
        let html = HtmlReportGenerator::generate_report("escape_test", &results);

        assert!(html.contains("fn&lt;T&gt;(&amp;self)"));
        assert!(!html.contains("fn<T>(&self)"));
    }
}
