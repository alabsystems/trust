use std::path::Path;

use super::evaluate::{hardened_finding_label, is_hardened_kind};
use super::report::LabReport;

pub(super) fn print_terminal_report(report: &LabReport) {
    println!("Trust hardened lab");
    println!("  manifest: {}", report.manifest_path);
    println!("  analyzer: {}", report.analyzer);
    println!("  raw JSON: {}", report.raw_analyzer_command);
    println!();
    println!(
        "  files: {}  functions: {}  hardened findings: {}  claims: {}/{}  walkthroughs: {}/{}",
        report.summary.files_analyzed,
        report.summary.functions_found,
        report.summary.hardened_vcs,
        report.summary.claims_passed,
        report.summary.claims_total,
        report.summary.walkthroughs_passed,
        report.summary.walkthroughs_total
    );
    println!();

    for claim in &report.claims {
        let status = if claim.passed { "PASS" } else { "FAIL" };
        println!("  [{status}] {} / {} [{}]", claim.id, claim.category, claim.report_label);
        println!("        {}", claim.title);
        println!("        binding: {}", claim.standalone_binding);
        if let Some(first) = claim.matches.first() {
            println!("        match: {}:{}: {}", first.file, first.function, first.description);
        } else if let Some(message) = &claim.failure_message {
            println!("        missing: {message}");
        }
        for evidence in &claim.walkthrough_evidence {
            let evidence_status = if evidence.passed { "pass" } else { "fail" };
            let requirements = evidence
                .requirements
                .iter()
                .map(|requirement| format!("{}={}", requirement.key, requirement.value))
                .collect::<Vec<_>>()
                .join(", ");
            println!(
                "        walkthrough: {} [{evidence_status}] requires {requirements}",
                evidence.bin
            );
            if let Some(message) = &evidence.failure_message {
                println!("        walkthrough missing: {message}");
            }
        }
    }

    println!();
    println!("Rootless walkthrough executions:");
    if report.walkthroughs.is_empty() {
        println!("  [FAIL] no walkthrough bins discovered under the example crate's src/bin");
    }
    for walkthrough in &report.walkthroughs {
        let status = if walkthrough.success { "PASS" } else { "FAIL" };
        println!("  [{status}] {} ({})", walkthrough.bin, walkthrough.status);
        println!("        source: {}", walkthrough.source);
        println!("        command: {}", walkthrough.command);
        println!(
            "        process: {}  transcript: {}",
            if walkthrough.process_success { "pass" } else { "fail" },
            if walkthrough.transcript_passed { "pass" } else { "fail" }
        );
        for error in &walkthrough.transcript_errors {
            println!("        transcript error: {error}");
        }
        print_prefixed_output("stdout", &walkthrough.stdout);
        print_prefixed_output("stderr", &walkthrough.stderr);
    }

    println!();
    match (report.claims_passed, report.walkthroughs_passed) {
        (true, true) => {
            println!(
                "All advertised hardened lab claims were found and all rootless walkthroughs ran."
            );
        }
        (false, true) => println!("One or more advertised hardened lab claims were not found."),
        (true, false) => println!("One or more rootless walkthroughs did not run successfully."),
        (false, false) => {
            println!("One or more advertised hardened lab claims and rootless walkthroughs failed.")
        }
    }

    if let Some(vcs) = &report.vcs {
        println!();
        println!("Underlying hardened analyzer findings:");
        for vc in vcs {
            if !is_hardened_kind(vc.kind) {
                continue;
            }
            if let Some(label) = hardened_finding_label(vc.kind) {
                println!(
                    "  [{label} via {:?}] {}:{}: {}",
                    vc.kind,
                    display_path(&vc.file),
                    vc.function,
                    vc.description
                );
            } else {
                println!(
                    "  [{:?}] {}:{}: {}",
                    vc.kind,
                    display_path(&vc.file),
                    vc.function,
                    vc.description
                );
            }
        }
    }
}

fn print_prefixed_output(label: &str, output: &str) {
    if output.is_empty() {
        println!("        {label}: <empty>");
        return;
    }

    println!("        {label}:");
    for line in output.lines() {
        println!("          {line}");
    }
}

pub(super) fn print_usage() {
    println!(
        "\
Usage: targo trust hardened-lab [options]

Run the hardened example corpus through the real standalone hardened analyzer
and its rootless walkthrough binaries. Fail unless every advertised hardened
claim has matching analyzer output and matching walkthrough transcript evidence.

Options:
  --manifest-path <path>  Analyze a specific hardened example Cargo.toml
  --format <terminal|json>  Output format (terminal default)
  --json                  Alias for --format json
  --show-vcs              Include raw analyzer VCs in terminal/JSON output
  --help                  Show this help

Examples:
  targo trust hardened-lab
  targo trust hardened-lab --format json --show-vcs
  targo trust hardened-lab --manifest-path examples/hardened/Cargo.toml
"
    );
}

pub(super) fn display_path(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}
