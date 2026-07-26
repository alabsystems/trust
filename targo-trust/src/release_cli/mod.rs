mod gates;
mod identity;
mod product_proof;
mod product_proof_catalog;
mod publication;
mod seed;
mod trustd_evidence;
mod types;

use std::path::PathBuf;
use std::process::ExitCode;

use trust_release::{AggregateReport, GateFinding, GateReport};

use self::gates::{build_release_reports, build_toolchain_surface_proof};
use self::identity::{
    build_version_identity, discover_repo_root, generated_at_unix_seconds, option_value,
    repo_dirty, repo_dirty_metadata,
};
use self::product_proof::{
    product_proof_components, product_proof_evidence_classes, run_product_proof_report_subcommand,
    run_product_proof_stub_subcommand,
};
use self::trustd_evidence::run_collect_trustd_evidence_subcommand;
use self::types::{
    CANDIDATE_COMMAND_VERSION, RELEASE_REPORT_SCHEMA, ReleaseCheckOutput, ReleaseEvidenceMode,
    ReleaseEvidenceSemantics, ReleaseProfile, ReleaseRunner, ReleaseVisibility,
};

fn release_gate_filter_includes(
    profile: ReleaseProfile,
    visibility: ReleaseVisibility,
    filter: &str,
    gate: &str,
) -> bool {
    gate == filter
        || (profile.requires_bound_tools()
            && matches!(
                gate,
                "required-metadata"
                    | "version-identity"
                    | "bound-tool-files"
                    | "toolchain-surface-sysroot"
                    | "tool-names"
                    | "owned-deps"
                    | "seed-freshness"
            ))
        || (profile == ReleaseProfile::ProductProof
            && matches!(gate, "trust-extra" | "product-proof-coverage"))
        || (visibility == ReleaseVisibility::Public
            && matches!(profile, ReleaseProfile::Publication | ReleaseProfile::ProductProof)
            && matches!(
                gate,
                "publication-inputs" | "publication-artifacts" | "publication-ledger"
            ))
}

pub(crate) fn run_version_subcommand(args: &[String]) -> ExitCode {
    let mut json = false;
    let mut repo_root = None;

    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--json" => json = true,
            "--format" => match iter.next().map(String::as_str) {
                Some("json") => json = true,
                Some("terminal" | "text") => json = false,
                Some(other) => {
                    eprintln!("targo trust version: unsupported format `{other}`");
                    return ExitCode::from(2);
                }
                None => {
                    eprintln!("targo trust version: --format requires a value");
                    return ExitCode::from(2);
                }
            },
            "--repo-root" => match iter.next() {
                Some(path) => repo_root = Some(PathBuf::from(path)),
                None => {
                    eprintln!("targo trust version: --repo-root requires a path");
                    return ExitCode::from(2);
                }
            },
            "--help" | "-h" => {
                print!("{}", version_usage_text());
                return ExitCode::SUCCESS;
            }
            other => {
                if let Some(format) = option_value(other, "--format") {
                    match format {
                        "json" => json = true,
                        "terminal" | "text" => json = false,
                        _ => {
                            eprintln!("targo trust version: unsupported format `{format}`");
                            return ExitCode::from(2);
                        }
                    }
                    continue;
                }
                if let Some(path) = option_value(other, "--repo-root") {
                    repo_root = Some(PathBuf::from(path));
                    continue;
                }
                eprintln!("targo trust version: unknown option `{other}`");
                eprint!("{}", version_usage_text());
                return ExitCode::from(2);
            }
        }
    }

    let identity = match build_version_identity(repo_root.as_deref()) {
        Ok(identity) => identity,
        Err(err) => {
            eprintln!("targo trust version: {err}");
            return ExitCode::from(2);
        }
    };

    if json {
        match identity.render_json_pretty() {
            Ok(text) => println!("{text}"),
            Err(err) => {
                eprintln!("targo trust version: failed to render JSON: {err}");
                return ExitCode::from(2);
            }
        }
    } else {
        print!("{}", identity.render_text());
    }

    ExitCode::SUCCESS
}

pub(crate) fn run_release_subcommand(args: &[String]) -> ExitCode {
    let Some(command) = args.first().map(String::as_str) else {
        eprint!("{}", release_usage_text());
        return ExitCode::from(2);
    };

    if matches!(command, "--help" | "-h" | "help") {
        print!("{}", release_usage_text());
        return ExitCode::SUCCESS;
    }

    if command == "product-proof-stub" {
        return run_product_proof_stub_subcommand(&args[1..]);
    }
    if command == "product-proof-report" {
        return run_product_proof_report_subcommand(&args[1..]);
    }
    if command == "collect-trustd-evidence" {
        return run_collect_trustd_evidence_subcommand(&args[1..]);
    }

    if command != "check" {
        if let Some(exit_code) = crate::script_cli::try_run_release_script_subcommand(args) {
            return exit_code;
        }
        eprintln!("targo trust release: unknown subcommand `{command}`");
        eprint!("{}", release_usage_text());
        return ExitCode::from(2);
    }

    let mut json = false;
    let mut profile = ReleaseProfile::Metadata;
    let mut visibility = ReleaseVisibility::Private;
    let mut visibility_explicit = false;
    let mut repo_root = None;
    let mut gate_filter: Option<String> = None;

    let mut iter = args[1..].iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--json" => json = true,
            "--format" => match iter.next().map(String::as_str) {
                Some("json") => json = true,
                Some("terminal" | "text") => json = false,
                Some(other) => {
                    eprintln!("targo trust release check: unsupported format `{other}`");
                    return ExitCode::from(2);
                }
                None => {
                    eprintln!("targo trust release check: --format requires a value");
                    return ExitCode::from(2);
                }
            },
            "--profile" => match iter.next().map(String::as_str).and_then(ReleaseProfile::parse) {
                Some(parsed) => profile = parsed,
                None => {
                    eprintln!(
                        "targo trust release check: --profile must be metadata, publication, or product-proof"
                    );
                    return ExitCode::from(2);
                }
            },
            "--visibility" => {
                match iter.next().map(String::as_str).and_then(ReleaseVisibility::parse) {
                    Some(parsed) => {
                        visibility = parsed;
                        visibility_explicit = true;
                    }
                    None => {
                        eprintln!(
                            "targo trust release check: --visibility must be private or public"
                        );
                        return ExitCode::from(2);
                    }
                }
            }
            "--audience" => {
                eprintln!(
                    "targo trust release check: --audience has been removed; use --visibility"
                );
                return ExitCode::from(2);
            }
            "--private" => return removed_visibility_alias("--private", "private"),
            "--public" => return removed_visibility_alias("--public", "public"),
            "--repo-root" => match iter.next() {
                Some(path) => repo_root = Some(PathBuf::from(path)),
                None => {
                    eprintln!("targo trust release check: --repo-root requires a path");
                    return ExitCode::from(2);
                }
            },
            "--gate" => match iter.next() {
                Some(gate) => gate_filter = Some(gate.clone()),
                None => {
                    eprintln!("targo trust release check: --gate requires a gate name");
                    return ExitCode::from(2);
                }
            },
            "--help" | "-h" => {
                print!("{}", release_usage_text());
                return ExitCode::SUCCESS;
            }
            other => {
                if let Some(format) = option_value(other, "--format") {
                    match format {
                        "json" => json = true,
                        "terminal" | "text" => json = false,
                        _ => {
                            eprintln!("targo trust release check: unsupported format `{format}`");
                            return ExitCode::from(2);
                        }
                    }
                    continue;
                }
                if let Some(value) = option_value(other, "--profile") {
                    match ReleaseProfile::parse(value) {
                        Some(parsed) => profile = parsed,
                        None => {
                            eprintln!(
                                "targo trust release check: --profile must be metadata, publication, or product-proof"
                            );
                            return ExitCode::from(2);
                        }
                    }
                    continue;
                }
                if let Some(value) = option_value(other, "--visibility") {
                    match ReleaseVisibility::parse(value) {
                        Some(parsed) => {
                            visibility = parsed;
                            visibility_explicit = true;
                        }
                        None => {
                            eprintln!(
                                "targo trust release check: --visibility must be private or public"
                            );
                            return ExitCode::from(2);
                        }
                    }
                    continue;
                }
                if option_value(other, "--audience").is_some() {
                    eprintln!(
                        "targo trust release check: --audience has been removed; use --visibility"
                    );
                    return ExitCode::from(2);
                }
                if let Some(path) = option_value(other, "--repo-root") {
                    repo_root = Some(PathBuf::from(path));
                    continue;
                }
                if let Some(gate) = option_value(other, "--gate") {
                    gate_filter = Some(gate.to_string());
                    continue;
                }
                eprintln!("targo trust release check: unknown option `{other}`");
                eprint!("{}", release_usage_text());
                return ExitCode::from(2);
            }
        }
    }

    if profile == ReleaseProfile::Publication
        && (!visibility_explicit || visibility != ReleaseVisibility::Public)
    {
        eprintln!(
            "targo trust release check: --profile publication requires explicit --visibility public"
        );
        return ExitCode::from(2);
    }

    let root = match discover_repo_root(repo_root.as_deref()) {
        Ok(root) => root,
        Err(err) => {
            eprintln!("targo trust release check: failed to resolve repo root: {err}");
            return ExitCode::from(2);
        }
    };
    let identity = match build_version_identity(Some(&root)) {
        Ok(identity) => identity,
        Err(err) => {
            eprintln!("targo trust release check: {err}");
            return ExitCode::from(2);
        }
    };

    let all_reports = build_release_reports(&root, profile, visibility, &identity);
    let mut reports = all_reports.clone();
    if let Some(filter) = gate_filter.as_deref() {
        if all_reports.iter().any(|report| report.gate == filter) {
            reports = all_reports
                .iter()
                .filter(|report| {
                    release_gate_filter_includes(profile, visibility, filter, &report.gate)
                })
                .cloned()
                .collect();
        } else {
            reports = vec![GateReport::new(
                "gate-filter",
                vec![GateFinding::error(
                    "unknown-gate",
                    format!("no release gate named `{filter}`"),
                )],
            )];
        }
    }

    let aggregate = AggregateReport::new(reports.clone());
    let evidence_mode = ReleaseEvidenceMode::for_release_check(profile, visibility);
    let tools = identity.tools.clone();
    let toolchain_surface_proof = build_toolchain_surface_proof(&identity.tools);
    let product_proof_evidence_classes = if profile == ReleaseProfile::ProductProof {
        product_proof_evidence_classes(&root, &all_reports)
    } else {
        Vec::new()
    };
    let product_proof_components = if profile == ReleaseProfile::ProductProof {
        product_proof_components(
            &root,
            identity.candidate_commit.as_deref(),
            Some(&identity.tools.daemon),
        )
    } else {
        Vec::new()
    };
    let output = ReleaseCheckOutput {
        schema_version: RELEASE_REPORT_SCHEMA,
        generated_at: generated_at_unix_seconds(),
        profile,
        visibility,
        evidence_mode,
        release_evidence: ReleaseEvidenceSemantics::for_mode(evidence_mode),
        status: aggregate.status(),
        exit_code_kind: aggregate.exit_code_kind(),
        candidate_commit: identity.candidate_commit.clone(),
        repo_root: root.display().to_string(),
        gate_filter,
        repo_dirty: repo_dirty(&root),
        repo_dirty_metadata: repo_dirty_metadata(&root),
        runner: ReleaseRunner {
            implementation: "rust",
            entrypoint: "targo trust release check",
            python_used: false,
            tool: "targo-trust",
            kind: identity.runner_kind.clone(),
        },
        runner_kind: identity.runner_kind.clone(),
        candidate_command: "targo trust release check",
        candidate_command_version: CANDIDATE_COMMAND_VERSION,
        tools,
        toolchain_surface_proof,
        version_identity: identity,
        reports,
        product_proof_evidence_classes,
        product_proof_components,
    };

    if json {
        match serde_json::to_string_pretty(&output) {
            Ok(text) => println!("{text}"),
            Err(err) => {
                eprintln!("targo trust release check: failed to render JSON: {err}");
                return ExitCode::from(2);
            }
        }
    } else {
        print_release_text(&output);
    }

    ExitCode::from(output.exit_code_kind.as_i32() as u8)
}

fn removed_visibility_alias(alias: &str, visibility: &str) -> ExitCode {
    eprintln!("targo trust release check: {alias} has been removed; use --visibility {visibility}");
    ExitCode::from(2)
}

fn print_release_text(output: &ReleaseCheckOutput) {
    println!(
        "Trust release check {} [{}]: {:?}",
        output.profile.label(),
        output.visibility.label(),
        output.status
    );
    println!("schema: {}", output.schema_version);
    println!("evidence mode: {}", output.evidence_mode.label());
    println!("release evidence claim: {}", output.release_evidence.claim);
    println!("release evidence reason: {}", output.release_evidence.reason);
    if let Some(commit) = &output.candidate_commit {
        println!("candidate: {commit}");
    }
    println!("runner: {}", output.runner_kind);
    println!("exit: {:?}", output.exit_code_kind);
    for report in &output.reports {
        println!("- {}: {:?} ({} findings)", report.gate, report.status, report.findings.len());
        for finding in report.findings.iter().take(5) {
            println!("  {}: {}", finding.code, finding.message);
        }
        if report.findings.len() > 5 {
            println!("  ... {} more", report.findings.len() - 5);
        }
    }
}

fn version_usage_text() -> &'static str {
    "Usage: targo trust version [--json] [--repo-root <path>]\n\nEmits bound identity for the complete Trust toolchain, including trustc, targo, targo-trust, and trustd.\n"
}

fn release_usage_text() -> String {
    let mut text = String::from(
        "Usage: targo trust release check --profile metadata|publication|product-proof [--visibility private|public] [--json] [--repo-root <path>] [--gate <name>]\n       targo trust release collect-trustd-evidence --candidate-commit <40-hex> [--repo-root <path>] [--out <ignored-repo-relative-json>] [--json]\n       targo trust release product-proof-stub --candidate-commit <40-hex> --evidence-kind <compile-back-kind> --artifact <digest-field=repo-relative-path> [--selected-image-range <start>..<end>] [--stage2-trustc <repo-relative-path>] [--source-tarball <repo-relative-path>] [--out <repo-relative-json>] [--report-out <repo-relative-json>] [--certificate-out <repo-relative-json>] [--manifest-out <repo-relative-toml>]\n       targo trust release product-proof-report --candidate-commit <40-hex> --evidence <repo-relative-json> [--out <repo-relative-json>]\nPublication profile requires explicit --visibility public.\n",
    );
    text.push_str(crate::script_cli::release_script_usage_text());
    text.push('\n');
    text
}

#[cfg(test)]
mod tests;
