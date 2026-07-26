// Explicit non-proof source-audit renderer.
//
// Runs source_analysis without invoking the compiler and renders an explicitly
// non-proof SourceAnalysisSummary as terminal text or JSON.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

use serde::Serialize;

use crate::cli::SubcommandArgs;
use crate::source_analysis;
use crate::types::OutputFormat;

#[derive(Serialize)]
struct SourceAuditJsonReport<'a> {
    schema_version: &'static str,
    mode: &'static str,
    proof_authority: &'static str,
    compiler_verification_performed: bool,
    audit_passed: bool,
    duration_ms: u64,
    #[serde(flatten)]
    summary: &'a source_analysis::SourceAnalysisSummary,
}

/// Run a source audit without invoking the compiler or claiming proof authority.
pub(crate) fn run_standalone_check(sub_args: &SubcommandArgs, crate_root: &Path) -> ExitCode {
    if matches!(sub_args.format, OutputFormat::Html) {
        eprintln!(
            "targo trust: standalone check does not support HTML output; use terminal or json"
        );
        return ExitCode::from(2);
    }
    let start = Instant::now();

    let summary = if sub_args.is_single_file {
        let file = PathBuf::from(
            sub_args.single_file_path().expect("single-file mode should have a file path"),
        );
        if !file.exists() {
            eprintln!("targo trust: error: file not found: {}", file.display());
            return ExitCode::from(2);
        }
        eprintln!("targo trust: standalone analysis of {}", file.display());
        source_analysis::analyze_file_with_options(
            &file,
            source_analysis::SourceAnalysisOptions { hardened: sub_args.hardened },
        )
    } else {
        eprintln!("targo trust: standalone analysis of crate at {}", crate_root.display());
        source_analysis::analyze_crate_with_options(
            crate_root,
            source_analysis::SourceAnalysisOptions { hardened: sub_args.hardened },
        )
    };

    let duration_ms = start.elapsed().as_millis() as u64;

    if let Err(error) = validate_source_audit_identities(&summary) {
        eprintln!("targo trust: source audit rejected: {error}");
        return ExitCode::from(2);
    }

    let render_result = match sub_args.format {
        OutputFormat::Json => render_standalone_json(&summary, duration_ms),
        OutputFormat::Terminal => {
            render_standalone_terminal(&summary, duration_ms);
            Ok(())
        }
        OutputFormat::Html => unreachable!("HTML rejected before standalone rendering"),
    };
    if let Err(error) = render_result {
        eprintln!("targo trust: failed to render source-audit report: {error}");
        return ExitCode::from(2);
    }

    if standalone_audit_passed(&summary) { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

fn standalone_audit_passed(summary: &source_analysis::SourceAnalysisSummary) -> bool {
    // The standalone lane is a SOURCE AUDIT (`proof_authority: "none"`,
    // `compiler_verification_performed: false`): its exit signals "inventory
    // complete, no failed checks", never proof. `Unknown` rows are inventory
    // OBSERVATIONS — `UnspecifiedPublicApi` (a public fn without specs) and
    // `UnsafeFunction` (an unsafe fn awaiting its safety proof) — facts a
    // no-authority audit reports but cannot adjudicate; they stay visible in
    // the report/JSON for consumers. Requiring `unknown == 0` here made every
    // crate with an unspecified public fn exit 1, which the basic-contracts
    // e2e pins as wrong (its corpus deliberately carries unspecified functions
    // and requires audit exit 0 with `failed == 0`). `Failed` rows (hardened
    // source rules) still fail the audit.
    summary.total_audit_rows > 0 && summary.failed == 0
}

fn validate_source_audit_identities(
    summary: &source_analysis::SourceAnalysisSummary,
) -> Result<(), String> {
    for path in summary
        .functions
        .iter()
        .map(|function| &function.file)
        .chain(summary.vcs.iter().map(|row| &row.file))
    {
        let path = path.to_str().ok_or_else(|| "source path is not UTF-8".to_string())?;
        if path.chars().any(char::is_control) {
            return Err("source path contains a control character".to_string());
        }
    }
    Ok(())
}

fn render_standalone_terminal(summary: &source_analysis::SourceAnalysisSummary, duration_ms: u64) {
    eprintln!();
    eprintln!("=== Trust Non-Proof Source Audit ===");
    eprintln!(
        "Mode: source-audit | Proof authority: NONE | Compiler verification: NOT RUN | Duration: {}ms",
        duration_ms
    );
    eprintln!();
    eprintln!("Files analyzed:      {}", summary.files_analyzed);
    eprintln!("Functions found:     {}", summary.functions_found);
    eprintln!("  Public:            {}", summary.public_functions);
    eprintln!("  Unsafe:            {}", summary.unsafe_functions);
    eprintln!("  With specs:        {}", summary.specified_functions);
    eprintln!();

    if summary.vcs.is_empty() {
        eprintln!("  No source-audit rows generated.");
    } else {
        for vc in &summary.vcs {
            let icon = match vc.outcome {
                source_analysis::StandaloneOutcome::Present => "PRESENT",
                source_analysis::StandaloneOutcome::Failed => "FAILED",
                source_analysis::StandaloneOutcome::Unknown => "UNKNOWN",
            };
            let kind_str = match vc.kind {
                source_analysis::VcKind::PreconditionPresent => "requires",
                source_analysis::VcKind::PostconditionPresent => "ensures",
                source_analysis::VcKind::UnsafeFunction => "unsafe",
                source_analysis::VcKind::UnspecifiedPublicApi => "no-spec",
                source_analysis::VcKind::HardenedRawPathApi => "hardened:path",
                source_analysis::VcKind::HardenedPathIdentity => "hardened:path-identity",
                source_analysis::VcKind::HardenedPermissionChange => "hardened:permission-change",
                source_analysis::VcKind::HardenedPermissionCreate => "hardened:permission-create",
                source_analysis::VcKind::HardenedPermissionWindow => "hardened:permission-window",
                source_analysis::VcKind::HardenedByteLoss => "hardened:bytes",
                source_analysis::VcKind::HardenedUtf8Boundary => "hardened:utf8",
                source_analysis::VcKind::HardenedErrorDiscard => "hardened:error",
                source_analysis::VcKind::HardenedPanic => "hardened:panic",
                source_analysis::VcKind::HardenedTrustBoundary => "hardened:trust",
                source_analysis::VcKind::HardenedTrustDomainOrder => "hardened:trust-order",
                source_analysis::VcKind::HardenedCompatibility => "hardened:compat",
                source_analysis::VcKind::HardenedProcessSemantics => "hardened:process",
                source_analysis::VcKind::HardenedUnsafeOperation => "hardened:unsafe",
                source_analysis::VcKind::HardenedFfiBoundary => "hardened:ffi",
            };
            eprintln!("  [{icon}] [{kind_str}] {}", vc.description);
            if vc.outcome == source_analysis::StandaloneOutcome::Failed {
                if let Some(help) = standalone_hardened_help(vc.kind) {
                    eprintln!("    help: {help}");
                }
            }
        }
    }

    eprintln!();
    eprintln!(
        "Summary: {} source facts present, {} failed checks, {} unknown checks ({} total audit rows)",
        summary.present, summary.failed, summary.unknown, summary.total_audit_rows
    );
    let status = if standalone_audit_passed(summary) { "PASS" } else { "FAIL" };
    eprintln!("Audit result: {status} (non-proof; run canonical trustc for verification)");
    eprintln!("=============================================");
}

pub(super) fn standalone_hardened_help(kind: source_analysis::VcKind) -> Option<&'static str> {
    match kind {
        source_analysis::VcKind::HardenedRawPathApi => {
            Some("use a verified dirfd/handle-relative wrapper and carry identity evidence")
        }
        source_analysis::VcKind::HardenedPathIdentity => {
            Some("compare stable file identity from handles/metadata, not path strings")
        }
        source_analysis::VcKind::HardenedPermissionChange => {
            Some("change permissions through a verified handle and prove target identity")
        }
        source_analysis::VcKind::HardenedPermissionCreate => {
            Some("create under a trusted parent with explicit mode and umask accounting")
        }
        source_analysis::VcKind::HardenedPermissionWindow => {
            Some("create with final mode/owner atomically or keep the object private until fixed")
        }
        source_analysis::VcKind::HardenedByteLoss => {
            Some("keep boundary data as bytes/OsStr and make lossy conversion explicit")
        }
        source_analysis::VcKind::HardenedUtf8Boundary => {
            Some("accept bytes/OsStr at Unix boundaries or prove UTF-8 before conversion")
        }
        source_analysis::VcKind::HardenedErrorDiscard => {
            Some("propagate the Result or record an explicit checked-discard policy")
        }
        source_analysis::VcKind::HardenedPanic => {
            Some("return a checked error or prove the unwrap/panic precondition")
        }
        source_analysis::VcKind::HardenedTrustBoundary => {
            Some("resolve trusted inputs before root/privilege changes and model the new domain")
        }
        source_analysis::VcKind::HardenedTrustDomainOrder => Some(
            "move NSS/dlopen lookups before the domain transition or prove the later source trusted",
        ),
        source_analysis::VcKind::HardenedCompatibility => {
            Some("model OsString/byte CLI inputs and document compatibility differences")
        }
        source_analysis::VcKind::HardenedProcessSemantics => {
            Some("define SIGPIPE/broken-pipe behavior and handle stdio write errors")
        }
        source_analysis::VcKind::HardenedUnsafeOperation => {
            Some("wrap unsafe code in an audited API with stated invariants")
        }
        source_analysis::VcKind::HardenedFfiBoundary => {
            Some("state ABI, ownership, lifetime, and trust assumptions for the extern boundary")
        }
        source_analysis::VcKind::PreconditionPresent
        | source_analysis::VcKind::PostconditionPresent
        | source_analysis::VcKind::UnsafeFunction
        | source_analysis::VcKind::UnspecifiedPublicApi => None,
    }
}

fn render_standalone_json(
    summary: &source_analysis::SourceAnalysisSummary,
    duration_ms: u64,
) -> Result<(), String> {
    let report = SourceAuditJsonReport {
        schema_version: "trust.source-audit.v1",
        mode: "source-audit",
        proof_authority: "none",
        compiler_verification_performed: false,
        audit_passed: standalone_audit_passed(summary),
        duration_ms,
        summary,
    };
    let json = serde_json::to_string_pretty(&report)
        .map_err(|error| format!("JSON serialization failed: {error}"))?;
    println!("{json}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_envelope_cannot_impersonate_compiler_proof() {
        let summary = source_analysis::SourceAnalysisSummary {
            files_analyzed: 0,
            functions_found: 0,
            public_functions: 0,
            unsafe_functions: 0,
            specified_functions: 0,
            total_audit_rows: 0,
            present: 0,
            failed: 0,
            unknown: 0,
            functions: Vec::new(),
            vcs: Vec::new(),
        };
        let value = serde_json::to_value(SourceAuditJsonReport {
            schema_version: "trust.source-audit.v1",
            mode: "source-audit",
            proof_authority: "none",
            compiler_verification_performed: false,
            audit_passed: standalone_audit_passed(&summary),
            duration_ms: 0,
            summary: &summary,
        })
        .expect("source-audit envelope serializes");

        assert_eq!(value["proof_authority"], "none");
        assert_eq!(value["compiler_verification_performed"], false);
        assert_eq!(value["audit_passed"], false);
        assert!(value.get("proved").is_none());
        assert!(value.get("vcs").is_none());
        assert!(value.get("audit_rows").is_some());
    }

    #[cfg(unix)]
    #[test]
    fn non_utf8_source_identity_is_rejected_before_rendering() {
        use std::ffi::OsString;
        use std::os::unix::ffi::OsStringExt;

        let summary = source_analysis::SourceAnalysisSummary {
            files_analyzed: 1,
            functions_found: 1,
            public_functions: 0,
            unsafe_functions: 0,
            specified_functions: 0,
            total_audit_rows: 0,
            present: 0,
            failed: 0,
            unknown: 0,
            functions: vec![source_analysis::ParsedFunction {
                name: "f".to_string(),
                file: PathBuf::from(OsString::from_vec(b"src/\xff.rs".to_vec())),
                line: 1,
                is_public: false,
                is_unsafe: false,
                has_requires: false,
                has_ensures: false,
                return_type: None,
                params: Vec::new(),
                typed_params: Vec::new(),
            }],
            vcs: Vec::new(),
        };
        assert!(validate_source_audit_identities(&summary).is_err());
    }
}
