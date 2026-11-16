// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-08-21; do not grow casually
use std::collections::{BTreeMap, BTreeSet};
use std::io::{Read as _, Seek as _};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use std::{fs, io};

use serde::de::{self, DeserializeSeed, MapAccess, SeqAccess, Visitor};
use serde_json::json;
use sha2::{Digest as _, Sha256};
use trust_release::{GateFinding, GateReport, GateStatus};
use trust_version::BoundToolIdentity;

use super::identity::{
    RepositoryStatus, TOOL_IDENTITY_PROBE_HANG_GUARD, bound_file_sha256, discover_repo_root,
    file_sha256, generated_at_unix_seconds, is_executable_file, option_value, repo_relative_path,
    repository_status, trustd_version_output_is_bound,
};
pub(super) use super::product_proof_catalog::{
    product_proof_component_requirements, product_proof_evidence_class_requirements,
};
use super::types::{
    CANDIDATE_COMMAND_VERSION, ProductProofComponent, ProductProofEvidenceClass,
    ProductProofManifest, ProductProofManifestComponent,
};
use crate::bounded_process;
use crate::durable_io::atomic_write_private;
use crate::input_limits::{
    MAX_RELEASE_METADATA_BYTES, MAX_RELEASE_TRANSCRIPT_REPORT_BYTES, read_bounded_file,
    read_bounded_utf8_file,
};
use crate::pipeline::probe::{
    TrustdRuntimeClosure, apply_trustd_runtime_closure, inspect_trustd_runtime_closure,
};

const PRODUCT_PROOF_EVIDENCE_SCHEMA: &str = "trust.product-proof.v1";
const PRODUCT_PROOF_RELEASE_ARTIFACT_SCHEMA: &str =
    "trust.product-proof-release-artifact-report.v1";
const PRODUCT_PROOF_RELEASE_BINDING_SCHEMA: &str = "trust.product-proof-release-binding.v1";
const PRODUCT_PROOF_RELEASE_CERTIFICATE_SCHEMA: &str = "trust.product-proof-release-certificate.v1";
const SELECTED_IMAGE_REPLAY_SCHEMA: &str = "trust.product-proof-selected-image-replay.v1";
const PRODUCT_PROOF_STUB_COMMAND: &str = "targo trust release product-proof-stub";
const PRODUCT_PROOF_REPORT_COMMAND: &str = "targo trust release product-proof-report";
const PRODUCT_PROOF_SOLVER_EVIDENCE_UNVERIFIED: &str = "product-proof-solver-evidence-unverified";
const PRODUCT_PROOF_DEFAULT_RELEASE_CERTIFICATE_PATH: &str =
    "release/evidence/product-proof/product-proof-release-certificate.json";
// The maintained vendored source distribution includes LLVM and all nine
// first-party repositories. The 2026-09-25 archive has 508,468 entries, 2.67 GB
// compressed and 8.55 GB of file contents; tar framing adds further bytes.
// Decode in bounded memory, retaining only bounded path metadata (see below).
const MAX_SOURCE_ARCHIVE_COMPRESSED_BYTES: u64 = 4 * 1024 * 1024 * 1024;
const MAX_SOURCE_ARCHIVE_DECOMPRESSED_BYTES: u64 = 16 * 1024 * 1024 * 1024;
const MAX_SOURCE_ARCHIVE_MEMBERS: usize = 1_000_000;
mod source_archive;
const MAX_SOURCE_ARCHIVE_LONGNAME_BYTES: u64 = 64 * 1024;
const MAX_SOURCE_ARCHIVE_XZ_MEMORY_BYTES: u64 = 256 * 1024 * 1024;
const MAX_SOURCE_ARCHIVE_XZ_PADDING_BYTES: u64 = 1024 * 1024;
const PRODUCT_PROOF_RELEASE_REQUIRED_COMPILE_BACK_KINDS: &[&str] = &[
    "compile-back-artifact-digests-bound",
    "compile-back-lifted-binary-trust_ir-sha256",
    "compile-back-rust-source-sha256",
    "compile-back-reconstructed-trust_ir-sha256",
    "compile-back-refinement-artifact-sha256",
    "compile-back-root-artifact-sha256",
    "compile-back-selected-image-sha256",
    "compile-back-selected-image-range",
];

#[derive(Default)]
struct ProductProofStubOptions {
    repo_root: Option<PathBuf>,
    candidate_commit: Option<String>,
    evidence_kind: Option<String>,
    artifacts: Vec<String>,
    selected_image_range: Option<String>,
    stage2_trustc: Option<String>,
    source_tarball: Option<String>,
    out: Option<String>,
    report_out: Option<String>,
    certificate_out: Option<String>,
    manifest_out: Option<String>,
    json: bool,
}

struct ProductProofStubArtifactBinding {
    path_field: &'static str,
    path_text: String,
    sha256: String,
}

#[derive(Default)]
struct ProductProofReportOptions {
    repo_root: Option<PathBuf>,
    candidate_commit: Option<String>,
    evidence: Option<String>,
    out: Option<String>,
    json: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProductProofContentClass {
    SolverProof,
    TrustdOperational,
}

pub(super) fn run_product_proof_stub_subcommand(args: &[String]) -> ExitCode {
    if args.first().is_some_and(|arg| matches!(arg.as_str(), "--help" | "-h" | "help")) {
        print!("{}", product_proof_stub_usage_text());
        return ExitCode::SUCCESS;
    }

    let mut options = ProductProofStubOptions::default();
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--json" => options.json = true,
            "--format" => match iter.next().map(String::as_str) {
                Some("json") => options.json = true,
                Some("terminal" | "text") => options.json = false,
                Some(other) => {
                    return product_proof_stub_arg_error(format!("unsupported format `{other}`"));
                }
                None => return product_proof_stub_arg_error("--format requires a value"),
            },
            "--repo-root" => match iter.next() {
                Some(path) => options.repo_root = Some(PathBuf::from(path)),
                None => return product_proof_stub_arg_error("--repo-root requires a path"),
            },
            "--candidate-commit" => match iter.next() {
                Some(commit) => options.candidate_commit = Some(commit.clone()),
                None => {
                    return product_proof_stub_arg_error(
                        "--candidate-commit requires a 40-hex commit",
                    );
                }
            },
            "--evidence-kind" => match iter.next() {
                Some(kind) => options.evidence_kind = Some(kind.clone()),
                None => return product_proof_stub_arg_error("--evidence-kind requires a value"),
            },
            "--artifact" => match iter.next() {
                Some(artifact) => options.artifacts.push(artifact.clone()),
                None => {
                    return product_proof_stub_arg_error(
                        "--artifact requires `<digest-field>=<repo-relative path>`",
                    );
                }
            },
            "--selected-image-range" => match iter.next() {
                Some(range) => options.selected_image_range = Some(range.clone()),
                None => {
                    return product_proof_stub_arg_error(
                        "--selected-image-range requires `<start>..<end>`",
                    );
                }
            },
            "--stage2-trustc" | "--stage2-trust-compiler" => match iter.next() {
                Some(path) => options.stage2_trustc = Some(path.clone()),
                None => {
                    return product_proof_stub_arg_error(
                        "--stage2-trustc requires a repo-relative stage2 trustc path",
                    );
                }
            },
            "--source-tarball" | "--source-archive" => match iter.next() {
                Some(path) => options.source_tarball = Some(path.clone()),
                None => {
                    return product_proof_stub_arg_error(
                        "--source-tarball requires a repo-relative source .tar.xz path",
                    );
                }
            },
            "--out" | "--output" => match iter.next() {
                Some(path) => options.out = Some(path.clone()),
                None => return product_proof_stub_arg_error("--out requires a repo-relative path"),
            },
            "--report-out" | "--bundle-out" => match iter.next() {
                Some(path) => options.report_out = Some(path.clone()),
                None => {
                    return product_proof_stub_arg_error(
                        "--report-out requires a repo-relative JSON path",
                    );
                }
            },
            "--certificate-out" | "--cert-out" => match iter.next() {
                Some(path) => options.certificate_out = Some(path.clone()),
                None => {
                    return product_proof_stub_arg_error(
                        "--certificate-out requires a repo-relative JSON path",
                    );
                }
            },
            "--manifest-out" => match iter.next() {
                Some(path) => options.manifest_out = Some(path.clone()),
                None => {
                    return product_proof_stub_arg_error(
                        "--manifest-out requires a repo-relative TOML path",
                    );
                }
            },
            other => {
                if let Some(format) = option_value(other, "--format") {
                    match format {
                        "json" => options.json = true,
                        "terminal" | "text" => options.json = false,
                        _ => {
                            return product_proof_stub_arg_error(format!(
                                "unsupported format `{format}`"
                            ));
                        }
                    }
                    continue;
                }
                if let Some(path) = option_value(other, "--repo-root") {
                    options.repo_root = Some(PathBuf::from(path));
                    continue;
                }
                if let Some(commit) = option_value(other, "--candidate-commit") {
                    options.candidate_commit = Some(commit.to_string());
                    continue;
                }
                if let Some(kind) = option_value(other, "--evidence-kind") {
                    options.evidence_kind = Some(kind.to_string());
                    continue;
                }
                if let Some(artifact) = option_value(other, "--artifact") {
                    options.artifacts.push(artifact.to_string());
                    continue;
                }
                if let Some(range) = option_value(other, "--selected-image-range") {
                    options.selected_image_range = Some(range.to_string());
                    continue;
                }
                if let Some(path) = option_value(other, "--stage2-trustc")
                    .or_else(|| option_value(other, "--stage2-trust-compiler"))
                {
                    options.stage2_trustc = Some(path.to_string());
                    continue;
                }
                if let Some(path) = option_value(other, "--source-tarball")
                    .or_else(|| option_value(other, "--source-archive"))
                {
                    options.source_tarball = Some(path.to_string());
                    continue;
                }
                if let Some(path) =
                    option_value(other, "--out").or_else(|| option_value(other, "--output"))
                {
                    options.out = Some(path.to_string());
                    continue;
                }
                if let Some(path) = option_value(other, "--report-out")
                    .or_else(|| option_value(other, "--bundle-out"))
                {
                    options.report_out = Some(path.to_string());
                    continue;
                }
                if let Some(path) = option_value(other, "--certificate-out")
                    .or_else(|| option_value(other, "--cert-out"))
                {
                    options.certificate_out = Some(path.to_string());
                    continue;
                }
                if let Some(path) = option_value(other, "--manifest-out") {
                    options.manifest_out = Some(path.to_string());
                    continue;
                }
                return product_proof_stub_arg_error(format!("unknown option `{other}`"));
            }
        }
    }

    let root = match discover_repo_root(options.repo_root.as_deref()) {
        Ok(root) => root,
        Err(err) => {
            return product_proof_stub_arg_error(format!("failed to resolve repo root: {err}"));
        }
    };
    let output_path = match product_proof_stub_output_path(&root, options.out.as_deref(), "--out") {
        Ok(path) => path,
        Err(err) => return product_proof_stub_arg_error(err),
    };
    let report_output_path = match product_proof_stub_output_path(
        &root,
        options.report_out.as_deref(),
        "--report-out",
    ) {
        Ok(path) => path,
        Err(err) => return product_proof_stub_arg_error(err),
    };
    if output_path.is_some() && output_path == report_output_path {
        return product_proof_stub_arg_error("--report-out must be distinct from --out");
    }
    let effective_certificate_out = options.certificate_out.clone().or_else(|| {
        manifest_output_path_placeholder(options.manifest_out.as_deref()).map(str::to_string)
    });
    let certificate_output_path = match product_proof_stub_output_path(
        &root,
        effective_certificate_out.as_deref(),
        "--certificate-out",
    ) {
        Ok(path) => path,
        Err(err) => return product_proof_stub_arg_error(err),
    };
    if certificate_output_path.is_some() && output_path.is_none() {
        return product_proof_stub_arg_error(
            "--certificate-out requires --out so the certificate can bind a materialized evidence JSON",
        );
    }
    if certificate_output_path.is_some()
        && (certificate_output_path == output_path || certificate_output_path == report_output_path)
    {
        return product_proof_stub_arg_error(
            "--certificate-out must be distinct from --out and --report-out",
        );
    }
    let manifest_output_path = match product_proof_manifest_skeleton_output_path(
        &root,
        options.manifest_out.as_deref(),
        "--manifest-out",
    ) {
        Ok(path) => path,
        Err(err) => return product_proof_stub_arg_error(err),
    };
    if let Some(path) = &manifest_output_path {
        if output_path.is_none() {
            return product_proof_stub_arg_error(
                "--manifest-out requires --out so the manifest can bind a materialized evidence JSON",
            );
        }
        if output_path.as_ref() == Some(path) || report_output_path.as_ref() == Some(path) {
            return product_proof_stub_arg_error(
                "--manifest-out must be distinct from --out and --report-out",
            );
        }
        if certificate_output_path.as_ref() == Some(path) {
            return product_proof_stub_arg_error(
                "--manifest-out must be distinct from --certificate-out",
            );
        }
        if options.evidence_kind.as_deref().map(str::trim)
            != Some("compile-back-artifact-digests-bound")
        {
            return product_proof_stub_arg_error(
                "--manifest-out requires --evidence-kind compile-back-artifact-digests-bound",
            );
        }
    }
    if certificate_output_path.is_some()
        && options.evidence_kind.as_deref().map(str::trim)
            != Some("compile-back-artifact-digests-bound")
    {
        return product_proof_stub_arg_error(
            "--certificate-out requires --evidence-kind compile-back-artifact-digests-bound",
        );
    }
    if manifest_output_path.is_some() || certificate_output_path.is_some() {
        if options.stage2_trustc.as_deref().map(str::trim).filter(|path| !path.is_empty()).is_none()
        {
            return product_proof_stub_arg_error(
                "--manifest-out/--certificate-out require --stage2-trustc <repo-relative build/*/stage2/bin/trustc>",
            );
        }
        if options
            .source_tarball
            .as_deref()
            .map(str::trim)
            .filter(|path| !path.is_empty())
            .is_none()
        {
            return product_proof_stub_arg_error(
                "--manifest-out/--certificate-out require --source-tarball <repo-relative source .tar.xz>",
            );
        }
    }
    let evidence = match build_product_proof_stub_evidence(&root, &options) {
        Ok(evidence) => evidence,
        Err(err) => return product_proof_stub_arg_error(err),
    };
    let rendered = match serde_json::to_string_pretty(&evidence) {
        Ok(rendered) => rendered,
        Err(err) => return product_proof_stub_arg_error(format!("failed to render JSON: {err}")),
    };

    if let Some(path) = &output_path {
        if let Err(err) = atomic_write_private(path, format!("{rendered}\n").as_bytes()) {
            return product_proof_stub_arg_error(format!(
                "failed to publish {} atomically: {err}",
                path.display()
            ));
        }
    }

    if let Some(path) = &certificate_output_path {
        let Some(certificate_out) = effective_certificate_out.as_deref() else {
            return product_proof_stub_arg_error("--certificate-out is required");
        };
        let certificate = match build_product_proof_stub_release_certificate(
            certificate_out,
            &options,
            &evidence,
            output_path.as_deref(),
        ) {
            Ok(certificate) => certificate,
            Err(err) => return product_proof_stub_arg_error(err),
        };
        let rendered_certificate = match serde_json::to_string_pretty(&certificate) {
            Ok(rendered) => rendered,
            Err(err) => {
                return product_proof_stub_arg_error(format!(
                    "failed to render release certificate JSON: {err}"
                ));
            }
        };
        if let Err(err) = atomic_write_private(path, format!("{rendered_certificate}\n").as_bytes())
        {
            return product_proof_stub_arg_error(format!(
                "failed to publish {} atomically: {err}",
                path.display()
            ));
        }
    }

    if let Some(path) = &report_output_path {
        let report = match build_product_proof_stub_release_report(
            &root,
            &options,
            &evidence,
            output_path.as_deref(),
            effective_certificate_out.as_deref(),
            certificate_output_path.as_deref(),
        ) {
            Ok(report) => report,
            Err(err) => return product_proof_stub_arg_error(err),
        };
        let rendered_report = match serde_json::to_string_pretty(&report) {
            Ok(rendered) => rendered,
            Err(err) => {
                return product_proof_stub_arg_error(format!(
                    "failed to render release artifact report JSON: {err}"
                ));
            }
        };
        if let Err(err) = atomic_write_private(path, format!("{rendered_report}\n").as_bytes()) {
            return product_proof_stub_arg_error(format!(
                "failed to publish {} atomically: {err}",
                path.display()
            ));
        }
    }

    if let Some(path) = &manifest_output_path {
        let Some(evidence_ref_path) =
            options.out.as_deref().map(str::trim).filter(|out| !out.is_empty())
        else {
            return product_proof_stub_arg_error("--manifest-out requires --out");
        };
        let manifest = product_proof_manifest_skeleton_text(
            evidence_ref_path,
            effective_certificate_out.as_deref(),
            evidence.get("release_artifact_binding"),
        );
        if let Err(err) = atomic_write_private(path, manifest.as_bytes()) {
            return product_proof_stub_arg_error(format!(
                "failed to publish {} atomically: {err}",
                path.display()
            ));
        }
    }

    if options.json || output_path.is_none() {
        println!("{rendered}");
    } else if let Some(out) = options.out.as_deref() {
        println!("wrote digest-bound product-proof stub: {out}");
        if let Some(report_out) = options.report_out.as_deref() {
            println!("wrote blocked product-proof release artifact report: {report_out}");
        }
        if let Some(certificate_out) = effective_certificate_out.as_deref() {
            println!("wrote blocked product-proof release certificate: {certificate_out}");
        }
        if let Some(manifest_out) = options.manifest_out.as_deref() {
            println!("wrote blocked product-proof manifest skeleton: {manifest_out}");
        }
    }

    ExitCode::SUCCESS
}

pub(super) fn run_product_proof_report_subcommand(args: &[String]) -> ExitCode {
    if args.first().is_some_and(|arg| matches!(arg.as_str(), "--help" | "-h" | "help")) {
        print!("{}", product_proof_report_usage_text());
        return ExitCode::SUCCESS;
    }

    let mut options = ProductProofReportOptions::default();
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--json" => options.json = true,
            "--format" => match iter.next().map(String::as_str) {
                Some("json") => options.json = true,
                Some("terminal" | "text") => options.json = false,
                Some(other) => {
                    return product_proof_report_arg_error(format!("unsupported format `{other}`"));
                }
                None => return product_proof_report_arg_error("--format requires a value"),
            },
            "--repo-root" => match iter.next() {
                Some(path) => options.repo_root = Some(PathBuf::from(path)),
                None => return product_proof_report_arg_error("--repo-root requires a path"),
            },
            "--candidate-commit" => match iter.next() {
                Some(commit) => options.candidate_commit = Some(commit.clone()),
                None => {
                    return product_proof_report_arg_error(
                        "--candidate-commit requires a 40-hex commit",
                    );
                }
            },
            "--evidence" | "--input" => match iter.next() {
                Some(path) => options.evidence = Some(path.clone()),
                None => {
                    return product_proof_report_arg_error(
                        "--evidence requires a repo-relative JSON path",
                    );
                }
            },
            "--out" | "--output" => match iter.next() {
                Some(path) => options.out = Some(path.clone()),
                None => {
                    return product_proof_report_arg_error("--out requires a repo-relative path");
                }
            },
            other => {
                if let Some(format) = option_value(other, "--format") {
                    match format {
                        "json" => options.json = true,
                        "terminal" | "text" => options.json = false,
                        _ => {
                            return product_proof_report_arg_error(format!(
                                "unsupported format `{format}`"
                            ));
                        }
                    }
                    continue;
                }
                if let Some(path) = option_value(other, "--repo-root") {
                    options.repo_root = Some(PathBuf::from(path));
                    continue;
                }
                if let Some(commit) = option_value(other, "--candidate-commit") {
                    options.candidate_commit = Some(commit.to_string());
                    continue;
                }
                if let Some(path) =
                    option_value(other, "--evidence").or_else(|| option_value(other, "--input"))
                {
                    options.evidence = Some(path.to_string());
                    continue;
                }
                if let Some(path) =
                    option_value(other, "--out").or_else(|| option_value(other, "--output"))
                {
                    options.out = Some(path.to_string());
                    continue;
                }
                return product_proof_report_arg_error(format!("unknown option `{other}`"));
            }
        }
    }

    let root = match discover_repo_root(options.repo_root.as_deref()) {
        Ok(root) => root,
        Err(err) => {
            return product_proof_report_arg_error(format!("failed to resolve repo root: {err}"));
        }
    };
    let candidate_commit = match options
        .candidate_commit
        .as_deref()
        .map(str::trim)
        .filter(|commit| !commit.is_empty())
    {
        Some(commit) if candidate_commit_is_40_hex(commit) => commit,
        Some(_) => {
            return product_proof_report_arg_error("--candidate-commit must be a 40-hex commit");
        }
        None => return product_proof_report_arg_error("--candidate-commit is required"),
    };
    let evidence_path_text =
        match options.evidence.as_deref().map(str::trim).filter(|path| !path.is_empty()) {
            Some(path) => path,
            None => return product_proof_report_arg_error("--evidence is required"),
        };
    let Some(evidence_path) = repo_relative_exact_file(&root, evidence_path_text) else {
        return product_proof_report_arg_error(
            "--evidence must be an exact regular repo-relative file with no symlink components",
        );
    };
    let output_path = match product_proof_stub_output_path(&root, options.out.as_deref(), "--out") {
        Ok(path) => path,
        Err(err) => return product_proof_report_arg_error(err),
    };
    if output_path.as_ref().is_some_and(|out| out == &evidence_path) {
        return product_proof_report_arg_error("--out must be distinct from --evidence");
    }

    let report = build_product_proof_release_report(
        &root,
        candidate_commit,
        evidence_path_text,
        &evidence_path,
    );
    let rendered = match serde_json::to_string_pretty(&report) {
        Ok(rendered) => rendered,
        Err(err) => {
            return product_proof_report_arg_error(format!(
                "failed to render release artifact report JSON: {err}"
            ));
        }
    };

    if let Some(path) = &output_path {
        if let Err(err) = atomic_write_private(path, format!("{rendered}\n").as_bytes()) {
            return product_proof_report_arg_error(format!(
                "failed to publish {} atomically: {err}",
                path.display()
            ));
        }
    }

    let passed = report
        .get("status")
        .and_then(serde_json::Value::as_str)
        .is_some_and(|status| status == "passed");
    if options.json || output_path.is_none() {
        println!("{rendered}");
    } else if let Some(out) = options.out.as_deref() {
        println!(
            "wrote product-proof release artifact report: {out} [{}]",
            if passed { "passed" } else { "blocked" }
        );
    }

    if passed { ExitCode::SUCCESS } else { ExitCode::from(1) }
}

pub(super) fn product_proof_stub_usage_text() -> &'static str {
    "\
Usage: targo trust release product-proof-stub --candidate-commit <40-hex> --evidence-kind <compile-back-kind> --artifact <digest-field=repo-relative-path> [--selected-image-range <start>..<end>] [--stage2-trustc <repo-relative-path>] [--source-tarball <repo-relative-path>] [--repo-root <path>] [--out <repo-relative-json>] [--report-out <repo-relative-json>] [--certificate-out <repo-relative-json>] [--manifest-out <repo-relative-toml>] [--json]\n\
\n\
Writes or prints a blocked trust.product-proof.v1 scaffold after recomputing SHA-256 over every --artifact path. --report-out/--bundle-out emits a structured blocked release artifact report. --manifest-out emits a blocked release/product-proof.toml skeleton only for compile-back-artifact-digests-bound after every compile-back artifact input is hash-bound and --stage2-trustc plus --source-tarball are materialized. --manifest-out also writes a blocked certificate at release/evidence/product-proof/product-proof-release-certificate.json unless --certificate-out is supplied. It never reports proof success. Do not mark the manifest accepted by hand: solver-class evidence remains checklist material until a kind-specific Rust collector and strict obligation replay validator are implemented and registered.\n"
}

pub(super) fn product_proof_report_usage_text() -> &'static str {
    "\
Usage: targo trust release product-proof-report --candidate-commit <40-hex> --evidence <repo-relative-json> [--repo-root <path>] [--out <repo-relative-json>] [--json]\n\
\n\
Reads a trust.product-proof.v1 checklist artifact, recomputes all compile-back artifact hashes, rejects blocked stubs, and emits trust.product-proof-release-artifact-report.v1. Structural counts, runner labels, and transcript hashes are not proof authority. The current report remains blocked for solver-class evidence until a kind-specific Rust collector binds the exact candidate executable, digest, invocation, and obligation set and a strict validator replays its transcript.\n"
}

fn manifest_output_path_placeholder(manifest_out: Option<&str>) -> Option<&'static str> {
    manifest_out
        .map(str::trim)
        .filter(|path| !path.is_empty())
        .map(|_| PRODUCT_PROOF_DEFAULT_RELEASE_CERTIFICATE_PATH)
}

fn product_proof_stub_arg_error(message: impl AsRef<str>) -> ExitCode {
    eprintln!("{PRODUCT_PROOF_STUB_COMMAND}: {}", message.as_ref());
    ExitCode::from(2)
}

fn product_proof_report_arg_error(message: impl AsRef<str>) -> ExitCode {
    eprintln!("{PRODUCT_PROOF_REPORT_COMMAND}: {}", message.as_ref());
    ExitCode::from(2)
}

fn product_proof_stub_output_path(
    root: &Path,
    out: Option<&str>,
    flag: &str,
) -> Result<Option<PathBuf>, String> {
    let Some(out) = out.map(str::trim).filter(|out| !out.is_empty()) else {
        return Ok(None);
    };
    if Path::new(out).extension().and_then(|extension| extension.to_str()) != Some("json") {
        return Err(format!("{flag} must name a JSON file"));
    }
    repo_relative_path(root, out)
        .map(Some)
        .ok_or_else(|| format!("{flag} must be repo-relative and stay inside the repository"))
}

fn product_proof_manifest_skeleton_output_path(
    root: &Path,
    out: Option<&str>,
    flag: &str,
) -> Result<Option<PathBuf>, String> {
    let Some(out) = out.map(str::trim).filter(|out| !out.is_empty()) else {
        return Ok(None);
    };
    if Path::new(out).extension().and_then(|extension| extension.to_str()) != Some("toml") {
        return Err(format!("{flag} must name a TOML file"));
    }
    repo_relative_path(root, out)
        .map(Some)
        .ok_or_else(|| format!("{flag} must be repo-relative and stay inside the repository"))
}

fn repo_relative_exact_file(root: &Path, path_text: &str) -> Option<PathBuf> {
    let path = repo_relative_path(root, path_text)?;
    let root_metadata = fs::symlink_metadata(root).ok()?;
    if root_metadata.file_type().is_symlink() || !root_metadata.file_type().is_dir() {
        return None;
    }

    let components = Path::new(path_text).components().collect::<Vec<_>>();
    let mut current = root.to_path_buf();
    for (index, component) in components.iter().enumerate() {
        let std::path::Component::Normal(name) = component else {
            return None;
        };
        current.push(name);
        let mut metadata = fs::symlink_metadata(&current).ok()?;
        if metadata.file_type().is_symlink() {
            // The one admitted link: `build` itself under the sanctioned
            // `build -> build.noindex` Spotlight layout (docs/BUILD_AND_INSTALL.md).
            if index != 0
                || name.to_str() != Some("build")
                || !crate::stage2_tools::is_sanctioned_build_link(root)
            {
                return None;
            }
            metadata = fs::metadata(&current).ok()?;
        }
        let is_last = index + 1 == components.len();
        if (is_last && !metadata.file_type().is_file())
            || (!is_last && !metadata.file_type().is_dir())
        {
            return None;
        }
    }
    (!components.is_empty()).then_some(path)
}

fn build_product_proof_stub_evidence(
    root: &Path,
    options: &ProductProofStubOptions,
) -> Result<serde_json::Value, String> {
    let candidate_commit = options
        .candidate_commit
        .as_deref()
        .map(str::trim)
        .filter(|commit| !commit.is_empty())
        .ok_or_else(|| "--candidate-commit is required".to_string())?;
    if !candidate_commit_is_40_hex(candidate_commit) {
        return Err("--candidate-commit must be a 40-hex commit".to_string());
    }

    let evidence_kind = options
        .evidence_kind
        .as_deref()
        .map(str::trim)
        .filter(|kind| !kind.is_empty())
        .ok_or_else(|| "--evidence-kind is required".to_string())?;
    let requirements =
        compile_back_artifact_digest_requirements(evidence_kind).ok_or_else(|| {
            format!("`{evidence_kind}` is not a supported compile-back product-proof evidence kind")
        })?;

    let artifact_bindings = product_proof_stub_artifact_bindings(root, &options.artifacts)?;
    if artifact_bindings.is_empty() {
        return Err(
            "at least one digest-bound --artifact is required before a stub can be emitted"
                .to_string(),
        );
    }
    validate_product_proof_stub_required_material(
        evidence_kind,
        requirements,
        &artifact_bindings,
        options.selected_image_range.as_deref(),
    )?;

    let generated_at = generated_at_unix_seconds();
    let runner = product_proof_stub_runner_json();
    let blockers = product_proof_stub_blockers_json();
    let artifact_checks = product_proof_stub_artifact_checks_json(&artifact_bindings);
    let selected_image_range_check =
        product_proof_stub_selected_image_range_check(options.selected_image_range.as_deref());
    let release_artifact_binding =
        product_proof_stub_release_artifact_binding_json(root, options, candidate_commit)?;

    let mut binding = serde_json::Map::new();
    for (field, artifact) in &artifact_bindings {
        binding.insert(field.clone(), artifact.sha256.clone().into());
        binding.insert(artifact.path_field.to_string(), artifact.path_text.clone().into());
    }
    if let Some(range) = options.selected_image_range.as_deref() {
        let normalized_range = normalize_compile_back_digest_value(
            &serde_json::Value::String(range.to_string()),
            CompileBackDigestValueKind::Range,
        )
        .ok_or_else(|| {
            "--selected-image-range must be a numeric `<start>..<end>` range".to_string()
        })?;
        binding.insert("selected_image_range".to_string(), normalized_range.into());
    }
    if matches!(
        evidence_kind,
        "compile-back-artifact-digests-bound" | "compile-back-selected-image-range"
    ) {
        if let Some(defect) = selected_image_range_binding_defect(
            root,
            Some(&serde_json::Value::Object(binding.clone())),
        ) {
            return Err(format!("`{evidence_kind}` selected-image range is invalid: {defect}"));
        }
    }

    let mut evidence = json!({
        "schema_version": PRODUCT_PROOF_EVIDENCE_SCHEMA,
        "evidence_kind": evidence_kind,
        "evidence_kinds": product_proof_stub_declared_evidence_kinds_json(evidence_kind),
        "candidate_commit": candidate_commit,
        "generated_at": generated_at,
        "runner": runner.clone(),
        "candidate_command": PRODUCT_PROOF_STUB_COMMAND,
        "candidate_command_version": CANDIDATE_COMMAND_VERSION,
        "candidate_commit_binding": {
            "field": "candidate_commit",
            "value": candidate_commit,
            "status": "bound",
        },
        "status": "blocked",
        "reason": "digest-bound scaffold only; no proof success is claimed",
        "blockers": blockers.clone(),
        "proof_results": {
            "proved": 0,
            "total": 0,
            "failed": 0,
            "unknown": 0,
            "skipped": 0,
            "by_solver": []
        },
        "compile_back_artifact_digest_binding": binding,
        "release_artifact": {
            "schema_version": PRODUCT_PROOF_RELEASE_ARTIFACT_SCHEMA,
            "artifact_kind": "product-proof-stub",
            "status": "blocked",
            "candidate_commit": candidate_commit,
            "candidate_commit_binding": {
                "field": "candidate_commit",
                "value": candidate_commit,
                "status": "bound",
            },
            "runner": runner,
            "artifact_sha256_checks": artifact_checks,
            "selected_image_range_check": selected_image_range_check,
            "release_artifact_binding": release_artifact_binding.clone().unwrap_or(serde_json::Value::Null),
            "blockers": blockers,
            "product_proof_pass_evidence": false,
            "domination_admissible": false,
        },
    });
    if let Some(release_artifact_binding) = release_artifact_binding {
        evidence["release_artifact_binding"] = release_artifact_binding;
    }
    if let Some(out) = options.out.as_deref().map(str::trim).filter(|out| !out.is_empty()) {
        evidence["product_proof_manifest_stub"] = json!({
            "component": "binary/decomp gates",
            "status": "blocked",
            "evidence_ref": format!("{evidence_kind}:{out}"),
            "evidence_refs": product_proof_stub_manifest_evidence_refs_json(evidence_kind, out),
            "release_product_proof_toml": "release/product-proof.toml",
            "reason": "scaffold only; keep blocked until proof_results are produced by proof tooling"
        });
        if let Some(manifest_out) =
            options.manifest_out.as_deref().map(str::trim).filter(|out| !out.is_empty())
        {
            evidence["product_proof_manifest_stub"]["release_product_proof_toml"] =
                manifest_out.into();
        }
    }
    Ok(evidence)
}

fn product_proof_stub_declared_evidence_kinds_json(evidence_kind: &str) -> serde_json::Value {
    if evidence_kind == "compile-back-artifact-digests-bound" {
        return serde_json::Value::Array(
            PRODUCT_PROOF_RELEASE_REQUIRED_COMPILE_BACK_KINDS
                .iter()
                .map(|kind| serde_json::Value::String((*kind).to_string()))
                .collect(),
        );
    }
    serde_json::Value::Array(vec![serde_json::Value::String(evidence_kind.to_string())])
}

fn product_proof_stub_manifest_evidence_refs_json(
    evidence_kind: &str,
    out: &str,
) -> serde_json::Value {
    if evidence_kind == "compile-back-artifact-digests-bound" {
        return serde_json::Value::Array(
            PRODUCT_PROOF_RELEASE_REQUIRED_COMPILE_BACK_KINDS
                .iter()
                .map(|kind| serde_json::Value::String(format!("{kind}:{out}")))
                .collect(),
        );
    }
    serde_json::Value::Array(vec![serde_json::Value::String(format!("{evidence_kind}:{out}"))])
}

fn product_proof_stub_runner_json() -> serde_json::Value {
    json!({
        "implementation": "rust",
        "entrypoint": PRODUCT_PROOF_STUB_COMMAND,
        "python_used": false,
        "tool": "targo-trust",
    })
}

fn product_proof_stub_blockers_json() -> serde_json::Value {
    json!([
        {
            "code": "product-proof-stub-blocked",
            "severity": "blocker",
            "message": "digest-bound scaffold only; no proof success is claimed"
        },
        {
            "code": "product-proof-evidence-content-insufficient",
            "severity": "blocker",
            "message": "proof_results.proved is zero; blocked stubs are not admissible product-proof pass evidence"
        }
    ])
}

fn product_proof_stub_artifact_checks_json(
    artifact_bindings: &BTreeMap<String, ProductProofStubArtifactBinding>,
) -> serde_json::Value {
    serde_json::Value::Array(
        artifact_bindings
            .iter()
            .map(|(field, artifact)| {
                json!({
                    "status": "passed",
                    "check": "sha256-readback",
                    "digest_field": field,
                    "path_field": artifact.path_field,
                    "path": artifact.path_text,
                    "sha256": artifact.sha256,
                })
            })
            .collect(),
    )
}

fn product_proof_stub_selected_image_range_check(range: Option<&str>) -> serde_json::Value {
    match range.and_then(|range| {
        normalize_compile_back_digest_value(
            &serde_json::Value::String(range.to_string()),
            CompileBackDigestValueKind::Range,
        )
    }) {
        Some(normalized) => json!({
            "status": "passed",
            "check": "selected-image-range",
            "range": normalized,
        }),
        None => json!({
            "status": "not-applicable",
            "check": "selected-image-range",
        }),
    }
}

fn product_proof_stub_release_artifact_binding_json(
    root: &Path,
    options: &ProductProofStubOptions,
    candidate_commit: &str,
) -> Result<Option<serde_json::Value>, String> {
    let has_binding_input = options.stage2_trustc.is_some() || options.source_tarball.is_some();
    if !has_binding_input {
        return Ok(None);
    }

    let stage2_trustc_path = options
        .stage2_trustc
        .as_deref()
        .map(str::trim)
        .filter(|path| !path.is_empty())
        .ok_or_else(|| {
            "release artifact binding requires --stage2-trustc <repo-relative build/*/stage2/bin/trustc>"
                .to_string()
        })?;
    let source_tarball_path = options
        .source_tarball
        .as_deref()
        .map(str::trim)
        .filter(|path| !path.is_empty())
        .ok_or_else(|| {
            "release artifact binding requires --source-tarball <repo-relative source .tar.xz>"
                .to_string()
        })?;

    let stage2_trustc =
        product_proof_stage2_trustc_binding_from_path(root, stage2_trustc_path, candidate_commit)?;
    let source_tarball = product_proof_source_tarball_binding_from_path(
        root,
        source_tarball_path,
        candidate_commit,
    )?;

    Ok(Some(json!({
        "schema_version": PRODUCT_PROOF_RELEASE_BINDING_SCHEMA,
        "status": "blocked",
        "candidate_commit": candidate_commit,
        "stage2_trustc": stage2_trustc,
        "source_tarball": source_tarball,
        "compile_back_evidence": {
            "status": "digest-bound-scaffold",
            "path": options.out.as_deref().map(str::trim).filter(|out| !out.is_empty()),
            "evidence_kinds": PRODUCT_PROOF_RELEASE_REQUIRED_COMPILE_BACK_KINDS,
        },
        "product_proof_pass_evidence": false,
        "domination_admissible": false,
    })))
}

fn product_proof_stage2_trustc_binding_from_path(
    root: &Path,
    path_text: &str,
    candidate_commit: &str,
) -> Result<serde_json::Value, String> {
    let Some(path) = repo_relative_exact_file(root, path_text) else {
        return Err(format!(
            "--stage2-trustc path `{path_text}` must be an exact regular repo-relative file with no symlink components"
        ));
    };
    if !stage2_trustc_path_satisfied(path_text) {
        return Err(format!(
            "--stage2-trustc path `{path_text}` must name build/*/stage2/bin/trustc"
        ));
    }
    if !is_executable_file(&path) {
        return Err(format!(
            "--stage2-trustc path must be an exact regular executable (not a symlink): {}",
            path.display()
        ));
    }
    let sha256 = bound_file_sha256(&path)
        .ok_or_else(|| format!("failed to hash exact --stage2-trustc {}", path.display()))?;
    let version_output = command_output_text(&path, &["-Vv"]).ok_or_else(|| {
        format!("--stage2-trustc {} did not produce `trustc -Vv` output", path.display())
    })?;
    let post_version_sha256 = bound_file_sha256(&path).ok_or_else(|| {
        format!("failed to re-hash exact --stage2-trustc {} after `-Vv`", path.display())
    })?;
    if post_version_sha256 != sha256 {
        return Err(format!(
            "--stage2-trustc {} changed while its release identity was captured",
            path.display()
        ));
    }
    let commit_hash = parse_trustc_commit_hash(&version_output).ok_or_else(|| {
        format!(
            "--stage2-trustc {} did not report a 40-hex commit-hash in `-Vv` output",
            path.display()
        )
    })?;
    if commit_hash != candidate_commit {
        return Err(format!(
            "--stage2-trustc {} reports commit-hash {commit_hash}, expected candidate {candidate_commit}",
            path.display()
        ));
    }
    Ok(json!({
        "name": "trustc",
        "stage": "stage2",
        "path": path_text,
        "sha256": sha256,
        "executable": true,
        "version": version_output.lines().next().unwrap_or("trustc").trim(),
        "commit_hash": commit_hash,
        "candidate_commit": candidate_commit,
        "status": "bound",
    }))
}

fn product_proof_source_tarball_binding_from_path(
    root: &Path,
    path_text: &str,
    candidate_commit: &str,
) -> Result<serde_json::Value, String> {
    let Some(path) = repo_relative_exact_file(root, path_text) else {
        return Err(format!(
            "--source-tarball path `{path_text}` must be an exact regular repo-relative file with no symlink components"
        ));
    };
    if !source_tarball_path_satisfied(path_text) {
        return Err(format!("--source-tarball path `{path_text}` must name a .tar.xz archive"));
    }
    let (sha256, archive_commit) = source_tarball_archive_identity(&path).map_err(|detail| {
        format!("--source-tarball {} is not a bound source archive: {detail}", path.display())
    })?;
    if archive_commit != candidate_commit {
        return Err(format!(
            "--source-tarball {} embeds git-commit-hash {archive_commit}, expected candidate {candidate_commit}",
            path.display()
        ));
    }
    Ok(json!({
        "path": path_text,
        "sha256": sha256,
        "candidate_commit": candidate_commit,
        "status": "bound",
    }))
}

fn build_product_proof_stub_release_report(
    root: &Path,
    options: &ProductProofStubOptions,
    evidence: &serde_json::Value,
    output_path: Option<&Path>,
    certificate_out: Option<&str>,
    certificate_path: Option<&Path>,
) -> Result<serde_json::Value, String> {
    let product_proof_artifact = match (options.out.as_deref(), output_path) {
        (Some(out), Some(path)) => {
            let sha256 = file_sha256(path).ok_or_else(|| {
                format!("failed to read written product-proof stub {}", path.display())
            })?;
            json!({
                "path": out,
                "sha256": sha256,
                "schema_version": PRODUCT_PROOF_EVIDENCE_SCHEMA,
                "artifact_kind": "product-proof-stub",
                "status": "blocked",
            })
        }
        _ => json!({
            "status": "not-written",
            "artifact_kind": "product-proof-stub",
            "reason": "--out was not provided; stub was printed instead of materialized",
        }),
    };
    let release_certificate = match (certificate_out, certificate_path) {
        (Some(out), Some(path)) => {
            let sha256 = file_sha256(path).ok_or_else(|| {
                format!("failed to read written product-proof certificate {}", path.display())
            })?;
            json!({
                "path": out,
                "sha256": sha256,
                "schema_version": PRODUCT_PROOF_RELEASE_CERTIFICATE_SCHEMA,
                "artifact_kind": "product-proof-release-certificate",
                "status": "blocked",
            })
        }
        _ => json!({
            "status": "not-written",
            "artifact_kind": "product-proof-release-certificate",
            "reason": "--certificate-out was not provided and --manifest-out did not request the default certificate",
        }),
    };

    let evidence_ref = options.out.as_deref().and_then(|out| {
        options.evidence_kind.as_deref().map(|kind| format!("{}:{}", kind.trim(), out.trim()))
    });
    let repo_status = repository_status(
        root,
        evidence.get("candidate_commit").and_then(serde_json::Value::as_str),
    );

    Ok(json!({
        "schema_version": PRODUCT_PROOF_RELEASE_ARTIFACT_SCHEMA,
        "generated_at": generated_at_unix_seconds(),
        "status": "blocked",
        "artifact_kind": "product-proof-stub-release-report",
        "candidate_commit": evidence.get("candidate_commit").cloned().unwrap_or(serde_json::Value::Null),
        "candidate_commit_binding": evidence
            .get("candidate_commit_binding")
            .cloned()
            .unwrap_or(serde_json::Value::Null),
        "repo_dirty": repo_status.is_dirty_or_unavailable(),
        "repo_dirty_metadata": repo_status.metadata(),
        "runner": evidence.get("runner").cloned().unwrap_or_else(product_proof_stub_runner_json),
        "candidate_command": PRODUCT_PROOF_STUB_COMMAND,
        "candidate_command_version": CANDIDATE_COMMAND_VERSION,
        "product_proof_artifact": product_proof_artifact,
        "release_certificate": release_certificate,
        "evidence_ref": evidence_ref,
        "artifact_sha256_checks": evidence
            .get("release_artifact")
            .and_then(|artifact| artifact.get("artifact_sha256_checks"))
            .cloned()
            .unwrap_or_else(|| serde_json::Value::Array(Vec::new())),
        "selected_image_range_check": evidence
            .get("release_artifact")
            .and_then(|artifact| artifact.get("selected_image_range_check"))
            .cloned()
            .unwrap_or(serde_json::Value::Null),
        "release_artifact_binding": evidence
            .get("release_artifact_binding")
            .cloned()
            .unwrap_or(serde_json::Value::Null),
        "blockers": evidence
            .get("blockers")
            .cloned()
            .unwrap_or_else(product_proof_stub_blockers_json),
        "product_proof_pass_evidence": false,
        "domination_admissible": false,
    }))
}

fn build_product_proof_stub_release_certificate(
    certificate_out: &str,
    options: &ProductProofStubOptions,
    evidence: &serde_json::Value,
    output_path: Option<&Path>,
) -> Result<serde_json::Value, String> {
    let Some(evidence_out) = options.out.as_deref().map(str::trim).filter(|out| !out.is_empty())
    else {
        return Err("--certificate-out requires --out".to_string());
    };
    let Some(output_path) = output_path else {
        return Err("--certificate-out requires a materialized --out evidence JSON".to_string());
    };
    let evidence_sha256 = file_sha256(output_path).ok_or_else(|| {
        format!("failed to hash product-proof evidence JSON {}", output_path.display())
    })?;
    let release_artifact_binding = evidence.get("release_artifact_binding").cloned().ok_or_else(|| {
        "--certificate-out requires --stage2-trustc and --source-tarball release artifact binding"
            .to_string()
    })?;

    Ok(json!({
        "schema_version": PRODUCT_PROOF_RELEASE_CERTIFICATE_SCHEMA,
        "artifact_kind": "product-proof-release-certificate",
        "path": certificate_out,
        "generated_at": generated_at_unix_seconds(),
        "status": "blocked",
        "candidate_commit": evidence.get("candidate_commit").cloned().unwrap_or(serde_json::Value::Null),
        "candidate_commit_binding": evidence
            .get("candidate_commit_binding")
            .cloned()
            .unwrap_or(serde_json::Value::Null),
        "runner": evidence.get("runner").cloned().unwrap_or_else(product_proof_stub_runner_json),
        "candidate_command": PRODUCT_PROOF_STUB_COMMAND,
        "candidate_command_version": CANDIDATE_COMMAND_VERSION,
        "product_proof_artifact": {
            "path": evidence_out,
            "sha256": evidence_sha256,
            "schema_version": PRODUCT_PROOF_EVIDENCE_SCHEMA,
            "artifact_kind": "product-proof-stub",
            "status": "blocked",
        },
        "release_artifact_binding": release_artifact_binding,
        "blockers": evidence
            .get("blockers")
            .cloned()
            .unwrap_or_else(product_proof_stub_blockers_json),
        "product_proof_pass_evidence": false,
        "domination_admissible": false,
    }))
}

fn build_product_proof_release_report(
    root: &Path,
    candidate_commit: &str,
    evidence_path_text: &str,
    evidence_path: &Path,
) -> serde_json::Value {
    let generated_at = generated_at_unix_seconds();
    let current_repo_status = repository_status(root, Some(candidate_commit));
    let evidence_result = read_product_proof_release_evidence(evidence_path);
    let (evidence, evidence_sha256, mut findings) = match evidence_result {
        Ok((evidence, sha256)) => {
            let findings = validate_product_proof_release_artifact_evidence(
                root,
                candidate_commit,
                evidence_path,
                &evidence,
            );
            (Some(evidence), Some(sha256), findings)
        }
        Err(finding) => (None, None, vec![finding]),
    };
    findings.extend(product_proof_release_current_repo_findings(
        root,
        candidate_commit,
        &current_repo_status,
    ));
    let evidence = evidence.as_ref();
    let passed = findings.is_empty();
    let status = if passed { "passed" } else { "blocked" };
    let gate_report =
        GateReport::new("product-proof-release-artifact", std::mem::take(&mut findings));
    let findings = gate_report.findings.clone();
    let blockers = product_proof_release_findings_json(&findings);
    let candidate_commit_binding =
        product_proof_release_candidate_commit_binding_json(candidate_commit, evidence);

    json!({
        "schema_version": PRODUCT_PROOF_RELEASE_ARTIFACT_SCHEMA,
        "generated_at": generated_at,
        "status": status,
        "artifact_kind": "product-proof-release-report",
        "candidate_commit": candidate_commit,
        "candidate_commit_binding": candidate_commit_binding,
        "repo_dirty": current_repo_status.is_dirty_or_unavailable(),
        "repo_dirty_metadata": current_repo_status.metadata(),
        "runner": product_proof_release_report_runner_json(),
        "candidate_command": PRODUCT_PROOF_REPORT_COMMAND,
        "candidate_command_version": CANDIDATE_COMMAND_VERSION,
        "product_proof_artifact": {
            "path": evidence_path_text,
            "sha256": evidence_sha256,
            "schema_version": evidence
                .and_then(|value| value.get("schema_version"))
                .cloned()
                .unwrap_or(serde_json::Value::Null),
            "artifact_kind": evidence
                .and_then(|value| value.get("artifact_kind"))
                .cloned()
                .unwrap_or_else(|| serde_json::Value::String("product-proof-evidence".to_string())),
            "status": status,
        },
        "ingested_evidence_runner": evidence
            .and_then(|value| value.get("runner"))
            .cloned()
            .unwrap_or(serde_json::Value::Null),
        "proof_results": evidence
            .and_then(|value| value.get("proof_results"))
            .cloned()
            .unwrap_or(serde_json::Value::Null),
        "declared_compile_back_evidence_kinds": declared_compile_back_evidence_kinds_json(evidence),
        "compile_back_evidence_kinds": compile_back_evidence_kind_checks_json(evidence),
        "artifact_sha256_checks": evidence
            .map(|value| product_proof_release_artifact_checks_json(root, value))
            .unwrap_or_else(|| serde_json::Value::Array(Vec::new())),
        "selected_image_range_check": evidence
            .map(|value| product_proof_release_selected_image_range_check_json(root, value))
            .unwrap_or_else(|| {
                json!({
                    "status": "blocked",
                    "check": "selected-image-range",
                    "reason": "product-proof evidence could not be parsed",
                })
            }),
        "selected_image_replay_check": evidence
            .map(|value| selected_image_replay_check_json(root, candidate_commit, value))
            .unwrap_or_else(|| json!({
                "status": "blocked",
                "scope": "selected-image-byte-relation-only",
                "reason": "product-proof evidence could not be parsed",
            })),
        "release_artifact_binding_check": evidence
            .map(|value| {
                product_proof_release_artifact_binding_check_json(root, candidate_commit, value)
            })
            .unwrap_or_else(|| {
                json!({
                    "status": "blocked",
                    "check": "release-artifact-binding",
                    "defects": ["product-proof evidence could not be parsed"],
                })
            }),
        "runner_clean_provenance": evidence
            .map(product_proof_release_clean_runner_json)
            .unwrap_or_else(|| {
                json!({
                    "status": "blocked",
                    "check": "runner-clean-provenance",
                    "reason": "product-proof evidence could not be parsed",
                })
            }),
        "gate_report": gate_report,
        "blockers": blockers,
        "product_proof_pass_evidence": passed,
        "domination_admissible": passed,
    })
}

fn product_proof_release_current_repo_findings(
    root: &Path,
    candidate_commit: &str,
    status: &RepositoryStatus,
) -> Vec<GateFinding> {
    match status {
        RepositoryStatus::Clean => Vec::new(),
        RepositoryStatus::Dirty(lines) => vec![GateFinding::blocker(
            "product-proof-release-repo-dirty",
            format!(
                "{} must be clean before emitting product-proof release evidence; git status has {} entr{}",
                root.display(),
                lines.len(),
                if lines.len() == 1 { "y" } else { "ies" }
            ),
        )],
        RepositoryStatus::Unavailable(error) => vec![GateFinding::blocker(
            "product-proof-release-repo-provenance-unavailable",
            format!(
                "{} repository status for candidate {candidate_commit} is unavailable: {error}",
                root.display()
            ),
        )],
    }
}

fn read_product_proof_release_evidence(
    path: &Path,
) -> Result<(serde_json::Value, String), GateFinding> {
    let bytes = read_bounded_file(path, MAX_RELEASE_TRANSCRIPT_REPORT_BYTES).map_err(|err| {
        GateFinding::blocker(
            "product-proof-release-evidence-read",
            format!("failed to read product-proof evidence {}: {err}", path.display()),
        )
    })?;
    let sha256 = format!("{:x}", Sha256::digest(&bytes));
    let evidence = parse_product_proof_json(&bytes).map_err(|err| {
        GateFinding::blocker(
            "product-proof-release-evidence-json",
            format!("{} is not a JSON product-proof evidence artifact: {err}", path.display()),
        )
    })?;
    Ok((evidence, sha256))
}

/// Parse untrusted product-proof JSON without serde_json's last-key-wins
/// ambiguity. Duplicate keys are rejected at every object depth, including
/// keys whose escape spellings decode to the same string.
fn parse_product_proof_json(bytes: &[u8]) -> Result<serde_json::Value, serde_json::Error> {
    let mut deserializer = serde_json::Deserializer::from_slice(bytes);
    let value = StrictJsonValueSeed.deserialize(&mut deserializer)?;
    deserializer.end()?;
    Ok(value)
}

struct StrictJsonValueSeed;

impl<'de> DeserializeSeed<'de> for StrictJsonValueSeed {
    type Value = serde_json::Value;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(StrictJsonValueVisitor)
    }
}

struct StrictJsonValueVisitor;

impl<'de> Visitor<'de> for StrictJsonValueVisitor {
    type Value = serde_json::Value;

    fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("JSON without duplicate object keys")
    }

    fn visit_bool<E>(self, value: bool) -> Result<Self::Value, E> {
        Ok(value.into())
    }

    fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E> {
        Ok(value.into())
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E> {
        Ok(value.into())
    }

    fn visit_f64<E>(self, value: f64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        serde_json::Number::from_f64(value)
            .map(serde_json::Value::Number)
            .ok_or_else(|| E::custom("non-finite JSON number"))
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E> {
        Ok(value.into())
    }

    fn visit_string<E>(self, value: String) -> Result<Self::Value, E> {
        Ok(value.into())
    }

    fn visit_none<E>(self) -> Result<Self::Value, E> {
        Ok(serde_json::Value::Null)
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E> {
        Ok(serde_json::Value::Null)
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        StrictJsonValueSeed.deserialize(deserializer)
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let mut values = Vec::with_capacity(sequence.size_hint().unwrap_or(0));
        while let Some(value) = sequence.next_element_seed(StrictJsonValueSeed)? {
            values.push(value);
        }
        Ok(serde_json::Value::Array(values))
    }

    fn visit_map<A>(self, mut object: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut values = serde_json::Map::new();
        while let Some(key) = object.next_key::<String>()? {
            if values.contains_key(&key) {
                return Err(de::Error::custom(format!("duplicate object key `{key}`")));
            }
            let value = object.next_value_seed(StrictJsonValueSeed)?;
            values.insert(key, value);
        }
        Ok(serde_json::Value::Object(values))
    }
}

fn validate_product_proof_release_artifact_evidence(
    root: &Path,
    candidate_commit: &str,
    evidence_path: &Path,
    evidence: &serde_json::Value,
) -> Vec<GateFinding> {
    let mut findings = Vec::new();
    if evidence.get("schema_version").and_then(serde_json::Value::as_str)
        != Some(PRODUCT_PROOF_EVIDENCE_SCHEMA)
    {
        findings.push(GateFinding::blocker(
            "product-proof-release-evidence-schema",
            format!(
                "{} must have schema_version `{PRODUCT_PROOF_EVIDENCE_SCHEMA}`",
                evidence_path.display()
            ),
        ));
    }

    if let Some(detail) = product_proof_stub_evidence_defect(evidence) {
        findings.push(GateFinding::blocker(
            "product-proof-stub-blocked",
            format!("{} is blocked stub evidence: {detail}", evidence_path.display()),
        ));
    }

    match declared_candidate_commit(evidence) {
        Some(declared) if declared == candidate_commit => {}
        Some(declared) => findings.push(GateFinding::blocker(
            "product-proof-release-candidate-mismatch",
            format!(
                "{} declares candidate_commit {declared}, expected {candidate_commit}",
                evidence_path.display()
            ),
        )),
        None => findings.push(GateFinding::blocker(
            "product-proof-release-candidate-missing",
            format!("{} does not bind candidate_commit", evidence_path.display()),
        )),
    }
    let mut candidate_values = Vec::new();
    collect_candidate_commit_values(evidence, &mut candidate_values);
    if candidate_values.iter().any(|value| *value != candidate_commit) {
        findings.push(GateFinding::blocker(
            "product-proof-release-candidate-conflict",
            format!(
                "{} contains candidate_commit values that do not all bind {candidate_commit}",
                evidence_path.display()
            ),
        ));
    }

    if let Some((code, detail)) = proof_content_defect(evidence) {
        findings.push(GateFinding::blocker(
            code,
            format!(
                "{} evidence content is not release-admissible: {detail}",
                evidence_path.display()
            ),
        ));
    }
    if let Err(detail) = replay_selected_image_range(root, candidate_commit, evidence) {
        findings.push(GateFinding::blocker(
            "product-proof-selected-image-replay-invalid",
            format!("{} selected-image byte replay failed: {detail}", evidence_path.display()),
        ));
    }
    findings.push(GateFinding::blocker(
        PRODUCT_PROOF_SOLVER_EVIDENCE_UNVERIFIED,
        format!(
            "{} compile-back evidence is checklist material only: {}",
            evidence_path.display(),
            solver_evidence_admission_defect("aggregate compile-back solver evidence")
        ),
    ));
    if let Some(detail) = runner_clean_provenance_defect(evidence) {
        findings.push(GateFinding::blocker(
            "product-proof-evidence-runner-dirty",
            format!("{} runner provenance is not clean: {detail}", evidence_path.display()),
        ));
    }

    for kind in PRODUCT_PROOF_RELEASE_REQUIRED_COMPILE_BACK_KINDS {
        if !json_declares_evidence_kind(evidence, kind) {
            findings.push(GateFinding::blocker(
                "product-proof-compile-back-kind-missing",
                format!("{} does not declare evidence kind `{kind}`", evidence_path.display()),
            ));
            continue;
        }
        if let Some(detail) = compile_back_artifact_digest_evidence_defect(root, kind, evidence) {
            findings.push(GateFinding::blocker(
                "product-proof-compile-back-artifact-digest-missing",
                format!(
                    "{} evidence kind `{kind}` is not materialized: {detail}",
                    evidence_path.display()
                ),
            ));
        }
    }
    if let Some(detail) = selected_image_release_binding_defect(root, evidence) {
        findings.push(GateFinding::blocker(
            "product-proof-selected-image-binding-missing",
            format!(
                "{} selected-image evidence is not hash-bound: {detail}",
                evidence_path.display()
            ),
        ));
    }
    findings.extend(product_proof_release_artifact_binding_findings(
        root,
        candidate_commit,
        evidence_path,
        evidence,
    ));

    findings
}

fn product_proof_stub_evidence_defect(evidence: &serde_json::Value) -> Option<String> {
    if evidence.get("blockers").and_then(serde_json::Value::as_array).is_some_and(|blockers| {
        blockers.iter().any(|blocker| {
            blocker.get("code").and_then(serde_json::Value::as_str)
                == Some("product-proof-stub-blocked")
        })
    }) {
        return Some("blockers include product-proof-stub-blocked".to_string());
    }
    if evidence.get("product_proof_manifest_stub").is_some() {
        return Some("contains product_proof_manifest_stub".to_string());
    }
    for path in [
        "candidate_command",
        "runner.entrypoint",
        "runner.command",
        "release_artifact.artifact_kind",
        "product_proof_artifact.artifact_kind",
    ] {
        if dotted_value(evidence, path)
            .and_then(serde_json::Value::as_str)
            .is_some_and(|value| value.contains("product-proof-stub"))
        {
            return Some(format!("declares {path} as product-proof-stub"));
        }
    }
    None
}

fn runner_clean_provenance_defect(evidence: &serde_json::Value) -> Option<String> {
    let dirty_paths = [
        "repo_dirty",
        "repo_dirty_metadata.dirty",
        "provenance.repo_dirty",
        "provenance.repo_dirty_metadata.dirty",
        "runner.repo_dirty",
        "runner.repo_dirty_metadata.dirty",
        "runner.git_dirty",
        "runner.git.dirty",
    ];
    let clean_paths =
        ["repo_clean", "provenance.repo_clean", "runner.repo_clean", "runner.git.clean"];

    let mut saw_clean = false;
    for (paths, expected) in [(dirty_paths.as_slice(), false), (clean_paths.as_slice(), true)] {
        for path in paths {
            let Some(value) = dotted_value(evidence, path) else {
                continue;
            };
            match value.as_bool() {
                Some(actual) if actual == expected => saw_clean = true,
                Some(actual) => return Some(format!("declares {path}={actual}")),
                None => return Some(format!("declares {path} with a non-boolean value")),
            }
        }
    }

    (!saw_clean).then(|| {
        "declares no explicit clean git/worktree provenance such as runner.repo_dirty=false"
            .to_string()
    })
}

fn selected_image_release_binding_defect(
    root: &Path,
    evidence: &serde_json::Value,
) -> Option<String> {
    selected_image_range_binding_defect(root, evidence.get("compile_back_artifact_digest_binding"))
}

// This is a replay of one finite byte relation, not a compile-back proof or
// evidence that the candidate compiler produced either artifact.
fn replay_selected_image_range(
    root: &Path,
    candidate_commit: &str,
    evidence: &serde_json::Value,
) -> Result<(), String> {
    let replay =
        evidence.get("selected_image_replay").ok_or("missing selected_image_replay transcript")?;
    for field in ["obligations", "transcript"] {
        if replay.get(field).and_then(serde_json::Value::as_array).map(Vec::len) != Some(1) {
            return Err(format!("selected_image_replay.{field} must contain exactly one entry"));
        }
    }
    let expected = expected_selected_image_replay(root, candidate_commit, evidence)?;
    if replay != &expected {
        return Err("selected_image_replay is not the exact closed candidate/tree/executable/artifact/obligation transcript recomputed from live bytes".to_string());
    }
    Ok(())
}

fn expected_selected_image_replay(
    root: &Path,
    candidate_commit: &str,
    evidence: &serde_json::Value,
) -> Result<serde_json::Value, String> {
    if declared_candidate_commit(evidence) != Some(candidate_commit) {
        return Err("selected-image evidence does not bind the requested candidate commit".into());
    }
    let mut candidate_values = Vec::new();
    collect_candidate_commit_values(evidence, &mut candidate_values);
    if candidate_values.iter().any(|value| *value != candidate_commit) {
        return Err("selected-image replay contains a conflicting candidate commit".into());
    }
    let head = crate::controlled_git::canonical_head(
        root,
        "selected-image replay candidate HEAD",
        64 * 1024,
        Duration::from_secs(10),
    )?;
    if head != candidate_commit {
        return Err(format!("selected-image replay HEAD {head} differs from {candidate_commit}"));
    }
    let tree = crate::controlled_git::text(
        root,
        &["rev-parse", "--verify", &format!("{candidate_commit}^{{tree}}")],
        "selected-image replay candidate tree",
        64 * 1024,
        Duration::from_secs(10),
    )?;
    if !matches!(tree.len(), 40 | 64)
        || !tree.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err("candidate tree is not a canonical Git object ID".into());
    }

    let identity = find_stage2_trustc_identity(evidence)
        .ok_or("selected-image replay has no stage2 executable binding")?;
    let identity_defects = stage2_trustc_identity_defects(root, candidate_commit, identity);
    if !identity_defects.is_empty() {
        return Err(format!("selected-image replay executable: {}", identity_defects[0].1));
    }
    let executable = json!({
        "path": identity["path"],
        "sha256": normalized_sha256_value(&identity["sha256"])
            .ok_or("invalid selected-image replay executable digest")?,
        "version": identity["version"].as_str().ok_or("missing executable version")?.trim(),
        "commit_hash": candidate_commit,
    });

    let binding = evidence
        .get("compile_back_artifact_digest_binding")
        .and_then(serde_json::Value::as_object)
        .ok_or("missing compile-back artifact binding")?;
    for requirement in COMPILE_BACK_SELECTED_IMAGE_RANGE_MATERIAL {
        if let Some(defect) = compile_back_digest_requirement_defect(
            root,
            evidence.get("compile_back_artifact_digest_binding"),
            requirement,
        ) {
            return Err(format!("selected-image replay artifact: {defect}"));
        }
    }
    let range = normalize_compile_back_digest_value(
        binding.get("selected_image_range").ok_or("missing selected_image_range")?,
        CompileBackDigestValueKind::Range,
    )
    .ok_or("invalid selected_image_range")?;
    let (start, end) = range.split_once("..").ok_or("invalid selected_image_range")?;
    let start = start.parse::<u64>().map_err(|_| "invalid selected_image_range")?;
    let end = end.parse::<u64>().map_err(|_| "invalid selected_image_range")?;
    let root_path_text = binding["root_artifact_path"].as_str().ok_or("missing root path")?;
    let selected_path_text =
        binding["selected_image_path"].as_str().ok_or("missing selected path")?;
    let root_path = repo_relative_exact_file(root, root_path_text).ok_or("unsafe root path")?;
    let selected_path =
        repo_relative_exact_file(root, selected_path_text).ok_or("unsafe selected path")?;
    let root_sha256 = normalize_compile_back_digest_value(
        &binding["root_artifact_sha256"],
        CompileBackDigestValueKind::Sha256,
    )
    .ok_or("invalid root digest")?;
    let selected_sha256 = normalize_compile_back_digest_value(
        &binding["selected_image_sha256"],
        CompileBackDigestValueKind::Sha256,
    )
    .ok_or("invalid selected digest")?;

    let mut root_file =
        fs::File::open(&root_path).map_err(|err| format!("root artifact: {err}"))?;
    let mut selected_file =
        fs::File::open(&selected_path).map_err(|err| format!("selected image: {err}"))?;
    let (root_len, selected_len, root_range_sha256) = verify_selected_image_byte_relation(
        &mut root_file,
        &mut selected_file,
        start,
        end,
        &root_sha256,
        &selected_sha256,
    )?;
    if file_sha256(&root_path).as_deref() != Some(&root_sha256)
        || file_sha256(&selected_path).as_deref() != Some(&selected_sha256)
    {
        return Err("selected-image replay artifact changed during readback".into());
    }

    let artifact_census = json!([
        {"role": "root-artifact", "path": root_path_text, "sha256": root_sha256, "bytes": root_len},
        {"role": "selected-image", "path": selected_path_text, "sha256": selected_sha256, "bytes": selected_len},
    ]);
    let subject = json!({
        "candidate_commit": candidate_commit,
        "candidate_tree_oid": tree,
        "executable": executable,
        "artifact_census": artifact_census,
        "range": range,
    });
    let subject_bytes = serde_json::to_vec(&subject).map_err(|err| err.to_string())?;
    let obligation_id = format!("sha256:{:x}", Sha256::digest(&subject_bytes));
    Ok(json!({
        "schema_version": SELECTED_IMAGE_REPLAY_SCHEMA,
        "candidate_commit": candidate_commit,
        "candidate_tree_oid": tree,
        "executable": executable,
        "artifact_census": artifact_census,
        "obligations": [{
            "id": obligation_id,
            "relation": "root-range-equals-selected-image/v1",
            "range": range,
        }],
        "transcript": [{
            "obligation_id": obligation_id,
            "root_range_sha256": root_range_sha256,
            "selected_image_sha256": selected_sha256,
        }],
    }))
}

fn selected_image_replay_check_json(
    root: &Path,
    candidate_commit: &str,
    evidence: &serde_json::Value,
) -> serde_json::Value {
    match replay_selected_image_range(root, candidate_commit, evidence) {
        Ok(()) => json!({"status": "passed", "scope": "selected-image-byte-relation-only"}),
        Err(reason) => {
            json!({"status": "blocked", "scope": "selected-image-byte-relation-only", "reason": reason})
        }
    }
}

fn product_proof_release_findings_json(findings: &[GateFinding]) -> serde_json::Value {
    serde_json::Value::Array(
        findings
            .iter()
            .map(|finding| {
                serde_json::to_value(finding).unwrap_or_else(|_| {
                    json!({
                        "code": finding.code,
                        "message": finding.message,
                    })
                })
            })
            .collect(),
    )
}

fn product_proof_release_candidate_commit_binding_json(
    expected: &str,
    evidence: Option<&serde_json::Value>,
) -> serde_json::Value {
    let actual = evidence.and_then(declared_candidate_commit);
    json!({
        "field": "candidate_commit",
        "expected": expected,
        "actual": actual,
        "status": if actual == Some(expected) { "bound" } else { "blocked" },
    })
}

fn product_proof_release_report_runner_json() -> serde_json::Value {
    json!({
        "implementation": "rust",
        "entrypoint": PRODUCT_PROOF_REPORT_COMMAND,
        "python_used": false,
        "tool": "targo-trust",
    })
}

fn declared_compile_back_evidence_kinds_json(
    evidence: Option<&serde_json::Value>,
) -> serde_json::Value {
    let Some(evidence) = evidence else {
        return serde_json::Value::Array(Vec::new());
    };
    let mut declared = BTreeSet::new();
    if let Some(kind) = evidence.get("evidence_kind").and_then(serde_json::Value::as_str) {
        declared.insert(kind.to_string());
    }
    if let Some(kinds) = evidence.get("evidence_kinds").and_then(serde_json::Value::as_array) {
        for kind in kinds.iter().filter_map(serde_json::Value::as_str) {
            declared.insert(kind.to_string());
        }
    }
    serde_json::Value::Array(declared.into_iter().map(serde_json::Value::String).collect())
}

fn compile_back_evidence_kind_checks_json(
    evidence: Option<&serde_json::Value>,
) -> serde_json::Value {
    serde_json::Value::Array(
        PRODUCT_PROOF_RELEASE_REQUIRED_COMPILE_BACK_KINDS
            .iter()
            .map(|kind| {
                let declared =
                    evidence.is_some_and(|evidence| json_declares_evidence_kind(evidence, kind));
                json!({
                    "kind": kind,
                    "status": if declared { "passed" } else { "blocked" },
                    "declared": declared,
                })
            })
            .collect(),
    )
}

fn product_proof_release_artifact_checks_json(
    root: &Path,
    evidence: &serde_json::Value,
) -> serde_json::Value {
    let binding =
        evidence.get("compile_back_artifact_digest_binding").and_then(serde_json::Value::as_object);
    serde_json::Value::Array(
        COMPILE_BACK_ALL_DIGESTS
            .iter()
            .filter(|requirement| {
                matches!(requirement.value_kind, CompileBackDigestValueKind::Sha256)
            })
            .map(|requirement| {
                let path_field = requirement.path_field.expect("sha256 requirement has a path");
                let expected_sha256 =
                    binding.and_then(|binding| binding.get(requirement.json_field)).and_then(
                        |value| normalize_compile_back_digest_value(value, requirement.value_kind),
                    );
                let path_text = binding
                    .and_then(|binding| binding.get(path_field))
                    .and_then(serde_json::Value::as_str)
                    .map(str::trim)
                    .filter(|path| !path.is_empty());
                let actual_sha256 = path_text
                    .and_then(|path_text| repo_relative_exact_file(root, path_text))
                    .and_then(|path| file_sha256(&path));
                let passed = expected_sha256
                    .as_deref()
                    .zip(actual_sha256.as_deref())
                    .is_some_and(|(expected, actual)| expected == actual);
                json!({
                    "status": if passed { "passed" } else { "blocked" },
                    "check": "sha256-readback",
                    "digest_field": requirement.json_field,
                    "path_field": path_field,
                    "path": path_text,
                    "expected_sha256": expected_sha256,
                    "actual_sha256": actual_sha256,
                })
            })
            .collect(),
    )
}

fn product_proof_release_selected_image_range_check_json(
    root: &Path,
    evidence: &serde_json::Value,
) -> serde_json::Value {
    let binding = evidence.get("compile_back_artifact_digest_binding");
    let digest_defect = compile_back_digest_requirement_defect(
        root,
        binding,
        &COMPILE_BACK_SELECTED_IMAGE_DIGEST[0],
    );
    let range_defect = compile_back_digest_requirement_defect(
        root,
        binding,
        &COMPILE_BACK_SELECTED_IMAGE_RANGE[0],
    );
    let root_digest_defect = compile_back_digest_requirement_defect(
        root,
        binding,
        &COMPILE_BACK_ROOT_ARTIFACT_DIGEST[0],
    );
    let defect = selected_image_range_binding_defect(root, binding);
    let range = binding.and_then(|binding| binding.get("selected_image_range")).and_then(|value| {
        normalize_compile_back_digest_value(value, CompileBackDigestValueKind::Range)
    });
    let path = binding
        .and_then(|binding| binding.get("selected_image_path"))
        .and_then(serde_json::Value::as_str)
        .map(str::trim)
        .filter(|path| !path.is_empty());
    let digest =
        binding.and_then(|binding| binding.get("selected_image_sha256")).and_then(|value| {
            normalize_compile_back_digest_value(value, CompileBackDigestValueKind::Sha256)
        });
    let passed = defect.is_none();
    json!({
        "status": if passed { "passed" } else { "blocked" },
        "check": "selected-image-range-and-digest",
        "range": range,
        "selected_image_path": path,
        "selected_image_sha256": digest,
        "hash_bound": digest_defect.is_none(),
        "root_hash_bound": root_digest_defect.is_none(),
        "range_bound": range_defect.is_none(),
        "defect": defect,
    })
}

fn product_proof_release_clean_runner_json(evidence: &serde_json::Value) -> serde_json::Value {
    match runner_clean_provenance_defect(evidence) {
        Some(defect) => json!({
            "status": "blocked",
            "check": "runner-clean-provenance",
            "reason": defect,
        }),
        None => json!({
            "status": "passed",
            "check": "runner-clean-provenance",
        }),
    }
}

fn product_proof_release_artifact_binding_check_json(
    root: &Path,
    candidate_commit: &str,
    evidence: &serde_json::Value,
) -> serde_json::Value {
    let defects = product_proof_release_artifact_binding_defects(root, candidate_commit, evidence);
    json!({
        "status": if defects.is_empty() { "passed" } else { "blocked" },
        "check": "release-artifact-binding",
        "required": {
            "candidate_commit": candidate_commit,
            "stage2_trustc": "repo-relative build/*/stage2/bin/trustc with sha256 and matching commit_hash",
            "source_tarball": "repo-relative source .tar.xz with sha256",
            "compile_back_evidence": PRODUCT_PROOF_RELEASE_REQUIRED_COMPILE_BACK_KINDS,
        },
        "defects": defects.into_iter().map(|(_, detail)| detail).collect::<Vec<_>>(),
    })
}

fn product_proof_release_artifact_binding_findings(
    root: &Path,
    candidate_commit: &str,
    evidence_path: &Path,
    evidence: &serde_json::Value,
) -> Vec<GateFinding> {
    product_proof_release_artifact_binding_defects(root, candidate_commit, evidence)
        .into_iter()
        .map(|(code, detail)| {
            GateFinding::blocker(
                code,
                format!(
                    "{} release artifact binding is incomplete: {detail}",
                    evidence_path.display()
                ),
            )
        })
        .collect()
}

fn product_proof_release_artifact_binding_defects(
    root: &Path,
    candidate_commit: &str,
    evidence: &serde_json::Value,
) -> Vec<(&'static str, String)> {
    let mut defects = Vec::new();
    let binding = release_artifact_binding(evidence);
    if binding.and_then(|binding| binding.get("schema_version")).and_then(serde_json::Value::as_str)
        != Some(PRODUCT_PROOF_RELEASE_BINDING_SCHEMA)
    {
        defects.push((
            "product-proof-release-binding-schema",
            format!(
                "`release_artifact_binding.schema_version` must be `{PRODUCT_PROOF_RELEASE_BINDING_SCHEMA}`"
            ),
        ));
    }
    match binding.and_then(|binding| binding.get("candidate_commit")).and_then(
        serde_json::Value::as_str,
    ) {
        Some(actual) if actual == candidate_commit => {}
        Some(actual) => defects.push((
            "product-proof-release-binding-candidate-mismatch",
            format!(
                "`release_artifact_binding.candidate_commit` is `{actual}`, expected `{candidate_commit}`"
            ),
        )),
        None => defects.push((
            "product-proof-release-binding-candidate-missing",
            "`release_artifact_binding.candidate_commit` is required".to_string(),
        )),
    }

    match find_stage2_trustc_identity(evidence) {
        Some(identity) => {
            defects.extend(stage2_trustc_identity_defects(root, candidate_commit, identity));
        }
        None => defects.push((
            "product-proof-release-stage2-trustc-missing",
            "missing stage2 Trust compiler binding; provide `release_artifact_binding.stage2_trustc` with repo-relative build/*/stage2/bin/trustc path, sha256, executable=true, version, and commit_hash"
                .to_string(),
        )),
    }

    match find_source_tarball_identity(evidence) {
        Some(identity) => {
            defects.extend(source_tarball_identity_defects(root, candidate_commit, identity));
        }
        None => defects.push((
            "product-proof-release-source-tarball-missing",
            "missing source tarball binding; provide `release_artifact_binding.source_tarball` with repo-relative .tar.xz path, sha256, and candidate_commit"
                .to_string(),
        )),
    }

    defects
}

fn release_artifact_binding(value: &serde_json::Value) -> Option<&serde_json::Value> {
    value.get("release_artifact_binding").filter(|binding| binding.is_object())
}

fn find_stage2_trustc_identity(value: &serde_json::Value) -> Option<&serde_json::Value> {
    release_artifact_binding(value).and_then(|binding| binding.get("stage2_trustc"))
}

fn stage2_trustc_identity_defects(
    root: &Path,
    candidate_commit: &str,
    identity: &serde_json::Value,
) -> Vec<(&'static str, String)> {
    let mut defects = Vec::new();
    if !identity.is_object() {
        return vec![(
            "product-proof-release-stage2-trustc-invalid",
            "stage2 Trust compiler binding is not a structured object".to_string(),
        )];
    }
    if identity.get("name").and_then(serde_json::Value::as_str) != Some("trustc") {
        defects.push((
            "product-proof-release-stage2-trustc-invalid",
            "`stage2_trustc.name` must be `trustc`".to_string(),
        ));
    }
    if identity.get("stage").and_then(serde_json::Value::as_str) != Some("stage2") {
        defects.push((
            "product-proof-release-stage2-trustc-invalid",
            "`stage2_trustc.stage` must be `stage2`".to_string(),
        ));
    }
    let path_text = identity.get("path").and_then(nonempty_json_string_value);
    match path_text {
        Some(path_text) if stage2_trustc_path_satisfied(path_text) => {}
        Some(path_text) => defects.push((
            "product-proof-release-stage2-trustc-path",
            format!("stage2 Trust compiler path `{path_text}` must name build/*/stage2/bin/trustc"),
        )),
        None => defects.push((
            "product-proof-release-stage2-trustc-path",
            "stage2 Trust compiler binding must include repo-relative `path`".to_string(),
        )),
    }
    if !nonempty_json_string(identity, "version") {
        defects.push((
            "product-proof-release-stage2-trustc-version-missing",
            "stage2 Trust compiler binding must include `version` from trustc -Vv".to_string(),
        ));
    }
    match identity.get("commit_hash").and_then(serde_json::Value::as_str) {
        Some(actual) if actual == candidate_commit => {}
        Some(actual) => defects.push((
            "product-proof-release-stage2-trustc-commit-mismatch",
            format!(
                "stage2 Trust compiler commit_hash `{actual}` must match candidate_commit `{candidate_commit}`"
            ),
        )),
        None => defects.push((
            "product-proof-release-stage2-trustc-commit-missing",
            "stage2 Trust compiler binding must include trustc -Vv `commit_hash`".to_string(),
        )),
    }
    if identity.get("executable").and_then(serde_json::Value::as_bool) != Some(true) {
        defects.push((
            "product-proof-release-stage2-trustc-not-executable",
            "stage2 Trust compiler binding must declare executable=true".to_string(),
        ));
    }
    let expected_sha256 = identity.get("sha256").and_then(normalized_sha256_value);
    match (path_text, expected_sha256.as_deref()) {
        (Some(path_text), Some(expected_sha256)) => {
            if let Some(path) = repo_relative_exact_file(root, path_text) {
                if !is_executable_file(&path) {
                    defects.push((
                        "product-proof-release-stage2-trustc-not-executable",
                        format!(
                            "stage2 Trust compiler is not an exact regular executable: {}",
                            path.display()
                        ),
                    ));
                } else {
                    match bound_file_sha256(&path) {
                        Some(actual) if actual == expected_sha256 => {
                            match command_output_text(&path, &["-Vv"]) {
                                Some(output) => {
                                    let live_version = output.lines().next().map(str::trim);
                                    if live_version
                                        != identity
                                            .get("version")
                                            .and_then(serde_json::Value::as_str)
                                            .map(str::trim)
                                    {
                                        defects.push((
                                            "product-proof-release-stage2-trustc-version-mismatch",
                                            "stage2 Trust compiler live `-Vv` version does not match the bound version"
                                                .to_string(),
                                        ));
                                    }
                                    if parse_trustc_commit_hash(&output).as_deref()
                                        != Some(candidate_commit)
                                    {
                                        defects.push((
                                            "product-proof-release-stage2-trustc-commit-mismatch",
                                            format!(
                                                "stage2 Trust compiler live `-Vv` output does not bind candidate {candidate_commit}"
                                            ),
                                        ));
                                    }
                                }
                                None => defects.push((
                                    "product-proof-release-stage2-trustc-version-missing",
                                    "stage2 Trust compiler did not produce bounded successful `-Vv` output"
                                        .to_string(),
                                )),
                            }
                            if bound_file_sha256(&path).as_deref() != Some(expected_sha256) {
                                defects.push((
                                    "product-proof-release-stage2-trustc-hash",
                                    "stage2 Trust compiler changed during live identity revalidation"
                                        .to_string(),
                                ));
                            }
                        }
                        Some(actual) => defects.push((
                            "product-proof-release-stage2-trustc-hash",
                            format!(
                                "stage2 Trust compiler {} hash mismatch: expected {expected_sha256}, observed {actual}",
                                path.display()
                            ),
                        )),
                        None => defects.push((
                            "product-proof-release-stage2-trustc-hash",
                            format!(
                                "stage2 Trust compiler {} could not be hashed as an exact regular file",
                                path.display()
                            ),
                        )),
                    }
                }
            } else {
                defects.push((
                    "product-proof-release-stage2-trustc-path",
                    format!(
                        "stage2 Trust compiler path `{path_text}` is not an exact regular repo-relative file or contains a symlink component"
                    ),
                ));
            }
        }
        (_, None) => defects.push((
            "product-proof-release-stage2-trustc-hash",
            "stage2 Trust compiler binding must include a valid 64-hex `sha256`".to_string(),
        )),
        _ => {}
    }
    defects
}

fn find_source_tarball_identity(value: &serde_json::Value) -> Option<&serde_json::Value> {
    release_artifact_binding(value).and_then(|binding| binding.get("source_tarball"))
}

fn source_tarball_identity_defects(
    root: &Path,
    candidate_commit: &str,
    identity: &serde_json::Value,
) -> Vec<(&'static str, String)> {
    let mut defects = Vec::new();
    if !identity.is_object() {
        return vec![(
            "product-proof-release-source-tarball-invalid",
            "source tarball binding is not a structured object".to_string(),
        )];
    }
    let path_text = source_tarball_entry_path_text(identity);
    match path_text {
        Some(path_text) if source_tarball_path_satisfied(path_text) => {}
        Some(path_text) => defects.push((
            "product-proof-release-source-tarball-path",
            format!("source tarball path `{path_text}` must name a .tar.xz archive"),
        )),
        None => defects.push((
            "product-proof-release-source-tarball-path",
            "source tarball binding must include canonical repo-relative `path`".to_string(),
        )),
    }
    match identity.get("candidate_commit").and_then(serde_json::Value::as_str) {
        Some(actual) if actual == candidate_commit => {}
        Some(actual) => defects.push((
            "product-proof-release-source-tarball-candidate-mismatch",
            format!("source tarball candidate_commit `{actual}` must match `{candidate_commit}`"),
        )),
        None => defects.push((
            "product-proof-release-source-tarball-candidate-missing",
            "source tarball binding must include `candidate_commit`".to_string(),
        )),
    }
    let expected_sha256 = identity.get("sha256").and_then(normalized_sha256_value);
    match (path_text, expected_sha256.as_deref()) {
        (Some(path_text), Some(expected_sha256)) => match repo_relative_exact_file(root, path_text) {
            Some(path) => match source_tarball_archive_identity(&path) {
                Ok((actual, archive_commit)) => {
                    if actual != expected_sha256 {
                        defects.push((
                            "product-proof-release-source-tarball-hash",
                            format!(
                                "source tarball hash mismatch for {}: expected {expected_sha256}, got {actual}",
                                path.display()
                            ),
                        ));
                    }
                    if archive_commit != candidate_commit {
                        defects.push((
                            "product-proof-release-source-tarball-candidate-mismatch",
                            format!(
                                "source tarball {} embeds git-commit-hash {archive_commit}, expected {candidate_commit}",
                                path.display()
                            ),
                        ));
                    }
                }
                Err(detail) => defects.push((
                    "product-proof-release-source-tarball-hash",
                    format!("source tarball {} is not a bound source archive: {detail}", path.display()),
                )),
            },
            None => defects.push((
                "product-proof-release-source-tarball-hash",
                "source tarball must be an exact regular repo-relative archive without symlink components"
                    .to_string(),
            )),
        },
        (_, None) => defects.push((
            "product-proof-release-source-tarball-hash",
            "source tarball binding must include canonical 64-hex `sha256`".to_string(),
        )),
        _ => {}
    }
    defects
}

fn source_tarball_entry_path_text(entry: &serde_json::Value) -> Option<&str> {
    entry.get("path").and_then(nonempty_json_string_value)
}

fn source_tarball_archive_identity(path: &Path) -> Result<(String, String), String> {
    let before = fs::symlink_metadata(path).map_err(|err| format!("archive metadata: {err}"))?;
    if !before.file_type().is_file() || before.len() > MAX_SOURCE_ARCHIVE_COMPRESSED_BYTES {
        return Err(format!(
            "archive must be an exact regular file within the compressed-byte bound \
             ({}/{} bytes)",
            before.len(),
            MAX_SOURCE_ARCHIVE_COMPRESSED_BYTES
        ));
    }
    let mut file = fs::File::open(path).map_err(|err| format!("open archive: {err}"))?;
    let opened = file.metadata().map_err(|err| format!("opened archive metadata: {err}"))?;
    if !same_source_archive_snapshot(&before, &opened) {
        return Err("archive changed before it was opened".into());
    }
    let sha256 = opened_source_archive_sha256(&mut file, before.len())?;
    let filename = path.file_name().and_then(|name| name.to_str()).ok_or("invalid archive name")?;
    let package = filename.strip_suffix(".tar.xz").ok_or("invalid archive suffix")?;
    let member = format!("{package}/git-commit-hash");
    file.seek(io::SeekFrom::Start(0)).map_err(|err| format!("rewind archive: {err}"))?;
    let stream = xz2::stream::Stream::new_stream_decoder(MAX_SOURCE_ARCHIVE_XZ_MEMORY_BYTES, 0)
        .map_err(|err| format!("initialize bounded XZ decoder: {err}"))?;
    let decoder = xz2::bufread::XzDecoder::new_stream(io::BufReader::new(&mut file), stream);
    let mut archive = tar::Archive::new(BoundedSourceArchiveReader { inner: decoder, bytes: 0 });
    let mut archive_commit = None;
    let mut members = 0_usize;
    let mut pending_longname: Option<Vec<u8>> = None;
    let mut namespace = source_archive::Namespace::new(package);
    for entry in archive.entries().map_err(|err| format!("read tar entries: {err}"))?.raw(true) {
        let mut entry = entry.map_err(|err| format!("read tar member: {err}"))?;
        members += 1;
        if members > MAX_SOURCE_ARCHIVE_MEMBERS {
            return Err("source archive member count exceeds its bound".into());
        }
        if entry.size() > MAX_SOURCE_ARCHIVE_DECOMPRESSED_BYTES {
            return Err("source archive member size exceeds its bound".into());
        }
        match entry.header().entry_type() {
            tar::EntryType::GNULongName => {
                if pending_longname.is_some() || entry.size() > MAX_SOURCE_ARCHIVE_LONGNAME_BYTES {
                    return Err("source archive has ambiguous or oversized GNU long name".into());
                }
                let mut longname = Vec::with_capacity(entry.size() as usize);
                entry
                    .read_to_end(&mut longname)
                    .map_err(|err| format!("read GNU long name: {err}"))?;
                let longname_path =
                    longname
                        .strip_suffix(&[0])
                        .filter(|path| !path.contains(&0))
                        .ok_or("source archive has an ambiguous GNU long name terminator")?;
                if source_archive_path_targets_revision(longname_path, member.as_bytes())? {
                    return Err(format!("source archive has a GNU long-name alias for {member}"));
                }
                pending_longname = Some(longname_path.to_vec());
                continue;
            }
            tar::EntryType::GNULongLink
            | tar::EntryType::XHeader
            | tar::EntryType::XGlobalHeader => {
                return Err("source archive has unsupported extended tar headers".into());
            }
            _ => {}
        }
        let longname = pending_longname.take();
        let path_bytes = entry.path_bytes();
        let raw_path = path_bytes.as_ref();
        if source_archive_path_targets_revision(raw_path, member.as_bytes())?
            && raw_path != member.as_bytes()
        {
            return Err(format!("source archive member path aliases {member}"));
        }
        if raw_path != member.as_bytes() {
            namespace.register(
                longname.as_deref().unwrap_or(raw_path),
                entry.header().entry_type(),
                entry.link_name_bytes().as_deref(),
                entry.size(),
            )?;
            continue;
        }
        if longname.is_some() {
            return Err(format!("{member} is overridden by a GNU long-name alias"));
        }
        if archive_commit.is_some() {
            return Err(format!("archive has duplicate {member} entries"));
        }
        if !entry.header().entry_type().is_file() || entry.size() != 40 {
            return Err(format!("{member} must be an exact regular 40-byte member"));
        }
        namespace.register(raw_path, tar::EntryType::Regular, None, entry.size())?;
        let mut bytes = [0_u8; 40];
        entry.read_exact(&mut bytes).map_err(|err| format!("read {member}: {err}"))?;
        let commit = std::str::from_utf8(&bytes).map_err(|_| format!("{member} is not UTF-8"))?;
        if !candidate_commit_is_40_hex(commit) {
            return Err(format!("{member} must contain exactly one 40-hex revision"));
        }
        archive_commit = Some(commit.to_string());
    }
    if pending_longname.is_some() {
        return Err("source archive ends with an unmatched GNU long-name header".into());
    }
    namespace.finish()?;
    let mut reader = archive.into_inner();
    let mut remaining = [0_u8; 8192];
    loop {
        let read = reader.read(&mut remaining).map_err(|err| format!("finish XZ stream: {err}"))?;
        if read == 0 {
            break;
        }
        if remaining[..read].iter().any(|byte| *byte != 0) {
            return Err("source archive has nonzero data after the tar terminator".into());
        }
    }
    let mut compressed = reader.inner.into_inner();
    let mut padding_len = 0_u64;
    loop {
        let read = compressed
            .read(&mut remaining)
            .map_err(|err| format!("read XZ stream padding: {err}"))?;
        if read == 0 {
            break;
        }
        padding_len += read as u64;
        if padding_len > MAX_SOURCE_ARCHIVE_XZ_PADDING_BYTES
            || remaining[..read].iter().any(|byte| *byte != 0)
        {
            return Err("source archive has invalid or excessive XZ stream padding".into());
        }
    }
    if !padding_len.is_multiple_of(4) {
        return Err("XZ stream padding is not four-byte aligned".into());
    }
    drop(compressed);
    if opened_source_archive_sha256(&mut file, before.len())? != sha256 {
        return Err("archive changed during revision readback".to_string());
    }
    let opened_after = file.metadata().map_err(|err| format!("opened archive metadata: {err}"))?;
    let after = fs::symlink_metadata(path).map_err(|err| format!("archive metadata: {err}"))?;
    if !same_source_archive_snapshot(&before, &opened_after)
        || !same_source_archive_snapshot(&before, &after)
    {
        return Err("archive path or opened file changed during revision readback".into());
    }
    Ok((sha256, archive_commit.ok_or_else(|| format!("archive lacks {member}"))?))
}

fn source_archive_path_targets_revision(path: &[u8], member: &[u8]) -> Result<bool, String> {
    if path.is_empty() || path[0] == b'/' || path.contains(&b'\\') {
        return Err("source archive member has an ambiguous extraction path".into());
    }
    let mut parts = Vec::new();
    for part in path.split(|byte| *byte == b'/') {
        match part {
            b"" | b"." => {}
            b".." => {
                if parts.pop().is_none() {
                    return Err("source archive member escapes its extraction root".into());
                }
            }
            _ => parts.push(part),
        }
    }
    if parts.is_empty() {
        return Err("source archive member has an empty extraction path".into());
    }
    let mut expected = member.split(|byte| *byte == b'/');
    Ok(parts
        .into_iter()
        .all(|part| expected.next().is_some_and(|target| part.eq_ignore_ascii_case(target)))
        && expected.next().is_none())
}

struct BoundedSourceArchiveReader<R> {
    inner: R,
    bytes: u64,
}

impl<R: io::Read> io::Read for BoundedSourceArchiveReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }
        let remaining = MAX_SOURCE_ARCHIVE_DECOMPRESSED_BYTES.saturating_sub(self.bytes);
        let allowed =
            usize::try_from(remaining.saturating_add(1)).unwrap_or(usize::MAX).min(buf.len());
        let read = self.inner.read(&mut buf[..allowed])?;
        if read as u64 > remaining {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "source archive exceeds its decompressed-byte bound",
            ));
        }
        self.bytes += read as u64;
        Ok(read)
    }
}

fn opened_source_archive_sha256(file: &mut fs::File, expected_len: u64) -> Result<String, String> {
    file.seek(io::SeekFrom::Start(0)).map_err(|err| format!("rewind archive: {err}"))?;
    let mut prefix = [0_u8; 6];
    file.read_exact(&mut prefix).map_err(|err| format!("read XZ header: {err}"))?;
    if prefix != [0xfd, b'7', b'z', b'X', b'Z', 0x00] {
        return Err("archive lacks the XZ stream header".into());
    }
    let mut hasher = Sha256::new();
    hasher.update(prefix);
    let mut total = 6_u64;
    let mut bytes = [0_u8; 64 * 1024];
    loop {
        let read = file.read(&mut bytes).map_err(|err| format!("hash archive: {err}"))?;
        if read == 0 {
            break;
        }
        total = total.checked_add(read as u64).ok_or("archive length overflow")?;
        if total > expected_len {
            return Err("archive grew during hash readback".into());
        }
        hasher.update(&bytes[..read]);
    }
    if total != expected_len {
        return Err("archive length changed during hash readback".into());
    }
    Ok(format!("{:x}", hasher.finalize()))
}

#[cfg(unix)]
fn same_source_archive_snapshot(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    use std::os::unix::fs::MetadataExt as _;

    left.file_type().is_file()
        && right.file_type().is_file()
        && left.dev() == right.dev()
        && left.ino() == right.ino()
        && left.len() == right.len()
        && left.mode() == right.mode()
        && left.mtime() == right.mtime()
        && left.mtime_nsec() == right.mtime_nsec()
        && left.ctime() == right.ctime()
        && left.ctime_nsec() == right.ctime_nsec()
}

#[cfg(not(unix))]
fn same_source_archive_snapshot(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.file_type().is_file()
        && right.file_type().is_file()
        && left.len() == right.len()
        && left.modified().ok() == right.modified().ok()
}

fn stage2_trustc_path_satisfied(path_text: &str) -> bool {
    let components: Vec<_> = Path::new(path_text)
        .components()
        .filter_map(|component| match component {
            std::path::Component::Normal(value) => value.to_str(),
            _ => None,
        })
        .collect();
    components.len() == 5
        && components[0] == "build"
        && !components[1].is_empty()
        && components[2] == "stage2"
        && components[3] == "bin"
        && components[4] == format!("trustc{}", std::env::consts::EXE_SUFFIX)
}

fn source_tarball_path_satisfied(path_text: &str) -> bool {
    Path::new(path_text)
        .file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| name.ends_with(".tar.xz"))
}

fn command_output_text(path: &Path, args: &[&str]) -> Option<String> {
    let mut command = Command::new(path);
    command.args(args);
    let output = bounded_process::output(
        &mut command,
        &format!("product-proof tool identity probe for {}", path.display()),
        64 * 1024,
        TOOL_IDENTITY_PROBE_HANG_GUARD,
    )
    .ok()?;
    if !output.status.success() {
        return None;
    }
    String::from_utf8(output.stdout).ok()
}

fn parse_trustc_commit_hash(version_output: &str) -> Option<String> {
    version_output.lines().find_map(|line| {
        let (key, value) = line.split_once(':')?;
        let value = value.trim();
        (key.trim() == "commit-hash" && candidate_commit_is_40_hex(value))
            .then(|| value.to_string())
    })
}

fn candidate_commit_is_40_hex(candidate_commit: &str) -> bool {
    candidate_commit.len() == 40 && candidate_commit.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn product_proof_stub_artifact_bindings(
    root: &Path,
    artifacts: &[String],
) -> Result<BTreeMap<String, ProductProofStubArtifactBinding>, String> {
    let mut bindings = BTreeMap::new();
    for artifact in artifacts {
        let (field, path_text) = product_proof_stub_artifact_spec(artifact)?;
        let requirement = compile_back_artifact_requirement_for_input(field).ok_or_else(|| {
            format!(
                "`{field}` is not a digest-bound compile-back artifact field; use one of {}",
                compile_back_stub_artifact_field_list()
            )
        })?;
        let path_field = requirement.path_field.expect("artifact field has path");
        let path_text = path_text.trim();
        let Some(path) = repo_relative_exact_file(root, path_text) else {
            return Err(format!(
                "--artifact {field}=... path `{path_text}` must be an exact regular repo-relative file with no symlink components"
            ));
        };
        let sha256 = file_sha256(&path).ok_or_else(|| {
            format!("--artifact {field}=... path is missing or unreadable: {}", path.display())
        })?;
        if bindings
            .insert(
                requirement.json_field.to_string(),
                ProductProofStubArtifactBinding {
                    path_field,
                    path_text: path_text.to_string(),
                    sha256,
                },
            )
            .is_some()
        {
            return Err(format!(
                "duplicate --artifact for compile-back digest field `{}`",
                requirement.json_field
            ));
        }
    }
    Ok(bindings)
}

fn product_proof_stub_artifact_spec(spec: &str) -> Result<(&str, &str), String> {
    let Some((field, path)) = spec.split_once('=') else {
        return Err(format!("--artifact `{spec}` must use `<digest-field>=<repo-relative path>`"));
    };
    let field = field.trim();
    let path = path.trim();
    if field.is_empty() || path.is_empty() {
        return Err(format!("--artifact `{spec}` must include both a digest field and a path"));
    }
    Ok((field, path))
}

fn compile_back_artifact_requirement_for_input(
    field: &str,
) -> Option<&'static CompileBackDigestRequirement> {
    COMPILE_BACK_ALL_DIGESTS.iter().filter(|requirement| requirement.path_field.is_some()).find(
        |requirement| field == requirement.json_field || requirement.path_field == Some(field),
    )
}

fn validate_product_proof_stub_required_material(
    evidence_kind: &str,
    requirements: &'static [CompileBackDigestRequirement],
    artifact_bindings: &BTreeMap<String, ProductProofStubArtifactBinding>,
    selected_image_range: Option<&str>,
) -> Result<(), String> {
    let mut missing = BTreeSet::new();
    for requirement in requirements {
        match requirement.value_kind {
            CompileBackDigestValueKind::Sha256 => {
                if !artifact_bindings.contains_key(requirement.json_field) {
                    missing.insert(format!(
                        "--artifact {}=<repo-relative path>",
                        requirement.json_field
                    ));
                }
            }
            CompileBackDigestValueKind::Range => {
                if selected_image_range.is_none() {
                    missing.insert("--selected-image-range <start>..<end>".to_string());
                }
            }
        }
    }
    if evidence_kind == "compile-back-selected-image-range"
        && !artifact_bindings.contains_key("selected_image_sha256")
    {
        missing.insert("--artifact selected_image_sha256=<repo-relative path>".to_string());
    }
    if missing.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "`{evidence_kind}` stub is missing required digest-bound input material: {}",
            missing.into_iter().collect::<Vec<_>>().join(", ")
        ))
    }
}

fn product_proof_manifest_skeleton_text(
    compile_back_evidence_path: &str,
    certificate_path: Option<&str>,
    release_artifact_binding: Option<&serde_json::Value>,
) -> String {
    let mut manifest = String::new();
    manifest.push_str("schema_version = \"trust.product-proof-manifest.v1\"\n");
    manifest.push_str("status = \"blocked\"\n");
    manifest.push_str(
        "reason = \"fail-closed skeleton: compile-back artifacts are digest-bound, but product-proof pass evidence has not been produced\"\n\n",
    );
    manifest.push_str("[release_artifact_binding]\n");
    manifest.push_str("status = \"blocked\"\n");
    manifest
        .push_str(&format!("compile_back_evidence = {}\n", toml_quote(compile_back_evidence_path)));
    if let Some(certificate_path) = certificate_path {
        manifest.push_str(&format!("certificate = {}\n", toml_quote(certificate_path)));
    }
    if let Some(binding) = release_artifact_binding {
        if let Some(candidate_commit) =
            binding.get("candidate_commit").and_then(serde_json::Value::as_str)
        {
            manifest.push_str(&format!("candidate_commit = {}\n", toml_quote(candidate_commit)));
        }
        if let Some(stage2) = binding.get("stage2_trustc") {
            if let Some(path) = stage2.get("path").and_then(serde_json::Value::as_str) {
                manifest.push_str(&format!("stage2_trustc = {}\n", toml_quote(path)));
            }
            if let Some(sha256) = stage2.get("sha256").and_then(serde_json::Value::as_str) {
                manifest.push_str(&format!("stage2_trustc_sha256 = {}\n", toml_quote(sha256)));
            }
        }
        if let Some(source) = binding.get("source_tarball") {
            if let Some(path) = source.get("path").and_then(serde_json::Value::as_str) {
                manifest.push_str(&format!("source_tarball = {}\n", toml_quote(path)));
            }
            if let Some(sha256) = source.get("sha256").and_then(serde_json::Value::as_str) {
                manifest.push_str(&format!("source_tarball_sha256 = {}\n", toml_quote(sha256)));
            }
        }
    }
    manifest.push('\n');

    for class in product_proof_evidence_class_requirements() {
        manifest.push_str("[[evidence_classes]]\n");
        manifest.push_str(&format!("class = {}\n", toml_quote(class.class)));
        manifest.push_str("status = \"blocked\"\n");
        manifest.push_str(
            "reason = \"release evidence for this product-proof class has not been produced\"\n\n",
        );
    }

    for component in product_proof_component_requirements() {
        manifest.push_str("[[components]]\n");
        manifest.push_str(&format!("component = {}\n", toml_quote(component.component)));
        manifest.push_str("status = \"blocked\"\n");
        if component.component == "binary/decomp gates" {
            manifest.push_str(
                "reason = \"compile-back artifact digests are hash-bound; binary lift, decompile, checked-certificate, and proof_results evidence remain blocked\"\n",
            );
            manifest.push_str("evidence = [\n");
            for kind in PRODUCT_PROOF_RELEASE_REQUIRED_COMPILE_BACK_KINDS {
                manifest.push_str(&format!(
                    "  {},\n",
                    toml_quote(&format!("{kind}:{compile_back_evidence_path}"))
                ));
            }
            manifest.push_str("]\n\n");
        } else {
            manifest.push_str(
                "reason = \"release product-proof evidence has not been produced for this component\"\n\n",
            );
        }
    }

    manifest
}

fn toml_quote(value: &str) -> String {
    serde_json::to_string(value).expect("TOML strings use JSON-compatible escaping here")
}

fn compile_back_stub_artifact_field_list() -> String {
    COMPILE_BACK_ALL_DIGESTS
        .iter()
        .filter(|requirement| requirement.path_field.is_some())
        .map(|requirement| requirement.json_field)
        .collect::<Vec<_>>()
        .join(", ")
}

pub(super) fn check_product_proof_coverage(
    root: &Path,
    candidate_commit: Option<&str>,
    candidate_daemon: Option<&BoundToolIdentity>,
) -> GateReport {
    let manifest_path = root.join("release/product-proof.toml");
    let manifest = match read_product_proof_manifest(&manifest_path) {
        Ok(Some(manifest)) => manifest,
        Ok(None) => {
            let mut findings = vec![missing_product_proof_manifest_finding()];
            findings.extend(product_proof_component_requirements().into_iter().map(|component| {
                GateFinding::blocker(
                    "product-proof-evidence-missing",
                    format!(
                        "{} has no accepted product-proof evidence manifest; required evidence: {}",
                        component.component,
                        component.required_evidence.join(", ")
                    ),
                )
            }));
            return GateReport::new("product-proof-coverage", findings);
        }
        Err(err) => {
            return GateReport::new(
                "product-proof-coverage",
                vec![GateFinding::blocker("product-proof-manifest-parse", err)],
            );
        }
    };

    let mut findings = Vec::new();
    let mut evidence_refs = Vec::new();
    findings.extend(validate_product_proof_manifest_metadata(&manifest));
    let requirements = product_proof_component_requirements();
    for required in &requirements {
        let entry = manifest
            .components
            .iter()
            .find(|entry| product_proof_component_matches(&entry.component, required.component));
        match entry {
            Some(entry) if entry.status == "accepted" => {
                validate_product_proof_evidence(ProductProofEvidenceInput {
                    root,
                    candidate_commit,
                    candidate_daemon,
                    required,
                    entry,
                    require_all_required_evidence: true,
                    findings: &mut findings,
                    evidence_refs: &mut evidence_refs,
                });
            }
            Some(entry) if matches!(entry.status.as_str(), "not_shipped" | "not_claimed") => {
                validate_product_proof_evidence(ProductProofEvidenceInput {
                    root,
                    candidate_commit,
                    candidate_daemon,
                    required,
                    entry,
                    require_all_required_evidence: false,
                    findings: &mut findings,
                    evidence_refs: &mut evidence_refs,
                });
                findings.push(GateFinding::blocker(
                    "product-proof-component-excluded",
                    format!(
                        "{} is {}{}",
                        required.component,
                        entry.status.replace('_', "-"),
                        entry
                            .reason
                            .as_deref()
                            .map(|reason| format!(": {reason}"))
                            .unwrap_or_default()
                    ),
                ));
            }
            Some(entry) if entry.status == "blocked" => {
                findings.push(GateFinding::blocker(
                    "product-proof-component-blocked",
                    format!(
                        "{} is blocked{}",
                        required.component,
                        entry
                            .reason
                            .as_deref()
                            .map(|reason| format!(": {reason}"))
                            .unwrap_or_default()
                    ),
                ));
            }
            Some(entry) => findings.push(GateFinding::error(
                "product-proof-status-unsupported",
                format!(
                    "{} has unsupported product-proof status `{}`",
                    required.component, entry.status
                ),
            )),
            None => findings.push(GateFinding::blocker(
                "product-proof-component-missing",
                missing_product_proof_component_message(required),
            )),
        }
    }
    for entry in &manifest.components {
        if !requirements
            .iter()
            .any(|required| product_proof_component_matches(&entry.component, required.component))
        {
            findings.push(GateFinding::error(
                "product-proof-component-unknown",
                format!(
                    "unknown product-proof component `{}`; use canonical Trust component names",
                    entry.component
                ),
            ));
        }
    }

    GateReport::new("product-proof-coverage", findings).with_evidence_refs(evidence_refs)
}

fn missing_product_proof_manifest_finding() -> GateFinding {
    let compile_back_refs = PRODUCT_PROOF_RELEASE_REQUIRED_COMPILE_BACK_KINDS
        .iter()
        .map(|kind| format!("{kind}:<repo-relative JSON path>"))
        .collect::<Vec<_>>()
        .join(", ");
    GateFinding::blocker(
        "product-proof-manifest-missing",
        format!(
            "missing release/product-proof.toml; a product-proof release report is domination-admissible only after that manifest declares schema_version = \"trust.product-proof-manifest.v1\", status = \"accepted\", accepted component rows, and binary/decomp gates evidence refs for: {compile_back_refs}"
        ),
    )
}

fn missing_product_proof_component_message(required: &ProductProofComponent) -> String {
    if required.component == "binary/decomp gates" {
        format!(
            "missing product-proof component `binary/decomp gates` in release/product-proof.toml; domination requires [[components]] component = \"binary/decomp gates\", status = \"accepted\", and evidence refs for: {}",
            PRODUCT_PROOF_RELEASE_REQUIRED_COMPILE_BACK_KINDS
                .iter()
                .map(|kind| format!("{kind}:<repo-relative JSON path>"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    } else {
        format!("missing product-proof component `{}`", required.component)
    }
}

fn validate_product_proof_manifest_metadata(manifest: &ProductProofManifest) -> Vec<GateFinding> {
    let mut findings = Vec::new();
    match manifest.schema_version.as_deref() {
        Some("trust.product-proof-manifest.v1") => {}
        Some(schema_version) => findings.push(GateFinding::error(
            "product-proof-manifest-schema",
            format!("unsupported product-proof manifest schema `{schema_version}`"),
        )),
        None => findings.push(GateFinding::blocker(
            "product-proof-manifest-schema-missing",
            "product-proof manifest must declare schema_version = \"trust.product-proof-manifest.v1\"",
        )),
    }
    match manifest.status.as_deref() {
        Some("accepted") => {}
        Some("blocked") => findings.push(GateFinding::blocker(
            "product-proof-manifest-blocked",
            format!(
                "product-proof manifest is blocked{}",
                manifest.reason.as_deref().map(|reason| format!(": {reason}")).unwrap_or_default()
            ),
        )),
        Some(other) => findings.push(GateFinding::error(
            "product-proof-manifest-status-unsupported",
            format!("unsupported product-proof manifest status `{other}`"),
        )),
        None => findings.push(GateFinding::blocker(
            "product-proof-manifest-status-missing",
            "product-proof manifest must declare top-level status = \"accepted\"",
        )),
    }

    let class_requirements = product_proof_evidence_class_requirements();
    let mut seen = Vec::new();
    for entry in &manifest.evidence_classes {
        if !class_requirements.iter().any(|required| required.class == entry.class) {
            findings.push(GateFinding::error(
                "product-proof-evidence-class-unknown",
                format!("unknown product-proof evidence class `{}`", entry.class),
            ));
        }
        if seen.iter().any(|class| class == &entry.class) {
            findings.push(GateFinding::error(
                "product-proof-evidence-class-duplicate",
                format!("duplicate product-proof evidence class `{}`", entry.class),
            ));
        }
        seen.push(entry.class.clone());
        if !product_proof_manifest_status_supported(&entry.status) {
            findings.push(GateFinding::error(
                "product-proof-evidence-class-status-unsupported",
                format!(
                    "{} has unsupported product-proof evidence-class status `{}`",
                    entry.class, entry.status
                ),
            ));
        }
        if entry.status == "accepted" {
            let bound_gates = class_requirements
                .iter()
                .find(|required| required.class == entry.class)
                .map(|required| required.gates)
                .unwrap_or(&[]);
            if bound_gates.is_empty() {
                findings.push(GateFinding::blocker(
                    "product-proof-evidence-class-unbound",
                    format!(
                        "{} cannot be accepted without release gate binding evidence",
                        entry.class
                    ),
                ));
            }
        }
    }

    let mut seen_components = BTreeSet::new();
    for entry in &manifest.components {
        if !seen_components.insert(entry.component.as_str()) {
            findings.push(GateFinding::error(
                "product-proof-component-duplicate",
                format!("duplicate product-proof component `{}`", entry.component),
            ));
        }
    }
    findings
}

fn product_proof_manifest_status_supported(status: &str) -> bool {
    matches!(status, "accepted" | "blocked" | "missing_evidence" | "not_claimed" | "not_shipped")
}

struct ProductProofEvidenceInput<'a> {
    root: &'a Path,
    candidate_commit: Option<&'a str>,
    candidate_daemon: Option<&'a BoundToolIdentity>,
    required: &'a ProductProofComponent,
    entry: &'a ProductProofManifestComponent,
    require_all_required_evidence: bool,
    findings: &'a mut Vec<GateFinding>,
    evidence_refs: &'a mut Vec<String>,
}

fn validate_product_proof_evidence(input: ProductProofEvidenceInput<'_>) {
    let ProductProofEvidenceInput {
        root,
        candidate_commit,
        candidate_daemon,
        required,
        entry,
        require_all_required_evidence,
        findings,
        evidence_refs,
    } = input;
    if entry.evidence.is_empty() {
        findings.push(GateFinding::blocker(
            "product-proof-evidence-empty",
            format!("{} has no evidence references", required.component),
        ));
        return;
    }

    let Some(candidate_commit) = candidate_commit else {
        findings.push(GateFinding::blocker(
            "product-proof-candidate-missing",
            format!("{} cannot bind evidence without a candidate commit", required.component),
        ));
        return;
    };

    let mut covered = Vec::new();
    for evidence in &entry.evidence {
        let Some((kind, path_text)) = evidence.split_once(':') else {
            findings.push(GateFinding::blocker(
                "product-proof-evidence-untyped",
                format!(
                    "{} evidence `{evidence}` must use `<required evidence>:<repo-relative JSON path>`",
                    required.component
                ),
            ));
            continue;
        };
        let kind = kind.trim();
        if !required.required_evidence.contains(&kind) {
            findings.push(GateFinding::blocker(
                "product-proof-evidence-kind",
                format!(
                    "{} evidence kind `{kind}` is not one of: {}",
                    required.component,
                    required.required_evidence.join(", ")
                ),
            ));
            continue;
        }

        let Some(path) = repo_relative_exact_file(root, path_text.trim()) else {
            findings.push(GateFinding::blocker(
                "product-proof-evidence-path",
                format!(
                    "{} evidence `{evidence}` must point to an exact regular repo-relative file with no symlink components",
                    required.component
                ),
            ));
            continue;
        };

        let bytes = match read_bounded_file(&path, MAX_RELEASE_TRANSCRIPT_REPORT_BYTES) {
            Ok(bytes) => bytes,
            Err(err) if err.kind() == io::ErrorKind::NotFound => {
                findings.push(GateFinding::blocker(
                    "product-proof-evidence-missing",
                    format!("{} evidence file is missing: {}", required.component, path.display()),
                ));
                continue;
            }
            Err(err) => {
                findings.push(GateFinding::error(
                    "product-proof-evidence-read",
                    format!("failed to read {}: {err}", path.display()),
                ));
                continue;
            }
        };

        let json = match parse_product_proof_json(&bytes) {
            Ok(json) => json,
            Err(err) => {
                findings.push(GateFinding::blocker(
                    "product-proof-evidence-json",
                    format!("{} is not a JSON evidence artifact: {err}", path.display()),
                ));
                continue;
            }
        };

        if json.get("schema_version").and_then(serde_json::Value::as_str)
            != Some(PRODUCT_PROOF_EVIDENCE_SCHEMA)
        {
            findings.push(GateFinding::blocker(
                "product-proof-evidence-schema",
                format!(
                    "{} must declare schema_version `{PRODUCT_PROOF_EVIDENCE_SCHEMA}`",
                    path.display()
                ),
            ));
            continue;
        }
        if !json_declares_evidence_kind(&json, kind) {
            findings.push(GateFinding::blocker(
                "product-proof-evidence-kind-mismatch",
                format!("{} does not declare evidence_kind `{kind}`", path.display()),
            ));
            continue;
        }

        let Some(declared_candidate) = declared_candidate_commit(&json) else {
            findings.push(GateFinding::blocker(
                "product-proof-evidence-candidate-missing",
                format!("{} does not bind candidate_commit at the evidence root", path.display()),
            ));
            continue;
        };
        if declared_candidate != candidate_commit {
            findings.push(GateFinding::blocker(
                "product-proof-evidence-candidate-mismatch",
                format!("{} does not bind candidate commit {candidate_commit}", path.display()),
            ));
            continue;
        }
        let mut candidate_values = Vec::new();
        collect_candidate_commit_values(&json, &mut candidate_values);
        if candidate_values.iter().any(|value| *value != candidate_commit) {
            findings.push(GateFinding::blocker(
                "product-proof-evidence-candidate-mismatch",
                format!(
                    "{} contains conflicting candidate_commit values for {candidate_commit}",
                    path.display()
                ),
            ));
            continue;
        }

        // a `proof` release claim must be backed by actual
        // discharge *content*, not merely well-formed metadata (schema version,
        // kind, commit). Without this the gate stamps "proof" on a placeholder.
        let content_class = if kind == "Trust daemon protocol smoke" {
            ProductProofContentClass::TrustdOperational
        } else {
            ProductProofContentClass::SolverProof
        };
        if let Some((code, detail)) = proof_content_defect_for_class(&json, content_class) {
            findings.push(GateFinding::blocker(
                code,
                format!("{} evidence {}: {detail}", required.component, path.display()),
            ));
            continue;
        }
        if matches!(
            kind,
            "Trust daemon binary identity" | "Trust daemon protocol smoke" | "version identity"
        ) {
            if let Some(detail) = candidate_daemon_binding_defect(
                root,
                candidate_commit,
                candidate_daemon,
                kind,
                &json,
            ) {
                findings.push(GateFinding::blocker(
                    "product-proof-daemon-candidate-binding-missing",
                    format!("{} evidence {}: {detail}", required.component, path.display()),
                ));
                continue;
            }
        }
        if let Some((code, detail)) =
            materialized_evidence_defect(root, kind, &json, candidate_daemon)
        {
            findings.push(GateFinding::blocker(
                code,
                format!("{} evidence {}: {detail}", required.component, path.display()),
            ));
            continue;
        }
        if let Some(detail) = compile_back_artifact_digest_evidence_defect(root, kind, &json) {
            findings.push(GateFinding::blocker(
                "product-proof-compile-back-artifact-digest-missing",
                format!("{} evidence {}: {detail}", required.component, path.display()),
            ));
            continue;
        }
        if required.component == "binary/decomp gates"
            && compile_back_artifact_digest_requirements(kind).is_some()
        {
            let binding_findings = product_proof_release_artifact_binding_findings(
                root,
                candidate_commit,
                &path,
                &json,
            );
            if !binding_findings.is_empty() {
                findings.extend(binding_findings);
                continue;
            }
        }

        if content_class == ProductProofContentClass::SolverProof {
            findings.push(GateFinding::blocker(
                PRODUCT_PROOF_SOLVER_EVIDENCE_UNVERIFIED,
                format!(
                    "{} evidence {}: {}",
                    required.component,
                    path.display(),
                    solver_evidence_admission_defect(kind)
                ),
            ));
            continue;
        }

        covered.push(kind.to_string());
        evidence_refs.push(format!("{kind}:{}", path_text.trim()));
    }

    if require_all_required_evidence {
        for &required_kind in required.required_evidence {
            if !covered.iter().any(|covered_kind| covered_kind == required_kind) {
                findings.push(GateFinding::blocker(
                    "product-proof-evidence-kind-missing",
                    missing_required_evidence_message(required.component, required_kind),
                ));
            }
        }
    }
}

/// Detect product-proof evidence that lacks the minimum discharge *shape*.
/// Returns `Some((code, detail))` when the evidence must be rejected.
///
/// The caller, rather than attacker-controlled JSON tags, selects the content
/// class. This check deliberately does not grant solver-proof authority:
/// runner labels, counters, and hashes are all self-declared JSON. Solver-class
/// callers must also apply `solver_evidence_admission_defect`, which remains
/// fail-closed until a kind-specific collector/replayer exists. The one
/// operational class requires a complete daemon state transition and
/// explicitly forbids ceremonial solver counts.
fn proof_content_defect(json: &serde_json::Value) -> Option<(&'static str, String)> {
    proof_content_defect_for_class(json, ProductProofContentClass::SolverProof)
}

/// Return the unconditional admission defect for today's generic solver
/// evidence format. A saved compiler report carries a claim digest, not the
/// canonical VC needed by `trust_certify::recheck_vc`; the structural binary
/// certificate checker binds bytes but does not replay LRAT/LFSC. Neither API
/// can turn an authored JSON transcript into proof authority here.
fn solver_evidence_admission_defect(kind: &str) -> String {
    format!(
        "`{kind}` has no registered kind-specific Rust collector/replayer; self-declared \
         runner identity, proof counts, solver names, artifact hashes, certificate labels, and \
         transcript hashes are not proof. Missing producer contract: invoke the exact candidate \
         executable with a canonical path, pre/post SHA-256, candidate commit and version, exact \
         argv and sanitized environment; export the complete typed obligation set with stable IDs, \
         canonical VC/query bytes, semantic digests, and raw proof bytes in a bounded transcript. \
         Missing replayer contract: independently regenerate the canonical VC/query and digests, \
         reconcile every ID exactly once, and check each proof in its actual format against that \
         query at the declared grade. The saved claim_digest_sha256 cannot reconstruct the VC, \
         and StructuralBinaryCertificateChecker checks bindings, not LRAT/LFSC derivations"
    )
}

fn proof_content_defect_for_class(
    json: &serde_json::Value,
    content_class: ProductProofContentClass,
) -> Option<(&'static str, String)> {
    if let Some((code, detail)) = rust_owned_runner_defect(json) {
        return Some((
            code,
            format!("{detail}; product-proof evidence must come from Rust-owned Trust tooling"),
        ));
    }

    let status_is_invalid = json.get("status").is_some_and(|status| {
        !matches!(status.as_str(), Some("passed" | "accepted" | "proved" | "verified" | "success"))
    });
    let false_or_malformed_bool =
        |field: &str| json.get(field).is_some_and(|value| value.as_bool() != Some(true));
    if status_is_invalid
        || false_or_malformed_bool("product_proof_pass_evidence")
        || false_or_malformed_bool("domination_admissible")
    {
        return Some((
            "product-proof-evidence-content-insufficient",
            "evidence explicitly declares a non-passing or non-admissible status".to_string(),
        ));
    }

    if content_class == ProductProofContentClass::TrustdOperational {
        if json.get("proof_results").is_some() {
            return Some((
                "product-proof-evidence-content-insufficient",
                "daemon protocol evidence is an operational state-transition check, not a solver proof; omit ceremonial `proof_results`"
                    .to_string(),
            ));
        }
        let required = ["ping", "identity", "status", "reserve", "release"];
        let checks = json.get("operational_checks").and_then(serde_json::Value::as_object);
        if checks.is_none_or(|checks| {
            checks.len() != required.len()
                || required.iter().any(|name| {
                    checks.get(*name).and_then(serde_json::Value::as_bool) != Some(true)
                })
        }) {
            return Some((
                "product-proof-evidence-content-insufficient",
                "daemon protocol evidence requires exactly five passing operational_checks: ping, identity, status, reserve, release"
                    .to_string(),
            ));
        }
        return (!proof_evidence_timestamp_satisfied(json)).then(|| {
            (
                "product-proof-evidence-timestamp-missing",
                "daemon protocol evidence requires a material generated_at/checked_at timestamp"
                    .to_string(),
            )
        });
    }

    let Some(results) = json.get("proof_results") else {
        return Some((
            "product-proof-evidence-content-missing",
            "declares no `proof_results`; a product-proof claim requires discharge \
             content (proved/total counts plus a solver attribution), not metadata alone"
                .to_string(),
        ));
    };
    let Some(result_fields) = results.as_object() else {
        return Some((
            "product-proof-evidence-content-insufficient",
            "`proof_results` must be a structured object".to_string(),
        ));
    };

    const RESULT_FIELDS: &[&str] = &[
        "proved",
        "total",
        "total_obligations",
        "failed",
        "unknown",
        "timed_out",
        "timeout",
        "timeouts",
        "total_timed_out",
        "timeout_results",
        "skipped",
        "unknown_results",
        "total_unknown",
        "skipped_results",
        "total_skipped",
        "runtime_checked",
        "inconclusive",
        "unsupported",
        "errored",
        "errors",
        "unattributed_failed",
        "unattributed_unknown",
        "unattributed_proved",
        "design_requirements",
        "by_solver",
    ];
    if let Some(field) = result_fields.keys().find(|field| !RESULT_FIELDS.contains(&field.as_str()))
    {
        return Some((
            "product-proof-evidence-content-insufficient",
            format!("proof_results contains unknown field `{field}`"),
        ));
    }

    let proved = results.get("proved").and_then(serde_json::Value::as_u64);
    let total = results.get("total").and_then(serde_json::Value::as_u64);
    let total_obligations = results.get("total_obligations").and_then(serde_json::Value::as_u64);
    if total.zip(total_obligations).is_some_and(|(left, right)| left != right) {
        return Some((
            "product-proof-evidence-content-insufficient",
            "proof_results.total conflicts with proof_results.total_obligations".to_string(),
        ));
    }
    let total = total.or(total_obligations);
    let counter_defects = non_proof_counter_defects(results);

    match (proved, total) {
        (Some(proved), Some(total))
            if proved > 0 && proved == total && counter_defects.is_empty() =>
        {
            // Fully discharged on paper — but the counts must bind to a concrete
            // run, or they could be fabricated wholesale.
            let has_solver = results
                .get("by_solver")
                .and_then(serde_json::Value::as_array)
                .is_some_and(|solvers| {
                    !solvers.is_empty() && solvers.iter().all(valid_solver_identity_value)
                });
            let has_concrete_binding = proof_concrete_binding_satisfied(json);
            if has_transcript_hash(json) || (has_solver && has_concrete_binding) {
                if proof_evidence_timestamp_satisfied(json) {
                    None
                } else {
                    Some((
                        "product-proof-evidence-timestamp-missing",
                        "declares no material evidence timestamp; proof-grade product-proof \
                         evidence must carry generated_at/checked_at provenance"
                            .to_string(),
                    ))
                }
            } else {
                Some((
                    "product-proof-evidence-unattributed",
                    format!(
                        "reports {proved} proved obligations but binds no solver \
                         attribution plus concrete transcript/artifact binding"
                    ),
                ))
            }
        }
        _ => Some((
            "product-proof-evidence-content-insufficient",
            format!(
                "does not show a fully-discharged proof (require proof_results.proved > 0, \
                 proved == total, and all non-proof counters zero); non-proof counters: {}",
                if counter_defects.is_empty() {
                    "none".to_string()
                } else {
                    counter_defects.join(", ")
                }
            ),
        )),
    }
}

fn rust_owned_runner_defect(json: &serde_json::Value) -> Option<(&'static str, String)> {
    if let Some(detail) = python_runner_defect(json) {
        return Some(("product-proof-evidence-python-runner", detail));
    }

    let Some(runner) = json.get("runner") else {
        return Some((
            "product-proof-evidence-runner-untrusted",
            "declares no structured `runner` identity".to_string(),
        ));
    };
    let Some(runner) = runner.as_object() else {
        return Some((
            "product-proof-evidence-runner-untrusted",
            "declares `runner` but it is not a structured object".to_string(),
        ));
    };

    match runner.get("python_used") {
        Some(serde_json::Value::Bool(false)) => {}
        Some(value) => {
            return Some((
                "product-proof-evidence-runner-untrusted",
                format!("declares runner.python_used={value}; expected false"),
            ));
        }
        None => {
            return Some((
                "product-proof-evidence-runner-untrusted",
                "declares no runner.python_used=false marker".to_string(),
            ));
        }
    }

    if runner_declares_rust_owned_identity(runner) {
        None
    } else {
        Some((
            "product-proof-evidence-runner-untrusted",
            "runner must identify a Rust implementation and Trust-owned entrypoint".to_string(),
        ))
    }
}

fn python_runner_defect(json: &serde_json::Value) -> Option<String> {
    for path in [
        "python_used",
        "runner_python_used",
        "runner_kind",
        "runner_implementation",
        "runner.python_used",
        "runner.language",
        "runner.kind",
        "runner.implementation",
        "runner.command",
        "runner.executable",
        "runner.path",
        "host.runner",
    ] {
        if let Some(value) = dotted_value(json, path) {
            if path_value_declares_python(path, value) {
                return Some(format!("declares {path}={value}"));
            }
        }
    }
    None
}

fn runner_declares_rust_owned_identity(
    runner: &serde_json::Map<String, serde_json::Value>,
) -> bool {
    if runner.get("implementation").and_then(serde_json::Value::as_str) != Some("rust") {
        return false;
    }
    const TOOLS: &[&str] = &[
        "targo-trust",
        "targo",
        "trustc",
        "trustdoc",
        "trustfmt",
        "targo-fmt",
        "tippy",
        "targo-tippy",
        "tippy-driver",
        "trust-analyzer",
        "trustd",
        "trust-miri",
        "targo-miri",
        "trust-mc",
        "trust-bmc",
        "trust-vc-trust-runner",
    ];
    let tool_matches = runner
        .get("tool")
        .and_then(serde_json::Value::as_str)
        .is_some_and(|tool| TOOLS.contains(&tool));
    let entrypoint_matches =
        runner.get("entrypoint").and_then(serde_json::Value::as_str).is_some_and(|entrypoint| {
            entrypoint == "targo trust"
                || entrypoint.starts_with("targo trust ")
                || TOOLS.iter().any(|tool| {
                    entrypoint == *tool
                        || entrypoint
                            .strip_prefix(tool)
                            .is_some_and(|suffix| suffix.starts_with(' '))
                })
        });
    tool_matches || entrypoint_matches
}

fn dotted_value<'a>(value: &'a serde_json::Value, path: &str) -> Option<&'a serde_json::Value> {
    let mut current = value;
    for segment in path.split('.') {
        current = current.get(segment)?;
    }
    Some(current)
}

fn path_value_declares_python(path: &str, value: &serde_json::Value) -> bool {
    if matches!(path, "python_used" | "runner_python_used" | "runner.python_used")
        && value.as_bool() == Some(true)
    {
        return true;
    }
    value_declares_python(value)
}

fn value_declares_python(value: &serde_json::Value) -> bool {
    match value {
        serde_json::Value::String(text) => {
            let lower = text.to_ascii_lowercase();
            lower == "true"
                || lower == "python"
                || lower == "python3"
                || lower == "python2"
                || lower.contains("python")
                || lower.contains(".py")
        }
        serde_json::Value::Array(values) => values.iter().any(value_declares_python),
        serde_json::Value::Object(map) => map.iter().any(|(key, value)| {
            (key == "python_used" && value.as_bool() == Some(true)) || value_declares_python(value)
        }),
        _ => false,
    }
}

fn has_transcript_hash(json: &serde_json::Value) -> bool {
    json.get("proof_transcript_hash")
        .and_then(serde_json::Value::as_str)
        .is_some_and(sha256_value_satisfied)
}

fn proof_concrete_binding_satisfied(json: &serde_json::Value) -> bool {
    has_transcript_hash(json)
        || json
            .get("proof_artifact_sha256")
            .and_then(serde_json::Value::as_str)
            .is_some_and(sha256_value_satisfied)
        || json
            .get("compile_back_artifact_digest_binding")
            .is_some_and(compile_back_artifact_digest_binding_satisfied)
        || json.get("tool_identity").is_some_and(tool_identity_binding_satisfied)
        || (json.get("version_identity").is_some() && version_identity_defect(json).is_none())
        || json.get("binary_identity").is_some_and(binary_identity_binding_satisfied)
        || (declares_source_archive_hashes(json) && source_archive_hashes_defect(json).is_none())
        || (declares_component_artifact_binding(json)
            && artifact_evidence_defect("proof artifact binding", json).is_none())
}

fn proof_evidence_timestamp_satisfied(json: &serde_json::Value) -> bool {
    ["generated_at", "checked_at", "produced_at", "timestamp"]
        .into_iter()
        .filter_map(|field| json.get(field))
        .any(timestamp_value_satisfied)
        || ["generated_at", "checked_at", "produced_at", "timestamp"]
            .into_iter()
            .filter_map(|field| json.get("provenance").and_then(|provenance| provenance.get(field)))
            .any(timestamp_value_satisfied)
        || ["generated_at", "checked_at", "timestamp"]
            .into_iter()
            .filter_map(|field| json.get("runner").and_then(|runner| runner.get(field)))
            .any(timestamp_value_satisfied)
}

fn timestamp_value_satisfied(value: &serde_json::Value) -> bool {
    match value {
        serde_json::Value::Number(number) => {
            number.as_u64().is_some_and(timestamp_unix_seconds_satisfied)
        }
        serde_json::Value::String(text) => {
            rfc3339_timestamp_unix_seconds(text).is_some_and(timestamp_unix_seconds_satisfied)
        }
        _ => false,
    }
}

pub(super) const PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS: u64 = 1_735_689_600;
const PRODUCT_PROOF_TIMESTAMP_MAX_FUTURE_SKEW_SECONDS: u64 = 300;

fn timestamp_unix_seconds_satisfied(timestamp: u64) -> bool {
    if timestamp < PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS {
        return false;
    }
    let Ok(now) = SystemTime::now().duration_since(UNIX_EPOCH) else {
        return false;
    };
    timestamp <= now.as_secs().saturating_add(PRODUCT_PROOF_TIMESTAMP_MAX_FUTURE_SKEW_SECONDS)
}

fn rfc3339_timestamp_unix_seconds(text: &str) -> Option<u64> {
    let text = text.trim();
    let (date_time, offset_seconds) = rfc3339_split_offset(text)?;
    let date_time = rfc3339_strip_fractional_seconds(date_time)?;
    if date_time.len() != 19 {
        return None;
    }
    let bytes = date_time.as_bytes();
    if bytes.get(4) != Some(&b'-')
        || bytes.get(7) != Some(&b'-')
        || !matches!(bytes.get(10), Some(b'T' | b't'))
        || bytes.get(13) != Some(&b':')
        || bytes.get(16) != Some(&b':')
    {
        return None;
    }

    let year = parse_fixed_u32(&date_time[0..4])? as i32;
    let month = parse_fixed_u32(&date_time[5..7])?;
    let day = parse_fixed_u32(&date_time[8..10])?;
    let hour = parse_fixed_u32(&date_time[11..13])?;
    let minute = parse_fixed_u32(&date_time[14..16])?;
    let second = parse_fixed_u32(&date_time[17..19])?;
    if !(1..=12).contains(&month)
        || day == 0
        || day > days_in_month(year, month)?
        || hour > 23
        || minute > 59
        || second > 59
    {
        return None;
    }

    let unix_seconds = days_from_civil(year, month, day)
        .checked_mul(86_400)?
        .checked_add(i64::from(hour * 3_600 + minute * 60 + second))?
        .checked_sub(offset_seconds)?;
    u64::try_from(unix_seconds).ok()
}

fn rfc3339_split_offset(text: &str) -> Option<(&str, i64)> {
    if let Some(date_time) = text.strip_suffix('Z').or_else(|| text.strip_suffix('z')) {
        return Some((date_time, 0));
    }
    if text.len() < 25 {
        return None;
    }
    let offset = &text[text.len() - 6..];
    let sign = match offset.as_bytes().first()? {
        b'+' => 1_i64,
        b'-' => -1_i64,
        _ => return None,
    };
    if offset.as_bytes().get(3) != Some(&b':') {
        return None;
    }
    let hours = parse_fixed_u32(&offset[1..3])?;
    let minutes = parse_fixed_u32(&offset[4..6])?;
    if hours > 23 || minutes > 59 {
        return None;
    }
    Some((&text[..text.len() - 6], sign * i64::from(hours * 3_600 + minutes * 60)))
}

fn rfc3339_strip_fractional_seconds(date_time: &str) -> Option<&str> {
    let Some((base, fractional)) = date_time.split_once('.') else {
        return Some(date_time);
    };
    (!fractional.is_empty() && fractional.bytes().all(|byte| byte.is_ascii_digit())).then_some(base)
}

fn parse_fixed_u32(text: &str) -> Option<u32> {
    text.bytes().all(|byte| byte.is_ascii_digit()).then(|| text.parse().ok()).flatten()
}

fn days_in_month(year: i32, month: u32) -> Option<u32> {
    Some(match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if leap_year(year) => 29,
        2 => 28,
        _ => return None,
    })
}

fn leap_year(year: i32) -> bool {
    (year % 4 == 0 && year % 100 != 0) || year % 400 == 0
}

fn days_from_civil(year: i32, month: u32, day: u32) -> i64 {
    let year = year - i32::from(month <= 2);
    let era = if year >= 0 { year } else { year - 399 } / 400;
    let year_of_era = year - era * 400;
    let month = month as i32;
    let month_prime = month + if month > 2 { -3 } else { 9 };
    let day_of_year = (153 * month_prime + 2) / 5 + day as i32 - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    i64::from(era * 146_097 + day_of_era - 719_468)
}

fn compile_back_artifact_digest_binding_satisfied(value: &serde_json::Value) -> bool {
    let Some(binding) = value.as_object() else {
        return false;
    };
    COMPILE_BACK_ALL_DIGESTS
        .iter()
        .filter(|requirement| matches!(requirement.value_kind, CompileBackDigestValueKind::Sha256))
        .any(|requirement| {
            binding
                .get(requirement.json_field)
                .and_then(|value| {
                    normalize_compile_back_digest_value(value, requirement.value_kind)
                })
                .is_some()
                && requirement.path_field.is_some_and(|path_field| {
                    binding
                        .get(path_field)
                        .and_then(serde_json::Value::as_str)
                        .is_some_and(|path| !path.trim().is_empty())
                })
        })
}

fn tool_identity_binding_satisfied(identity: &serde_json::Value) -> bool {
    identity.is_object()
        && nonempty_json_string(identity, "name")
        && nonempty_json_string(identity, "path")
        && nonempty_json_string(identity, "version")
        && identity.get("executable").and_then(serde_json::Value::as_bool) == Some(true)
        && identity
            .get("sha256")
            .and_then(serde_json::Value::as_str)
            .is_some_and(sha256_value_satisfied)
}

fn binary_identity_binding_satisfied(identity: &serde_json::Value) -> bool {
    identity.is_object()
        && (nonempty_json_string(identity, "path")
            || nonempty_json_string(identity, "file")
            || nonempty_json_string(identity, "binary_path"))
        && identity
            .get("sha256")
            .or_else(|| identity.get("binary_sha256"))
            .or_else(|| identity.get("digest"))
            .and_then(serde_json::Value::as_str)
            .is_some_and(sha256_value_satisfied)
}

fn declares_source_archive_hashes(json: &serde_json::Value) -> bool {
    json.get("source_archive_hashes").is_some()
        || json.get("source_archives").is_some()
        || json.get("source_archive").is_some()
}

fn declares_component_artifact_binding(json: &serde_json::Value) -> bool {
    json.get("component_artifacts").is_some()
        || json.get("component_artifact").is_some()
        || json.get("artifacts").is_some()
        || json.get("artifact").is_some()
}

fn non_proof_counter_defects(results: &serde_json::Value) -> Vec<String> {
    [
        "failed",
        "unknown",
        "timed_out",
        "timeout",
        "timeouts",
        "total_timed_out",
        "timeout_results",
        "skipped",
        "unknown_results",
        "total_unknown",
        "skipped_results",
        "total_skipped",
        "runtime_checked",
        "inconclusive",
        "unsupported",
        "errored",
        "errors",
        "unattributed_failed",
        "unattributed_unknown",
        "unattributed_proved",
        "design_requirements",
    ]
    .into_iter()
    .filter_map(|key| {
        let value = results.get(key)?;
        match value.as_u64() {
            Some(0) => None,
            Some(value) => Some(format!("{key}={value}")),
            None => Some(format!("{key}=<non-u64>")),
        }
    })
    .collect()
}

fn valid_solver_identity_value(value: &serde_json::Value) -> bool {
    value.as_str().is_some_and(valid_solver_identity)
}

fn valid_solver_identity(value: &str) -> bool {
    let trimmed = value.trim();
    !trimmed.is_empty()
        && trimmed == value
        && trimmed.chars().all(|ch| ch.is_ascii_alphanumeric() || matches!(ch, '-' | '_' | '.'))
}

fn materialized_evidence_defect(
    root: &Path,
    kind: &str,
    json: &serde_json::Value,
    candidate_daemon: Option<&BoundToolIdentity>,
) -> Option<(&'static str, String)> {
    if let Some(detail) = proof_artifact_materialization_defect(root, json) {
        return Some(("product-proof-artifact-materialization-missing", detail));
    }
    if kind == "release check transcript" || declares_proof_transcript_binding(json) {
        if let Some(detail) = proof_transcript_materialization_defect(root, kind, json) {
            return Some(("product-proof-transcript-materialization-missing", detail));
        }
    }
    if declares_component_artifact_binding(json) {
        if let Some(detail) = artifact_evidence_materialization_defect(root, kind, json) {
            return Some(("product-proof-artifact-materialization-missing", detail));
        }
    }
    if declares_source_archive_hashes(json) {
        if let Some(detail) = source_archive_hashes_materialization_defect(root, json) {
            return Some(("product-proof-source-hashes-materialization-missing", detail));
        }
    }

    match kind {
        "trustc -Vv identity" => {
            if let Some(detail) = trustc_vv_identity_materialization_defect(root, json) {
                return Some(("product-proof-tool-identity-materialization-missing", detail));
            }
        }
        "targo identity" => {
            if let Some(detail) =
                tool_identity_materialization_defect(root, json, kind, "targo", "frontend", false)
            {
                return Some(("product-proof-tool-identity-materialization-missing", detail));
            }
        }
        "version identity" => {
            if let Some(detail) = version_identity_materialization_defect(root, json) {
                return Some(("product-proof-version-identity-materialization-missing", detail));
            }
        }
        "source archive hashes" => {
            if let Some(detail) = source_archive_hashes_materialization_defect(root, json) {
                return Some(("product-proof-source-hashes-materialization-missing", detail));
            }
        }
        "Trust daemon protocol smoke" => {
            if let Some(detail) =
                trustd_protocol_smoke_materialization_defect(root, json, candidate_daemon)
            {
                return Some(("product-proof-daemon-protocol-materialization-missing", detail));
            }
        }
        _ if artifact_evidence_kind_requires_materialization(kind) => {
            if let Some(detail) = artifact_evidence_materialization_defect(root, kind, json) {
                return Some(("product-proof-artifact-materialization-missing", detail));
            }
        }
        _ if binary_identity_tool_slot(kind).is_some() => {
            let (tool_name, tool_slot) = binary_identity_tool_slot(kind).expect("checked above");
            let require_commit_hash = kind == "Trust daemon binary identity";
            if let Some(detail) = tool_identity_materialization_defect(
                root,
                json,
                kind,
                tool_name,
                tool_slot,
                require_commit_hash,
            ) {
                return Some(("product-proof-binary-identity-materialization-missing", detail));
            }
            if kind == "Trust daemon binary identity" {
                if let Some(detail) = trustd_tool_identity_defect(root, json, kind, None) {
                    return Some(("product-proof-binary-identity-materialization-missing", detail));
                }
            }
        }
        _ => {}
    }

    if let Some(detail) = declared_identity_materialization_defect(root, json) {
        return Some(("product-proof-identity-materialization-missing", detail));
    }
    None
}

fn trustc_vv_identity_materialization_defect(
    root: &Path,
    json: &serde_json::Value,
) -> Option<String> {
    tool_identity_materialization_defect(
        root,
        json,
        "trustc -Vv identity",
        "trustc",
        "compiler",
        true,
    )
}

fn tool_identity_materialization_defect(
    root: &Path,
    json: &serde_json::Value,
    kind: &str,
    expected_name: &str,
    tool_slot: &str,
    require_commit_hash: bool,
) -> Option<String> {
    if let Some(detail) =
        tool_identity_defect(json, kind, expected_name, tool_slot, require_commit_hash)
    {
        return Some(detail);
    }
    let identity = find_tool_identity(json, tool_slot)?;
    tool_identity_path_hash_defect(root, &format!("`{kind}` tool identity"), identity)
}

fn candidate_daemon_binding_defect(
    root: &Path,
    candidate_commit: &str,
    candidate_daemon: Option<&BoundToolIdentity>,
    kind: &str,
    json: &serde_json::Value,
) -> Option<String> {
    let Some(candidate_daemon) = candidate_daemon else {
        return Some(format!(
            "`{kind}` cannot be accepted without the release identity's canonical trustd binding"
        ));
    };
    if candidate_daemon.name != "trustd" || candidate_daemon.executable != Some(true) {
        return Some("release identity does not bind an executable named `trustd`".to_string());
    }
    let Some(candidate_path_text) = candidate_daemon.path.as_deref() else {
        return Some("release identity trustd binding has no path".to_string());
    };
    let candidate_path = Path::new(candidate_path_text);
    if !is_executable_file(candidate_path) {
        return Some("release identity trustd path is not an exact regular executable".to_string());
    }
    let Some(candidate_sha256) = candidate_daemon.sha256.as_deref() else {
        return Some("release identity trustd binding has no SHA-256".to_string());
    };
    if !sha256_value_satisfied(candidate_sha256)
        || bound_file_sha256(candidate_path).as_deref() != Some(candidate_sha256)
    {
        return Some("release identity trustd digest does not match its current bytes".to_string());
    }
    let Some(candidate_version) = candidate_daemon.version.as_deref() else {
        return Some("release identity trustd binding has no version".to_string());
    };
    if candidate_daemon.commit_hash.as_deref() != Some(candidate_commit) {
        return Some(
            "release identity trustd commit does not match the release candidate".to_string(),
        );
    }

    let Some(evidence_identity) = find_tool_identity(json, "daemon") else {
        return Some(format!("`{kind}` lacks daemon tool identity"));
    };
    let Some(evidence_path_text) =
        evidence_identity.get("path").and_then(nonempty_json_string_value)
    else {
        return Some(format!("`{kind}` daemon identity has no repo-relative path"));
    };
    let Some(evidence_path) = repo_relative_exact_file(root, evidence_path_text) else {
        return Some(format!("`{kind}` daemon path is not an exact repo-local file"));
    };
    let Ok(candidate_canonical) = fs::canonicalize(candidate_path) else {
        return Some("release identity trustd path cannot be canonicalized".to_string());
    };
    let Ok(evidence_canonical) = fs::canonicalize(&evidence_path) else {
        return Some(format!("`{kind}` daemon path cannot be canonicalized"));
    };
    if evidence_canonical != candidate_canonical {
        return Some(format!(
            "`{kind}` daemon path does not name the release identity's canonical trustd"
        ));
    }
    if evidence_identity.get("name").and_then(serde_json::Value::as_str) != Some("trustd")
        || evidence_identity.get("executable").and_then(serde_json::Value::as_bool) != Some(true)
        || evidence_identity.get("sha256").and_then(serde_json::Value::as_str)
            != Some(candidate_sha256)
        || evidence_identity.get("version").and_then(serde_json::Value::as_str)
            != Some(candidate_version)
        || evidence_identity.get("commit_hash").and_then(serde_json::Value::as_str)
            != Some(candidate_commit)
    {
        return Some(format!(
            "`{kind}` daemon identity does not exactly match the release identity path, digest, version, and commit"
        ));
    }
    None
}

fn required_trustd_runtime_closure(
    json: &serde_json::Value,
    kind: &str,
) -> Result<TrustdRuntimeClosure, String> {
    let value = json.get("runtime_closure").ok_or_else(|| {
        format!("`{kind}` requires a closed `runtime_closure` proving loader_environment `none`")
    })?;
    let closure = serde_json::from_value::<TrustdRuntimeClosure>(value.clone())
        .map_err(|error| format!("`{kind}` runtime_closure violates its closed schema: {error}"))?;
    closure.validate().map_err(|detail| format!("`{kind}` {detail}"))?;
    Ok(closure)
}

fn trustd_tool_identity_defect(
    root: &Path,
    json: &serde_json::Value,
    kind: &str,
    admitted_runtime_closure: Option<&TrustdRuntimeClosure>,
) -> Option<String> {
    let Some(identity) = find_tool_identity(json, "daemon") else {
        return Some(format!("`{kind}` lacks daemon tool identity"));
    };
    let Some(candidate) = json.get("candidate_commit").and_then(serde_json::Value::as_str) else {
        return Some(format!("`{kind}` lacks candidate_commit"));
    };
    let version = identity.get("version").and_then(serde_json::Value::as_str).unwrap_or_default();
    let Some(tool_release) = version.strip_prefix("trustd ").filter(|release| !release.is_empty())
    else {
        return Some(format!("`{kind}` version must be branded `trustd <release>`"));
    };
    match identity.get("commit_hash").and_then(serde_json::Value::as_str) {
        Some(commit) if commit == candidate => {}
        Some(commit) => {
            return Some(format!(
                "`{kind}` commit_hash `{commit}` must match candidate_commit `{candidate}`"
            ));
        }
        None => return Some(format!("`{kind}` requires commit_hash bound to candidate_commit")),
    }
    let Some(path_text) = identity.get("path").and_then(nonempty_json_string_value) else {
        return Some(format!("`{kind}` requires repo-relative daemon path"));
    };
    let Some(path) = repo_relative_exact_file(root, path_text) else {
        return Some(format!("`{kind}` daemon path is not an exact repo-local file"));
    };
    let runtime_closure = match admitted_runtime_closure {
        Some(runtime_closure) => runtime_closure.clone(),
        None => match inspect_trustd_runtime_closure(&path) {
            Ok(runtime_closure) => runtime_closure,
            Err(detail) => {
                return Some(format!(
                    "`{kind}` cannot establish the exact trustd runtime closure: {detail}"
                ));
            }
        },
    };
    let probe_root = match tempfile::Builder::new().prefix("trustd-version-proof-").tempdir() {
        Ok(root) => root,
        Err(error) => {
            return Some(format!(
                "`{kind}` could not create a private trustd probe directory: {error}"
            ));
        }
    };
    let mut command = Command::new(&path);
    command.arg("--version").current_dir(probe_root.path());
    if let Err(detail) = apply_trustd_runtime_closure(&mut command, &path, &runtime_closure) {
        return Some(format!("`{kind}` cannot admit its trustd runtime closure: {detail}"));
    }
    let probe_result = (|| -> Result<(), String> {
        let output = bounded_process::output(
            &mut command,
            "Trust daemon product-proof identity",
            64 * 1024,
            TOOL_IDENTITY_PROBE_HANG_GUARD,
        )
        .map_err(|error| format!("`{kind}` exact daemon --version failed: {error}"))?;
        if !output.status.success() {
            return Err(format!("`{kind}` exact daemon --version exited {}", output.status));
        }
        if !output.stderr.is_empty() {
            return Err(format!("`{kind}` exact daemon --version wrote to stderr"));
        }
        let stdout = String::from_utf8(output.stdout)
            .map_err(|_| format!("`{kind}` exact daemon --version was not UTF-8"))?;
        if !trustd_version_output_is_bound(&stdout, tool_release) {
            return Err(format!(
                "`{kind}` exact daemon --version has invalid identity/protocol fields"
            ));
        }
        let commits = stdout
            .lines()
            .filter_map(|line| line.trim().strip_prefix("commit-hash:").map(str::trim))
            .collect::<Vec<_>>();
        if commits != [candidate] {
            return Err(format!("`{kind}` live daemon commit does not match candidate_commit"));
        }
        Ok(())
    })();
    if bound_file_sha256(&path).as_deref()
        != identity.get("sha256").and_then(serde_json::Value::as_str)
    {
        return Some(format!("`{kind}` exact daemon changed during its --version probe"));
    }
    if let Err(detail) = runtime_closure.validate_for_candidate(&path) {
        return Some(format!("`{kind}` trustd runtime closure changed during its probe: {detail}"));
    }
    probe_result.err()
}

fn trustd_protocol_smoke_materialization_defect(
    root: &Path,
    json: &serde_json::Value,
    candidate_daemon: Option<&BoundToolIdentity>,
) -> Option<String> {
    let kind = "Trust daemon protocol smoke";
    let runtime_closure = match required_trustd_runtime_closure(json, kind) {
        Ok(runtime_closure) => runtime_closure,
        Err(detail) => return Some(detail),
    };
    if let Some(detail) =
        tool_identity_materialization_defect(root, json, kind, "trustd", "daemon", true)
    {
        return Some(detail);
    }
    let Some(identity) = find_tool_identity(json, "daemon") else {
        return Some("`Trust daemon protocol smoke` lacks daemon tool identity".to_string());
    };
    let Some(candidate) = json.get("candidate_commit").and_then(serde_json::Value::as_str) else {
        return Some("`Trust daemon protocol smoke` lacks candidate_commit".to_string());
    };
    let Some(tool_sha256) = identity.get("sha256").and_then(normalized_sha256_value) else {
        return Some("`Trust daemon protocol smoke` lacks daemon SHA-256".to_string());
    };
    let Some(tool_release) = identity
        .get("version")
        .and_then(serde_json::Value::as_str)
        .and_then(|version| version.strip_prefix("trustd "))
    else {
        return Some("`Trust daemon protocol smoke` lacks branded daemon release".to_string());
    };
    let Some(smoke) = json.get("trustd_protocol_smoke").filter(|value| value.is_object()) else {
        return Some(format!("`{kind}` requires structured `trustd_protocol_smoke` material"));
    };
    let expected_requests =
        serde_json::json!(["PING", "IDENTITY", "STATUS", "RESERVE", "STATUS", "RELEASE", "STATUS"]);
    if smoke.get("requests") != Some(&expected_requests)
        || smoke.get("ping_response").and_then(serde_json::Value::as_str) != Some("PONG")
        || smoke.get("reservation_bytes").and_then(serde_json::Value::as_u64) != Some(1)
        || smoke.get("reservation_label").and_then(serde_json::Value::as_str)
            != Some("product-proof-live-smoke")
    {
        return Some(
            "`trustd_protocol_smoke` must record the exact PING/IDENTITY/STATUS/RESERVE/STATUS/RELEASE/STATUS sequence, PONG, and one-byte labeled reservation"
                .to_string(),
        );
    }
    let Some(response) = smoke.get("identity_response") else {
        return Some("`trustd_protocol_smoke.identity_response` is required".to_string());
    };
    let Ok(daemon_identity) =
        serde_json::from_value::<trust_router::coordinator::DaemonIdentity>(response.clone())
    else {
        return Some(
            "`trustd_protocol_smoke.identity_response` violates the closed IDENTITY schema"
                .to_string(),
        );
    };
    if daemon_identity.version != trust_router::coordinator::IDENTITY_VERSION
        || daemon_identity.protocol != trust_router::coordinator::STATUS_VERSION
        || daemon_identity.release != tool_release
        || daemon_identity.commit != candidate
        || daemon_identity.executable_sha256 != tool_sha256
    {
        return Some(
            "`trustd_protocol_smoke.identity_response` does not bind the exact candidate daemon, release, commit, digest, and protocol"
                .to_string(),
        );
    }
    let Some(status_before_json) = smoke.get("status_before") else {
        return Some("`trustd_protocol_smoke.status_before` is required".to_string());
    };
    let Some(status_reserved_json) = smoke.get("status_reserved") else {
        return Some("`trustd_protocol_smoke.status_reserved` is required".to_string());
    };
    let Some(status_released_json) = smoke.get("status_released") else {
        return Some("`trustd_protocol_smoke.status_released` is required".to_string());
    };
    let Ok(status_before) = serde_json::from_value::<trust_router::coordinator::DaemonStatus>(
        status_before_json.clone(),
    ) else {
        return Some(
            "`trustd_protocol_smoke.status_before` violates the closed STATUS schema".to_string(),
        );
    };
    let Ok(status_reserved) = serde_json::from_value::<trust_router::coordinator::DaemonStatus>(
        status_reserved_json.clone(),
    ) else {
        return Some(
            "`trustd_protocol_smoke.status_reserved` violates the closed STATUS schema".to_string(),
        );
    };
    let Ok(status_released) = serde_json::from_value::<trust_router::coordinator::DaemonStatus>(
        status_released_json.clone(),
    ) else {
        return Some(
            "`trustd_protocol_smoke.status_released` violates the closed STATUS schema".to_string(),
        );
    };
    let recorded_pid = smoke.get("reservation_pid").and_then(serde_json::Value::as_u64);
    let recorded_token = smoke.get("reservation_token").and_then(serde_json::Value::as_u64);
    if recorded_pid.is_none_or(|pid| pid == 0 || pid > u64::from(u32::MAX))
        || recorded_token.is_none_or(|token| token == 0)
        || !trustd_status_transition_is_valid(
            &status_before,
            &status_reserved,
            &status_released,
            recorded_pid.unwrap_or_default() as u32,
            recorded_token.unwrap_or_default(),
        )
    {
        return Some(
            "`trustd_protocol_smoke` STATUS snapshots do not prove one live reservation followed by its release"
                .to_string(),
        );
    }
    let Some(transcript_path) = smoke.get("transcript_path").and_then(nonempty_json_string_value)
    else {
        return Some("`trustd_protocol_smoke.transcript_path` is required".to_string());
    };
    let Some(transcript_sha256) = smoke.get("transcript_sha256").and_then(normalized_sha256_value)
    else {
        return Some("`trustd_protocol_smoke.transcript_sha256` is required".to_string());
    };
    if let Some(detail) = artifact_path_hash_defect(
        root,
        "trustd protocol transcript",
        transcript_path,
        &transcript_sha256,
    ) {
        return Some(detail);
    }
    let Some(transcript_file) = repo_relative_exact_file(root, transcript_path) else {
        return Some("trustd protocol transcript path is not an exact repo-local file".to_string());
    };
    let transcript =
        match read_bounded_utf8_file(&transcript_file, MAX_RELEASE_TRANSCRIPT_REPORT_BYTES) {
            Ok(transcript) => transcript,
            Err(error) => {
                return Some(format!("trustd protocol transcript is unreadable: {error}"));
            }
        };
    let Ok(identity_line) = serde_json::to_string(response) else {
        return Some("trustd IDENTITY response could not be serialized".to_string());
    };
    let Ok(status_before_line) = serde_json::to_string(status_before_json) else {
        return Some("trustd pre-reservation STATUS could not be serialized".to_string());
    };
    let Ok(status_reserved_line) = serde_json::to_string(status_reserved_json) else {
        return Some("trustd reserved STATUS could not be serialized".to_string());
    };
    let Ok(status_released_line) = serde_json::to_string(status_released_json) else {
        return Some("trustd released STATUS could not be serialized".to_string());
    };
    let expected_transcript = format!(
        "> PING\n< PONG\n> IDENTITY\n< {identity_line}\n> STATUS\n< {status_before_line}\n> RESERVE 1 {recorded_pid} product-proof-live-smoke\n< GRANTED {recorded_token}\n> STATUS\n< {status_reserved_line}\n> RELEASE {recorded_token}\n< OK\n> STATUS\n< {status_released_line}\n",
        recorded_pid = recorded_pid.unwrap_or_default(),
        recorded_token = recorded_token.unwrap_or_default(),
    );
    if transcript != expected_transcript {
        return Some(
            "trustd protocol transcript must exactly bind the recorded identity and reservation state transition"
                .to_string(),
        );
    }
    if let Some(detail) = trustd_tool_identity_defect(root, json, kind, Some(&runtime_closure)) {
        return Some(detail);
    }
    let Some(candidate_path) =
        candidate_daemon.and_then(|daemon| daemon.path.as_deref()).map(Path::new)
    else {
        return Some("live trustd smoke lacks the release identity's canonical daemon".to_string());
    };
    live_trustd_protocol_smoke_defect(
        candidate_path,
        candidate,
        tool_release,
        &tool_sha256,
        &runtime_closure,
    )
}

fn trustd_status_transition_is_valid(
    before: &trust_router::coordinator::DaemonStatus,
    reserved: &trust_router::coordinator::DaemonStatus,
    released: &trust_router::coordinator::DaemonStatus,
    pid: u32,
    token: u64,
) -> bool {
    before.is_semantically_valid()
        && reserved.is_semantically_valid()
        && released.is_semantically_valid()
        && before.reserved_bytes == 0
        && before.active.is_empty()
        && before.budget_bytes > 0
        && reserved.version == before.version
        && reserved.started_at == before.started_at
        && reserved.budget_bytes == before.budget_bytes
        && reserved.reserved_bytes == 1
        && reserved.free_bytes == before.free_bytes.saturating_sub(1)
        && reserved.granted_total == before.granted_total.saturating_add(1)
        && reserved.released_total == before.released_total
        && reserved.active.len() == 1
        && reserved.active[0].pid == pid
        && reserved.active[0].bytes == 1
        && reserved.active[0].label == "product-proof-live-smoke"
        && token != 0
        && reserved.active[0].token == token
        && released.version == before.version
        && released.started_at == before.started_at
        && released.budget_bytes == before.budget_bytes
        && released.reserved_bytes == 0
        && released.free_bytes == before.free_bytes
        && released.granted_total == reserved.granted_total
        && released.released_total == before.released_total.saturating_add(1)
        && released.active.is_empty()
}

#[cfg(unix)]
struct ProductProofTrustdChild {
    child: std::process::Child,
    pid: u32,
    _ownership: crate::process_lifecycle::Ownership,
}

#[cfg(unix)]
impl Drop for ProductProofTrustdChild {
    fn drop(&mut self) {
        // The private daemon runs until it is stopped; the smoke is done with it.
        let _ = crate::process_lifecycle::stop_tree(
            self.pid,
            crate::process_lifecycle::StopCause::Released,
        );
        let _ = self.child.wait();
    }
}

#[cfg(unix)]
fn live_trustd_protocol_smoke_defect(
    path: &Path,
    candidate: &str,
    release: &str,
    sha256: &str,
    runtime_closure: &TrustdRuntimeClosure,
) -> Option<String> {
    use std::os::unix::fs::PermissionsExt as _;

    if bound_file_sha256(path).as_deref() != Some(sha256) {
        return Some("canonical trustd digest changed before the live smoke".to_string());
    }
    let socket_root =
        match crate::smoke_socket_root::create(crate::smoke_socket_root::Purpose::ProductProof) {
            Ok(root) => root,
            Err(error) => {
                return Some(format!("could not create private trustd smoke directory: {error}"));
            }
        };
    if let Err(error) = fs::set_permissions(socket_root.path(), fs::Permissions::from_mode(0o700)) {
        return Some(format!("could not make trustd smoke directory owner-private: {error}"));
    }
    let socket = socket_root.path().join("trustd.sock");
    let mut command = Command::new(path);
    command
        .arg("--socket")
        .arg(&socket)
        .current_dir(socket_root.path())
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    if let Err(detail) = apply_trustd_runtime_closure(&mut command, path, runtime_closure) {
        return Some(format!("could not admit the trustd runtime closure: {detail}"));
    }
    let (child, ownership) = match crate::process_lifecycle::spawn_owned(&mut command) {
        Ok(owned) => owned,
        Err(error) => {
            if bound_file_sha256(path).as_deref() != Some(sha256) {
                return Some("canonical trustd changed during its failed launch".to_string());
            }
            if let Err(detail) = runtime_closure.validate_for_candidate(path) {
                return Some(format!(
                    "trustd runtime closure changed during its failed launch: {detail}"
                ));
            }
            return Some(format!("could not start canonical trustd for live smoke: {error}"));
        }
    };
    let pid = child.id();
    let mut child = ProductProofTrustdChild { child, pid, _ownership: ownership };

    let result = (|| -> Result<(), String> {
        // Same wall-clock/contention hazard as a bounded probe deadline, so it
        // is resolved through the same helper.
        let ready_timeout = crate::bounded_process::resolve_probe_deadline(Duration::from_secs(5));
        let ready_deadline = std::time::Instant::now()
            .checked_add(ready_timeout)
            .ok_or_else(|| "trustd readiness deadline overflowed".to_string())?;
        loop {
            match crate::bounded_process::exited_without_reaping(&mut child.child) {
                Ok(true) => return Err("canonical trustd exited before becoming ready".to_string()),
                Ok(false) => {}
                Err(error) => return Err(format!("could not poll canonical trustd: {error}")),
            }
            if trust_router::coordinator::daemon_matches_executable_from_pid(
                &socket, path, child.pid,
            ) {
                break;
            }
            if std::time::Instant::now() >= ready_deadline {
                return Err(format!(
                    "canonical trustd did not become identity/status ready within {ready_timeout:?}"
                ));
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        if crate::bounded_process::exited_without_reaping(&mut child.child)
            .map_err(|error| format!("could not poll canonical trustd: {error}"))?
        {
            return Err("canonical trustd exited before the live exchange".to_string());
        }

        let smoke = trust_router::coordinator::exercise_daemon_at_from_pid(
            &socket,
            path,
            "product-proof-live-smoke",
            child.pid,
        )?;
        if smoke.identity.version != trust_router::coordinator::IDENTITY_VERSION
            || smoke.identity.protocol != trust_router::coordinator::STATUS_VERSION
            || smoke.identity.release != release
            || smoke.identity.commit != candidate
            || smoke.identity.executable_sha256 != sha256
            || smoke.reservation_bytes != 1
            || smoke.reservation_label != "product-proof-live-smoke"
            || !trustd_status_transition_is_valid(
                &smoke.status_before,
                &smoke.status_reserved,
                &smoke.status_released,
                smoke.reservation_pid,
                smoke.reservation_token,
            )
        {
            return Err(
                "live trustd exchange did not bind the exact release candidate state transition"
                    .to_string(),
            );
        }
        if crate::bounded_process::exited_without_reaping(&mut child.child)
            .map_err(|error| format!("could not poll canonical trustd: {error}"))?
        {
            return Err("canonical trustd exited before the final smoke observation".to_string());
        }
        Ok(())
    })();

    if bound_file_sha256(path).as_deref() != Some(sha256) {
        return Some("canonical trustd changed during the live smoke".to_string());
    }
    if let Err(detail) = runtime_closure.validate_for_candidate(path) {
        return Some(format!("trustd runtime closure changed during the live smoke: {detail}"));
    }
    result.err()
}

#[cfg(not(unix))]
fn live_trustd_protocol_smoke_defect(
    _path: &Path,
    _candidate: &str,
    _release: &str,
    _sha256: &str,
    _runtime_closure: &TrustdRuntimeClosure,
) -> Option<String> {
    Some("Trust daemon protocol smoke requires a Unix-domain socket host".to_string())
}

fn version_identity_materialization_defect(
    root: &Path,
    json: &serde_json::Value,
) -> Option<String> {
    if let Some(detail) = version_identity_defect(json) {
        return Some(detail);
    }

    let identity = find_version_identity(json)?;
    let tools = identity.get("tools").unwrap_or(&serde_json::Value::Null);
    for slot in ["frontend", "extension", "compiler", "daemon"] {
        if let Some(tool) = tools.get(slot).filter(|value| value.is_object()) {
            if let Some(detail) = tool_identity_path_hash_defect(
                root,
                &format!("version_identity.tools.{slot}"),
                tool,
            ) {
                return Some(detail);
            }
        }
    }
    if let Some(detail) = trustd_tool_identity_defect(root, json, "version identity", None) {
        return Some(detail);
    }
    None
}

fn declared_identity_materialization_defect(
    root: &Path,
    json: &serde_json::Value,
) -> Option<String> {
    if let Some(identity) = json.get("tool_identity") {
        if !identity.is_object() {
            return Some("`tool_identity` must be a structured object".to_string());
        }
        if let Some(detail) = tool_identity_path_hash_defect(root, "`tool_identity`", identity) {
            return Some(detail);
        }
    }
    if json.get("version_identity").is_some() {
        if let Some(detail) = version_identity_materialization_defect(root, json) {
            return Some(detail);
        }
    }
    if let Some(detail) = binary_identity_materialization_defect(root, json) {
        return Some(detail);
    }
    None
}

fn tool_identity_defect(
    json: &serde_json::Value,
    kind: &str,
    expected_name: &str,
    tool_slot: &str,
    require_commit_hash: bool,
) -> Option<String> {
    let Some(identity) = find_tool_identity(json, tool_slot) else {
        return Some(format!(
            "`{kind}` requires structured `tool_identity` or \
             `version_identity.tools.{tool_slot}` material"
        ));
    };

    let mut missing = Vec::new();
    if identity.get("name").and_then(serde_json::Value::as_str) != Some(expected_name) {
        missing.push(format!("name = {expected_name:?}"));
    }
    if !nonempty_json_string(identity, "path") {
        missing.push("path".to_string());
    }
    if identity.get("executable").and_then(serde_json::Value::as_bool) != Some(true) {
        missing.push("executable = true".to_string());
    }
    if !nonempty_json_string(identity, "version") {
        missing.push("version".to_string());
    }
    if require_commit_hash && !nonempty_json_string(identity, "commit_hash") {
        missing.push("commit_hash".to_string());
    }
    if !identity
        .get("sha256")
        .and_then(serde_json::Value::as_str)
        .is_some_and(sha256_value_satisfied)
    {
        missing.push("sha256".to_string());
    }

    if missing.is_empty() {
        None
    } else {
        Some(format!(
            "`{kind}` requires materialized Trust tool identity fields: {}",
            missing.join(", ")
        ))
    }
}

fn version_identity_defect(json: &serde_json::Value) -> Option<String> {
    let Some(identity) = find_version_identity(json) else {
        return Some(
            "`version identity` requires structured `version_identity` material".to_string(),
        );
    };

    let mut missing = Vec::new();
    for field in ["product", "toolchain_alias", "trust_product_version", "candidate_commit"] {
        if !nonempty_json_string(identity, field) {
            missing.push(field.to_string());
        }
    }
    if identity
        .get("candidate_command_version")
        .and_then(serde_json::Value::as_u64)
        .is_none_or(|version| version == 0)
    {
        missing.push("candidate_command_version".to_string());
    }
    let tools = identity.get("tools").unwrap_or(&serde_json::Value::Null);
    for (slot, name, require_commit_hash) in [
        ("frontend", "targo", false),
        ("extension", "targo-trust", false),
        ("compiler", "trustc", true),
        ("daemon", "trustd", true),
    ] {
        match tools.get(slot).filter(|value| value.is_object()) {
            Some(tool) => {
                if let Some(detail) = tool_identity_object_defect(
                    tool,
                    &format!("version_identity.tools.{slot}"),
                    name,
                    require_commit_hash,
                ) {
                    missing.push(detail);
                }
            }
            None => missing.push(format!("tools.{slot}")),
        }
    }

    if missing.is_empty() {
        None
    } else {
        Some(format!(
            "`version identity` requires materialized Trust version identity fields: {}",
            missing.join(", ")
        ))
    }
}

fn tool_identity_object_defect(
    identity: &serde_json::Value,
    label: &str,
    expected_name: &str,
    require_commit_hash: bool,
) -> Option<String> {
    let mut missing = Vec::new();
    if identity.get("name").and_then(serde_json::Value::as_str) != Some(expected_name) {
        missing.push(format!("name = {expected_name:?}"));
    }
    if !nonempty_json_string(identity, "path") {
        missing.push("path".to_string());
    }
    if identity.get("executable").and_then(serde_json::Value::as_bool) != Some(true) {
        missing.push("executable = true".to_string());
    }
    if !nonempty_json_string(identity, "version") {
        missing.push("version".to_string());
    }
    if require_commit_hash && !nonempty_json_string(identity, "commit_hash") {
        missing.push("commit_hash".to_string());
    }
    if !identity
        .get("sha256")
        .and_then(serde_json::Value::as_str)
        .is_some_and(sha256_value_satisfied)
    {
        missing.push("sha256".to_string());
    }

    if missing.is_empty() { None } else { Some(format!("{label}.{}", missing.join("+"))) }
}

fn tool_identity_path_hash_defect(
    root: &Path,
    label: &str,
    identity: &serde_json::Value,
) -> Option<String> {
    if !identity.is_object() {
        return Some(format!("{label} is not a structured object"));
    }
    let Some(expected_sha256) = identity.get("sha256").and_then(normalized_sha256_value) else {
        return Some(format!("{label} is missing a valid `sha256`"));
    };
    let Some(path_text) = identity.get("path").and_then(nonempty_json_string_value) else {
        return Some(format!("{label} is missing repo-relative `path` for readback"));
    };
    let Some(path) = repo_relative_exact_file(root, path_text) else {
        return Some(format!(
            "{label} path `{path_text}` must be repo-relative, exact regular, and have no symlink components"
        ));
    };
    if !is_executable_file(&path) {
        return Some(format!("{label} path {} is not executable", path.display()));
    }
    artifact_path_hash_defect(root, label, path_text, &expected_sha256)
}

fn binary_identity_materialization_defect(root: &Path, json: &serde_json::Value) -> Option<String> {
    let identity = json.get("binary_identity")?;
    if !identity.is_object() {
        return Some("`binary_identity` must be a structured object".to_string());
    }
    let Some(expected_sha256) = binary_identity_sha256(identity) else {
        return Some(
            "`binary_identity` is missing a valid `sha256`, `binary_sha256`, or `digest`"
                .to_string(),
        );
    };
    let Some(path_text) = binary_identity_path_text(identity) else {
        if nonempty_json_string(identity, "name") {
            return Some(
                "`binary_identity` uses only `name`; provide repo-relative `path` or `file` \
                 for readback"
                    .to_string(),
            );
        }
        return Some("`binary_identity` is missing repo-relative `path` or `file`".to_string());
    };
    artifact_path_hash_defect(root, "`binary_identity`", path_text, &expected_sha256)
}

fn binary_identity_path_text(identity: &serde_json::Value) -> Option<&str> {
    ["path", "file", "binary_path"]
        .into_iter()
        .filter_map(|field| identity.get(field))
        .find_map(nonempty_json_string_value)
}

fn binary_identity_sha256(identity: &serde_json::Value) -> Option<String> {
    identity
        .get("sha256")
        .or_else(|| identity.get("binary_sha256"))
        .or_else(|| identity.get("digest"))
        .and_then(normalized_sha256_value)
}

fn source_archive_hashes_defect(json: &serde_json::Value) -> Option<String> {
    let Some(value) = json
        .get("source_archive_hashes")
        .or_else(|| json.get("source_archives"))
        .or_else(|| json.get("source_archive"))
    else {
        return Some(
            "`source archive hashes` requires structured `source_archive_hashes` material"
                .to_string(),
        );
    };

    let entries: Vec<_> = match value {
        serde_json::Value::Array(values) => values.iter().collect(),
        serde_json::Value::Object(_) => vec![value],
        _ => Vec::new(),
    };

    if entries.is_empty() {
        return Some(
            "`source archive hashes` requires one or more structured source archive entries"
                .to_string(),
        );
    }
    if entries.iter().any(|entry| !source_archive_entry_satisfied(entry)) {
        return Some(
            "`source archive hashes` entries must bind source archive name/path and 64-hex sha256"
                .to_string(),
        );
    }
    None
}

fn source_archive_entry_satisfied(entry: &serde_json::Value) -> bool {
    entry.is_object()
        && (nonempty_json_string(entry, "path")
            || nonempty_json_string(entry, "file")
            || nonempty_json_string(entry, "name"))
        && entry
            .get("sha256")
            .or_else(|| entry.get("source_sha256"))
            .and_then(serde_json::Value::as_str)
            .is_some_and(sha256_value_satisfied)
}

fn source_archive_hashes_materialization_defect(
    root: &Path,
    json: &serde_json::Value,
) -> Option<String> {
    let Some(value) = json
        .get("source_archive_hashes")
        .or_else(|| json.get("source_archives"))
        .or_else(|| json.get("source_archive"))
    else {
        return Some(
            "`source archive hashes` requires structured `source_archive_hashes` material"
                .to_string(),
        );
    };

    let entries: Vec<_> = match value {
        serde_json::Value::Array(values) => values.iter().collect(),
        serde_json::Value::Object(_) => vec![value],
        _ => Vec::new(),
    };

    if entries.is_empty() {
        return Some(
            "`source archive hashes` requires one or more structured source archive entries"
                .to_string(),
        );
    }

    for entry in entries {
        if let Some(detail) = source_archive_entry_materialization_defect(root, entry) {
            return Some(format!(
                "`source archive hashes` entries must bind repo-relative source archive path/file \
                 and matching 64-hex sha256; {detail}"
            ));
        }
    }
    None
}

fn source_archive_entry_materialization_defect(
    root: &Path,
    entry: &serde_json::Value,
) -> Option<String> {
    if !entry.is_object() {
        return Some("entry is not a structured object".to_string());
    }
    let Some(expected_sha256) = source_archive_entry_sha256(entry) else {
        return Some("entry is missing a valid `sha256` or `source_sha256`".to_string());
    };
    let Some(path_text) = source_archive_entry_path_text(entry) else {
        if nonempty_json_string(entry, "name") {
            return Some(
                "entry uses only `name`; provide repo-relative `path` or `file` for readback"
                    .to_string(),
            );
        }
        return Some("entry is missing repo-relative `path` or `file`".to_string());
    };
    artifact_path_hash_defect(root, "source archive entry", path_text, &expected_sha256)
}

fn source_archive_entry_path_text(entry: &serde_json::Value) -> Option<&str> {
    ["path", "file", "source_path", "archive_path"]
        .into_iter()
        .filter_map(|field| entry.get(field))
        .find_map(nonempty_json_string_value)
}

fn source_archive_entry_sha256(entry: &serde_json::Value) -> Option<String> {
    entry.get("sha256").or_else(|| entry.get("source_sha256")).and_then(normalized_sha256_value)
}

fn artifact_evidence_kind_requires_materialization(kind: &str) -> bool {
    matches!(
        kind,
        "documentation build"
            | "formatting component artifact"
            | "Cargo formatting component artifact"
            | "lint component artifact"
            | "lint driver component artifact"
            | "Trust analyzer component artifact"
            | "standard library artifacts"
            | "trust-src artifact"
            | "trust-docs artifact"
    )
}

fn artifact_evidence_defect(kind: &str, json: &serde_json::Value) -> Option<String> {
    let Some(value) = json
        .get("component_artifacts")
        .or_else(|| json.get("component_artifact"))
        .or_else(|| json.get("artifacts"))
        .or_else(|| json.get("artifact"))
    else {
        return Some(format!(
            "`{kind}` requires structured artifact material under `component_artifacts`, \
             `component_artifact`, `artifacts`, or `artifact`"
        ));
    };

    let entries: Vec<_> = match value {
        serde_json::Value::Array(values) => values.iter().collect(),
        serde_json::Value::Object(_) => vec![value],
        _ => Vec::new(),
    };

    if entries.is_empty() {
        return Some(format!("`{kind}` requires one or more structured artifact entries"));
    }
    if entries.iter().any(|entry| !artifact_entry_satisfied(entry)) {
        return Some(format!(
            "`{kind}` artifact entries must bind artifact name/path and 64-hex sha256"
        ));
    }
    None
}

fn artifact_entry_satisfied(entry: &serde_json::Value) -> bool {
    entry.is_object()
        && (nonempty_json_string(entry, "path")
            || nonempty_json_string(entry, "file")
            || nonempty_json_string(entry, "name"))
        && entry
            .get("sha256")
            .or_else(|| entry.get("artifact_sha256"))
            .or_else(|| entry.get("digest"))
            .and_then(serde_json::Value::as_str)
            .is_some_and(sha256_value_satisfied)
}

fn proof_artifact_materialization_defect(root: &Path, json: &serde_json::Value) -> Option<String> {
    let sha256_value = json.get("proof_artifact_sha256")?;
    let Some(expected_sha256) = normalized_sha256_value(sha256_value) else {
        return Some("`proof_artifact_sha256` must be a 64-hex sha256".to_string());
    };
    let Some(path_text) = proof_artifact_path_text(json) else {
        return Some(
            "`proof_artifact_sha256` requires a repo-relative proof artifact path under \
             `proof_artifact_path`, `artifact_path`, or `proof_artifact.path`"
                .to_string(),
        );
    };
    artifact_path_hash_defect(root, "`proof_artifact_sha256`", path_text, &expected_sha256)
}

fn proof_artifact_path_text(json: &serde_json::Value) -> Option<&str> {
    ["proof_artifact_path", "artifact_path", "proof_artifact_file", "artifact_file"]
        .into_iter()
        .filter_map(|field| json.get(field))
        .find_map(nonempty_json_string_value)
        .or_else(|| {
            json.get("proof_artifact").and_then(|artifact| artifact_entry_path_text(artifact))
        })
}

fn declares_proof_transcript_binding(json: &serde_json::Value) -> bool {
    [
        "proof_transcript_hash",
        "proof_transcript_sha256",
        "transcript_hash",
        "transcript_sha256",
        "proof_transcript_path",
        "transcript_path",
        "proof_transcript_file",
        "transcript_file",
    ]
    .into_iter()
    .any(|field| json.get(field).is_some())
        || json.get("proof_transcript").is_some()
}

fn proof_transcript_materialization_defect(
    root: &Path,
    kind: &str,
    json: &serde_json::Value,
) -> Option<String> {
    let Some(expected_sha256) = proof_transcript_sha256(json) else {
        return Some(format!(
            "`{kind}` requires a valid 64-hex proof transcript hash under \
             `proof_transcript_hash`, `proof_transcript_sha256`, `transcript_hash`, \
             `transcript_sha256`, or `proof_transcript.sha256`"
        ));
    };
    let Some(path_text) = proof_transcript_path_text(json) else {
        return Some(format!(
            "`{kind}` requires a repo-relative proof transcript path under \
             `proof_transcript_path`, `transcript_path`, `proof_transcript_file`, \
             `transcript_file`, or `proof_transcript.path`"
        ));
    };
    artifact_path_hash_defect(root, "`proof_transcript_hash`", path_text, &expected_sha256)
}

fn proof_transcript_path_text(json: &serde_json::Value) -> Option<&str> {
    ["proof_transcript_path", "transcript_path", "proof_transcript_file", "transcript_file"]
        .into_iter()
        .filter_map(|field| json.get(field))
        .find_map(nonempty_json_string_value)
        .or_else(|| {
            json.get("proof_transcript").and_then(|transcript| artifact_entry_path_text(transcript))
        })
}

fn proof_transcript_sha256(json: &serde_json::Value) -> Option<String> {
    ["proof_transcript_hash", "proof_transcript_sha256", "transcript_hash", "transcript_sha256"]
        .into_iter()
        .filter_map(|field| json.get(field))
        .find_map(normalized_sha256_value)
        .or_else(|| {
            json.get("proof_transcript").and_then(|transcript| {
                transcript
                    .get("sha256")
                    .or_else(|| transcript.get("hash"))
                    .or_else(|| transcript.get("digest"))
                    .and_then(normalized_sha256_value)
            })
        })
}

fn artifact_evidence_materialization_defect(
    root: &Path,
    kind: &str,
    json: &serde_json::Value,
) -> Option<String> {
    let Some(value) = json
        .get("component_artifacts")
        .or_else(|| json.get("component_artifact"))
        .or_else(|| json.get("artifacts"))
        .or_else(|| json.get("artifact"))
    else {
        return Some(format!(
            "`{kind}` requires structured artifact material under `component_artifacts`, \
             `component_artifact`, `artifacts`, or `artifact`"
        ));
    };

    let entries: Vec<_> = match value {
        serde_json::Value::Array(values) => values.iter().collect(),
        serde_json::Value::Object(_) => vec![value],
        _ => Vec::new(),
    };

    if entries.is_empty() {
        return Some(format!("`{kind}` requires one or more structured artifact entries"));
    }

    for entry in entries {
        if let Some(detail) = artifact_entry_materialization_defect(root, entry) {
            return Some(format!(
                "`{kind}` artifact entries must bind repo-relative artifact path/file and \
                 matching 64-hex sha256; {detail}"
            ));
        }
    }
    None
}

fn artifact_entry_materialization_defect(root: &Path, entry: &serde_json::Value) -> Option<String> {
    if !entry.is_object() {
        return Some("entry is not a structured object".to_string());
    }
    let Some(expected_sha256) = artifact_entry_sha256(entry) else {
        return Some(
            "entry is missing a valid `sha256`, `artifact_sha256`, or `digest`".to_string(),
        );
    };
    let Some(path_text) = artifact_entry_path_text(entry) else {
        if nonempty_json_string(entry, "name") {
            return Some(
                "entry uses only `name`; provide repo-relative `path` or `file` for readback"
                    .to_string(),
            );
        }
        return Some("entry is missing repo-relative `path` or `file`".to_string());
    };
    artifact_path_hash_defect(root, "artifact entry", path_text, &expected_sha256)
}

fn artifact_entry_path_text(entry: &serde_json::Value) -> Option<&str> {
    ["path", "file", "artifact_path"]
        .into_iter()
        .filter_map(|field| entry.get(field))
        .find_map(nonempty_json_string_value)
}

fn artifact_entry_sha256(entry: &serde_json::Value) -> Option<String> {
    entry
        .get("sha256")
        .or_else(|| entry.get("artifact_sha256"))
        .or_else(|| entry.get("digest"))
        .and_then(normalized_sha256_value)
}

fn artifact_path_hash_defect(
    root: &Path,
    label: &str,
    path_text: &str,
    expected_sha256: &str,
) -> Option<String> {
    let Some(path) = repo_relative_exact_file(root, path_text.trim()) else {
        return Some(format!(
            "{label} path `{}` must be repo-relative, exact regular, and have no symlink components",
            path_text.trim()
        ));
    };
    match file_sha256(&path) {
        Some(actual) if actual == expected_sha256 => None,
        Some(actual) => Some(format!(
            "{label} hash mismatch for {}: expected {expected_sha256}, got {actual}",
            path.display()
        )),
        None => Some(format!("{label} path is not readable: {}", path.display())),
    }
}

fn normalized_sha256_value(value: &serde_json::Value) -> Option<String> {
    let value = value.as_str()?.trim();
    let value = value.strip_prefix("sha256:").unwrap_or(value).trim();
    sha256_value_satisfied(value).then(|| value.to_ascii_lowercase())
}

fn nonempty_json_string_value(value: &serde_json::Value) -> Option<&str> {
    value.as_str().map(str::trim).filter(|text| !text.is_empty())
}

fn binary_identity_tool_slot(kind: &str) -> Option<(&'static str, &'static str)> {
    match kind {
        "Trust documentation binary identity" => Some(("trustdoc", "documentation")),
        "Trust formatting binary identity" => Some(("trustfmt", "formatter")),
        "Trust Cargo formatting binary identity" => Some(("targo-fmt", "cargo_formatter")),
        "Trust lint binary identity" => Some(("tippy", "tippy")),
        "Trust lint subcommand identity" => Some(("targo-tippy", "targo_tippy")),
        "Trust lint driver binary identity" => Some(("tippy-driver", "tippy_driver")),
        "Trust daemon binary identity" => Some(("trustd", "daemon")),
        _ => None,
    }
}

fn find_version_identity(json: &serde_json::Value) -> Option<&serde_json::Value> {
    json.get("version_identity").filter(|value| value.is_object()).or_else(|| {
        (json.get("tools").is_some()
            && json.get("candidate_command_version").and_then(serde_json::Value::as_u64).is_some())
        .then_some(json)
    })
}

fn find_tool_identity<'a>(
    json: &'a serde_json::Value,
    tool_slot: &str,
) -> Option<&'a serde_json::Value> {
    json.get("tool_identity")
        .filter(|value| value.is_object())
        .or_else(|| {
            json.get("version_identity")
                .and_then(|value| value.get("tools"))
                .and_then(|tools| tools.get(tool_slot))
                .filter(|value| value.is_object())
        })
        .or_else(|| {
            json.get("tools")
                .and_then(|tools| tools.get(tool_slot))
                .filter(|value| value.is_object())
        })
}

fn nonempty_json_string(value: &serde_json::Value, key: &str) -> bool {
    value.get(key).and_then(serde_json::Value::as_str).is_some_and(|text| !text.trim().is_empty())
}

#[derive(Clone, Copy)]
enum CompileBackDigestValueKind {
    Sha256,
    Range,
}

#[derive(Clone, Copy)]
struct CompileBackDigestRequirement {
    json_field: &'static str,
    path_field: Option<&'static str>,
    value_kind: CompileBackDigestValueKind,
}

const COMPILE_BACK_LIFTED_BINARY_TRUST_IR_DIGEST: &[CompileBackDigestRequirement] =
    &[CompileBackDigestRequirement {
        json_field: "lifted_binary_trust_ir_sha256",
        path_field: Some("lifted_binary_trust_ir_path"),
        value_kind: CompileBackDigestValueKind::Sha256,
    }];
const COMPILE_BACK_RUST_SOURCE_DIGEST: &[CompileBackDigestRequirement] =
    &[CompileBackDigestRequirement {
        json_field: "rust_source_sha256",
        path_field: Some("rust_source_path"),
        value_kind: CompileBackDigestValueKind::Sha256,
    }];
const COMPILE_BACK_RECONSTRUCTED_TRUST_IR_DIGEST: &[CompileBackDigestRequirement] =
    &[CompileBackDigestRequirement {
        json_field: "reconstructed_trust_ir_sha256",
        path_field: Some("reconstructed_trust_ir_path"),
        value_kind: CompileBackDigestValueKind::Sha256,
    }];
const COMPILE_BACK_REFINEMENT_ARTIFACT_DIGEST: &[CompileBackDigestRequirement] =
    &[CompileBackDigestRequirement {
        json_field: "refinement_artifact_sha256",
        path_field: Some("refinement_artifact_path"),
        value_kind: CompileBackDigestValueKind::Sha256,
    }];
const COMPILE_BACK_ROOT_ARTIFACT_DIGEST: &[CompileBackDigestRequirement] =
    &[CompileBackDigestRequirement {
        json_field: "root_artifact_sha256",
        path_field: Some("root_artifact_path"),
        value_kind: CompileBackDigestValueKind::Sha256,
    }];
const COMPILE_BACK_SELECTED_IMAGE_DIGEST: &[CompileBackDigestRequirement] =
    &[CompileBackDigestRequirement {
        json_field: "selected_image_sha256",
        path_field: Some("selected_image_path"),
        value_kind: CompileBackDigestValueKind::Sha256,
    }];
const COMPILE_BACK_SELECTED_IMAGE_RANGE: &[CompileBackDigestRequirement] =
    &[CompileBackDigestRequirement {
        json_field: "selected_image_range",
        path_field: None,
        value_kind: CompileBackDigestValueKind::Range,
    }];
const COMPILE_BACK_SELECTED_IMAGE_RANGE_MATERIAL: &[CompileBackDigestRequirement] = &[
    COMPILE_BACK_ROOT_ARTIFACT_DIGEST[0],
    COMPILE_BACK_SELECTED_IMAGE_DIGEST[0],
    COMPILE_BACK_SELECTED_IMAGE_RANGE[0],
];
const COMPILE_BACK_ALL_DIGESTS: &[CompileBackDigestRequirement] = &[
    COMPILE_BACK_LIFTED_BINARY_TRUST_IR_DIGEST[0],
    COMPILE_BACK_RUST_SOURCE_DIGEST[0],
    COMPILE_BACK_RECONSTRUCTED_TRUST_IR_DIGEST[0],
    COMPILE_BACK_REFINEMENT_ARTIFACT_DIGEST[0],
    COMPILE_BACK_ROOT_ARTIFACT_DIGEST[0],
    COMPILE_BACK_SELECTED_IMAGE_DIGEST[0],
    COMPILE_BACK_SELECTED_IMAGE_RANGE[0],
];

fn missing_required_evidence_message(component: &str, required_kind: &str) -> String {
    let message = format!("{component} is missing required evidence `{required_kind}`");
    if compile_back_artifact_digest_requirements(required_kind).is_some() {
        format!(
            "{message}; add `{required_kind}:<repo-relative JSON path>` to \
             `release/product-proof.toml` under [[components]] component = {component:?}, \
             and ensure that JSON declares `evidence_kind`/`evidence_kinds` \
             `{required_kind}` with structured `compile_back_artifact_digest_binding` fields"
        )
    } else {
        message
    }
}

fn compile_back_artifact_digest_evidence_defect(
    root: &Path,
    kind: &str,
    json: &serde_json::Value,
) -> Option<String> {
    let requirements = compile_back_artifact_digest_requirements(kind)?;
    let binding = json.get("compile_back_artifact_digest_binding");
    let mut missing: Vec<_> = requirements
        .iter()
        .filter_map(|requirement| {
            compile_back_digest_requirement_defect(root, binding, requirement)
        })
        .collect();
    if missing.is_empty()
        && matches!(
            kind,
            "compile-back-artifact-digests-bound" | "compile-back-selected-image-range"
        )
    {
        missing.extend(selected_image_range_binding_defect(root, binding));
    }

    if missing.is_empty() {
        None
    } else {
        Some(format!(
            "compile-back artifact digest evidence `{kind}` must be materialized by \
             `release/product-proof.toml` as `{kind}:<repo-relative JSON path>` and by \
             that JSON as `evidence_kind`/`evidence_kinds` `{kind}` plus concrete \
             digest/range material with repo-relative artifact paths whose hashes are \
             recomputed; missing or invalid {}",
            missing.join(", ")
        ))
    }
}

fn compile_back_artifact_digest_requirements(
    kind: &str,
) -> Option<&'static [CompileBackDigestRequirement]> {
    match kind {
        "compile-back-artifact-digests-bound" => Some(COMPILE_BACK_ALL_DIGESTS),
        "compile-back-lifted-binary-trust_ir-sha256" => {
            Some(COMPILE_BACK_LIFTED_BINARY_TRUST_IR_DIGEST)
        }
        "compile-back-rust-source-sha256" => Some(COMPILE_BACK_RUST_SOURCE_DIGEST),
        "compile-back-reconstructed-trust_ir-sha256" => {
            Some(COMPILE_BACK_RECONSTRUCTED_TRUST_IR_DIGEST)
        }
        "compile-back-refinement-artifact-sha256" => Some(COMPILE_BACK_REFINEMENT_ARTIFACT_DIGEST),
        "compile-back-root-artifact-sha256" => Some(COMPILE_BACK_ROOT_ARTIFACT_DIGEST),
        "compile-back-selected-image-sha256" => Some(COMPILE_BACK_SELECTED_IMAGE_DIGEST),
        "compile-back-selected-image-range" => Some(COMPILE_BACK_SELECTED_IMAGE_RANGE_MATERIAL),
        _ => None,
    }
}

fn compile_back_digest_requirement_defect(
    root: &Path,
    binding: Option<&serde_json::Value>,
    requirement: &CompileBackDigestRequirement,
) -> Option<String> {
    let Some(binding) = binding.and_then(serde_json::Value::as_object) else {
        return Some(format!("`compile_back_artifact_digest_binding.{}`", requirement.json_field));
    };
    let Some(value) = binding.get(requirement.json_field) else {
        return Some(format!("`compile_back_artifact_digest_binding.{}`", requirement.json_field));
    };
    let Some(normalized_value) = normalize_compile_back_digest_value(value, requirement.value_kind)
    else {
        return Some(format!("`compile_back_artifact_digest_binding.{}`", requirement.json_field));
    };
    let path_field = requirement.path_field?;
    let Some(path_text) = binding
        .get(path_field)
        .and_then(serde_json::Value::as_str)
        .map(str::trim)
        .filter(|text| !text.is_empty())
    else {
        return Some(format!("`compile_back_artifact_digest_binding.{path_field}`"));
    };
    let Some(path) = repo_relative_exact_file(root, path_text) else {
        return Some(format!("safe `compile_back_artifact_digest_binding.{path_field}`"));
    };
    match file_sha256(&path) {
        Some(actual) if actual == normalized_value => None,
        Some(_) => Some(format!(
            "`compile_back_artifact_digest_binding.{}` hash matching `{path_field}`",
            requirement.json_field
        )),
        None => Some(format!("readable `compile_back_artifact_digest_binding.{path_field}`")),
    }
}

fn selected_image_range_binding_defect(
    root: &Path,
    binding: Option<&serde_json::Value>,
) -> Option<String> {
    let check = || -> Result<(), String> {
        for requirement in COMPILE_BACK_SELECTED_IMAGE_RANGE_MATERIAL {
            if let Some(defect) = compile_back_digest_requirement_defect(root, binding, requirement)
            {
                return Err(defect);
            }
        }
        let binding = binding.and_then(serde_json::Value::as_object).ok_or("missing binding")?;
        let range = normalize_compile_back_digest_value(
            binding.get("selected_image_range").ok_or("missing selected_image_range")?,
            CompileBackDigestValueKind::Range,
        )
        .ok_or("invalid selected_image_range")?;
        let (start, end) = range.split_once("..").ok_or("invalid selected_image_range")?;
        let start = start.parse::<u64>().map_err(|_| "invalid selected_image_range")?;
        let end = end.parse::<u64>().map_err(|_| "invalid selected_image_range")?;
        let bound_path = |field| -> Result<PathBuf, String> {
            let path = binding
                .get(field)
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| format!("missing {field}"))?;
            repo_relative_exact_file(root, path).ok_or_else(|| format!("unsafe or missing {field}"))
        };
        let root_path = bound_path("root_artifact_path")?;
        let selected_path = bound_path("selected_image_path")?;
        let mut root_image = fs::File::open(&root_path)
            .map_err(|err| format!("cannot open root artifact {}: {err}", root_path.display()))?;
        let mut selected_image = fs::File::open(&selected_path).map_err(|err| {
            format!("cannot open selected image {}: {err}", selected_path.display())
        })?;
        let root_sha256 = normalize_compile_back_digest_value(
            &binding["root_artifact_sha256"],
            CompileBackDigestValueKind::Sha256,
        )
        .ok_or("invalid root digest")?;
        let selected_sha256 = normalize_compile_back_digest_value(
            &binding["selected_image_sha256"],
            CompileBackDigestValueKind::Sha256,
        )
        .ok_or("invalid selected digest")?;
        verify_selected_image_byte_relation(
            &mut root_image,
            &mut selected_image,
            start,
            end,
            &root_sha256,
            &selected_sha256,
        )?;
        Ok(())
    };
    check().err()
}

fn verify_selected_image_byte_relation(
    root_file: &mut fs::File,
    selected_file: &mut fs::File,
    start: u64,
    end: u64,
    expected_root_sha256: &str,
    expected_selected_sha256: &str,
) -> Result<(u64, u64, String), String> {
    let root_len = root_file.metadata().map_err(|err| format!("root artifact: {err}"))?.len();
    let selected_len =
        selected_file.metadata().map_err(|err| format!("selected image: {err}"))?.len();
    if start >= end {
        return Err("invalid selected_image_range".into());
    }
    if end > root_len {
        return Err(format!(
            "selected_image_range {start}..{end} exceeds root artifact length {root_len}"
        ));
    }
    if selected_len != end - start {
        return Err(format!(
            "selected image length {selected_len} does not equal selected_image_range length {}",
            end - start
        ));
    }
    root_file.seek(io::SeekFrom::Start(0)).map_err(|err| format!("root artifact: {err}"))?;
    selected_file.seek(io::SeekFrom::Start(0)).map_err(|err| format!("selected image: {err}"))?;

    let mut root_hash = Sha256::new();
    let mut selected_hash = Sha256::new();
    let mut range_hash = Sha256::new();
    let mut root_bytes = [0; 8192];
    let mut selected_bytes = [0; 8192];
    let mut offset = 0_u64;
    loop {
        let count =
            root_file.read(&mut root_bytes).map_err(|err| format!("root artifact: {err}"))?;
        if count == 0 {
            break;
        }
        root_hash.update(&root_bytes[..count]);
        let chunk_end = offset.checked_add(count as u64).ok_or("root artifact length overflow")?;
        let overlap_start = start.max(offset);
        let overlap_end = end.min(chunk_end);
        if overlap_start < overlap_end {
            let begin = (overlap_start - offset) as usize;
            let len = (overlap_end - overlap_start) as usize;
            selected_file
                .read_exact(&mut selected_bytes[..len])
                .map_err(|err| format!("selected image: {err}"))?;
            range_hash.update(&root_bytes[begin..begin + len]);
            selected_hash.update(&selected_bytes[..len]);
            if root_bytes[begin..begin + len] != selected_bytes[..len] {
                return Err("selected image bytes do not equal root artifact range".into());
            }
        }
        offset = chunk_end;
    }
    if offset != root_len
        || selected_file
            .read(&mut selected_bytes[..1])
            .map_err(|err| format!("selected image: {err}"))?
            != 0
    {
        return Err("selected-image artifact length changed during readback".into());
    }
    if format!("{:x}", root_hash.finalize()) != expected_root_sha256
        || format!("{:x}", selected_hash.finalize()) != expected_selected_sha256
    {
        return Err("selected-image opened artifact hash does not match its binding".into());
    }
    Ok((root_len, selected_len, format!("{:x}", range_hash.finalize())))
}

fn normalize_compile_back_digest_value(
    value: &serde_json::Value,
    value_kind: CompileBackDigestValueKind,
) -> Option<String> {
    match value_kind {
        CompileBackDigestValueKind::Sha256 => {
            let value = value.as_str()?.trim();
            let value = value.strip_prefix("sha256:").unwrap_or(value).trim();
            sha256_value_satisfied(value).then(|| value.to_ascii_lowercase())
        }
        CompileBackDigestValueKind::Range => match value {
            serde_json::Value::String(text) => {
                compile_back_range_value_satisfied(text).then(|| text.trim().to_string())
            }
            serde_json::Value::Object(map) => {
                let start = map.get("start").and_then(serde_json::Value::as_u64);
                let end = map.get("end").and_then(serde_json::Value::as_u64);
                match (start, end) {
                    (Some(start), Some(end)) if end > start => Some(format!("{start}..{end}")),
                    _ => None,
                }
            }
            _ => None,
        },
    }
}

fn sha256_value_satisfied(value: &str) -> bool {
    let value = value.trim().strip_prefix("sha256:").unwrap_or(value.trim());
    value.len() == 64 && value.chars().all(|ch| ch.is_ascii_hexdigit())
}

fn compile_back_range_value_satisfied(value: &str) -> bool {
    let Some((start, end)) = value.trim().split_once("..") else {
        return false;
    };
    let Ok(start) = start.parse::<u64>() else {
        return false;
    };
    let Ok(end) = end.parse::<u64>() else {
        return false;
    };
    end > start
}

pub(super) fn product_proof_evidence_classes(
    root: &Path,
    reports: &[GateReport],
) -> Vec<ProductProofEvidenceClass> {
    let manifest = match read_product_proof_manifest(root.join("release/product-proof.toml")) {
        Ok(manifest) => manifest,
        Err(err) => {
            return product_proof_evidence_class_requirements()
                .into_iter()
                .map(|mut class| {
                    class.status = "invalid_manifest".to_string();
                    class.reason = Some(err.clone());
                    class
                })
                .collect();
        }
    };
    let manifest_accepted = manifest
        .as_ref()
        .and_then(|manifest| manifest.status.as_deref())
        .is_some_and(|status| status == "accepted");
    product_proof_evidence_class_requirements()
        .into_iter()
        .map(|mut class| {
            if let Some(entry) = manifest.as_ref().and_then(|manifest| {
                manifest.evidence_classes.iter().find(|entry| entry.class == class.class)
            }) {
                if product_proof_manifest_status_supported(&entry.status) {
                    class.status = entry.status.clone();
                    class.reason = entry.reason.clone();
                } else {
                    class.status = "invalid_manifest".to_string();
                    class.reason = Some(format!(
                        "unsupported evidence-class status `{}` in release/product-proof.toml",
                        entry.status
                    ));
                }
                if entry.status == "accepted" {
                    if !manifest_accepted {
                        class.status = "blocked".to_string();
                        class.reason = Some(
                            "top-level product-proof manifest status is not accepted".to_string(),
                        );
                    } else if class.gates.is_empty() {
                        class.status = "blocked".to_string();
                        class.reason = Some(
                            "evidence class has no release gate binding; cannot claim accepted"
                                .to_string(),
                        );
                    } else {
                        let blocked_gates: Vec<_> = class
                            .gates
                            .iter()
                            .filter(|&&gate| {
                                match reports.iter().find(|report| report.gate == gate) {
                                    Some(report) => report.status != GateStatus::Pass,
                                    None => true,
                                }
                            })
                            .copied()
                            .collect();
                        if !blocked_gates.is_empty() {
                            class.status = "blocked".to_string();
                            class.reason = Some(format!(
                                "required release gate(s) are not passing: {}",
                                blocked_gates.join(", ")
                            ));
                        }
                    }
                }
            }
            class
        })
        .collect()
}

pub(super) fn product_proof_components(
    root: &Path,
    candidate_commit: Option<&str>,
    candidate_daemon: Option<&BoundToolIdentity>,
) -> Vec<ProductProofComponent> {
    let manifest = match read_product_proof_manifest(root.join("release/product-proof.toml")) {
        Ok(manifest) => manifest,
        Err(_) => {
            return product_proof_component_requirements()
                .into_iter()
                .map(|mut component| {
                    component.status = "invalid_manifest".to_string();
                    component
                })
                .collect();
        }
    };
    let manifest_accepted = manifest
        .as_ref()
        .and_then(|manifest| manifest.status.as_deref())
        .is_some_and(|status| status == "accepted");
    product_proof_component_requirements()
        .into_iter()
        .map(|mut component| {
            let Some(entry) = manifest.as_ref().and_then(|manifest| {
                manifest.components.iter().find(|entry| {
                    product_proof_component_matches(&entry.component, component.component)
                })
            }) else {
                component.status = "missing_evidence".to_string();
                return component;
            };

            if !product_proof_manifest_status_supported(&entry.status) {
                component.status = "invalid_manifest".to_string();
                return component;
            }

            component.status = entry.status.clone();
            if entry.status == "accepted" {
                if !manifest_accepted {
                    component.status = "blocked".to_string();
                } else {
                    let mut findings = Vec::new();
                    let mut evidence_refs = Vec::new();
                    validate_product_proof_evidence(ProductProofEvidenceInput {
                        root,
                        candidate_commit,
                        candidate_daemon,
                        required: &component,
                        entry,
                        require_all_required_evidence: true,
                        findings: &mut findings,
                        evidence_refs: &mut evidence_refs,
                    });
                    if !findings.is_empty() {
                        component.status = product_proof_component_status_for_findings(&findings);
                    }
                }
            }
            component
        })
        .collect()
}

fn product_proof_component_status_for_findings(findings: &[GateFinding]) -> String {
    if findings.iter().any(|finding| {
        matches!(
            finding.code.as_str(),
            "product-proof-evidence-empty"
                | "product-proof-evidence-missing"
                | "product-proof-component-missing"
        )
    }) {
        "missing_evidence".to_string()
    } else {
        "blocked".to_string()
    }
}

fn product_proof_component_matches(manifest_component: &str, required_component: &str) -> bool {
    manifest_component == required_component
        || product_proof_component_aliases(required_component).contains(&manifest_component)
}

fn product_proof_component_aliases(_required_component: &str) -> &'static [&'static str] {
    &[]
}

fn read_product_proof_manifest(
    path: impl AsRef<Path>,
) -> Result<Option<ProductProofManifest>, String> {
    let path = path.as_ref();
    let text = match read_bounded_utf8_file(path, MAX_RELEASE_METADATA_BYTES) {
        Ok(text) => text,
        Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(err) => return Err(format!("failed to read {}: {err}", path.display())),
    };
    toml::from_str::<ProductProofManifest>(&text)
        .map(Some)
        .map_err(|err| format!("failed to parse {}: {err}", path.display()))
}

fn collect_candidate_commit_values<'a>(value: &'a serde_json::Value, out: &mut Vec<&'a str>) {
    match value {
        serde_json::Value::Object(map) => {
            for (key, value) in map {
                if key == "candidate_commit" {
                    if let Some(commit) = value.as_str() {
                        out.push(commit);
                    }
                }
                collect_candidate_commit_values(value, out);
            }
        }
        serde_json::Value::Array(values) => {
            for value in values {
                collect_candidate_commit_values(value, out);
            }
        }
        _ => {}
    }
}

fn json_declares_evidence_kind(value: &serde_json::Value, expected: &str) -> bool {
    value
        .get("evidence_kind")
        .and_then(serde_json::Value::as_str)
        .is_some_and(|kind| kind == expected)
        || value
            .get("evidence_kinds")
            .and_then(serde_json::Value::as_array)
            .is_some_and(|kinds| kinds.iter().any(|kind| kind.as_str() == Some(expected)))
}

fn declared_candidate_commit(value: &serde_json::Value) -> Option<&str> {
    value.get("candidate_commit").and_then(serde_json::Value::as_str)
}

#[cfg(test)]
mod content_gate_tests {
    //! regression: a product-proof release claim must be backed
    //! by real discharge content, never metadata alone. A structurally-valid
    //! placeholder must be rejected (fail closed).
    use std::fs;
    use std::process::Command;
    use std::time::Duration;

    use serde_json::json;
    use sha2::{Digest as _, Sha256};

    use super::{
        PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS, ProductProofStubOptions,
        build_product_proof_release_report, build_product_proof_stub_release_report, file_sha256,
        product_proof_source_tarball_binding_from_path,
        product_proof_stage2_trustc_binding_from_path, proof_content_defect,
        replay_selected_image_range, repo_relative_exact_file, runner_clean_provenance_defect,
        selected_image_replay_check_json, solver_evidence_admission_defect,
        source_tarball_archive_identity, source_tarball_identity_defects,
        validate_product_proof_release_artifact_evidence, verify_selected_image_byte_relation,
    };

    const TEST_SHA256: &str = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

    #[test]
    fn runner_clean_provenance_rejects_conflicting_or_malformed_markers() {
        assert_eq!(runner_clean_provenance_defect(&json!({"repo_dirty": false})), None);
        assert_eq!(
            runner_clean_provenance_defect(&json!({"runner": {"git": {"clean": true}}})),
            None
        );

        let conflicting = json!({"repo_dirty": false, "runner": {"git": {"clean": false}}});
        assert!(
            runner_clean_provenance_defect(&conflicting)
                .expect("conflicting clean marker must block")
                .contains("runner.git.clean=false")
        );

        let malformed = json!({"repo_dirty": false, "provenance": {"repo_clean": "maybe"}});
        assert!(
            runner_clean_provenance_defect(&malformed)
                .expect("malformed clean marker must block")
                .contains("provenance.repo_clean with a non-boolean value")
        );
        assert!(
            runner_clean_provenance_defect(&json!({"repo_dirty": "false"}))
                .expect("string dirty marker must block")
                .contains("repo_dirty with a non-boolean value")
        );
    }

    #[test]
    fn product_proof_reports_bind_repo_fields_to_candidate_status() {
        let temp = tempfile::tempdir().expect("release report repository fixture");
        let root = temp.path();
        let git = crate::controlled_git::executable().expect("controlled Git executable");
        let run_git = |args: &[&str]| {
            let output = Command::new(&git)
                .current_dir(root)
                .args(args)
                .output()
                .expect("run Git fixture command");
            assert!(
                output.status.success(),
                "git {args:?} failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        };
        run_git(&["init", "--quiet"]);

        let candidate = "0123456789abcdef0123456789abcdef01234567";
        let evidence_path = root.join("evidence.json");
        let evidence = json!({
            "schema_version": "trust.product-proof.v1",
            "candidate_commit": candidate,
            "runner": rust_owned_runner_json(),
            "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
            "proof_results": valid_results_json(),
            "proof_artifact_sha256": TEST_SHA256,
            "repo_dirty": false,
        });
        fs::write(&evidence_path, serde_json::to_vec(&evidence).expect("render evidence"))
            .expect("write evidence");
        run_git(&["add", "evidence.json"]);
        run_git(&[
            "-c",
            "user.name=Release Test",
            "-c",
            "user.email=release-test@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "--quiet",
            "--no-verify",
            "-m",
            "fixture",
        ]);

        let head = crate::controlled_git::canonical_head(
            root,
            "release report fixture HEAD probe",
            64 * 1024,
            Duration::from_secs(10),
        )
        .expect("fixture HEAD");
        assert_ne!(head, candidate);

        let stub_options = ProductProofStubOptions::default();
        let mismatched_stub = build_product_proof_stub_release_report(
            root,
            &stub_options,
            &evidence,
            None,
            None,
            None,
        )
        .expect("blocked stub report");
        assert_eq!(mismatched_stub["repo_dirty"], true);
        assert_eq!(mismatched_stub["repo_dirty_metadata"]["available"], false);
        assert!(mismatched_stub["repo_dirty_metadata"]["dirty"].is_null());
        assert!(
            mismatched_stub["repo_dirty_metadata"]["error"]
                .as_str()
                .is_some_and(|error| error.contains("repository HEAD changed from candidate"))
        );
        assert_eq!(mismatched_stub["status"], "blocked");
        assert_eq!(mismatched_stub["product_proof_pass_evidence"], false);
        assert_eq!(mismatched_stub["domination_admissible"], false);

        let mismatched =
            build_product_proof_release_report(root, candidate, "evidence.json", &evidence_path);
        assert_eq!(mismatched["repo_dirty"], true);
        assert_eq!(mismatched["repo_dirty_metadata"]["available"], false);
        assert!(mismatched["repo_dirty_metadata"]["dirty"].is_null());
        let has_code = |report: &serde_json::Value, code: &str| {
            report["blockers"]
                .as_array()
                .expect("release blockers")
                .iter()
                .any(|finding| finding["code"] == code)
        };
        assert!(has_code(&mismatched, "product-proof-release-repo-provenance-unavailable"));
        assert!(has_code(&mismatched, "product-proof-solver-evidence-unverified"));
        assert_eq!(mismatched["status"], "blocked");
        assert_eq!(mismatched["product_proof_pass_evidence"], false);
        assert_eq!(mismatched["domination_admissible"], false);

        let mut matching_evidence = evidence.clone();
        matching_evidence["candidate_commit"] = json!(head);
        let matching_stub = build_product_proof_stub_release_report(
            root,
            &stub_options,
            &matching_evidence,
            None,
            None,
            None,
        )
        .expect("clean stub report");
        assert_eq!(matching_stub["repo_dirty"], false);
        assert_eq!(matching_stub["repo_dirty_metadata"]["available"], true);
        assert_eq!(matching_stub["repo_dirty_metadata"]["dirty"], false);
        assert_eq!(matching_stub["status"], "blocked");
        let matching =
            build_product_proof_release_report(root, &head, "evidence.json", &evidence_path);
        assert_eq!(matching["repo_dirty"], false);
        assert_eq!(matching["repo_dirty_metadata"]["dirty"], false);
        assert!(!has_code(&matching, "product-proof-release-repo-provenance-unavailable"));
        assert!(has_code(&matching, "product-proof-solver-evidence-unverified"));

        fs::write(root.join("untracked.txt"), b"dirty").expect("write untracked fixture");
        let dirty_stub = build_product_proof_stub_release_report(
            root,
            &stub_options,
            &matching_evidence,
            None,
            None,
            None,
        )
        .expect("dirty stub report");
        assert_eq!(dirty_stub["repo_dirty"], true);
        assert_eq!(dirty_stub["repo_dirty_metadata"]["available"], true);
        assert_eq!(dirty_stub["repo_dirty_metadata"]["dirty"], true);
        assert_eq!(dirty_stub["repo_dirty_metadata"]["porcelain_v1"].as_array().unwrap().len(), 1);
        assert_eq!(dirty_stub["status"], "blocked");
        let dirty =
            build_product_proof_release_report(root, &head, "evidence.json", &evidence_path);
        assert_eq!(dirty["repo_dirty"], true);
        assert_eq!(dirty["repo_dirty_metadata"]["available"], true);
        assert_eq!(dirty["repo_dirty_metadata"]["dirty"], true);
        assert!(has_code(&dirty, "product-proof-release-repo-dirty"));
        assert!(has_code(&dirty, "product-proof-solver-evidence-unverified"));
        assert_eq!(dirty["product_proof_pass_evidence"], false);
        assert_eq!(dirty["domination_admissible"], false);
    }

    #[test]
    fn product_proof_stub_report_without_candidate_has_unavailable_status() {
        let temp = tempfile::tempdir().expect("stub report fixture");
        let report = build_product_proof_stub_release_report(
            temp.path(),
            &ProductProofStubOptions::default(),
            &json!({}),
            None,
            None,
            None,
        )
        .expect("blocked stub report");

        assert_eq!(report["repo_dirty"], true);
        assert_eq!(report["repo_dirty_metadata"]["available"], false);
        assert!(report["repo_dirty_metadata"]["dirty"].is_null());
        assert_eq!(report["repo_dirty_metadata"]["error"], "candidate HEAD is unavailable");
        assert_eq!(report["status"], "blocked");
        assert_eq!(report["product_proof_pass_evidence"], false);
        assert_eq!(report["domination_admissible"], false);
    }

    #[cfg(unix)]
    #[test]
    fn stage2_release_binding_rejects_symlinked_compiler_leaf() {
        use std::fs;
        use std::os::unix::fs::{PermissionsExt, symlink};

        let temp = tempfile::tempdir().expect("stage2 trustc fixture");
        let path_text = "build/host/stage2/bin/trustc";
        let linked = temp.path().join(path_text);
        let real = temp.path().join("build/other/stage2/bin/trustc");
        fs::create_dir_all(linked.parent().expect("linked parent")).expect("linked parent");
        fs::create_dir_all(real.parent().expect("real parent")).expect("real parent");
        fs::write(&real, b"#!/bin/sh\nexit 0\n").expect("write real trustc");
        let mut permissions = fs::metadata(&real).expect("real metadata").permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&real, permissions).expect("make real trustc executable");
        symlink(&real, &linked).expect("link stage2 trustc");

        let error = product_proof_stage2_trustc_binding_from_path(
            temp.path(),
            path_text,
            "0123456789abcdef0123456789abcdef01234567",
        )
        .expect_err("release identity must reject a canonical compiler symlink");
        assert!(error.contains("no symlink components"), "{error}");
    }

    /// `build -> build.noindex` (the Spotlight layout, docs/BUILD_AND_INSTALL.md)
    /// is the one link a repo-relative exact file may pass through, and only as
    /// its first component. Any other `build` link is still refused.
    #[cfg(unix)]
    #[test]
    fn repo_relative_exact_file_admits_only_the_sanctioned_build_link() {
        use std::fs;
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("build.noindex fixture");
        let root = temp.path().canonicalize().expect("canonical fixture root");
        let path_text = "build/host/stage2/bin/trustc";
        let physical = root.join("build.noindex/host/stage2/bin/trustc");
        fs::create_dir_all(physical.parent().expect("parent")).expect("create stage2 bin");
        fs::write(&physical, b"#!/bin/sh\nexit 0\n").expect("write trustc");
        symlink("build.noindex", root.join("build")).expect("link build");
        assert_eq!(repo_relative_exact_file(&root, path_text), Some(root.join(path_text)));

        fs::remove_file(root.join("build")).expect("remove build link");
        fs::rename(root.join("build.noindex"), root.join("elsewhere")).expect("move tree");
        symlink("elsewhere", root.join("build")).expect("relink build");
        assert_eq!(repo_relative_exact_file(&root, path_text), None);
        // A link below the first component is still refused.
        fs::remove_file(root.join("build")).expect("remove build link");
        fs::create_dir(root.join("build")).expect("real build");
        symlink(root.join("elsewhere/host"), root.join("build/host")).expect("link host");
        assert_eq!(repo_relative_exact_file(&root, path_text), None);
    }

    #[test]
    fn source_tarball_rejects_a_different_candidate_with_a_matching_outer_digest() {
        let temp = tempfile::tempdir().expect("source archive fixture");
        let candidate = "0123456789abcdef0123456789abcdef01234567";
        let stale = "0123456789abcdef0123456789abcdef01234566";
        let name = "trust-src-1.96.0-trust";
        let path_text = format!("dist/{name}.tar.xz");
        let source_dir = temp.path().join(name);
        let archive = temp.path().join(&path_text);
        fs::create_dir_all(&source_dir).expect("create source tree");
        fs::create_dir_all(archive.parent().expect("archive parent")).expect("create dist");
        fs::write(source_dir.join("git-commit-hash"), stale).expect("write stale revision");
        fs::write(source_dir.join("README.md"), b"source archive\n").expect("write source file");
        let encoder =
            xz2::write::XzEncoder::new(fs::File::create(&archive).expect("create archive"), 6);
        let mut builder = tar::Builder::new(encoder);
        builder.append_dir_all(name, &source_dir).expect("add source tree");
        builder.into_inner().expect("finish tar archive").finish().expect("finish XZ stream");

        let identity = json!({
            "path": path_text,
            "sha256": file_sha256(&archive).expect("hash archive"),
            "candidate_commit": candidate,
        });
        assert!(
            source_tarball_identity_defects(temp.path(), candidate, &identity)
                .iter()
                .any(|(code, _)| *code == "product-proof-release-source-tarball-candidate-mismatch"),
            "archive from another revision must not be admitted"
        );
        assert!(
            product_proof_source_tarball_binding_from_path(temp.path(), &path_text, candidate)
                .is_err(),
            "stub exporter must refuse the same archive"
        );
    }

    #[test]
    fn source_tarball_revision_member_must_be_unique_and_regular() {
        let temp = tempfile::tempdir().expect("source archive fixture");
        let name = "trust-src-1.96.0-trust";
        let member = format!("{name}/git-commit-hash");
        let candidate = "0123456789abcdef0123456789abcdef01234567";
        let duplicate = temp.path().join(format!("{name}.tar.xz"));
        let encoder = xz2::write::XzEncoder::new(fs::File::create(&duplicate).expect("archive"), 6);
        let mut builder = tar::Builder::new(encoder);
        for _ in 0..2 {
            let mut header = tar::Header::new_gnu();
            header.set_entry_type(tar::EntryType::Regular);
            header.set_mode(0o644);
            header.set_size(40);
            builder.append_data(&mut header, &member, candidate.as_bytes()).expect("revision");
        }
        builder.into_inner().expect("finish tar").finish().expect("finish XZ");
        assert!(
            source_tarball_archive_identity(&duplicate)
                .expect_err("duplicate revision member")
                .contains("duplicate"),
        );

        let linked = temp.path().join(format!("{name}-link.tar.xz"));
        let encoder = xz2::write::XzEncoder::new(fs::File::create(&linked).expect("archive"), 6);
        let mut builder = tar::Builder::new(encoder);
        let mut header = tar::Header::new_gnu();
        header.set_entry_type(tar::EntryType::Symlink);
        header.set_mode(0o777);
        header.set_size(0);
        header.set_link_name("other").expect("link target");
        builder
            .append_data(&mut header, format!("{name}-link/git-commit-hash"), std::io::empty())
            .expect("linked revision");
        builder.into_inner().expect("finish tar").finish().expect("finish XZ");
        assert!(
            source_tarball_archive_identity(&linked)
                .expect_err("symlinked revision member")
                .contains("exact regular"),
        );
    }

    #[test]
    fn source_tarball_rejects_extended_header_alias_of_revision_member() {
        let temp = tempfile::tempdir().expect("source archive fixture");
        let name = "trust-src-1.96.0-trust";
        let member = format!("{name}/git-commit-hash");
        let candidate = "0123456789abcdef0123456789abcdef01234567";
        let archive = temp.path().join(format!("{name}.tar.xz"));
        let encoder = xz2::write::XzEncoder::new(fs::File::create(&archive).expect("archive"), 6);
        let mut builder = tar::Builder::new(encoder);
        let mut longname = member.as_bytes().to_vec();
        longname.push(0);
        let mut header = tar::Header::new_gnu();
        header.set_entry_type(tar::EntryType::GNULongName);
        header.set_mode(0o644);
        header.set_size(longname.len() as u64);
        builder.append_data(&mut header, "././@LongLink", &longname[..]).expect("long name");
        let mut header = tar::Header::new_gnu();
        header.set_entry_type(tar::EntryType::Regular);
        header.set_mode(0o644);
        header.set_size(40);
        builder.append_data(&mut header, "other", candidate.as_bytes()).expect("alias");
        let mut header = tar::Header::new_gnu();
        header.set_entry_type(tar::EntryType::Regular);
        header.set_mode(0o644);
        header.set_size(40);
        builder.append_data(&mut header, &member, candidate.as_bytes()).expect("revision");
        builder.into_inner().expect("finish tar").finish().expect("finish XZ");

        assert!(
            source_tarball_archive_identity(&archive)
                .expect_err("extended header aliases the revision member")
                .contains("alias"),
        );
    }

    #[test]
    fn source_tarball_rejects_lexical_aliases_after_revision_member() {
        let temp = tempfile::tempdir().expect("source archive fixture");
        let name = "trust-src-1.96.0-trust";
        let member = format!("{name}/git-commit-hash");
        let candidate = "0123456789abcdef0123456789abcdef01234567";
        let stale = "0123456789abcdef0123456789abcdef01234566";
        for (case, alias) in [
            ("dot", format!("{name}/./git-commit-hash")),
            ("parent", format!("{name}/sub/../git-commit-hash")),
            ("case", format!("{name}/GIT-COMMIT-HASH")),
        ] {
            let dir = temp.path().join(case);
            fs::create_dir(&dir).expect("archive case directory");
            let archive = dir.join(format!("{name}.tar.xz"));
            let encoder =
                xz2::write::XzEncoder::new(fs::File::create(&archive).expect("archive"), 6);
            let mut builder = tar::Builder::new(encoder);
            let mut header = tar::Header::new_gnu();
            header.set_entry_type(tar::EntryType::Regular);
            header.set_mode(0o644);
            header.set_size(40);
            builder.append_data(&mut header, &member, candidate.as_bytes()).expect("revision");
            let mut header = tar::Header::new_gnu();
            header.set_entry_type(tar::EntryType::Regular);
            header.set_mode(0o644);
            header.set_size(7);
            builder
                .append_data(&mut header, format!("{name}/README"), b"readme\n".as_slice())
                .expect("unrelated regular member");
            if case == "parent" {
                let mut header = tar::Header::new_gnu();
                header.set_entry_type(tar::EntryType::Directory);
                header.set_mode(0o755);
                header.set_size(0);
                builder
                    .append_data(&mut header, format!("{name}/sub/"), std::io::empty())
                    .expect("intermediate directory");
            }
            let mut header = tar::Header::new_gnu();
            header.set_entry_type(tar::EntryType::Regular);
            header.set_mode(0o644);
            header.set_size(40);
            header.as_mut_bytes()[..alias.len()].copy_from_slice(alias.as_bytes());
            header.set_cksum();
            builder.append(&header, stale.as_bytes()).expect("raw alias member");
            builder.into_inner().expect("finish tar").finish().expect("finish XZ");
            let error = source_tarball_archive_identity(&archive)
                .expect_err("lexical alias must not replace the exact revision member");
            assert!(error.contains("alias"), "{case}: {error}");
        }
    }

    #[test]
    fn source_tarball_rejects_unrelated_link_members() {
        let temp = tempfile::tempdir().expect("source archive fixture");
        let name = "trust-src-1.96.0-trust";
        let member = format!("{name}/git-commit-hash");
        let candidate = "0123456789abcdef0123456789abcdef01234567";
        for (case, kind, target) in [
            ("symlink", tar::EntryType::Symlink, "."),
            ("hardlink", tar::EntryType::Link, member.as_str()),
        ] {
            let dir = temp.path().join(case);
            fs::create_dir(&dir).expect("archive case directory");
            let archive = dir.join(format!("{name}.tar.xz"));
            let encoder =
                xz2::write::XzEncoder::new(fs::File::create(&archive).expect("archive"), 6);
            let mut builder = tar::Builder::new(encoder);
            let mut header = tar::Header::new_gnu();
            header.set_entry_type(tar::EntryType::Regular);
            header.set_mode(0o644);
            header.set_size(40);
            builder.append_data(&mut header, &member, candidate.as_bytes()).expect("revision");
            let mut header = tar::Header::new_gnu();
            header.set_entry_type(kind);
            header.set_mode(0o777);
            header.set_size(0);
            header.set_link_name(target).expect("link target");
            builder
                .append_data(&mut header, format!("{name}/alias"), std::io::empty())
                .expect("link alias");
            if kind == tar::EntryType::Symlink {
                let stale = "0123456789abcdef0123456789abcdef01234566";
                let mut header = tar::Header::new_gnu();
                header.set_entry_type(tar::EntryType::Regular);
                header.set_mode(0o644);
                header.set_size(40);
                builder
                    .append_data(
                        &mut header,
                        format!("{name}/alias/git-commit-hash"),
                        stale.as_bytes(),
                    )
                    .expect("revision through linked directory");
            }
            builder.into_inner().expect("finish tar").finish().expect("finish XZ");
            source_tarball_archive_identity(&archive).expect_err(
                "a hardlink member, or a member written through a symlink, must fail closed",
            );
        }
    }

    #[test]
    fn source_tarball_accepts_unrelated_regular_members() {
        let temp = tempfile::tempdir().expect("source archive fixture");
        let name = "trust-src-1.96.0-trust";
        let member = format!("{name}/git-commit-hash");
        let candidate = "0123456789abcdef0123456789abcdef01234567";
        let archive = temp.path().join(format!("{name}.tar.xz"));
        let encoder = xz2::write::XzEncoder::new(fs::File::create(&archive).expect("archive"), 6);
        let mut builder = tar::Builder::new(encoder);
        for (path, data) in [
            (member.as_str(), candidate.as_bytes()),
            ("trust-src-1.96.0-trust/README", b"readme\n".as_slice()),
        ] {
            let mut header = tar::Header::new_gnu();
            header.set_entry_type(tar::EntryType::Regular);
            header.set_mode(0o644);
            header.set_size(data.len() as u64);
            builder.append_data(&mut header, path, data).expect("regular member");
        }
        builder.into_inner().expect("finish tar").finish().expect("finish XZ");
        let (digest, embedded) =
            source_tarball_archive_identity(&archive).expect("valid archive identity");
        assert_eq!(digest, file_sha256(&archive).expect("outer digest"));
        assert_eq!(embedded, candidate);
    }

    #[test]
    fn source_tarball_diagnostic_byte_bounds_fail_closed() {
        let temp = tempfile::tempdir().expect("source archive fixture");
        let archive = temp.path().join("trust-src-1.96.0-trust.tar.xz");
        fs::File::create(&archive)
            .expect("create sparse archive")
            .set_len(super::MAX_SOURCE_ARCHIVE_COMPRESSED_BYTES + 1)
            .expect("extend sparse archive");
        assert!(
            source_tarball_archive_identity(&archive)
                .expect_err("oversized archive must fail before readback")
                .contains("compressed-byte bound")
        );

        let mut reader = super::BoundedSourceArchiveReader {
            inner: &[1_u8, 2][..],
            bytes: super::MAX_SOURCE_ARCHIVE_DECOMPRESSED_BYTES - 1,
        };
        assert!(std::io::Read::read(&mut reader, &mut [0_u8; 2]).is_err());
    }

    #[test]
    #[ignore = "requires TRUST_SOURCE_ARCHIVE_PROBE to name a real source .tar.xz"]
    fn source_tarball_real_archive_probe() {
        let path = std::env::var("TRUST_SOURCE_ARCHIVE_PROBE").expect("real source archive path");
        let started = std::time::Instant::now();
        let (digest, commit) = source_tarball_archive_identity(std::path::Path::new(&path))
            .expect("real archive identity");
        println!("source archive: sha256={digest} commit={commit} elapsed={:?}", started.elapsed());
    }

    #[test]
    fn metadata_only_evidence_is_rejected() {
        let j = json!({
            "schema_version": "trust.product-proof.v1",
            "evidence_kind": "k",
            "candidate_commit": "abc123",
            "runner": rust_owned_runner_json()
        });
        assert_eq!(
            proof_content_defect(&j).expect("must reject metadata-only").0,
            "product-proof-evidence-content-missing"
        );
    }

    #[test]
    fn empty_or_partial_results_rejected() {
        // Zero proved.
        assert_eq!(
            proof_content_defect(&proof_with_results(json!({"proved": 0, "total": 0}))).unwrap().0,
            "product-proof-evidence-content-insufficient"
        );
        // Not all obligations discharged.
        assert_eq!(
            proof_content_defect(&proof_with_results(json!({"proved": 3, "total": 5}))).unwrap().0,
            "product-proof-evidence-content-insufficient"
        );
        // proved == total but an unknown remains.
        assert_eq!(
            proof_content_defect(&proof_with_results(
                json!({"proved": 5, "total": 5, "unknown": 1})
            ))
            .unwrap()
            .0,
            "product-proof-evidence-content-insufficient"
        );
        // Any non-proof counter blocks a proof claim, not only failed/unknown.
        assert_eq!(
            proof_content_defect(&proof_with_results(
                json!({"proved": 5, "total": 5, "timed_out": 1})
            ))
            .unwrap()
            .0,
            "product-proof-evidence-content-insufficient"
        );
    }

    #[test]
    fn fully_discharged_but_unattributed_rejected() {
        let j = json!({
            "runner": rust_owned_runner_json(),
            "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
            "proof_results": {"proved": 4, "total": 4, "failed": 0, "unknown": 0}
        });
        assert_eq!(proof_content_defect(&j).unwrap().0, "product-proof-evidence-unattributed");
    }

    #[test]
    fn fully_discharged_and_attributed_passes_shape_check_only() {
        // These documents pass the minimum shape preflight. They still cannot
        // cross the separate solver admission boundary below.
        assert!(
            proof_content_defect(&json!({
                "runner": rust_owned_runner_json(),
                "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
                "proof_results": {"proved": 4, "total": 4, "failed": 0, "unknown": 0, "by_solver": ["ay"]},
                "proof_artifact_sha256": TEST_SHA256
            }))
            .is_none()
        );
        // Bound by a proof transcript hash.
        assert!(
            proof_content_defect(&json!({
                "runner": rust_owned_runner_json(),
                "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
                "proof_results": {"proved": 4, "total": 4},
                "proof_transcript_hash": TEST_SHA256
            }))
            .is_none()
        );
        // Bound by solver attribution plus structured artifact material.
        assert!(
            proof_content_defect(&json!({
                "runner": rust_owned_runner_json(),
                "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
                "proof_results": {"proved": 4, "total": 4, "failed": 0, "unknown": 0, "by_solver": ["ay"]},
                "component_artifact": {
                    "name": "trust-artifact.tar.xz",
                    "sha256": TEST_SHA256
                }
            }))
            .is_none()
        );

        let admission_defect =
            solver_evidence_admission_defect("fabricated solver evidence fixture");
        for required in [
            "no registered kind-specific Rust collector/replayer",
            "self-declared runner identity",
            "exact candidate executable",
            "complete typed obligation set with stable IDs",
            "canonical VC/query bytes",
            "reconcile every ID exactly once",
            "saved claim_digest_sha256 cannot reconstruct the VC",
            "checks bindings, not LRAT/LFSC derivations",
        ] {
            assert!(
                admission_defect.contains(required),
                "solver admission defect must name missing `{required}`: {admission_defect}"
            );
        }
    }

    #[test]
    fn authored_solver_transcript_and_certificate_cannot_clear_release_blocker() {
        let temp = tempfile::tempdir().expect("release evidence fixture");
        let candidate = "0123456789abcdef0123456789abcdef01234567";
        let evidence_path = temp.path().join("evidence.json");
        let evidence = json!({
            "schema_version": "trust.product-proof.v1",
            "candidate_commit": candidate,
            "runner": rust_owned_runner_json(),
            "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
            "repo_dirty": false,
            "status": "passed",
            "product_proof_pass_evidence": true,
            "domination_admissible": true,
            "proof_results": valid_results_json(),
            "proof_artifact_sha256": TEST_SHA256,
            "solver_transcript": {
                "status": "replayed",
                "candidate_executable_sha256": TEST_SHA256,
                "obligations": [{
                    "obligation_id": "division-by-zero:0",
                    "claim_digest_sha256": TEST_SHA256,
                    "status": "proved"
                }]
            },
            "checked_certificate": {
                "format": "lrat",
                "status": "checked",
                "proof_sha256": TEST_SHA256
            }
        });
        assert!(proof_content_defect(&evidence).is_none());
        fs::write(&evidence_path, serde_json::to_vec(&evidence).expect("render evidence"))
            .expect("write evidence");

        let findings = validate_product_proof_release_artifact_evidence(
            temp.path(),
            candidate,
            &evidence_path,
            &evidence,
        );
        let solver = findings
            .iter()
            .find(|finding| finding.code == "product-proof-solver-evidence-unverified")
            .expect("manual solver JSON must retain the unconditional blocker");
        assert!(solver.message.contains("Missing producer contract"));
        assert!(solver.message.contains("Missing replayer contract"));

        let report = build_product_proof_release_report(
            temp.path(),
            candidate,
            "evidence.json",
            &evidence_path,
        );
        assert_eq!(report["status"], "blocked");
        assert_eq!(report["product_proof_pass_evidence"], false);
        assert_eq!(report["domination_admissible"], false);
    }

    #[test]
    fn fully_discharged_without_timestamp_rejected() {
        let j = json!({
            "runner": rust_owned_runner_json(),
            "proof_results": valid_results_json(),
            "proof_artifact_sha256": TEST_SHA256
        });
        assert_eq!(proof_content_defect(&j).unwrap().0, "product-proof-evidence-timestamp-missing");
    }

    #[test]
    fn low_numeric_timestamps_rejected() {
        for timestamp in [0, 1, PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS - 1] {
            let j = json!({
                "runner": rust_owned_runner_json(),
                "generated_at": timestamp,
                "proof_results": valid_results_json(),
                "proof_artifact_sha256": TEST_SHA256
            });
            assert_eq!(
                proof_content_defect(&j).unwrap().0,
                "product-proof-evidence-timestamp-missing",
                "low timestamp should not satisfy product-proof evidence: {timestamp}"
            );
        }
    }

    #[test]
    fn malformed_timestamp_strings_rejected() {
        for timestamp in [
            "0",
            "built at 7",
            "2026-99-99T00:00:00Z",
            "not-a-date 1",
            "2024-01-01",
            "2024-01-01T00:00:00",
        ] {
            let j = json!({
                "runner": rust_owned_runner_json(),
                "generated_at": timestamp,
                "proof_results": valid_results_json(),
                "proof_artifact_sha256": TEST_SHA256
            });
            assert_eq!(
                proof_content_defect(&j).unwrap().0,
                "product-proof-evidence-timestamp-missing",
                "malformed timestamp should not satisfy product-proof evidence: {timestamp}"
            );
        }
    }

    #[test]
    fn stale_rfc3339_timestamp_strings_rejected() {
        for timestamp in
            ["2024-12-31T23:59:59Z", "2025-01-01T00:59:59+01:00", "2024-12-31T23:29:59-00:30"]
        {
            let j = json!({
                "runner": rust_owned_runner_json(),
                "generated_at": timestamp,
                "proof_results": valid_results_json(),
                "proof_artifact_sha256": TEST_SHA256
            });
            assert_eq!(
                proof_content_defect(&j).unwrap().0,
                "product-proof-evidence-timestamp-missing",
                "stale timestamp should not satisfy product-proof evidence: {timestamp}"
            );
        }
    }

    #[test]
    fn rfc3339_timestamp_strings_are_accepted() {
        for timestamp in [
            "2025-01-01T00:00:00Z",
            "2025-01-01t00:00:00z",
            "2025-01-01T00:00:00.123Z",
            "2025-01-01T01:30:00+01:30",
            "2025-01-01T00:30:00-00:30",
        ] {
            let j = json!({
                "runner": rust_owned_runner_json(),
                "generated_at": timestamp,
                "proof_results": valid_results_json(),
                "proof_artifact_sha256": TEST_SHA256
            });
            assert!(
                proof_content_defect(&j).is_none(),
                "valid RFC3339 timestamp should satisfy product-proof evidence: {timestamp}"
            );
        }
    }

    #[test]
    fn future_numeric_timestamps_rejected() {
        let j = json!({
            "runner": rust_owned_runner_json(),
            "generated_at": u64::MAX,
            "proof_results": valid_results_json(),
            "proof_artifact_sha256": TEST_SHA256
        });
        assert_eq!(proof_content_defect(&j).unwrap().0, "product-proof-evidence-timestamp-missing");
    }

    #[test]
    fn placeholder_concrete_bindings_are_rejected() {
        for j in [
            json!({
                "runner": rust_owned_runner_json(),
                "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
                "proof_results": valid_results_json(),
                "tool_identity": {}
            }),
            json!({
                "runner": rust_owned_runner_json(),
                "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
                "proof_results": valid_results_json(),
                "version_identity": {"tools": {}}
            }),
            json!({
                "runner": rust_owned_runner_json(),
                "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
                "proof_results": valid_results_json(),
                "binary_identity": {"path": "/tmp/trustdoc"}
            }),
            json!({
                "runner": rust_owned_runner_json(),
                "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
                "proof_results": valid_results_json(),
                "source_archive_hashes": [{"name": "trust-src.tar.xz"}]
            }),
            json!({
                "runner": rust_owned_runner_json(),
                "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
                "proof_results": valid_results_json(),
                "component_artifact": {"name": "trust-artifact.tar.xz"}
            }),
            json!({
                "runner": rust_owned_runner_json(),
                "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
                "proof_results": valid_results_json(),
                "compile_back_artifact_digest_binding": {"selected_image_range": "0..16"}
            }),
        ] {
            assert_eq!(
                proof_content_defect(&j).unwrap().0,
                "product-proof-evidence-unattributed",
                "placeholder binding should not count as concrete proof material: {j}"
            );
        }
    }

    #[test]
    fn label_only_attribution_and_short_hashes_are_rejected() {
        assert_eq!(
            proof_content_defect(&json!({
                "runner": rust_owned_runner_json(),
                "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
                "proof_results": {"proved": 4, "total": 4, "by_solver": ["focused product-proof test"]}
            }))
            .unwrap()
            .0,
            "product-proof-evidence-unattributed"
        );
        assert_eq!(
            proof_content_defect(&json!({
                "runner": rust_owned_runner_json(),
                "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
                "proof_results": {"proved": 4, "total": 4},
                "proof_transcript_hash": "deadbeef"
            }))
            .unwrap()
            .0,
            "product-proof-evidence-unattributed"
        );
    }

    #[test]
    fn rust_owned_runner_identity_is_required() {
        let missing_runner = json!({
            "proof_results": valid_results_json(),
            "proof_artifact_sha256": TEST_SHA256
        });
        assert_eq!(
            proof_content_defect(&missing_runner).unwrap().0,
            "product-proof-evidence-runner-untrusted"
        );

        let missing_python_marker = json!({
            "runner": {
                "implementation": "rust",
                "entrypoint": "targo trust release check"
            },
            "proof_results": valid_results_json(),
            "proof_artifact_sha256": TEST_SHA256
        });
        assert_eq!(
            proof_content_defect(&missing_python_marker).unwrap().0,
            "product-proof-evidence-runner-untrusted"
        );

        let missing_identity = json!({
            "runner": {"python_used": false},
            "proof_results": valid_results_json(),
            "proof_artifact_sha256": TEST_SHA256
        });
        assert_eq!(
            proof_content_defect(&missing_identity).unwrap().0,
            "product-proof-evidence-runner-untrusted"
        );

        let non_trust_runner = json!({
            "runner": {
                "implementation": "rust",
                "entrypoint": "./run-proof",
                "python_used": false
            },
            "proof_results": valid_results_json(),
            "proof_artifact_sha256": TEST_SHA256
        });
        assert_eq!(
            proof_content_defect(&non_trust_runner).unwrap().0,
            "product-proof-evidence-runner-untrusted"
        );

        for spoofed_runner in [
            json!({
                "implementation": "not-rust-but-contains-rust",
                "entrypoint": "targo trust release check",
                "python_used": false
            }),
            json!({
                "implementation": "rust",
                "entrypoint": "evil-targo-trust-wrapper",
                "python_used": false
            }),
            json!({
                "implementation": "rust",
                "tool": "trustc-wrapper",
                "python_used": false
            }),
        ] {
            let evidence = json!({
                "runner": spoofed_runner,
                "proof_results": valid_results_json(),
                "proof_artifact_sha256": TEST_SHA256
            });
            assert_eq!(
                proof_content_defect(&evidence).unwrap().0,
                "product-proof-evidence-runner-untrusted"
            );
        }
    }

    #[test]
    fn python_runner_evidence_is_rejected() {
        for j in [
            json!({
                "runner": {"python_used": true},
                "proof_results": {"proved": 4, "total": 4, "failed": 0, "unknown": 0, "by_solver": ["ay"]},
                "proof_artifact_sha256": TEST_SHA256,
            }),
            json!({
                "runner": {"implementation": "python"},
                "proof_results": {"proved": 4, "total": 4, "failed": 0, "unknown": 0, "by_solver": ["ay"]},
                "proof_artifact_sha256": TEST_SHA256,
            }),
            json!({
                "runner_kind": "python",
                "proof_results": {"proved": 4, "total": 4, "failed": 0, "unknown": 0, "by_solver": ["ay"]},
                "proof_artifact_sha256": TEST_SHA256,
            }),
            json!({
                "runner": {"python_used": "true"},
                "proof_results": {"proved": 4, "total": 4, "failed": 0, "unknown": 0, "by_solver": ["ay"]},
                "proof_artifact_sha256": TEST_SHA256,
            }),
        ] {
            assert_eq!(
                proof_content_defect(&j).expect("Python-backed proof evidence must fail closed").0,
                "product-proof-evidence-python-runner"
            );
        }
    }

    #[test]
    fn nonzero_result_alias_counters_are_rejected() {
        for key in [
            "total_timed_out",
            "timeout_results",
            "unknown_results",
            "total_unknown",
            "skipped_results",
            "total_skipped",
        ] {
            let mut results = valid_results_json();
            results
                .as_object_mut()
                .expect("valid results should be an object")
                .insert(key.to_string(), json!(1));
            let j = json!({
                "runner": rust_owned_runner_json(),
                "proof_results": results,
                "proof_artifact_sha256": TEST_SHA256
            });
            let defect = proof_content_defect(&j).expect("nonzero alias must fail closed");
            assert_eq!(
                defect.0, "product-proof-evidence-content-insufficient",
                "alias counter {key} should be rejected"
            );
            assert!(
                defect.1.contains(&format!("{key}=1")),
                "alias counter {key} should appear in defect detail: {}",
                defect.1
            );
        }
    }

    #[test]
    fn malformed_or_unknown_result_counters_are_rejected() {
        for (key, value) in [
            ("failed", json!("0")),
            ("unknown", json!(-1)),
            ("unsupported", serde_json::Value::Null),
            ("future_counter", json!(0)),
        ] {
            let mut results = valid_results_json();
            results
                .as_object_mut()
                .expect("valid results should be an object")
                .insert(key.to_string(), value);
            let evidence = proof_with_results(results);
            assert_eq!(
                proof_content_defect(&evidence).unwrap().0,
                "product-proof-evidence-content-insufficient",
                "malformed or unknown result field must fail closed: {key}"
            );
        }
    }

    #[test]
    fn explicit_nonpassing_root_claims_are_rejected() {
        for (key, value) in [
            ("status", json!("blocked")),
            ("status", json!(false)),
            ("product_proof_pass_evidence", json!(false)),
            ("product_proof_pass_evidence", json!("true")),
            ("domination_admissible", json!(false)),
        ] {
            let mut evidence = proof_with_results(valid_results_json());
            evidence
                .as_object_mut()
                .expect("proof fixture should be an object")
                .insert(key.to_string(), value);
            assert_eq!(
                proof_content_defect(&evidence).unwrap().0,
                "product-proof-evidence-content-insufficient",
                "explicit non-pass claim must override otherwise passing counters: {key}"
            );
        }
    }

    fn proof_with_results(results: serde_json::Value) -> serde_json::Value {
        json!({
            "runner": rust_owned_runner_json(),
            "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
            "proof_results": results
        })
    }

    fn valid_results_json() -> serde_json::Value {
        json!({
            "proved": 4,
            "total": 4,
            "failed": 0,
            "unknown": 0,
            "by_solver": ["ay"]
        })
    }

    fn rust_owned_runner_json() -> serde_json::Value {
        json!({
            "implementation": "rust",
            "entrypoint": "targo trust release check",
            "python_used": false
        })
    }

    #[cfg(unix)]
    fn selected_image_replay_fixture() -> (tempfile::TempDir, String, serde_json::Value) {
        use std::os::unix::fs::PermissionsExt;

        let temp = tempfile::tempdir().expect("selected-image replay repository");
        let root = temp.path();
        let git = crate::controlled_git::executable().expect("controlled Git executable");
        let run_git = |args: &[&str]| {
            let output = Command::new(&git).current_dir(root).args(args).output().expect("run Git");
            assert!(
                output.status.success(),
                "git {args:?}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        };
        run_git(&["init", "--quiet"]);
        run_git(&[
            "-c",
            "user.name=Replay Test",
            "-c",
            "user.email=replay@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "--quiet",
            "--allow-empty",
            "--no-verify",
            "-m",
            "seed",
        ]);
        let candidate = crate::controlled_git::canonical_head(
            root,
            "selected-image fixture HEAD",
            64 * 1024,
            Duration::from_secs(10),
        )
        .expect("fixture candidate");
        let tree = crate::controlled_git::text(
            root,
            &["rev-parse", "--verify", &format!("{candidate}^{{tree}}")],
            "selected-image fixture tree",
            64 * 1024,
            Duration::from_secs(10),
        )
        .expect("fixture tree");

        let executable_path = "build/host/stage2/bin/trustc";
        let executable = root.join(executable_path);
        fs::create_dir_all(executable.parent().expect("executable parent")).expect("mkdir");
        let script = format!("#!/bin/sh\nprintf 'trustc test\\ncommit-hash: {candidate}\\n'\n");
        fs::write(&executable, &script).expect("write executable");
        let mut permissions = fs::metadata(&executable).expect("executable metadata").permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&executable, permissions).expect("chmod executable");
        let executable_sha256 = format!("{:x}", Sha256::digest(script.as_bytes()));

        let root_bytes = b"AAhelloZZ";
        let selected_bytes = b"hello";
        fs::write(root.join("root.bin"), root_bytes).expect("write root artifact");
        fs::write(root.join("selected.bin"), selected_bytes).expect("write selected image");
        let root_sha256 = format!("{:x}", Sha256::digest(root_bytes));
        let selected_sha256 = format!("{:x}", Sha256::digest(selected_bytes));
        let artifact_census = json!([
            {"role": "root-artifact", "path": "root.bin", "sha256": root_sha256, "bytes": 9},
            {"role": "selected-image", "path": "selected.bin", "sha256": selected_sha256, "bytes": 5},
        ]);
        let executable_record = json!({
            "path": executable_path,
            "sha256": executable_sha256,
            "version": "trustc test",
            "commit_hash": candidate,
        });
        let subject = json!({
            "candidate_commit": candidate,
            "candidate_tree_oid": tree,
            "executable": executable_record,
            "artifact_census": artifact_census,
            "range": "2..7",
        });
        let obligation_id = format!(
            "sha256:{:x}",
            Sha256::digest(serde_json::to_vec(&subject).expect("render subject"))
        );
        let evidence = json!({
            "schema_version": "trust.product-proof.v1",
            "candidate_commit": candidate,
            "release_artifact_binding": {
                "schema_version": "trust.product-proof-release-binding.v1",
                "candidate_commit": candidate,
                "stage2_trustc": {
                    "name": "trustc", "stage": "stage2", "path": executable_path,
                    "sha256": executable_sha256, "executable": true,
                    "version": "trustc test", "commit_hash": candidate,
                },
            },
            "compile_back_artifact_digest_binding": {
                "root_artifact_path": "root.bin", "root_artifact_sha256": root_sha256,
                "selected_image_path": "selected.bin", "selected_image_sha256": selected_sha256,
                "selected_image_range": "2..7",
            },
            "selected_image_replay": {
                "schema_version": "trust.product-proof-selected-image-replay.v1",
                "candidate_commit": candidate,
                "candidate_tree_oid": tree,
                "executable": executable_record,
                "artifact_census": artifact_census,
                "obligations": [{
                    "id": obligation_id,
                    "relation": "root-range-equals-selected-image/v1",
                    "range": "2..7",
                }],
                "transcript": [{
                    "obligation_id": obligation_id,
                    "root_range_sha256": selected_sha256,
                    "selected_image_sha256": selected_sha256,
                }],
            },
        });
        (temp, candidate, evidence)
    }

    #[cfg(unix)]
    #[test]
    fn selected_image_relation_rejects_root_replaced_between_path_hash_and_read() {
        let temp = tempfile::tempdir().expect("artifact directory");
        let root_path = temp.path().join("root.bin");
        let selected_path = temp.path().join("selected.bin");
        let parked_path = temp.path().join("parked.bin");
        let bound_root = b"AAwrongZZ";
        let forged_root = b"AAhelloZZ";
        let selected = b"hello";
        fs::write(&root_path, bound_root).expect("write bound root");
        fs::write(&selected_path, selected).expect("write selected image");
        let root_sha256 = format!("{:x}", Sha256::digest(bound_root));
        let selected_sha256 = format!("{:x}", Sha256::digest(selected));

        fs::rename(&root_path, &parked_path).expect("park bound root");
        fs::write(&root_path, forged_root).expect("substitute root");
        let mut opened_root = fs::File::open(&root_path).expect("open substituted root");
        fs::remove_file(&root_path).expect("remove substituted root path");
        fs::rename(&parked_path, &root_path).expect("restore bound root path");
        let mut opened_selected = fs::File::open(&selected_path).expect("open selected image");

        assert_eq!(file_sha256(&root_path).as_deref(), Some(root_sha256.as_str()));
        assert_eq!(file_sha256(&selected_path).as_deref(), Some(selected_sha256.as_str()));
        assert_eq!(&forged_root[2..7], selected);
        assert_ne!(&bound_root[2..7], selected);
        assert!(
            verify_selected_image_byte_relation(
                &mut opened_root,
                &mut opened_selected,
                2,
                7,
                &root_sha256,
                &selected_sha256,
            )
            .expect_err("substituted open inode must fail")
            .contains("opened artifact hash")
        );
    }

    #[cfg(unix)]
    #[test]
    fn selected_image_relation_checks_cross_chunk_range() {
        let temp = tempfile::tempdir().expect("artifact directory");
        let mut root = vec![b'x'; 16_384];
        root[8_190..8_200].copy_from_slice(b"0123456789");
        let selected = b"0123456789";
        let root_path = temp.path().join("root.bin");
        let selected_path = temp.path().join("selected.bin");
        fs::write(&root_path, &root).expect("write root");
        fs::write(&selected_path, selected).expect("write selected image");
        let (root_len, selected_len, range_sha256) = verify_selected_image_byte_relation(
            &mut fs::File::open(&root_path).expect("open root"),
            &mut fs::File::open(&selected_path).expect("open selected image"),
            8_190,
            8_200,
            &format!("{:x}", Sha256::digest(&root)),
            &format!("{:x}", Sha256::digest(selected)),
        )
        .expect("cross-chunk byte relation");
        assert_eq!((root_len, selected_len), (16_384, 10));
        assert_eq!(range_sha256, format!("{:x}", Sha256::digest(selected)));
    }

    #[cfg(unix)]
    #[test]
    fn selected_image_replay_accepts_only_the_byte_relation() {
        let (temp, candidate, evidence) = selected_image_replay_fixture();
        replay_selected_image_range(temp.path(), &candidate, &evidence).expect("honest replay");
        assert_eq!(
            selected_image_replay_check_json(temp.path(), &candidate, &evidence)["status"],
            "passed"
        );
        let findings = validate_product_proof_release_artifact_evidence(
            temp.path(),
            &candidate,
            &temp.path().join("evidence.json"),
            &evidence,
        );
        assert!(
            findings
                .iter()
                .any(|finding| { finding.code == "product-proof-solver-evidence-unverified" })
        );
        assert!(
            !findings
                .iter()
                .any(|finding| { finding.code == "product-proof-selected-image-replay-invalid" })
        );

        fs::write(
            temp.path().join("evidence.json"),
            serde_json::to_vec(&evidence).expect("render evidence"),
        )
        .expect("write evidence");
        let report = build_product_proof_release_report(
            temp.path(),
            &candidate,
            "evidence.json",
            &temp.path().join("evidence.json"),
        );
        assert_eq!(report["selected_image_replay_check"]["status"], "passed");
        assert_eq!(
            report["selected_image_replay_check"]["scope"],
            "selected-image-byte-relation-only"
        );
        assert_eq!(report["status"], "blocked");
        assert_eq!(report["product_proof_pass_evidence"], false);
        assert_eq!(report["domination_admissible"], false);
        assert!(report["blockers"].as_array().is_some_and(|blockers| {
            blockers
                .iter()
                .any(|blocker| blocker["code"] == "product-proof-solver-evidence-unverified")
        }));
    }

    #[cfg(unix)]
    #[test]
    fn selected_image_replay_rejects_forged_range_even_with_matching_claim() {
        let (temp, candidate, mut evidence) = selected_image_replay_fixture();
        evidence["compile_back_artifact_digest_binding"]["selected_image_range"] = json!("1..6");
        evidence["selected_image_replay"]["obligations"][0]["range"] = json!("1..6");
        assert!(
            replay_selected_image_range(temp.path(), &candidate, &evidence)
                .expect_err("forged range")
                .contains("do not equal")
        );
    }

    #[cfg(unix)]
    #[test]
    fn selected_image_replay_rejects_missing_duplicate_and_authored_pass() {
        let (temp, candidate, evidence) = selected_image_replay_fixture();
        let mut missing = evidence.clone();
        missing["selected_image_replay"]["obligations"] = json!([]);
        assert!(replay_selected_image_range(temp.path(), &candidate, &missing).is_err());
        let mut duplicate = evidence.clone();
        let obligation = duplicate["selected_image_replay"]["obligations"][0].clone();
        duplicate["selected_image_replay"]["obligations"] = json!([obligation.clone(), obligation]);
        assert!(replay_selected_image_range(temp.path(), &candidate, &duplicate).is_err());
        let mut missing_step = evidence.clone();
        missing_step["selected_image_replay"]["transcript"] = json!([]);
        assert!(replay_selected_image_range(temp.path(), &candidate, &missing_step).is_err());
        let mut duplicate_step = evidence.clone();
        let step = duplicate_step["selected_image_replay"]["transcript"][0].clone();
        duplicate_step["selected_image_replay"]["transcript"] = json!([step.clone(), step]);
        assert!(replay_selected_image_range(temp.path(), &candidate, &duplicate_step).is_err());
        let mut forged_census = evidence.clone();
        forged_census["selected_image_replay"]["artifact_census"][0]["bytes"] = json!(8);
        assert!(replay_selected_image_range(temp.path(), &candidate, &forged_census).is_err());
        let mut wrong_candidate = evidence.clone();
        wrong_candidate["release_artifact_binding"]["candidate_commit"] = json!("0".repeat(40));
        assert!(
            replay_selected_image_range(temp.path(), &candidate, &wrong_candidate)
                .expect_err("conflicting candidate")
                .contains("conflicting candidate")
        );
        let mut authored_pass = evidence;
        authored_pass["selected_image_replay"]["status"] = json!("passed");
        assert!(replay_selected_image_range(temp.path(), &candidate, &authored_pass).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn selected_image_replay_rejects_altered_artifact_tree_and_executable() {
        let (temp, candidate, evidence) = selected_image_replay_fixture();
        let mut wrong_tree = evidence.clone();
        wrong_tree["selected_image_replay"]["candidate_tree_oid"] = json!("0".repeat(40));
        assert!(replay_selected_image_range(temp.path(), &candidate, &wrong_tree).is_err());
        fs::write(temp.path().join("selected.bin"), b"HELLO").expect("alter artifact");
        assert!(replay_selected_image_range(temp.path(), &candidate, &evidence).is_err());
        fs::write(temp.path().join("selected.bin"), b"hello").expect("restore test artifact");
        fs::write(temp.path().join("build/host/stage2/bin/trustc"), b"#!/bin/sh\nexit 0\n")
            .expect("alter executable");
        assert!(
            replay_selected_image_range(temp.path(), &candidate, &evidence)
                .expect_err("altered executable")
                .contains("executable")
        );
    }
}
