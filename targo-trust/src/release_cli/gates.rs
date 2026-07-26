use std::path::{Path, PathBuf};
use std::{fs, io};

use trust_release::{
    FindingSeverity, GateFinding, GateReport, GateStatus, VersionIdentityEvidence,
};
use trust_version::{
    BoundToolIdentity, BoundTools, DEFAULT_VERSION_SOURCE_PATH, TrustVersionIdentity,
};

use super::identity::{
    bound_file_sha256, canonicalize_or_display, host_executable_name, is_executable_file,
    is_executable_target, path_is_stage1_sysroot, same_file_or_exact_contents,
    tool_identity_summary,
};
use super::product_proof::check_product_proof_coverage;
use super::publication::{
    check_publication_artifacts, check_publication_inputs, check_publication_ledger,
};
use super::seed::check_seed_freshness;
use super::types::{
    ReleaseProfile, ReleaseVisibility, ToolchainSurfaceProof, ToolchainSurfaceProofAlias,
    ToolchainSurfaceProofTool,
};
use crate::input_limits::{MAX_RELEASE_METADATA_BYTES, read_bounded_utf8_file};
use crate::pipeline::surface::forbidden_trust_surface_entries;

pub(super) fn build_release_reports(
    root: &Path,
    profile: ReleaseProfile,
    visibility: ReleaseVisibility,
    identity: &TrustVersionIdentity,
) -> Vec<GateReport> {
    let mut reports = vec![
        check_required_metadata(root),
        check_version_identity(identity),
        check_bound_tool_files(identity, profile),
        check_toolchain_surface_sysroot(identity, profile),
        check_release_tool_names(root, visibility),
        check_owned_deps(root, profile, visibility),
        check_seed_freshness(root, profile),
    ];

    if visibility == ReleaseVisibility::Public
        && matches!(profile, ReleaseProfile::Publication | ReleaseProfile::ProductProof)
    {
        reports.push(check_publication_inputs(root));
        reports.push(check_publication_artifacts(root));
        reports.push(check_publication_ledger(root, identity.candidate_commit.as_deref()));
    }

    if profile == ReleaseProfile::ProductProof {
        let product_proof_coverage = check_product_proof_coverage(
            root,
            identity.candidate_commit.as_deref(),
            Some(&identity.tools.daemon),
        );
        reports.push(build_trust_extra_gate(&product_proof_coverage));
        reports.push(product_proof_coverage);
    }

    reports
}

fn build_trust_extra_gate(product_proof_coverage: &GateReport) -> GateReport {
    if product_proof_coverage.status == GateStatus::Pass {
        return GateReport::pass("trust-extra")
            .with_evidence_refs(product_proof_coverage.evidence_refs.clone());
    }

    GateReport::new(
        "trust-extra",
        vec![GateFinding::blocker(
            "trust-extra-product-proof-coverage",
            "trust-extra cannot pass until product-proof-coverage passes",
        )],
    )
    .with_evidence_refs(product_proof_coverage.evidence_refs.clone())
}

fn check_required_metadata(root: &Path) -> GateReport {
    let mut findings = Vec::new();
    for relative in [DEFAULT_VERSION_SOURCE_PATH, "src/version", "src/ci/channel"] {
        let valid = fs::symlink_metadata(root.join(relative)).ok().is_some_and(|metadata| {
            !metadata.file_type().is_symlink() && metadata.file_type().is_file()
        });
        if !valid {
            findings.push(GateFinding::error(
                "required-metadata-missing",
                format!("missing exact regular metadata file `{relative}` (symlinks are rejected)"),
            ));
        }
    }
    GateReport::new("required-metadata", findings).with_evidence_refs([
        DEFAULT_VERSION_SOURCE_PATH,
        "src/version",
        "src/ci/channel",
    ])
}

fn check_version_identity(identity: &TrustVersionIdentity) -> GateReport {
    let evidence = VersionIdentityEvidence {
        frontend: Some(tool_identity_summary(&identity.tools.frontend)),
        extension: Some(tool_identity_summary(&identity.tools.extension)),
        compiler: Some(tool_identity_summary(&identity.tools.compiler)),
        documentation: Some(tool_identity_summary(&identity.tools.documentation)),
        formatter: Some(tool_identity_summary(&identity.tools.formatter)),
        cargo_formatter: Some(tool_identity_summary(&identity.tools.cargo_formatter)),
        tippy: Some(tool_identity_summary(&identity.tools.tippy)),
        targo_tippy: Some(tool_identity_summary(&identity.tools.targo_tippy)),
        tippy_driver: Some(tool_identity_summary(&identity.tools.tippy_driver)),
        analyzer: Some(tool_identity_summary(&identity.tools.analyzer)),
        daemon: Some(tool_identity_summary(&identity.tools.daemon)),
        miri: Some(tool_identity_summary(&identity.tools.miri)),
        targo_miri: Some(tool_identity_summary(&identity.tools.targo_miri)),
        candidate_commit: identity.candidate_commit.clone(),
    };
    trust_release::check_version_identity(&evidence)
}

pub(super) fn check_bound_tool_files(
    identity: &TrustVersionIdentity,
    profile: ReleaseProfile,
) -> GateReport {
    let mut findings = Vec::new();
    let severity = if profile.requires_bound_tools() {
        FindingSeverity::Error
    } else {
        FindingSeverity::Warning
    };

    for tool in identity.tools.required() {
        check_bound_tool_identity(&mut findings, severity, tool, true, profile);
    }
    for tool in identity.tools.optional() {
        check_bound_tool_identity(&mut findings, severity, tool, false, profile);
    }
    if profile.requires_bound_tools() {
        match (identity.candidate_commit.as_deref(), identity.tools.daemon.commit_hash.as_deref()) {
            (Some(candidate), Some(commit)) if candidate == commit => {}
            (Some(candidate), Some(commit)) => findings.push(finding_with_severity(
                severity,
                "tool-commit-mismatch",
                format!(
                    "trustd reports commit-hash {commit}, expected release candidate {candidate}"
                ),
            )),
            (Some(_), None) => {}
            (None, _) => {}
        }
    }

    GateReport::new("bound-tool-files", findings)
}

pub(super) fn check_toolchain_surface_sysroot(
    identity: &TrustVersionIdentity,
    profile: ReleaseProfile,
) -> GateReport {
    let proof = build_toolchain_surface_proof(&identity.tools);
    let severity = if profile.requires_bound_tools() {
        FindingSeverity::Error
    } else {
        FindingSeverity::Warning
    };
    let mut findings = Vec::new();

    if proof.stage1_alias_evidence {
        findings.push(finding_with_severity(
            severity,
            "toolchain-surface-stage1",
            "Trust release evidence resolves under stage1; stage1 aliases are not installed/default Trust sysroot evidence",
        ));
    }
    if !proof.same_sysroot {
        findings.push(finding_with_severity(
            severity,
            "toolchain-surface-sysroot-mismatch",
            "canonical Trust tools do not all resolve from one selected Trust sysroot",
        ));
    }
    if let Some(bin_dir) = proof.bin_dir.as_deref() {
        for path in forbidden_trust_surface_entries(Path::new(bin_dir)) {
            findings.push(finding_with_severity(
                severity,
                "toolchain-surface-forbidden-entrypoint",
                format!(
                    "selected Trust sysroot contains forbidden retired public entrypoint {}",
                    path.display()
                ),
            ));
        }
    }

    for tool in proof.required_tools.iter().chain(proof.optional_tools.iter()) {
        if tool.required && !tool.present {
            findings.push(finding_with_severity(
                severity,
                "toolchain-surface-tool-missing",
                format!("{} is missing from the selected Trust sysroot", tool.name),
            ));
        }
        if tool.present && !tool.canonical_name {
            findings.push(finding_with_severity(
                severity,
                "toolchain-surface-noncanonical-name",
                tool.detail.clone().unwrap_or_else(|| {
                    format!(
                        "{} resolved through non-canonical executable evidence; expected `{}`",
                        tool.name, tool.name
                    )
                }),
            ));
        }
        if tool.present && !tool.same_sysroot {
            findings.push(finding_with_severity(
                severity,
                "toolchain-surface-tool-sysroot-mismatch",
                format!("{} does not resolve from the selected Trust sysroot", tool.name),
            ));
        }
        for alias in &tool.compatibility_aliases {
            if tool.required && !alias.present {
                findings.push(finding_with_severity(
                    severity,
                    "toolchain-surface-alias-missing",
                    format!(
                        "{} is missing required Rust-compatible alias {} in the selected Trust sysroot",
                        tool.name, alias.name
                    ),
                ));
            }
            if alias.present && !alias.same_sysroot {
                findings.push(finding_with_severity(
                    severity,
                    "toolchain-surface-alias-sysroot-mismatch",
                    format!(
                        "{} alias {} does not resolve from the selected Trust sysroot",
                        tool.name, alias.name
                    ),
                ));
            }
        }
    }

    GateReport::new("toolchain-surface-sysroot", findings)
}

pub(super) fn build_toolchain_surface_proof(tools: &BoundTools) -> ToolchainSurfaceProof {
    let mut required_tools: Vec<_> = tools
        .required()
        .into_iter()
        .map(|tool| build_toolchain_surface_proof_tool(tool, true))
        .collect();
    let mut optional_tools: Vec<_> = tools
        .optional()
        .into_iter()
        .map(|tool| build_toolchain_surface_proof_tool(tool, false))
        .collect();

    let selected_sysroot =
        required_tools.iter().find_map(|tool| tool.sysroot.as_deref().map(str::to_string));
    let selected_bin_dir =
        required_tools.iter().find_map(|tool| tool.bin_dir.as_deref().map(str::to_string));

    for tool in required_tools.iter_mut().chain(optional_tools.iter_mut()) {
        tool.same_sysroot = tool.present
            && selected_sysroot
                .as_deref()
                .is_some_and(|sysroot| tool.sysroot.as_deref() == Some(sysroot));
    }

    let required_ready = required_tools.iter().all(|tool| {
        tool.present
            && tool.canonical_name
            && tool.same_sysroot
            && tool.compatibility_aliases.iter().all(|alias| alias.present && alias.same_sysroot)
    });
    let optional_ready = optional_tools.iter().filter(|tool| tool.present).all(|tool| {
        tool.canonical_name
            && tool.same_sysroot
            && tool.compatibility_aliases.iter().all(|alias| alias.present && alias.same_sysroot)
    });
    let stage1_alias_evidence = selected_sysroot.as_deref().is_some_and(path_is_stage1_sysroot);
    let has_forbidden_entrypoints = selected_bin_dir
        .as_deref()
        .is_some_and(|bin_dir| !forbidden_trust_surface_entries(Path::new(bin_dir)).is_empty());
    let same_sysroot = selected_sysroot.is_some()
        && required_ready
        && optional_ready
        && !has_forbidden_entrypoints;
    let status = if same_sysroot && !stage1_alias_evidence { "passed" } else { "failed" };

    ToolchainSurfaceProof {
        schema: "trust.targo.toolchain-surface-sysroot.v1",
        status,
        same_sysroot,
        sysroot: selected_sysroot,
        bin_dir: selected_bin_dir,
        stage1_alias_evidence,
        required_tools,
        optional_tools,
    }
}

fn build_toolchain_surface_proof_tool(
    tool: &BoundToolIdentity,
    required: bool,
) -> ToolchainSurfaceProofTool {
    let path = tool.path.as_deref().filter(|path| !path.trim().is_empty());
    let path_buf = path.map(PathBuf::from);
    let bound_bin_dir = path_buf.as_deref().and_then(Path::parent).map(canonicalize_or_display);
    let present = path_buf.as_deref().is_some_and(is_executable_file);
    let resolved_path =
        present.then(|| path_buf.as_deref().and_then(|path| fs::canonicalize(path).ok())).flatten();
    let resolved_bin_dir =
        resolved_path.as_deref().and_then(Path::parent).map(canonicalize_or_display);
    let resolves_within_bound_bin = present && resolved_bin_dir == bound_bin_dir;
    let bin_dir = bound_bin_dir.as_ref().map(|path| path.display().to_string());
    let sysroot = bound_bin_dir
        .as_deref()
        .and_then(Path::parent)
        .map(|path| canonicalize_or_display(path).display().to_string());
    let expected_name = host_executable_name(&tool.name);
    let canonical_leaf = path_buf
        .as_deref()
        .and_then(Path::file_name)
        .is_some_and(|file_name| file_name == expected_name.as_str());
    let canonical_name = canonical_leaf && resolves_within_bound_bin;
    let detail = if path.is_none() {
        Some(format!("canonical `{}` is not bound", tool.name))
    } else if !present {
        Some(format!("bound canonical `{}` is missing or not executable", tool.name))
    } else if resolved_path.is_none() {
        Some(format!("bound canonical `{}` could not be canonicalized", tool.name))
    } else if !canonical_leaf {
        Some(format!("bound path does not end with canonical `{}`", tool.name))
    } else if !resolves_within_bound_bin {
        Some(format!(
            "bound canonical `{}` resolves outside its selected Trust bin directory to {}",
            tool.name,
            resolved_path
                .as_deref()
                .map_or_else(|| "<unresolved>".to_string(), |path| path.display().to_string())
        ))
    } else {
        None
    };
    let compatibility_aliases =
        compatibility_aliases_for_tool(&tool.name, path_buf.as_deref(), required);

    ToolchainSurfaceProofTool {
        name: tool.name.clone(),
        required,
        canonical_name,
        present,
        same_sysroot: false,
        path: path.map(str::to_string),
        sysroot,
        bin_dir,
        resolution: tool.resolution.clone(),
        compatibility_aliases,
        detail,
    }
}

fn compatibility_aliases_for_tool(
    tool_name: &str,
    tool_path: Option<&Path>,
    required_tool: bool,
) -> Vec<ToolchainSurfaceProofAlias> {
    let aliases = match tool_name {
        "trustc" => &["rustc"][..],
        "targo" => &["cargo"][..],
        // The selected Trust sysroot deliberately exposes every secondary
        // tool only through its canonical Trust name. Bootstrap and stage0
        // reject the retired Rust/upstream spellings, so treating them as
        // required compatibility aliases makes a correct release sysroot
        // impossible to certify. Only rustc/cargo remain load-bearing
        // compatibility entrypoints for the Rust build ecosystem.
        _ => &[][..],
    };
    let Some(bin_dir) = tool_path.and_then(Path::parent) else {
        return aliases
            .iter()
            .map(|name| ToolchainSurfaceProofAlias {
                name: (*name).to_string(),
                present: false,
                same_sysroot: false,
                path: None,
                detail: required_tool
                    .then(|| format!("required Rust-compatible alias `{name}` is not bound")),
            })
            .collect();
    };
    let expected_bin_dir = Some(canonicalize_or_display(bin_dir));
    aliases
        .iter()
        .map(|name| {
            let alias_path = bin_dir.join(host_executable_name(name));
            let present = is_executable_target(&alias_path);
            let canonical_alias_path =
                present.then(|| fs::canonicalize(&alias_path).ok()).flatten();
            let same_bin =
                canonical_alias_path.as_deref().and_then(Path::parent).map(canonicalize_or_display)
                    == expected_bin_dir;
            let binds_canonical = tool_path
                .is_some_and(|canonical| same_file_or_exact_contents(&alias_path, canonical));
            let same_sysroot = same_bin && binds_canonical;
            ToolchainSurfaceProofAlias {
                name: (*name).to_string(),
                present,
                same_sysroot,
                path: canonical_alias_path.as_ref().map(|path| path.display().to_string()),
                detail: if present && canonical_alias_path.is_none() {
                    Some(format!(
                        "required Rust-compatible alias `{name}` could not be canonicalized"
                    ))
                } else if present && !same_bin {
                    Some(format!(
                        "Rust-compatible alias `{name}` is outside the selected Trust sysroot"
                    ))
                } else if present && !binds_canonical {
                    Some(format!(
                        "Rust-compatible alias `{name}` does not bind to canonical `{tool_name}`"
                    ))
                } else if present {
                    (!same_sysroot).then(|| {
                        format!(
                            "Rust-compatible alias `{name}` is not valid in the selected Trust sysroot"
                        )
                    })
                } else {
                    Some(format!(
                        "required Rust-compatible alias `{name}` is missing or not executable"
                    ))
                },
            }
        })
        .collect()
}

fn check_bound_tool_identity(
    findings: &mut Vec<GateFinding>,
    severity: FindingSeverity,
    tool: &BoundToolIdentity,
    required: bool,
    profile: ReleaseProfile,
) {
    if required || tool.has_bound_path() {
        if !tool.has_bound_path() {
            findings.push(finding_with_severity(
                severity,
                "tool-path-missing",
                format!("{} does not resolve to a bound executable path", tool.name),
            ));
        }
        if tool.sha256.as_deref().is_none_or(str::is_empty) {
            findings.push(finding_with_severity(
                severity,
                "tool-sha256-missing",
                format!("{} does not have a bound executable SHA-256", tool.name),
            ));
        }
        if tool.executable != Some(true) {
            findings.push(finding_with_severity(
                severity,
                "tool-not-executable",
                format!("{} is not bound to an executable file", tool.name),
            ));
        }
        if tool.resolution.as_deref() != Some("bound-executable") {
            findings.push(finding_with_severity(
                severity,
                "tool-resolution-unbound",
                format!(
                    "{} resolution is `{}` instead of `bound-executable`",
                    tool.name,
                    tool.resolution.as_deref().unwrap_or("missing")
                ),
            ));
        }
        if tool.version.as_deref().is_none_or(str::is_empty) {
            findings.push(finding_with_severity(
                severity,
                "tool-version-missing",
                format!("{} did not produce version output", tool.name),
            ));
        }
        if profile.requires_bound_tools()
            && matches!(tool.name.as_str(), "trustc" | "trustd")
            && tool.commit_hash.as_deref().is_none_or(str::is_empty)
        {
            findings.push(finding_with_severity(
                severity,
                "tool-commit-missing",
                format!("{} did not report a commit-hash", tool.name),
            ));
        }

        if let Some(path) = tool.path.as_deref().filter(|path| !path.trim().is_empty()) {
            let path = Path::new(path);
            if !is_executable_file(path) {
                findings.push(finding_with_severity(
                    severity,
                    "tool-live-file-invalid",
                    format!(
                        "{} bound path {} is no longer an exact regular executable",
                        tool.name,
                        path.display()
                    ),
                ));
            } else if let Some(expected) = tool.sha256.as_deref().filter(|hash| !hash.is_empty()) {
                match bound_file_sha256(path) {
                    Some(actual) if actual == expected => {}
                    Some(actual) => findings.push(finding_with_severity(
                        severity,
                        "tool-sha256-mismatch",
                        format!(
                            "{} changed after identity capture (expected SHA-256 {expected}, observed {actual})",
                            tool.name
                        ),
                    )),
                    None => findings.push(finding_with_severity(
                        severity,
                        "tool-live-file-unreadable",
                        format!(
                            "{} bound path {} could not be re-hashed as an exact regular file",
                            tool.name,
                            path.display()
                        ),
                    )),
                }
            }
        }
    }
}

pub(super) fn check_release_tool_names(root: &Path, visibility: ReleaseVisibility) -> GateReport {
    if visibility == ReleaseVisibility::Private {
        return GateReport::pass("tool-names");
    }

    match trust_release::check_tool_names_files(trust_release::default_tool_name_evidence_paths(
        root,
    )) {
        Ok(report) => report,
        Err(err) => GateReport::new(
            "tool-names",
            vec![GateFinding::error(
                "tool-names-read",
                format!("failed to read release evidence files: {err}"),
            )],
        ),
    }
}

fn check_owned_deps(
    root: &Path,
    profile: ReleaseProfile,
    visibility: ReleaseVisibility,
) -> GateReport {
    let path = root.join("release/internal-repo-versions.toml");
    match read_bounded_utf8_file(&path, MAX_RELEASE_METADATA_BYTES) {
        Ok(text) => {
            trust_release::check_owned_deps_toml(&text, profile.evidence_profile(visibility))
        }
        Err(err) if err.kind() == io::ErrorKind::NotFound => GateReport::new(
            "owned-deps",
            vec![GateFinding::error(
                "owned-deps-missing",
                "missing release/internal-repo-versions.toml",
            )],
        ),
        Err(err) => GateReport::new(
            "owned-deps",
            vec![GateFinding::error(
                "owned-deps-read",
                format!("failed to read {}: {err}", path.display()),
            )],
        ),
    }
}

pub(super) fn finding_with_severity(
    severity: FindingSeverity,
    code: impl Into<String>,
    message: impl Into<String>,
) -> GateFinding {
    match severity {
        FindingSeverity::Warning => GateFinding::warning(code, message),
        FindingSeverity::Blocker => GateFinding::blocker(code, message),
        FindingSeverity::Error => GateFinding::error(code, message),
    }
}
