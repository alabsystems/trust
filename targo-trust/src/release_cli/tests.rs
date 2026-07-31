use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{SystemTime, UNIX_EPOCH};

use trust_release::{GateReport, GateStatus};
use trust_version::{BoundToolIdentity, BoundTools, TrustVersionIdentity};

use super::gates::{
    build_release_reports, build_toolchain_surface_proof, check_bound_tool_files,
    check_release_tool_names, check_toolchain_surface_sysroot,
};
use super::identity::{bound_tools, file_sha256, host_executable_name};
use super::product_proof::{
    PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS, check_product_proof_coverage,
    product_proof_component_requirements, product_proof_components, product_proof_evidence_classes,
    product_proof_report_usage_text, product_proof_stub_usage_text,
    run_product_proof_report_subcommand, run_product_proof_stub_subcommand,
};
use super::publication::{
    channel_manifest_binds_artifact, check_publication_artifacts, check_publication_ledger,
    find_dist_artifact,
};
use super::types::{
    CANDIDATE_COMMAND_VERSION, PRODUCT_COMPONENT_TARGO, PRODUCT_COMPONENT_TARGO_TRUST,
    PRODUCT_COMPONENT_TRUSTC, ReleaseProfile, ReleaseVisibility,
};
use super::{release_usage_text, version_usage_text};
use crate::pipeline::probe::inspect_trustd_runtime_closure;
use crate::pipeline::surface::{
    FORBIDDEN_TRUST_PUBLIC_BIN_NAMES, FORBIDDEN_TRUST_PUBLIC_LIBEXEC_NAMES,
};

const COMPILE_BACK_DIGEST_REQUIREMENTS: &[&str] = &[
    "compile-back-artifact-digests-bound",
    "compile-back-lifted-binary-trust_ir-sha256",
    "compile-back-rust-source-sha256",
    "compile-back-reconstructed-trust_ir-sha256",
    "compile-back-refinement-artifact-sha256",
    "compile-back-root-artifact-sha256",
    "compile-back-selected-image-sha256",
    "compile-back-selected-image-range",
];

const PRODUCT_PROOF_TEST_SHA256: &str =
    "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

#[test]
fn successful_help_text_documents_release_surface() {
    let version_usage = version_usage_text();
    assert!(version_usage.contains("targo trust version"));
    assert!(version_usage.ends_with('\n'));

    let release_usage = release_usage_text();
    for expected in [
        "targo trust release check",
        "targo trust release product-proof-stub",
        "targo trust release product-proof-report",
        "--report-out <repo-relative-json>",
        "targo trust release validate <gate>",
    ] {
        assert!(release_usage.contains(expected), "missing `{expected}`");
    }
    assert!(release_usage.ends_with('\n'));

    let product_proof_stub_usage = product_proof_stub_usage_text();
    for expected in [
        "product-proof-stub",
        "--report-out",
        "--bundle-out",
        "--manifest-out",
        "--stage2-trustc",
        "--source-tarball",
        "--certificate-out",
    ] {
        assert!(product_proof_stub_usage.contains(expected), "missing `{expected}`");
    }
    assert!(product_proof_stub_usage.ends_with('\n'));

    let product_proof_report_usage = product_proof_report_usage_text();
    for expected in [
        "product-proof-report",
        "--evidence <repo-relative-json>",
        "trust.product-proof-release-artifact-report.v1",
        "checklist artifact",
        "kind-specific Rust collector",
        "strict validator",
    ] {
        assert!(product_proof_report_usage.contains(expected), "missing `{expected}`");
    }
    assert!(product_proof_report_usage.ends_with('\n'));
}

#[test]
fn product_proof_matrix_names_the_full_toolchain() {
    let components: Vec<_> = product_proof_component_requirements()
        .into_iter()
        .map(|component| component.component)
        .collect();

    for expected in [
        PRODUCT_COMPONENT_TRUSTC,
        PRODUCT_COMPONENT_TARGO,
        PRODUCT_COMPONENT_TARGO_TRUST,
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
        "std",
        "source/docs",
        "LLVM/trust-cg",
        "stage0",
        "verifier engines",
        "upstream tests",
        "binary/decomp gates",
    ] {
        assert!(components.contains(&expected), "missing {expected}");
    }
}

#[test]
fn product_proof_trustd_component_uses_identity_bound_protocol_collector() {
    let trustd = product_proof_component_requirements()
        .into_iter()
        .find(|component| component.component == "trustd")
        .expect("trustd component");

    assert_eq!(trustd.required_evidence, &["Trust daemon protocol smoke"]);
    assert!(
        !trustd.required_evidence.contains(&"Trust daemon binary identity"),
        "a separate self-declared binary-identity document must not block or weaken the production live collector"
    );
}

#[test]
fn product_proof_binary_decomp_component_requires_compile_back_digest_binding() {
    let binary_decomp = product_proof_component_requirements()
        .into_iter()
        .find(|component| component.component == "binary/decomp gates")
        .expect("binary/decomp gates component");

    for required in COMPILE_BACK_DIGEST_REQUIREMENTS {
        assert!(
            binary_decomp.required_evidence.contains(required),
            "missing compile-back digest evidence requirement `{required}`"
        );
    }
}

#[test]
fn toolchain_surface_records_only_load_bearing_compatibility_aliases() {
    let mut identity = test_identity_with_candidate("abcdef1234567890");
    bind_required_test_tools(&mut identity);

    let proof = build_toolchain_surface_proof(&identity.tools);
    for tool in &proof.required_tools {
        let aliases =
            tool.compatibility_aliases.iter().map(|alias| alias.name.as_str()).collect::<Vec<_>>();
        match tool.name.as_str() {
            "trustc" => assert_eq!(aliases, ["rustc"]),
            "targo" => assert_eq!(aliases, ["cargo"]),
            _ => assert!(
                aliases.is_empty(),
                "canonical Trust-only tool {} retained retired aliases {aliases:?}",
                tool.name
            ),
        }
    }
}

#[test]
fn toolchain_surface_accepts_canonical_tools_with_only_rustc_and_cargo_aliases() {
    let root = temp_root("canonical-toolchain-surface");
    let mut identity = test_identity_with_candidate("abcdef1234567890");
    let bin = materialize_bound_required_test_tools(&mut identity, &root);

    let proof = build_toolchain_surface_proof(&identity.tools);
    let report = check_toolchain_surface_sysroot(&identity, ReleaseProfile::Publication);

    assert_eq!(proof.status, "passed");
    assert!(proof.same_sysroot);
    assert_eq!(report.status, GateStatus::Pass);
    for retired in [
        "cargo-trust",
        "rustdoc",
        "rustfmt",
        "cargo-fmt",
        "cargo-clippy",
        "clippy-driver",
        "rust-analyzer",
    ] {
        assert!(!bin.join(retired).exists(), "test accidentally admitted retired alias {retired}");
    }

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn toolchain_surface_sysroot_gate_accepts_one_canonical_sysroot() {
    let root = temp_root("one-canonical-sysroot");
    let mut identity = test_identity_with_candidate("abcdef1234567890");
    materialize_bound_required_test_tools(&mut identity, &root);

    let proof = build_toolchain_surface_proof(&identity.tools);
    let report = check_toolchain_surface_sysroot(&identity, ReleaseProfile::Publication);

    assert_eq!(proof.schema, "trust.targo.toolchain-surface-sysroot.v1");
    assert_eq!(proof.status, "passed");
    assert!(proof.same_sysroot);
    let canonical_root = std::fs::canonicalize(&root).expect("canonical test sysroot");
    assert_eq!(proof.sysroot.as_deref(), Some(canonical_root.display().to_string().as_str()));
    assert!(proof.required_tools.iter().all(|tool| tool.canonical_name && tool.same_sysroot));
    assert_eq!(report.status, GateStatus::Pass);

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn toolchain_surface_sysroot_gate_rejects_split_sysroots() {
    let root = temp_root("split-canonical-sysroot");
    let mut identity = test_identity_with_candidate("abcdef1234567890");
    materialize_bound_required_test_tools(&mut identity, &root);
    let other = temp_root("other-canonical-sysroot");
    let other_bin = other.join("bin");
    std::fs::create_dir_all(&other_bin).expect("create split sysroot bin");
    let other_analyzer = other_bin.join("trust-analyzer");
    write_executable_test_file(&other_analyzer, b"split analyzer fixture\n");
    identity.tools.analyzer.path = Some(other_analyzer.display().to_string());

    let report = check_toolchain_surface_sysroot(&identity, ReleaseProfile::Publication);
    let codes: Vec<_> = report.findings.iter().map(|finding| finding.code.as_str()).collect();

    assert_eq!(report.status, GateStatus::Fail);
    assert!(codes.contains(&"toolchain-surface-sysroot-mismatch"), "{codes:?}");
    assert!(codes.contains(&"toolchain-surface-tool-sysroot-mismatch"), "{codes:?}");

    let _ = std::fs::remove_dir_all(root);
    let _ = std::fs::remove_dir_all(other);
}

#[test]
fn toolchain_surface_sysroot_gate_rejects_stage1_alias_evidence() {
    let root = temp_root("stage1-alias-evidence");
    let stage1 = root.join("build/host/stage1");
    let mut identity = test_identity_with_candidate("abcdef1234567890");
    materialize_bound_required_test_tools(&mut identity, &stage1);

    let proof = build_toolchain_surface_proof(&identity.tools);
    let report = check_toolchain_surface_sysroot(&identity, ReleaseProfile::Publication);
    let codes: Vec<_> = report.findings.iter().map(|finding| finding.code.as_str()).collect();

    let canonical_stage1 = std::fs::canonicalize(&stage1).expect("canonical stage1 test sysroot");
    assert_eq!(proof.sysroot.as_deref(), Some(canonical_stage1.display().to_string().as_str()));
    assert!(proof.same_sysroot);
    assert!(proof.stage1_alias_evidence);
    assert_eq!(report.status, GateStatus::Fail);
    assert!(codes.contains(&"toolchain-surface-stage1"), "{codes:?}");

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn toolchain_surface_rejects_non_executable_canonical_tool() {
    use std::os::unix::fs::PermissionsExt;

    let root = temp_root("non-executable-canonical-tool");
    let mut identity = test_identity_with_candidate("abcdef1234567890");
    let bin = materialize_bound_required_test_tools(&mut identity, &root);
    let formatter = bin.join("trustfmt");
    let mut permissions = std::fs::metadata(&formatter).expect("formatter metadata").permissions();
    permissions.set_mode(0o644);
    std::fs::set_permissions(&formatter, permissions).expect("make formatter non-executable");

    let proof = build_toolchain_surface_proof(&identity.tools);
    let report = check_toolchain_surface_sysroot(&identity, ReleaseProfile::Publication);

    assert_eq!(proof.status, "failed");
    let formatter = proof
        .required_tools
        .iter()
        .find(|tool| tool.name == "trustfmt")
        .expect("trustfmt proof row");
    assert!(!formatter.present);
    assert!(report.findings.iter().any(|finding| finding.code == "toolchain-surface-tool-missing"));

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn toolchain_surface_rejects_canonical_leaf_symlinked_outside_selected_bin() {
    use std::os::unix::fs::symlink;

    let root = temp_root("outward-canonical-tool-link");
    let other = temp_root("outward-canonical-tool-target");
    let mut identity = test_identity_with_candidate("abcdef1234567890");
    let bin = materialize_bound_required_test_tools(&mut identity, &root);
    let other_bin = other.join("bin");
    std::fs::create_dir_all(&other_bin).expect("create external bin");
    let external = other_bin.join("trust-analyzer");
    write_executable_test_file(&external, b"external analyzer fixture\n");
    let linked = bin.join("trust-analyzer");
    std::fs::remove_file(&linked).expect("remove local analyzer");
    symlink(&external, &linked).expect("link analyzer outside selected bin");

    let proof = build_toolchain_surface_proof(&identity.tools);
    let report = check_toolchain_surface_sysroot(&identity, ReleaseProfile::Publication);

    assert_eq!(proof.status, "failed");
    let analyzer = proof
        .required_tools
        .iter()
        .find(|tool| tool.name == "trust-analyzer")
        .expect("trust-analyzer proof row");
    assert!(!analyzer.present);
    assert!(!analyzer.canonical_name);
    assert!(
        analyzer
            .detail
            .as_deref()
            .is_some_and(|detail| detail.contains("missing or not executable"))
    );
    assert!(report.findings.iter().any(|finding| finding.code == "toolchain-surface-tool-missing"));

    let _ = std::fs::remove_dir_all(root);
    let _ = std::fs::remove_dir_all(other);
}

#[cfg(unix)]
#[test]
fn version_identity_rejects_symlinked_canonical_bound_tool() {
    use std::os::unix::fs::symlink;

    let root = temp_root("symlinked-bound-tool");
    let bin = root.join("bin");
    std::fs::create_dir_all(&bin).expect("create bound tool bin");
    let current = bin.join("targo-trust");
    write_executable_test_file(&current, b"#!/bin/sh\necho 'targo-trust test'\n");
    let external = root.join("external-targo");
    write_executable_test_file(&external, b"#!/bin/sh\necho 'targo test'\n");
    symlink(&external, bin.join("targo")).expect("link canonical frontend");

    let tools = bound_tools(Some(&current), "1.96.0-dev");
    assert_eq!(tools.frontend.resolution.as_deref(), Some("rejected-symlink"));
    assert_eq!(tools.frontend.executable, Some(false));
    assert!(tools.frontend.sha256.is_none());
    assert!(tools.frontend.version.is_none());

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn version_identity_binds_sibling_trustd_via_version_flag() {
    let root = temp_root("bound-sibling-trustd");
    let bin = root.join("bin");
    std::fs::create_dir_all(&bin).expect("create bound tool bin");
    let current = bin.join("targo-trust");
    write_executable_test_file(&current, b"#!/bin/sh\necho 'targo-trust test'\n");
    let trustd = bin.join("trustd");
    write_executable_test_file(
        &trustd,
        b"#!/bin/sh\n[ \"$1\" = \"--version\" ] || exit 9\nprintf '%s\\n' 'trustd 1.96.0-dev' 'trust.identity=trustd' 'trust.protocol=trustd.status.v1' 'commit-hash: 0123456789abcdef0123456789abcdef01234567'\n",
    );

    let tools = bound_tools(Some(&current), "1.96.0-dev");

    assert_eq!(tools.daemon.name, "trustd");
    assert_eq!(tools.daemon.path.as_deref(), Some(trustd.display().to_string().as_str()));
    assert_eq!(tools.daemon.version.as_deref(), Some("trustd 1.96.0-dev"));
    assert_eq!(
        tools.daemon.commit_hash.as_deref(),
        Some("0123456789abcdef0123456789abcdef01234567")
    );
    assert_eq!(tools.daemon.resolution.as_deref(), Some("bound-executable"));

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn version_identity_rejects_unbranded_or_wrong_protocol_trustd() {
    let root = temp_root("reject-wrong-trustd-protocol");
    let bin = root.join("bin");
    std::fs::create_dir_all(&bin).expect("create bound tool bin");
    let current = bin.join("targo-trust");
    write_executable_test_file(&current, b"#!/bin/sh\necho 'targo-trust test'\n");
    write_executable_test_file(
        &bin.join("trustd"),
        b"#!/bin/sh\nprintf '%s\\n' 'trustd 1.96.0-dev' 'trust.identity=trustd' 'trust.protocol=wrong.v1' 'commit-hash: 0123456789abcdef0123456789abcdef01234567'\n",
    );

    let tools = bound_tools(Some(&current), "1.96.0-dev");
    assert_eq!(tools.daemon.resolution.as_deref(), Some("invalid-trustd-identity"));
    assert_eq!(tools.daemon.executable, Some(false));
    assert!(tools.daemon.sha256.is_none());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn release_identity_gates_require_bound_same_sysroot_trustd() {
    let root = temp_root("required-bound-trustd");
    let mut identity = test_identity_with_candidate("abcdef1234567890");
    let bin = materialize_bound_required_test_tools(&mut identity, &root);
    std::fs::remove_file(bin.join("trustd")).expect("remove required trustd fixture");

    let bound = check_bound_tool_files(&identity, ReleaseProfile::Publication);
    let surface = check_toolchain_surface_sysroot(&identity, ReleaseProfile::Publication);

    assert_eq!(bound.status, GateStatus::Fail);
    assert!(bound.findings.iter().any(|finding| {
        finding.code == "tool-live-file-invalid" && finding.message.contains("trustd")
    }));
    assert_eq!(surface.status, GateStatus::Fail);
    assert!(surface.findings.iter().any(|finding| {
        finding.code == "toolchain-surface-tool-missing" && finding.message.contains("trustd")
    }));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn release_identity_gate_rejects_wrong_commit_trustd() {
    let root = temp_root("wrong-commit-trustd");
    let mut identity = test_identity_with_candidate("abcdef1234567890");
    materialize_bound_required_test_tools(&mut identity, &root);
    identity.tools.daemon.commit_hash = Some("0123456789abcdef".to_string());

    let report = check_bound_tool_files(&identity, ReleaseProfile::Publication);
    assert_eq!(report.status, GateStatus::Fail);
    assert!(report.findings.iter().any(|finding| {
        finding.code == "tool-commit-mismatch" && finding.message.contains("trustd")
    }));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn bound_tool_gate_rehashes_live_executables() {
    let root = temp_root("live-bound-tool-rehash");
    let mut identity = test_identity_with_candidate("abcdef1234567890");
    let bin = materialize_bound_required_test_tools(&mut identity, &root);

    let initial = check_bound_tool_files(&identity, ReleaseProfile::Publication);
    assert_eq!(initial.status, GateStatus::Pass, "{:?}", initial.findings);

    std::fs::write(bin.join("trustfmt"), b"replaced Trust formatter fixture\n")
        .expect("replace bound formatter");
    let changed = check_bound_tool_files(&identity, ReleaseProfile::Publication);
    assert_eq!(changed.status, GateStatus::Fail);
    assert!(changed.findings.iter().any(|finding| {
        finding.code == "tool-sha256-mismatch" && finding.message.contains("trustfmt")
    }));

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn toolchain_surface_rejects_alias_outside_selected_bin_even_within_sysroot() {
    use std::os::unix::fs::symlink;

    let root = temp_root("outward-compatibility-alias");
    let mut identity = test_identity_with_candidate("abcdef1234567890");
    let bin = materialize_bound_required_test_tools(&mut identity, &root);
    let other_dir = root.join("libexec");
    std::fs::create_dir_all(&other_dir).expect("create other sysroot directory");
    let external = other_dir.join("rustc");
    write_executable_test_file(&external, b"misbound rustc fixture\n");
    let alias = bin.join("rustc");
    std::fs::remove_file(&alias).expect("remove local alias");
    symlink(&external, &alias).expect("link alias outside selected bin");

    let proof = build_toolchain_surface_proof(&identity.tools);
    let report = check_toolchain_surface_sysroot(&identity, ReleaseProfile::Publication);

    assert_eq!(proof.status, "failed");
    let compiler =
        proof.required_tools.iter().find(|tool| tool.name == "trustc").expect("trustc proof row");
    assert!(!compiler.compatibility_aliases[0].same_sysroot);
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.code == "toolchain-surface-alias-sysroot-mismatch")
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn toolchain_surface_rejects_same_bin_alias_with_different_identity() {
    let root = temp_root("misbound-same-bin-compatibility-alias");
    let mut identity = test_identity_with_candidate("abcdef1234567890");
    let bin = materialize_bound_required_test_tools(&mut identity, &root);
    write_executable_test_file(&bin.join("cargo"), b"unrelated same-bin executable\n");

    let proof = build_toolchain_surface_proof(&identity.tools);
    let report = check_toolchain_surface_sysroot(&identity, ReleaseProfile::Publication);

    assert_eq!(proof.status, "failed");
    let frontend =
        proof.required_tools.iter().find(|tool| tool.name == "targo").expect("targo proof row");
    assert!(!frontend.compatibility_aliases[0].same_sysroot);
    assert!(
        frontend.compatibility_aliases[0]
            .detail
            .as_deref()
            .is_some_and(|detail| detail.contains("does not bind to canonical `targo`"))
    );
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.code == "toolchain-surface-alias-sysroot-mismatch")
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn toolchain_surface_rejects_all_forbidden_public_entries() {
    for expected in ["rust-gdb", "rust-gdbgui", "rust-lldb", "rust-windbg.cmd"] {
        assert!(
            FORBIDDEN_TRUST_PUBLIC_BIN_NAMES.contains(&expected),
            "debugger compatibility spelling `{expected}` escaped the Trust-only contract"
        );
    }
    assert_eq!(FORBIDDEN_TRUST_PUBLIC_LIBEXEC_NAMES, ["rust-analyzer-proc-macro-srv"]);

    let root = temp_root("forbidden-public-entrypoints");
    let mut identity = test_identity_with_candidate("abcdef1234567890");
    let bin = materialize_bound_required_test_tools(&mut identity, &root);
    let mut paths = FORBIDDEN_TRUST_PUBLIC_BIN_NAMES
        .iter()
        .map(|name| {
            if name.ends_with(".cmd") {
                bin.join(name)
            } else {
                bin.join(host_executable_name(name))
            }
        })
        .collect::<Vec<_>>();
    paths.extend(
        FORBIDDEN_TRUST_PUBLIC_LIBEXEC_NAMES
            .iter()
            .map(|name| root.join("libexec").join(host_executable_name(name))),
    );

    for path in paths {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).expect("create forbidden entrypoint parent");
        }
        std::fs::write(&path, b"forbidden public entrypoint fixture\n")
            .expect("write forbidden entrypoint");

        let proof = build_toolchain_surface_proof(&identity.tools);
        let report = check_toolchain_surface_sysroot(&identity, ReleaseProfile::Publication);
        assert_eq!(proof.status, "failed", "{} escaped proof", path.display());
        assert!(
            report
                .findings
                .iter()
                .any(|finding| finding.code == "toolchain-surface-forbidden-entrypoint"),
            "{} escaped release gate: {:?}",
            path.display(),
            report.findings
        );

        std::fs::remove_file(&path).expect("remove forbidden entrypoint fixture");
    }

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn release_profile_parses_single_public_cli_shape() {
    assert_eq!(ReleaseProfile::parse("metadata"), Some(ReleaseProfile::Metadata));
    assert_eq!(ReleaseProfile::parse("publication"), Some(ReleaseProfile::Publication));
    assert_eq!(ReleaseProfile::parse("product-proof"), Some(ReleaseProfile::ProductProof));
    assert_eq!(ReleaseProfile::parse("public"), None);
    assert_eq!(ReleaseVisibility::parse("private"), Some(ReleaseVisibility::Private));
    assert_eq!(ReleaseVisibility::parse("public"), Some(ReleaseVisibility::Public));
    assert_eq!(ReleaseVisibility::parse("local"), None);
    assert_eq!(ReleaseVisibility::parse("internal"), None);
    assert_eq!(ReleaseVisibility::parse("metadata"), None);
}

#[test]
fn private_visibility_skips_public_wording_scan() {
    let root = temp_root("private-tool-names");
    std::fs::create_dir_all(root.join("scripts")).expect("create scripts dir");
    std::fs::write(root.join("scripts/stage2_noverify_self_build.sh"), "cargo test\n")
        .expect("write private script");

    let report = check_release_tool_names(&root, ReleaseVisibility::Private);

    assert_eq!(report.status, GateStatus::Pass);
    assert!(report.findings.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn public_visibility_keeps_public_wording_scan() {
    let root = temp_root("public-tool-names");
    std::fs::create_dir_all(root.join("scripts")).expect("create scripts dir");
    std::fs::write(root.join("scripts/stage2_noverify_self_build.sh"), "cargo test\n")
        .expect("write public script");

    let report = check_release_tool_names(&root, ReleaseVisibility::Public);

    assert_eq!(report.status, GateStatus::Fail);
    assert!(report.findings.iter().any(|finding| finding.code == "bare-cargo-command"));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn private_product_proof_does_not_run_publication_gates() {
    let root = temp_root("private-product-proof");
    std::fs::create_dir_all(root.join("release")).expect("create release dir");

    let reports = build_release_reports(
        &root,
        ReleaseProfile::ProductProof,
        ReleaseVisibility::Private,
        &test_identity_with_candidate("0123456789abcdef0123456789abcdef01234567"),
    );

    let gates: Vec<_> = reports.iter().map(|report| report.gate.as_str()).collect();
    assert!(!gates.contains(&"publication-inputs"), "{gates:?}");
    assert!(!gates.contains(&"publication-artifacts"), "{gates:?}");
    assert!(!gates.contains(&"publication-ledger"), "{gates:?}");
    assert!(gates.contains(&"trust-extra"), "{gates:?}");
    assert!(gates.contains(&"product-proof-coverage"), "{gates:?}");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn publication_ledger_requires_structured_release_evidence() {
    let root = temp_root("publication-ledger");
    let candidate_commit = "0123456789abcdef0123456789abcdef01234567";
    std::fs::create_dir_all(root.join("bootstrap/trust-stage0")).expect("create seed-ledger dir");
    std::fs::write(root.join("bootstrap/trust-stage0/seed-ledger.toml"), "")
        .expect("write empty ledger");

    let report = check_publication_ledger(&root, Some(candidate_commit));
    assert_eq!(report.status, GateStatus::Fail);
    assert!(report.findings.iter().any(|finding| {
        finding.code == "publication-ledger-tags"
            || finding.code == "publication-ledger-checksums"
            || finding.code == "publication-ledger-signatures"
            || finding.code == "publication-ledger-promotion"
    }));

    std::fs::write(
        root.join("bootstrap/trust-stage0/seed-ledger.toml"),
        r#"
tags = true
checksums = true
signatures = true
promotion = true
candidate_commit = "0123456789abcdef0123456789abcdef01234567"
"#,
    )
    .expect("write placeholder ledger");
    assert_eq!(check_publication_ledger(&root, Some(candidate_commit)).status, GateStatus::Fail);

    std::fs::write(
        root.join("bootstrap/trust-stage0/seed-ledger.toml"),
        r#"
tags = "x"
checksums = "x"
signatures = "x"
promotion = "x"
candidate_commit = "0123456789abcdef0123456789abcdef01234567"
"#,
    )
    .expect("write string placeholder ledger");
    assert_eq!(check_publication_ledger(&root, Some(candidate_commit)).status, GateStatus::Fail);

    std::fs::write(
        root.join("bootstrap/trust-stage0/seed-ledger.toml"),
        r#"
tags = ["trust-v0.1.0"]
checksums = ["sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"]
signatures = ["minisig:trusted"]
promotion_decision = "promote"
candidate_commit = "0123456789abcdef0123456789abcdef01234567"
"#,
    )
    .expect("write structured ledger");
    assert_eq!(check_publication_ledger(&root, Some(candidate_commit)).status, GateStatus::Pass);

    std::fs::write(
        root.join("bootstrap/trust-stage0/seed-ledger.toml"),
        r#"
tags = ["trust-v0.1.0"]
checksums = ["sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"]
signatures = ["minisig:trusted"]
promotion_decision = "promote"
candidate_commit = "0123456789abcdef0123456789abcdef01234567"
promotion = "promote"
"#,
    )
    .expect("write ledger with an authority alias");
    let report = check_publication_ledger(&root, Some(candidate_commit));
    assert_eq!(report.status, GateStatus::Fail);
    assert!(report.findings.iter().any(|finding| finding.code == "publication-ledger-schema"));

    for invalid_field in [
        "tags = [\"trust-v0.1.0\", \"\"]",
        "checksums = [\"sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef\", \"sha256:xyz\"]",
        "signatures = [\"minisig:trusted\", \"minisig:\"]",
        "tags = [\"trust-v0.1.0\", \"trust-v0.1.0\"]",
    ] {
        let tags = if invalid_field.starts_with("tags =") {
            invalid_field
        } else {
            "tags = [\"trust-v0.1.0\"]"
        };
        let checksums = if invalid_field.starts_with("checksums =") {
            invalid_field
        } else {
            "checksums = [\"sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef\"]"
        };
        let signatures = if invalid_field.starts_with("signatures =") {
            invalid_field
        } else {
            "signatures = [\"minisig:trusted\"]"
        };
        std::fs::write(
            root.join("bootstrap/trust-stage0/seed-ledger.toml"),
            format!(
                "{tags}\n{checksums}\n{signatures}\npromotion_decision = \"promote\"\n\
                 candidate_commit = \"{candidate_commit}\"\n"
            ),
        )
        .expect("write ledger with one invalid array member");
        assert_eq!(
            check_publication_ledger(&root, Some(candidate_commit)).status,
            GateStatus::Fail,
            "every ledger array member must be valid and unique: {invalid_field}"
        );
    }

    std::fs::write(
        root.join("bootstrap/trust-stage0/seed-ledger.toml"),
        r#"
tags = ["trust-v0.1.0"]
checksums = ["sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"]
signatures = ["minisig:trusted"]
promotion_decision = "promote"
candidate_commit = "fedcba9876543210fedcba9876543210fedcba98"
"#,
    )
    .expect("write mismatched candidate ledger");
    let report = check_publication_ledger(&root, Some(candidate_commit));
    assert_eq!(report.status, GateStatus::Fail);
    assert!(
        report.findings.iter().any(|finding| finding.code == "publication-ledger-candidate-commit")
    );

    std::fs::write(
        root.join("bootstrap/trust-stage0/seed-ledger.toml"),
        r#"
candidate_commit = "0123456789abcdef0123456789abcdef01234567"

[notes.unrelated]
tags = ["trust-v0.1.0"]
checksums = ["sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"]
signatures = ["minisig:trusted"]
promotion_decision = "promote"
"#,
    )
    .expect("write nested unrelated ledger");
    let report = check_publication_ledger(&root, Some(candidate_commit));
    assert_eq!(report.status, GateStatus::Fail);
    assert!(report.findings.iter().any(|finding| {
        finding.code == "publication-ledger-tags"
            || finding.code == "publication-ledger-checksums"
            || finding.code == "publication-ledger-signatures"
            || finding.code == "publication-ledger-promotion"
    }));

    for decision in ["blocked", "deferred"] {
        std::fs::write(
            root.join("bootstrap/trust-stage0/seed-ledger.toml"),
            format!(
                r#"
tags = ["trust-v0.1.0"]
checksums = ["sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"]
signatures = ["minisig:trusted"]
promotion_decision = "{decision}"
candidate_commit = "0123456789abcdef0123456789abcdef01234567"
"#
            ),
        )
        .expect("write blocked/deferred ledger");
        let report = check_publication_ledger(&root, Some(candidate_commit));
        assert_eq!(report.status, GateStatus::Fail, "{decision}");
        assert!(
            report.findings.iter().any(|finding| finding.code == "publication-ledger-promotion")
        );
    }

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn channel_manifest_binds_artifact_filename_and_hash_in_one_entry() {
    let manifest: toml::Value = toml::from_str(
        r#"
[pkg.trustc.target.host]
xz_url = "file://{trust-root}/dist/trustc-1.96.0-trust-host.tar.xz"
xz_hash = "sha-for-rustc"

[pkg.targo.target.host]
xz_url = "file://{trust-root}/dist/targo-1.96.0-trust-host.tar.xz"
xz_hash = "sha-for-cargo"
"#,
    )
    .expect("parse manifest");

    assert!(channel_manifest_binds_artifact(
        &manifest,
        "trustc-1.96.0-trust-host.tar.xz",
        "sha-for-rustc"
    ));
    assert!(!channel_manifest_binds_artifact(
        &manifest,
        "trustc-1.96.0-trust-host.tar.xz",
        "sha-for-cargo"
    ));
}

#[test]
fn publication_artifact_search_skips_stale_unbound_archives() {
    let root = temp_root("publication-artifact-search");
    std::fs::create_dir_all(&root).expect("create artifact root");
    let stale = root.join("trustc-1.96.0-trust-stale.tar.xz");
    let valid = root.join("trustc-1.96.0-trust-valid.tar.xz");
    std::fs::write(&stale, [0xfd, b'7', b'z', b'X', b'Z', 0x00, 1, 2, 3])
        .expect("write stale artifact");
    std::fs::write(&valid, [0xfd, b'7', b'z', b'X', b'Z', 0x00, 4, 5, 6])
        .expect("write valid artifact");
    let valid_sha = file_sha256(&valid).expect("hash valid artifact");
    let manifest: toml::Value = toml::from_str(&format!(
        r#"
[pkg.trustc.target.host]
xz_url = "file://{{trust-root}}/dist/trustc-1.96.0-trust-valid.tar.xz"
xz_hash = "{valid_sha}"
"#
    ))
    .expect("parse manifest");

    assert_eq!(
        find_dist_artifact(&root, "trustc-", &[], Some(&manifest)).as_deref(),
        Some(valid.as_path())
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn publication_artifact_search_does_not_cross_satisfy_overlapping_package_prefixes() {
    let root = temp_root("publication-artifact-prefix");
    std::fs::create_dir_all(&root).expect("create artifact root");
    let extension = root.join("targo-trust-1.96.0-trust-host.tar.xz");
    std::fs::write(&extension, [0xfd, b'7', b'z', b'X', b'Z', 0x00, 1, 2, 3])
        .expect("write extension artifact");
    let extension_sha = file_sha256(&extension).expect("hash extension artifact");
    let manifest: toml::Value = toml::from_str(&format!(
        r#"
[pkg.targo-trust.target.host]
xz_url = "file://{{trust-root}}/dist/targo-trust-1.96.0-trust-host.tar.xz"
xz_hash = "{extension_sha}"
"#
    ))
    .expect("parse manifest");

    assert!(find_dist_artifact(&root, "targo-", &[], Some(&manifest)).is_none());
    assert_eq!(
        find_dist_artifact(&root, "targo-trust-", &[], Some(&manifest)).as_deref(),
        Some(extension.as_path())
    );

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn publication_artifact_search_rejects_symlinked_archives() {
    use std::os::unix::fs::symlink;

    let root = temp_root("publication-artifact-symlink");
    let outside = temp_root("publication-artifact-symlink-target");
    std::fs::create_dir_all(&root).expect("create artifact root");
    std::fs::create_dir_all(&outside).expect("create target root");
    let target = outside.join("trustc-1.96.0-trust-host.tar.xz");
    let linked = root.join("trustc-1.96.0-trust-host.tar.xz");
    std::fs::write(&target, [0xfd, b'7', b'z', b'X', b'Z', 0x00, 1, 2, 3])
        .expect("write target artifact");
    let target_sha = file_sha256(&target).expect("hash target artifact");
    symlink(&target, &linked).expect("link archive into dist");
    let manifest: toml::Value = toml::from_str(&format!(
        r#"
[pkg.trustc.target.host]
xz_url = "file://{{trust-root}}/dist/trustc-1.96.0-trust-host.tar.xz"
xz_hash = "{target_sha}"
"#
    ))
    .expect("parse manifest");

    assert!(find_dist_artifact(&root, "trustc-", &[], Some(&manifest)).is_none());

    let _ = std::fs::remove_dir_all(root);
    let _ = std::fs::remove_dir_all(outside);
}

#[test]
fn publication_artifacts_ignore_sidecars_and_require_manifest_checksum() {
    let root = temp_root("publication-artifacts");
    let dist = root.join("bootstrap/trust-stage0/dist/2026-04-30");
    std::fs::create_dir_all(&dist).expect("create dist dir");
    std::fs::create_dir_all(root.join("bootstrap/trust-stage0/dist")).expect("create manifest dir");
    std::fs::write(root.join("bootstrap/trust-stage0/dist/channel-rust-trust.toml"), "")
        .expect("write empty channel manifest");

    for prefix in [
        "trustc-",
        "targo-",
        "targo-trust-",
        "trust-std-",
        "trust-src-",
        "trust-docs-",
        "trustfmt-",
        "tippy-",
        "trust-analyzer-",
        "llvm-tools-",
    ] {
        std::fs::write(
            dist.join(format!("{prefix}1.96.0-trust-aarch64-apple-darwin.tar.xz.sha256")),
            "not an artifact",
        )
        .expect("write sidecar");
    }

    let report = check_publication_artifacts(&root);
    assert_eq!(report.status, GateStatus::Fail);
    assert!(report.evidence_refs.is_empty());
    assert!(report.findings.iter().any(|finding| finding.code == "publication-artifact-missing"));
    assert!(
        report
            .findings
            .iter()
            .any(|finding| { finding.message.contains("trustc compiler package") })
    );
    assert!(
        report
            .findings
            .iter()
            .any(|finding| { finding.message.contains("targo frontend package") })
    );
    assert!(
        report
            .findings
            .iter()
            .any(|finding| { finding.message.contains("targo-trust subcommand package") })
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_rejects_generic_json_for_typed_evidence() {
    let root = temp_root("product-proof-generic-json");
    std::fs::create_dir_all(root.join("release/evidence")).expect("create evidence dir");
    std::fs::write(
        root.join("release/evidence/generic.json"),
        r#"{
  "schema_version": "trust.generic-evidence.v1",
  "candidate_commit": "0123456789abcdef0123456789abcdef01234567"
}"#,
    )
    .expect("write generic evidence");

    let mut manifest = String::new();
    for component in product_proof_component_requirements() {
        manifest.push_str("[[components]]\n");
        manifest.push_str(&format!("component = {:?}\n", component.component));
        manifest.push_str("status = \"accepted\"\n");
        manifest.push_str(&format!(
            "evidence = [{:?}]\n\n",
            format!("{}:release/evidence/generic.json", component.required_evidence[0])
        ));
    }
    std::fs::write(root.join("release/product-proof.toml"), manifest)
        .expect("write product proof manifest");

    let report =
        check_product_proof_coverage(&root, Some("0123456789abcdef0123456789abcdef01234567"), None);
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(report.findings.iter().any(|finding| finding.code == "product-proof-evidence-schema"));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_rejects_duplicate_json_keys_before_evidence_validation() {
    let root = temp_root("product-proof-duplicate-json-key");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    std::fs::create_dir_all(root.join("release/evidence")).expect("create evidence dir");
    std::fs::write(
        root.join("release/evidence/duplicate.json"),
        format!(
            r#"{{
  "schema_version": "trust.product-proof.v1",
  "evidence_kind": "release check transcript",
  "candidate_commit": "{candidate}",
  "proof_results": {{"proved": 0, "\u0070roved": 1, "total": 1}}
}}"#
        ),
    )
    .expect("write duplicate-key evidence");
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO_TRUST,
        "release check transcript",
        "release/evidence/duplicate.json",
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-evidence-json"
                && finding.message.contains("duplicate object key `proved`")
        }),
        "decoded duplicate keys must fail before last-key-wins validation: {:?}",
        report.findings
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_trustc_identity_rejects_label_only_proof_counts() {
    let root = temp_root("product-proof-trustc-identity-label-only");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    std::fs::create_dir_all(root.join("release/evidence")).expect("create evidence dir");
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "trustc -Vv identity",
        "candidate_commit": candidate,
        "proof_results": {
            "proved": 1,
            "total": 1,
            "failed": 0,
            "unknown": 0,
            "by_solver": ["focused-product-proof-test"]
        },
        "diagnostics": [
            "trustc -Vv identity accepted by label only",
            "sha256=0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
        ]
    });
    std::fs::write(
        root.join("release/evidence/trustc-identity.json"),
        serde_json::to_string_pretty(&trusted_product_proof_evidence(&root, &evidence))
            .expect("render evidence"),
    )
    .expect("write trustc identity evidence");
    write_trustc_identity_product_proof_manifest(&root, "release/evidence/trustc-identity.json");

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-tool-identity-materialization-missing")
        .expect("missing trustc identity materialization blocker");
    for expected in ["trustc -Vv identity", "tool_identity", "version_identity.tools.compiler"] {
        assert!(finding.message.contains(expected), "missing `{expected}` in {}", finding.message);
    }
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_trustc_identity_materializes_but_requires_registered_collector() {
    let root = temp_root("product-proof-trustc-identity-structured");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let tool_identity = materialized_trust_tool_identity_json(&root, "trustc", Some(candidate));
    std::fs::create_dir_all(root.join("release/evidence")).expect("create evidence dir");
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "trustc -Vv identity",
        "candidate_commit": candidate,
        "proof_results": {
            "proved": 1,
            "total": 1,
            "failed": 0,
            "unknown": 0,
            "by_solver": ["focused-product-proof-test"]
        },
        "tool_identity": tool_identity
    });
    std::fs::write(
        root.join("release/evidence/trustc-identity.json"),
        serde_json::to_string_pretty(&trusted_product_proof_evidence(&root, &evidence))
            .expect("render evidence"),
    )
    .expect("write trustc identity evidence");
    write_trustc_identity_product_proof_manifest(&root, "release/evidence/trustc-identity.json");

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert!(
        !report
            .findings
            .iter()
            .any(|finding| finding.code == "product-proof-tool-identity-materialization-missing")
    );
    assert_solver_checklist_only(&report, "trustc -Vv identity");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_targo_identity_rejects_label_only_proof_counts() {
    let root = temp_root("product-proof-targo-identity-label-only");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "targo identity",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "diagnostics": [
            "targo identity accepted by label only",
            format!("sha256={digest}")
        ]
    });
    let evidence_path = write_product_proof_evidence(&root, "targo-identity.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO,
        "targo identity",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-tool-identity-materialization-missing")
        .expect("missing targo identity materialization blocker");
    for expected in ["targo identity", "tool_identity", "version_identity.tools.frontend"] {
        assert!(finding.message.contains(expected), "missing `{expected}` in {}", finding.message);
    }
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_targo_identity_materializes_but_requires_registered_collector() {
    let root = temp_root("product-proof-targo-identity-structured");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let tool_identity = materialized_trust_tool_identity_json(&root, "targo", None);
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "targo identity",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "tool_identity": tool_identity,
    });
    let evidence_path = write_product_proof_evidence(&root, "targo-identity.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO,
        "targo identity",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert!(
        !report
            .findings
            .iter()
            .any(|finding| finding.code == "product-proof-tool-identity-materialization-missing")
    );
    assert_solver_checklist_only(&report, "targo identity");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_targo_identity_rejects_absolute_tool_path() {
    let root = temp_root("product-proof-targo-identity-absolute-path");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "targo identity",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "tool_identity": unmaterialized_trust_tool_identity_json(
            "targo",
            PRODUCT_PROOF_TEST_SHA256,
            None
        ),
    });
    let evidence_path = write_product_proof_evidence(&root, "targo-identity.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO,
        "targo identity",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-tool-identity-materialization-missing")
        .expect("missing absolute tool path materialization blocker");
    assert!(
        finding.message.contains("must be repo-relative"),
        "absolute tool path should require repo-local readback: {}",
        finding.message
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_version_identity_label_only_cannot_satisfy_daemon_binding() {
    let root = temp_root("product-proof-version-identity-label-only");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let daemon_identity = materialized_trust_tool_identity_json(&root, "trustd", Some(candidate));
    let candidate_daemon = candidate_daemon_from_json(&root, &daemon_identity);
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "version identity",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "diagnostics": [
            "version identity accepted by label only",
            "candidate_command_version=1",
            "tools.frontend=targo",
            "tools.extension=targo-trust",
            "tools.compiler=trustc"
        ]
    });
    let evidence_path = write_product_proof_evidence(&root, "version-identity.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO_TRUST,
        "version identity",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), Some(&candidate_daemon));
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-daemon-candidate-binding-missing")
        .expect("missing canonical daemon-binding blocker");
    assert!(
        finding.message.contains("lacks daemon tool identity"),
        "{}",
        finding.message
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn product_proof_version_identity_materializes_but_requires_registered_collector() {
    let root = temp_root("product-proof-version-identity-structured");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let frontend_identity = materialized_trust_tool_identity_json(&root, "targo", None);
    let extension_identity = materialized_trust_tool_identity_json(&root, "targo-trust", None);
    let compiler_identity = materialized_trust_tool_identity_json(&root, "trustc", Some(candidate));
    let daemon_identity = materialized_trust_tool_identity_json(&root, "trustd", Some(candidate));
    let candidate_daemon = candidate_daemon_from_json(&root, &daemon_identity);
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "version identity",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "version_identity": {
            "product": "Trust",
            "toolchain_alias": "trust",
            "trust_product_version": "0.1.0",
            "candidate_commit": candidate,
            "candidate_command_version": 1,
            "tools": {
                "frontend": frontend_identity,
                "extension": extension_identity,
                "compiler": compiler_identity,
                "daemon": daemon_identity
            }
        }
    });
    let evidence_path = write_product_proof_evidence(&root, "version-identity.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO_TRUST,
        "version identity",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), Some(&candidate_daemon));
    assert!(
        !report
            .findings
            .iter()
            .any(|finding| finding.code == "product-proof-version-identity-materialization-missing")
    );
    assert_solver_checklist_only(&report, "version identity");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_version_identity_rejects_tool_hash_mismatch() {
    let root = temp_root("product-proof-version-identity-hash-mismatch");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let mut frontend_identity = materialized_trust_tool_identity_json(&root, "targo", None);
    frontend_identity["sha256"] = PRODUCT_PROOF_TEST_SHA256.into();
    let extension_identity = materialized_trust_tool_identity_json(&root, "targo-trust", None);
    let compiler_identity = materialized_trust_tool_identity_json(&root, "trustc", Some(candidate));
    let daemon_identity = materialized_trust_tool_identity_json(&root, "trustd", Some(candidate));
    let candidate_daemon = candidate_daemon_from_json(&root, &daemon_identity);
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "version identity",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "version_identity": {
            "product": "Trust",
            "toolchain_alias": "trust",
            "trust_product_version": "0.1.0",
            "candidate_commit": candidate,
            "candidate_command_version": 1,
            "tools": {
                "frontend": frontend_identity,
                "extension": extension_identity,
                "compiler": compiler_identity,
                "daemon": daemon_identity
            }
        }
    });
    let evidence_path = write_product_proof_evidence(&root, "version-identity.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO_TRUST,
        "version identity",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), Some(&candidate_daemon));
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-version-identity-materialization-missing")
        .expect("missing version identity hash mismatch blocker");
    assert!(
        finding.message.contains("version_identity.tools.frontend")
            && finding.message.contains("hash mismatch"),
        "version tool hash mismatch should require repo-local readback: {}",
        finding.message
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_binary_identity_rejects_label_only_proof_counts() {
    let root = temp_root("product-proof-binary-identity-label-only");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "Trust documentation binary identity",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "diagnostics": [
            "trustdoc binary identity accepted by label only",
            format!("sha256={digest}")
        ]
    });
    let evidence_path =
        write_product_proof_evidence(&root, "trustdoc-binary-identity.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "trustdoc",
        "Trust documentation binary identity",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-binary-identity-materialization-missing")
        .expect("missing binary identity materialization blocker");
    for expected in ["Trust documentation binary identity", "tool_identity"] {
        assert!(finding.message.contains(expected), "missing `{expected}` in {}", finding.message);
    }
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_rejects_obsolete_trustd_binary_identity_evidence() {
    let root = temp_root("product-proof-obsolete-trustd-binary-identity");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "Trust daemon binary identity",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "diagnostics": ["trustd binary identity accepted by label only"]
    });
    let evidence_path =
        write_product_proof_evidence(&root, "trustd-binary-identity.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "trustd",
        "Trust daemon binary identity",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-evidence-kind"
                && finding.message.contains("Trust daemon binary identity")
                && finding.message.contains("Trust daemon protocol smoke")
        }),
        "the retired self-declared daemon identity kind must not re-enter the production matrix: {:?}",
        report.findings
    );
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-evidence-kind-missing"
                && finding.message.contains("Trust daemon protocol smoke")
        }),
        "retired identity evidence must not satisfy the live protocol requirement: {:?}",
        report.findings
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_trustd_protocol_rejects_generic_proof_counts() {
    let root = temp_root("product-proof-trustd-protocol-generic");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "Trust daemon protocol smoke",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
    });
    let evidence_path =
        write_product_proof_evidence(&root, "trustd-protocol-generic.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "trustd",
        "Trust daemon protocol smoke",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert!(report.findings.iter().any(|finding| {
        finding.code == "product-proof-evidence-content-insufficient"
            && finding.message.contains("ceremonial `proof_results`")
    }));
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_trustdoc_multikind_daemon_tag_cannot_select_operational_content() {
    let root = temp_root("product-proof-trustdoc-daemon-tag-confusion");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kinds": [
            "documentation build",
            "Trust documentation binary identity",
            "Trust daemon protocol smoke"
        ],
        "candidate_commit": candidate,
        "operational_checks": {
            "ping": true,
            "identity": true,
            "status": true,
            "reserve": true,
            "release": true,
        },
    });
    let evidence_path =
        write_product_proof_evidence(&root, "trustdoc-daemon-tag-confusion.json", &evidence);
    write_multi_evidence_product_proof_manifest(
        &root,
        "trustdoc",
        &["documentation build", "Trust documentation binary identity"],
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-evidence-content-missing"
                && finding.message.contains("trustdoc")
                && finding.message.contains("proof_results")
        }),
        "an attacker-controlled daemon tag must not reclassify trustdoc evidence as an operational check: {:?}",
        report.findings
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_compile_back_multikind_daemon_tag_still_requires_solver_proof() {
    let root = temp_root("product-proof-compile-back-daemon-tag-confusion");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let mut evidence_kinds = binary_decomp_required_evidence();
    evidence_kinds.push("Trust daemon protocol smoke");
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kinds": evidence_kinds,
        "candidate_commit": candidate,
        "operational_checks": {
            "ping": true,
            "identity": true,
            "status": true,
            "reserve": true,
            "release": true,
        },
        "compile_back_artifact_digest_binding": compile_back_digest_binding(&root, "0..16"),
        "release_artifact_binding": release_artifact_binding_json(&root, candidate),
    });
    let evidence_path =
        write_product_proof_evidence(&root, "compile-back-daemon-tag-confusion.json", &evidence);
    write_binary_decomp_product_proof_manifest(&root, &evidence_path);

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-evidence-content-missing"
                && finding.message.contains("binary/decomp gates")
                && finding.message.contains("proof_results")
        }),
        "a daemon tag must not turn compile-back release-artifact metadata into proof: {:?}",
        report.findings
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn product_proof_rejects_repo_local_fake_trustd_even_when_bytes_match_candidate() {
    let root = temp_root("product-proof-fake-trustd-candidate-binding");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let fake_identity = materialized_trust_tool_identity_json(&root, "trustd", Some(candidate));
    let fake_path = root.join(fake_identity["path"].as_str().expect("fake daemon path"));
    let candidate_path = root.join("release/evidence/candidate-tools/trustd");
    std::fs::create_dir_all(candidate_path.parent().expect("candidate daemon parent"))
        .expect("create candidate daemon parent");
    std::fs::copy(&fake_path, &candidate_path).expect("copy byte-identical candidate daemon");
    make_executable(&candidate_path);
    let candidate_daemon = BoundToolIdentity {
        name: "trustd".to_string(),
        path: Some(candidate_path.display().to_string()),
        sha256: Some(file_sha256(&candidate_path).expect("candidate daemon digest")),
        executable: Some(true),
        version: Some("trustd 1.96.0-trust".to_string()),
        commit_hash: Some(candidate.to_string()),
        rust_compat_version: None,
        resolution: Some("bound-executable".to_string()),
        rejected_inherited_name: None,
        rejected_path: None,
    };
    let version_identity = materialized_version_identity_json(&root, candidate, fake_identity);
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "version identity",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "version_identity": version_identity,
    });
    let evidence_path =
        write_product_proof_evidence(&root, "fake-trustd-version-identity.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO_TRUST,
        "version identity",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), Some(&candidate_daemon));
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-daemon-candidate-binding-missing"
                && finding.message.contains("canonical trustd")
        }),
        "repo-local evidence daemon must be rejected even when its bytes and claimed identity match the candidate: {:?}",
        report.findings
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(target_os = "macos")]
#[test]
fn product_proof_trustd_protocol_rejects_version_only_binary_and_fabricated_transcript() {
    let root = temp_root("product-proof-trustd-protocol-bound");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let (evidence, candidate_daemon) = fabricated_trustd_protocol_evidence(&root, candidate);
    let evidence_path =
        write_product_proof_evidence(&root, "trustd-protocol-bound.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "trustd",
        "Trust daemon protocol smoke",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), Some(&candidate_daemon));
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-daemon-protocol-materialization-missing"
                && (finding.message.contains("native")
                    || finding.message.contains("Mach-O")
                    || finding.message.contains("runtime closure"))
        }),
        "{:?}",
        report.findings
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(target_os = "macos")]
#[test]
fn product_proof_trustd_protocol_rejects_injected_runtime_closure_before_launch() {
    let root = temp_root("product-proof-trustd-hostile-runtime-closure");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let (mut evidence, candidate_daemon) = fabricated_trustd_protocol_evidence(&root, candidate);
    let ignored = root.join("build/ignored-runtime");
    std::fs::create_dir_all(&ignored).expect("create ignored runtime directory");
    let dylib = ignored.join("libattacker.dylib");
    std::fs::write(&dylib, b"mutable attacker dylib").expect("write attacker dylib");
    let symlink = ignored.join("libredirect.dylib");
    std::os::unix::fs::symlink(&dylib, &symlink).expect("create attacker dylib symlink");
    evidence["runtime_closure"]["loader_environment"] = "DYLD_LIBRARY_PATH".into();
    evidence["runtime_closure"]["loader_variable"] = "DYLD_LIBRARY_PATH".into();
    evidence["runtime_closure"]["search_paths"] =
        serde_json::json!([ignored.display().to_string()]);
    evidence["runtime_closure"]["directory_entries"] =
        serde_json::json!([dylib.display().to_string(), symlink.display().to_string(),]);
    let evidence_path =
        write_product_proof_evidence(&root, "trustd-hostile-runtime.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "trustd",
        "Trust daemon protocol smoke",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), Some(&candidate_daemon));
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-daemon-protocol-materialization-missing"
                && finding.message.contains("runtime closure")
        }),
        "an injected loader path and symlink must be rejected before trustd executes: {:?}",
        report.findings
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(target_os = "macos")]
#[test]
fn product_proof_trustd_protocol_requires_serialized_runtime_closure() {
    let root = temp_root("product-proof-trustd-missing-runtime-closure");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let (mut evidence, candidate_daemon) = fabricated_trustd_protocol_evidence(&root, candidate);
    evidence.as_object_mut().expect("evidence object").remove("runtime_closure");
    let evidence_path =
        write_product_proof_evidence(&root, "trustd-missing-runtime.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "trustd",
        "Trust daemon protocol smoke",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), Some(&candidate_daemon));
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-daemon-protocol-materialization-missing"
                && finding.message.contains("runtime_closure")
                && finding.message.contains("loader_environment")
        }),
        "protocol evidence without the serialized no-loader contract was accepted: {:?}",
        report.findings
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(target_os = "macos")]
#[test]
fn product_proof_trustd_protocol_rejects_missing_reservation_token() {
    let root = temp_root("product-proof-trustd-protocol-missing-token");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let (mut evidence, candidate_daemon) = fabricated_trustd_protocol_evidence(&root, candidate);
    evidence["trustd_protocol_smoke"]
        .as_object_mut()
        .expect("protocol smoke object")
        .remove("reservation_token");
    let evidence_path =
        write_product_proof_evidence(&root, "trustd-protocol-missing-token.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "trustd",
        "Trust daemon protocol smoke",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), Some(&candidate_daemon));
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-daemon-protocol-materialization-missing"
                && finding.message.contains("one live reservation followed by its release")
        }),
        "a transcript without a reservation token must be rejected before live replay: {:?}",
        report.findings
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(target_os = "macos")]
#[test]
fn product_proof_trustd_protocol_rejects_reservation_token_mismatch() {
    let root = temp_root("product-proof-trustd-protocol-wrong-token");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let (mut evidence, candidate_daemon) = fabricated_trustd_protocol_evidence(&root, candidate);
    evidence["trustd_protocol_smoke"]["reservation_token"] = 2.into();
    let evidence_path =
        write_product_proof_evidence(&root, "trustd-protocol-wrong-token.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "trustd",
        "Trust daemon protocol smoke",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), Some(&candidate_daemon));
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-daemon-protocol-materialization-missing"
                && finding.message.contains("one live reservation followed by its release")
        }),
        "the recorded reservation token must match the active STATUS entry and transcript: {:?}",
        report.findings
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn product_proof_version_identity_rejects_repeated_trustd_brand_prefix() {
    let root = temp_root("product-proof-trustd-repeated-prefix");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let mut tool_identity = materialized_trust_tool_identity_json(&root, "trustd", Some(candidate));
    tool_identity["version"] = "trustd trustd 1.96.0-trust".into();
    let candidate_daemon = candidate_daemon_from_json(&root, &tool_identity);
    let version_identity = materialized_version_identity_json(&root, candidate, tool_identity);
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "version identity",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "version_identity": version_identity,
    });
    let evidence_path = write_product_proof_evidence(
        &root,
        "version-identity-repeated-trustd-prefix.json",
        &evidence,
    );
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO_TRUST,
        "version identity",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), Some(&candidate_daemon));
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-version-identity-materialization-missing"
                && finding.message.contains("invalid identity/protocol fields")
        }),
        "repeating the `trustd ` brand prefix must not normalize to a valid release: {:?}",
        report.findings
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[cfg(unix)]
#[test]
fn product_proof_identity_probe_clears_ambient_loader_environment() {
    let output = std::process::Command::new(std::env::current_exe().expect("current test binary"))
        .args([
            "--exact",
            "release_cli::tests::product_proof_identity_probe_clears_ambient_loader_environment_child",
            "--nocapture",
        ])
        .env("TRUST_PRODUCT_PROOF_LOADER_ENV_CHILD", "1")
        .env("LD_LIBRARY_PATH", "/attacker-controlled")
        .env("DYLD_LIBRARY_PATH", "/attacker-controlled")
        .output()
        .expect("run isolated loader-environment regression child");
    assert!(
        output.status.success()
            && String::from_utf8_lossy(&output.stdout).contains("ambient-loader-child-ran"),
        "isolated loader-environment regression failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[cfg(unix)]
#[test]
fn product_proof_identity_probe_clears_ambient_loader_environment_child() {
    if std::env::var_os("TRUST_PRODUCT_PROOF_LOADER_ENV_CHILD").is_none() {
        return;
    }
    assert!(
        ["LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"]
            .into_iter()
            .any(|name| std::env::var_os(name).is_some()),
        "isolated child must begin with an ambient loader search path"
    );

    let root = temp_root("product-proof-loader-environment-child");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let path_text = "release/evidence/tools/trustd";
    let path = root.join(path_text);
    std::fs::create_dir_all(path.parent().expect("guarded trustd parent"))
        .expect("create guarded trustd parent");
    write_native_trustd_test_file(&path, candidate, true);
    let digest = file_sha256(&path).expect("guarded trustd digest");
    let tool_identity = trust_tool_identity_json("trustd", path_text, &digest, Some(candidate));
    let candidate_daemon = candidate_daemon_from_json(&root, &tool_identity);
    let version_identity = materialized_version_identity_json(&root, candidate, tool_identity);
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "version identity",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "version_identity": version_identity,
    });
    let evidence_path =
        write_product_proof_evidence(&root, "version-identity-loader-environment.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO_TRUST,
        "version identity",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), Some(&candidate_daemon));
    assert!(
        !report.findings.iter().any(|finding| {
            finding.code == "product-proof-version-identity-materialization-missing"
                || finding.code == "product-proof-daemon-candidate-binding-missing"
        }),
        "the exact daemon identity probe inherited an attacker-controlled loader path: {:?}",
        report.findings
    );
    assert_solver_checklist_only(&report, "version identity");
    println!("ambient-loader-child-ran");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_binary_identity_materializes_but_requires_registered_collector() {
    let root = temp_root("product-proof-binary-identity-structured");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let tool_identity = materialized_trust_tool_identity_json(&root, "trustdoc", None);
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "Trust documentation binary identity",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "tool_identity": tool_identity,
    });
    let evidence_path =
        write_product_proof_evidence(&root, "trustdoc-binary-identity.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "trustdoc",
        "Trust documentation binary identity",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert!(
        !report
            .findings
            .iter()
            .any(|finding| finding.code == "product-proof-binary-identity-materialization-missing")
    );
    assert_solver_checklist_only(&report, "Trust documentation binary identity");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_rejects_binary_identity_name_only_hash() {
    let root = temp_root("product-proof-binary-identity-name-only");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "crate-mode TrustVerify dispatch",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "binary_identity": {
            "name": "targo",
            "sha256": PRODUCT_PROOF_TEST_SHA256
        }
    });
    let evidence_path = write_product_proof_evidence(&root, "targo-dispatch.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO,
        "crate-mode TrustVerify dispatch",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-identity-materialization-missing")
        .expect("missing binary identity name-only materialization blocker");
    assert!(
        finding.message.contains("binary_identity")
            && finding.message.contains("uses only `name`")
            && finding.message.contains("repo-relative `path` or `file`"),
        "binary identity should require repo-local readback: {}",
        finding.message
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_source_archive_hashes_rejects_label_only_proof_counts() {
    let root = temp_root("product-proof-source-archive-hashes-label-only");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "source archive hashes",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "diagnostics": [
            "source archive hashes accepted by label only",
            format!("trust-src-1.96.0-trust.tar.xz sha256={digest}")
        ]
    });
    let evidence_path =
        write_product_proof_evidence(&root, "source-archive-hashes.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "source/docs",
        "source archive hashes",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-source-hashes-materialization-missing")
        .expect("missing source hash materialization blocker");
    assert!(finding.message.contains("source_archive_hashes"), "{}", finding.message);
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_source_archive_hashes_materialize_but_require_registered_collector() {
    let root = temp_root("product-proof-source-archive-hashes-structured");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let source_path = "dist/trust-src-1.96.0-trust.tar.xz";
    let docs_path = "dist/trust-docs-1.96.0-trust.tar.xz";
    let source = root.join(source_path);
    let docs = root.join(docs_path);
    std::fs::create_dir_all(source.parent().expect("source archive parent"))
        .expect("create source archive dir");
    std::fs::write(&source, b"materialized trust source archive\n").expect("write source archive");
    std::fs::write(&docs, b"materialized trust docs archive\n").expect("write docs archive");
    let source_digest = file_sha256(&source).expect("hash source archive");
    let docs_digest = file_sha256(&docs).expect("hash docs archive");
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "source archive hashes",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "source_archive_hashes": [
            {
                "path": source_path,
                "sha256": source_digest
            },
            {
                "path": docs_path,
                "source_sha256": docs_digest
            }
        ]
    });
    let evidence_path =
        write_product_proof_evidence(&root, "source-archive-hashes.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "source/docs",
        "source archive hashes",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert!(
        !report
            .findings
            .iter()
            .any(|finding| finding.code == "product-proof-source-hashes-materialization-missing")
    );
    assert_solver_checklist_only(&report, "source archive hashes");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_source_archive_hashes_rejects_hash_without_repo_path() {
    let root = temp_root("product-proof-source-archive-name-only");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "source archive hashes",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "source_archive_hashes": [{
            "name": "trust-src-1.96.0-trust.tar.xz",
            "sha256": PRODUCT_PROOF_TEST_SHA256
        }]
    });
    let evidence_path =
        write_product_proof_evidence(&root, "source-archive-hashes.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "source/docs",
        "source archive hashes",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-source-hashes-materialization-missing")
        .expect("missing hash-only source archive materialization blocker");
    assert!(
        finding.message.contains("uses only `name`")
            && finding.message.contains("repo-relative `path` or `file`"),
        "hash-only source archive should require repo-local readback: {}",
        finding.message
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_release_check_transcript_rejects_hash_without_repo_path() {
    let root = temp_root("product-proof-transcript-hash-only");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "release check transcript",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "proof_transcript_hash": PRODUCT_PROOF_TEST_SHA256
    });
    let evidence_path =
        write_product_proof_evidence(&root, "release-check-transcript.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO_TRUST,
        "release check transcript",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-transcript-materialization-missing")
        .expect("missing transcript materialization blocker");
    assert!(
        finding.message.contains("proof_transcript_path")
            && finding.message.contains("repo-relative proof transcript path"),
        "hash-only transcript should require repo-local readback: {}",
        finding.message
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_release_check_transcript_rejects_hash_mismatch() {
    let root = temp_root("product-proof-transcript-hash-mismatch");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let transcript_path = "release/evidence/transcripts/release-check.log";
    let transcript = root.join(transcript_path);
    std::fs::create_dir_all(transcript.parent().expect("transcript parent"))
        .expect("create transcript dir");
    std::fs::write(&transcript, b"materialized release check transcript\n")
        .expect("write transcript");
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "release check transcript",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "proof_transcript_path": transcript_path,
        "proof_transcript_hash": PRODUCT_PROOF_TEST_SHA256
    });
    let evidence_path =
        write_product_proof_evidence(&root, "release-check-transcript.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO_TRUST,
        "release check transcript",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-transcript-materialization-missing")
        .expect("transcript hash mismatch blocker");
    assert!(
        finding.message.contains("hash mismatch") && finding.message.contains(transcript_path),
        "transcript hash mismatch should be reported: {}",
        finding.message
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_release_check_transcript_hash_is_checklist_not_solver_proof() {
    let root = temp_root("product-proof-transcript-materialized");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let transcript_path = "release/evidence/transcripts/release-check.log";
    let transcript = root.join(transcript_path);
    std::fs::create_dir_all(transcript.parent().expect("transcript parent"))
        .expect("create transcript dir");
    std::fs::write(&transcript, b"materialized release check transcript\n")
        .expect("write transcript");
    let transcript_digest = file_sha256(&transcript).expect("hash transcript");
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "release check transcript",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "proof_transcript_path": transcript_path,
        "proof_transcript_hash": transcript_digest
    });
    let evidence_path =
        write_product_proof_evidence(&root, "release-check-transcript.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO_TRUST,
        "release check transcript",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert!(
        !report
            .findings
            .iter()
            .any(|finding| finding.code == "product-proof-transcript-materialization-missing")
    );
    assert_solver_checklist_only(&report, "release check transcript");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_component_artifact_rejects_label_only_proof_counts() {
    let root = temp_root("product-proof-component-artifact-label-only");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "documentation build",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "diagnostics": [
            "documentation build accepted by label only",
            format!("trustdoc-1.96.0-trust.tar.xz sha256={digest}")
        ]
    });
    let evidence_path = write_product_proof_evidence(&root, "documentation-build.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "trustdoc",
        "documentation build",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-artifact-materialization-missing")
        .expect("missing component artifact materialization blocker");
    for expected in ["documentation build", "component_artifacts", "artifact"] {
        assert!(finding.message.contains(expected), "missing `{expected}` in {}", finding.message);
    }
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_component_artifact_materializes_but_requires_registered_collector() {
    let root = temp_root("product-proof-component-artifact-structured");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let artifact_path = "release/evidence/artifacts/trustdoc-docs.tar.xz";
    let artifact = root.join(artifact_path);
    std::fs::create_dir_all(artifact.parent().expect("artifact parent"))
        .expect("create artifact dir");
    std::fs::write(&artifact, b"materialized trustdoc documentation artifact\n")
        .expect("write materialized artifact");
    let digest = file_sha256(&artifact).expect("hash materialized artifact");
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "documentation build",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "component_artifacts": [{
            "path": artifact_path,
            "sha256": digest
        }]
    });
    let evidence_path = write_product_proof_evidence(&root, "documentation-build.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "trustdoc",
        "documentation build",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert!(
        !report
            .findings
            .iter()
            .any(|finding| finding.code == "product-proof-artifact-materialization-missing")
    );
    assert_solver_checklist_only(&report, "documentation build");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_component_artifact_rejects_hash_without_repo_path() {
    let root = temp_root("product-proof-component-artifact-name-only");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "documentation build",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "component_artifacts": [{
            "name": "trustdoc-1.96.0-trust-aarch64-apple-darwin.tar.xz",
            "sha256": PRODUCT_PROOF_TEST_SHA256
        }]
    });
    let evidence_path = write_product_proof_evidence(&root, "documentation-build.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        "trustdoc",
        "documentation build",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-artifact-materialization-missing")
        .expect("missing hash-only artifact materialization blocker");
    assert!(
        finding.message.contains("uses only `name`")
            && finding.message.contains("repo-relative `path` or `file`"),
        "hash-only artifact should require repo-local readback: {}",
        finding.message
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_rejects_proof_artifact_hash_without_repo_path() {
    let root = temp_root("product-proof-proof-artifact-hash-only");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "targo identity",
        "candidate_commit": candidate,
        "proof_results": product_proof_results_json(),
        "proof_artifact_sha256": PRODUCT_PROOF_TEST_SHA256,
        "tool_identity": unmaterialized_trust_tool_identity_json(
            "targo",
            PRODUCT_PROOF_TEST_SHA256,
            None
        ),
    });
    let evidence_path = write_product_proof_evidence(&root, "targo-identity.json", &evidence);
    write_single_evidence_product_proof_manifest(
        &root,
        PRODUCT_COMPONENT_TARGO,
        "targo identity",
        &evidence_path,
    );

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-artifact-materialization-missing")
        .expect("missing proof artifact materialization blocker");
    assert!(
        finding.message.contains("proof_artifact_sha256")
            && finding.message.contains("proof_artifact_path"),
        "proof artifact hash must require a repo-local path: {}",
        finding.message
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_rejects_placeholder_evidence_refs() {
    let root = temp_root("product-proof");
    std::fs::create_dir_all(root.join("release")).expect("create release dir");
    let mut manifest = String::new();
    for component in product_proof_component_requirements() {
        manifest.push_str("[[components]]\n");
        manifest.push_str(&format!("component = {:?}\n", component.component));
        manifest.push_str("status = \"accepted\"\n");
        manifest.push_str("evidence = [\"placeholder\"]\n\n");
    }
    std::fs::write(root.join("release/product-proof.toml"), manifest)
        .expect("write product proof manifest");

    let report =
        check_product_proof_coverage(&root, Some("0123456789abcdef0123456789abcdef01234567"), None);
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(report.findings.iter().any(|finding| finding.code == "product-proof-evidence-untyped"));
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_missing_manifest_names_domination_release_blockers() {
    let root = temp_root("product-proof-missing-manifest");
    let report =
        check_product_proof_coverage(&root, Some("0123456789abcdef0123456789abcdef01234567"), None);

    assert_eq!(report.status, GateStatus::Blocked);
    let manifest_finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-manifest-missing")
        .expect("missing manifest blocker");
    for expected in [
        "release/product-proof.toml",
        "status = \"accepted\"",
        "binary/decomp gates",
        "compile-back-artifact-digests-bound:<repo-relative JSON path>",
        "compile-back-selected-image-range:<repo-relative JSON path>",
    ] {
        assert!(
            manifest_finding.message.contains(expected),
            "missing `{expected}` in {}",
            manifest_finding.message
        );
    }

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_missing_binary_decomp_component_names_compile_back_refs() {
    let root = temp_root("product-proof-missing-binary-decomp");
    std::fs::create_dir_all(root.join("release")).expect("create release dir");
    let mut manifest = String::from(
        r#"schema_version = "trust.product-proof-manifest.v1"
status = "accepted"

"#,
    );
    for component in product_proof_component_requirements() {
        if component.component == "binary/decomp gates" {
            continue;
        }
        manifest.push_str("[[components]]\n");
        manifest.push_str(&format!("component = {:?}\n", component.component));
        manifest.push_str("status = \"blocked\"\n");
        manifest.push_str("reason = \"outside focused binary/decomp missing-component test\"\n\n");
    }
    std::fs::write(root.join("release/product-proof.toml"), manifest)
        .expect("write product proof manifest");

    let report =
        check_product_proof_coverage(&root, Some("0123456789abcdef0123456789abcdef01234567"), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let component_finding = report
        .findings
        .iter()
        .find(|finding| {
            finding.code == "product-proof-component-missing"
                && finding.message.contains("binary/decomp gates")
        })
        .expect("missing binary/decomp component blocker");
    for expected in [
        "release/product-proof.toml",
        "status = \"accepted\"",
        "compile-back-artifact-digests-bound:<repo-relative JSON path>",
        "compile-back-selected-image-range:<repo-relative JSON path>",
    ] {
        assert!(
            component_finding.message.contains(expected),
            "missing `{expected}` in {}",
            component_finding.message
        );
    }

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_blocked_manifest_covers_matrix_without_claiming_release() {
    let root = temp_root("product-proof-blocked");
    std::fs::create_dir_all(root.join("release")).expect("create release dir");
    let mut manifest = String::new();
    for component in product_proof_component_requirements() {
        manifest.push_str("[[components]]\n");
        manifest.push_str(&format!("component = {:?}\n", component.component));
        manifest.push_str("status = \"blocked\"\n");
        manifest.push_str("reason = \"release evidence has not been produced\"\n\n");
    }
    std::fs::write(root.join("release/product-proof.toml"), manifest)
        .expect("write product proof manifest");

    let report =
        check_product_proof_coverage(&root, Some("0123456789abcdef0123456789abcdef01234567"), None);
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(
        report.findings.iter().all(|finding| finding.code != "product-proof-component-missing")
    );
    assert_eq!(
        report
            .findings
            .iter()
            .filter(|finding| finding.code == "product-proof-component-blocked")
            .count(),
        product_proof_component_requirements().len()
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_binary_decomp_acceptance_requires_compile_back_digest_binding() {
    let root = temp_root("product-proof-binary-decomp-digests");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence_path = root.join("release/evidence/binary-decomp.json");
    let proof_artifact_path = product_proof_artifact_path_text();
    let proof_artifact_sha256 = materialize_product_proof_artifact(&root);
    let generated_at = PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS;
    std::fs::create_dir_all(evidence_path.parent().expect("evidence parent"))
        .expect("create evidence dir");
    std::fs::write(
        &evidence_path,
        format!(
            r#"{{
  "schema_version": "trust.product-proof.v1",
  "evidence_kinds": [
    "binary lift gate",
    "decompile release gate",
    "checked certificate evidence"
  ],
  "candidate_commit": "{candidate}",
  "generated_at": {generated_at},
  "runner": {{
    "implementation": "rust",
    "entrypoint": "targo trust release check",
    "python_used": false,
    "tool": "targo-trust"
  }},
  "proof_artifact_path": "{proof_artifact_path}",
  "proof_artifact_sha256": "{proof_artifact_sha256}",
  "proof_results": {{
    "proved": 1,
    "total": 1,
    "failed": 0,
    "unknown": 0,
    "by_solver": ["focused-product-proof-test"]
  }}
}}"#
        ),
    )
    .expect("write binary/decomp evidence");

    let mut manifest = String::from(
        r#"schema_version = "trust.product-proof-manifest.v1"
status = "accepted"

"#,
    );
    for component in product_proof_component_requirements() {
        manifest.push_str("[[components]]\n");
        manifest.push_str(&format!("component = {:?}\n", component.component));
        if component.component == "binary/decomp gates" {
            manifest.push_str("status = \"accepted\"\n");
            manifest.push_str("evidence = [\n");
            for evidence_kind in
                ["binary lift gate", "decompile release gate", "checked certificate evidence"]
            {
                manifest.push_str(&format!(
                    "  {:?},\n",
                    format!("{evidence_kind}:release/evidence/binary-decomp.json")
                ));
            }
            manifest.push_str("]\n\n");
        } else {
            manifest.push_str("status = \"blocked\"\n");
            manifest.push_str("reason = \"outside focused binary/decomp digest-binding test\"\n\n");
        }
    }
    std::fs::write(root.join("release/product-proof.toml"), manifest)
        .expect("write product proof manifest");

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    for required in COMPILE_BACK_DIGEST_REQUIREMENTS {
        assert!(
            report.findings.iter().any(|finding| {
                finding.code == "product-proof-evidence-kind-missing"
                    && finding.message.contains(required)
            }),
            "missing fail-closed blocker for `{required}`"
        );
    }

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_compile_back_digest_evidence_requires_materialized_json_values() {
    let root = temp_root("product-proof-compile-back-digests-missing");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence_path = root.join("release/evidence/binary-decomp.json");
    let proof_artifact_sha256 = materialize_product_proof_artifact(&root);
    std::fs::create_dir_all(evidence_path.parent().expect("evidence parent"))
        .expect("create evidence dir");
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kinds": binary_decomp_required_evidence(),
        "candidate_commit": candidate,
        "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
        "runner": product_proof_runner_json(),
        "proof_artifact_path": product_proof_artifact_path_text(),
        "proof_artifact_sha256": proof_artifact_sha256,
        "proof_results": {
            "proved": 1,
            "total": 1,
            "failed": 0,
            "unknown": 0,
            "by_solver": ["focused-product-proof-test"]
        }
    });
    std::fs::write(
        &evidence_path,
        serde_json::to_string_pretty(&evidence).expect("render evidence"),
    )
    .expect("write binary/decomp evidence");
    write_binary_decomp_product_proof_manifest(&root, "release/evidence/binary-decomp.json");

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-compile-back-artifact-digest-missing")
        .expect("missing compile-back digest materialization blocker");
    for expected in [
        "release/product-proof.toml",
        "evidence_kind",
        "compile_back_artifact_digest_binding",
        "`compile_back_artifact_digest_binding.root_artifact_sha256`",
    ] {
        assert!(finding.message.contains(expected), "missing `{expected}` in {}", finding.message);
    }
    assert!(
        !finding.message.contains("diagnostic"),
        "diagnostic strings must not satisfy compile-back digest materialization: {}",
        finding.message
    );
    let missing_kind = report
        .findings
        .iter()
        .find(|finding| {
            finding.code == "product-proof-evidence-kind-missing"
                && finding.message.contains("compile-back-artifact-digests-bound")
        })
        .expect("missing required compile-back evidence kind blocker");
    assert!(missing_kind.message.contains("release/product-proof.toml"));
    assert!(missing_kind.message.contains("compile_back_artifact_digest_binding"));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_rejects_compile_back_digest_materialization_from_validation_evidence() {
    let root = temp_root("product-proof-compile-back-digests-diagnostics");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    let evidence_path = root.join("release/evidence/binary-decomp.json");
    let proof_artifact_sha256 = materialize_product_proof_artifact(&root);
    std::fs::create_dir_all(evidence_path.parent().expect("evidence parent"))
        .expect("create evidence dir");
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kinds": binary_decomp_required_evidence(),
        "candidate_commit": candidate,
        "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
        "runner": product_proof_runner_json(),
        "proof_artifact_path": product_proof_artifact_path_text(),
        "proof_artifact_sha256": proof_artifact_sha256,
        "proof_results": {
            "proved": 1,
            "total": 1,
            "failed": 0,
            "unknown": 0,
            "by_solver": ["focused-product-proof-test"]
        },
        "validation_records": [{
            "evidence": compile_back_digest_diagnostics(digest)
        }],
    });
    std::fs::write(
        &evidence_path,
        serde_json::to_string_pretty(&evidence).expect("render evidence"),
    )
    .expect("write binary/decomp evidence");
    write_binary_decomp_product_proof_manifest(&root, "release/evidence/binary-decomp.json");

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.code == "product-proof-compile-back-artifact-digest-missing"),
        "diagnostic-only material must not satisfy compile-back digest bindings: {:?}",
        report.findings
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_compile_back_digests_materialize_but_are_not_solver_proof() {
    let root = temp_root("product-proof-compile-back-digests-binding");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence_path = root.join("release/evidence/binary-decomp.json");
    std::fs::create_dir_all(evidence_path.parent().expect("evidence parent"))
        .expect("create evidence dir");
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kinds": binary_decomp_required_evidence(),
        "candidate_commit": candidate,
        "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
        "runner": product_proof_runner_json(),
        "proof_results": {
            "proved": 1,
            "total": 1,
            "failed": 0,
            "unknown": 0,
            "by_solver": ["focused-product-proof-test"]
        },
        "compile_back_artifact_digest_binding": compile_back_digest_binding(&root, "0..16"),
        "release_artifact_binding": release_artifact_binding_json(&root, candidate),
    });
    std::fs::write(
        &evidence_path,
        serde_json::to_string_pretty(&evidence).expect("render evidence"),
    )
    .expect("write binary/decomp evidence");
    write_binary_decomp_product_proof_manifest(&root, "release/evidence/binary-decomp.json");

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert!(
        !report.findings.iter().any(|finding| {
            finding.code == "product-proof-compile-back-artifact-digest-missing"
        })
    );
    assert_solver_checklist_only(&report, "compile-back-artifact-digests-bound");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_stub_exporter_writes_blocked_digest_bound_compile_back_json() {
    let root = temp_root("product-proof-stub-exporter");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let artifact_path = "release/evidence/artifacts/root.bin";
    let out_path = "release/evidence/root-stub.json";
    let artifact = root.join(artifact_path);
    std::fs::create_dir_all(artifact.parent().expect("artifact parent"))
        .expect("create artifact dir");
    std::fs::write(&artifact, b"digest-bound compile-back root artifact\n")
        .expect("write artifact");
    let digest = file_sha256(&artifact).expect("hash artifact");

    let args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence-kind",
        "compile-back-root-artifact-sha256",
        "--artifact",
        &format!("root_artifact_sha256={artifact_path}"),
        "--out",
        out_path,
    ]);
    assert_eq!(run_product_proof_stub_subcommand(&args), ExitCode::SUCCESS);

    let evidence: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join(out_path)).expect("read product-proof stub"),
    )
    .expect("parse product-proof stub");
    assert_eq!(evidence["schema_version"], "trust.product-proof.v1");
    assert_eq!(evidence["evidence_kind"], "compile-back-root-artifact-sha256");
    assert_eq!(evidence["candidate_commit"], candidate);
    assert_eq!(evidence["status"], "blocked");
    assert_eq!(evidence["proof_results"]["proved"].as_u64(), Some(0));
    assert_eq!(evidence["proof_results"]["total"].as_u64(), Some(0));
    assert_eq!(
        evidence["compile_back_artifact_digest_binding"]["root_artifact_sha256"].as_str(),
        Some(digest.as_str())
    );
    assert_eq!(
        evidence["compile_back_artifact_digest_binding"]["root_artifact_path"].as_str(),
        Some(artifact_path)
    );
    assert_eq!(evidence["runner"]["python_used"].as_bool(), Some(false));
    assert!(
        evidence["runner"]["entrypoint"]
            .as_str()
            .is_some_and(|entrypoint| entrypoint.contains("product-proof-stub"))
    );
    assert_eq!(
        evidence["product_proof_manifest_stub"]["evidence_ref"].as_str(),
        Some("compile-back-root-artifact-sha256:release/evidence/root-stub.json")
    );

    write_single_evidence_product_proof_manifest(
        &root,
        "binary/decomp gates",
        "compile-back-root-artifact-sha256",
        out_path,
    );
    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.code == "product-proof-evidence-content-insufficient"),
        "stub must not validate as proof success: {:?}",
        report.findings
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_stub_exporter_writes_blocked_release_artifact_report() {
    let root = temp_root("product-proof-stub-release-artifact-report");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let artifact_path = "release/evidence/artifacts/selected-image.bin";
    let out_path = "release/evidence/selected-image-range-stub.json";
    let report_path = "release/reports/selected-image-range-stub-report.json";
    let artifact = root.join(artifact_path);
    std::fs::create_dir_all(artifact.parent().expect("artifact parent"))
        .expect("create artifact dir");
    std::fs::write(&artifact, b"digest-bound selected image bytes\n").expect("write artifact");
    let artifact_digest = file_sha256(&artifact).expect("hash artifact");

    let args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence-kind",
        "compile-back-selected-image-range",
        "--artifact",
        &format!("selected_image_sha256={artifact_path}"),
        "--selected-image-range",
        "0..16",
        "--out",
        out_path,
        "--report-out",
        report_path,
    ]);
    assert_eq!(run_product_proof_stub_subcommand(&args), ExitCode::SUCCESS);

    let evidence: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join(out_path)).expect("read product-proof stub"),
    )
    .expect("parse product-proof stub");
    let report: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join(report_path)).expect("read release artifact report"),
    )
    .expect("parse release artifact report");
    let evidence_digest = file_sha256(&root.join(out_path)).expect("hash evidence artifact");

    assert_eq!(evidence["status"], "blocked");
    assert_eq!(evidence["candidate_commit_binding"]["value"], candidate);
    assert_eq!(
        evidence["compile_back_artifact_digest_binding"]["selected_image_sha256"].as_str(),
        Some(artifact_digest.as_str())
    );
    assert_eq!(
        evidence["compile_back_artifact_digest_binding"]["selected_image_path"].as_str(),
        Some(artifact_path)
    );
    assert_eq!(
        evidence["compile_back_artifact_digest_binding"]["selected_image_range"].as_str(),
        Some("0..16")
    );
    assert_eq!(
        evidence["release_artifact"]["artifact_sha256_checks"][0]["sha256"].as_str(),
        Some(artifact_digest.as_str())
    );
    assert_eq!(
        evidence["release_artifact"]["selected_image_range_check"]["range"].as_str(),
        Some("0..16")
    );
    assert_eq!(evidence["release_artifact"]["product_proof_pass_evidence"].as_bool(), Some(false));

    assert_eq!(report["schema_version"], "trust.product-proof-release-artifact-report.v1");
    assert_eq!(report["status"], "blocked");
    assert_eq!(report["candidate_commit"], candidate);
    assert_eq!(report["candidate_commit_binding"]["status"], "bound");
    assert_eq!(report["runner"]["implementation"], "rust");
    assert_eq!(report["runner"]["python_used"].as_bool(), Some(false));
    assert_eq!(report["product_proof_artifact"]["path"], out_path);
    assert_eq!(report["product_proof_artifact"]["sha256"].as_str(), Some(evidence_digest.as_str()));
    assert_eq!(report["artifact_sha256_checks"][0]["path"].as_str(), Some(artifact_path));
    assert_eq!(report["selected_image_range_check"]["range"].as_str(), Some("0..16"));
    assert_eq!(report["product_proof_pass_evidence"].as_bool(), Some(false));
    assert_eq!(report["domination_admissible"].as_bool(), Some(false));
    assert!(
        report["blockers"]
            .as_array()
            .expect("blockers")
            .iter()
            .any(|blocker| blocker["code"] == "product-proof-evidence-content-insufficient"),
        "release artifact report must carry product-proof blocker reasons: {report}"
    );

    write_single_evidence_product_proof_manifest(
        &root,
        "binary/decomp gates",
        "compile-back-selected-image-range",
        out_path,
    );
    let validation = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(validation.status, GateStatus::Blocked);
    assert!(
        validation
            .findings
            .iter()
            .any(|finding| finding.code == "product-proof-evidence-content-insufficient"),
        "blocked stub must still be rejected as product-proof pass evidence: {:?}",
        validation.findings
    );
    assert!(validation.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_stub_exporter_writes_blocked_manifest_skeleton_from_real_artifacts() {
    let root = temp_root("product-proof-stub-manifest-skeleton");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let artifact_path = "release/evidence/artifacts/compile-back-material.bin";
    let out_path = "release/evidence/product-proof/compile-back-digests-bound.json";
    let manifest_path = "release/product-proof.toml";
    let stage2_trustc_path = materialized_stage2_trustc_path(&root, candidate);
    let source_tarball_path = materialized_source_tarball_path(&root, candidate);
    let artifact = root.join(artifact_path);
    std::fs::create_dir_all(artifact.parent().expect("artifact parent"))
        .expect("create artifact dir");
    std::fs::write(&artifact, b"digest-bound compile-back release artifact material\n")
        .expect("write compile-back artifact");
    let artifact_digest = file_sha256(&artifact).expect("hash artifact");

    let args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence-kind",
        "compile-back-artifact-digests-bound",
        "--artifact",
        &format!("lifted_binary_trust_ir_sha256={artifact_path}"),
        "--artifact",
        &format!("rust_source_sha256={artifact_path}"),
        "--artifact",
        &format!("reconstructed_trust_ir_sha256={artifact_path}"),
        "--artifact",
        &format!("refinement_artifact_sha256={artifact_path}"),
        "--artifact",
        &format!("root_artifact_sha256={artifact_path}"),
        "--artifact",
        &format!("selected_image_sha256={artifact_path}"),
        "--selected-image-range",
        "0..16",
        "--stage2-trustc",
        &stage2_trustc_path,
        "--source-tarball",
        &source_tarball_path,
        "--out",
        out_path,
        "--manifest-out",
        manifest_path,
    ]);
    assert_eq!(run_product_proof_stub_subcommand(&args), ExitCode::SUCCESS);

    let evidence: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join(out_path)).expect("read product-proof stub"),
    )
    .expect("parse product-proof stub");
    assert_eq!(evidence["schema_version"], "trust.product-proof.v1");
    assert_eq!(evidence["status"], "blocked");
    assert_eq!(evidence["proof_results"]["proved"].as_u64(), Some(0));
    assert_eq!(
        evidence["release_artifact_binding"]["stage2_trustc"]["path"].as_str(),
        Some(stage2_trustc_path.as_str())
    );
    assert_eq!(
        evidence["release_artifact_binding"]["source_tarball"]["path"].as_str(),
        Some(source_tarball_path.as_str())
    );
    assert_eq!(
        evidence["compile_back_artifact_digest_binding"]["root_artifact_sha256"].as_str(),
        Some(artifact_digest.as_str())
    );
    assert!(
        COMPILE_BACK_DIGEST_REQUIREMENTS.iter().all(|required| {
            evidence["evidence_kinds"]
                .as_array()
                .expect("evidence_kinds")
                .iter()
                .any(|kind| kind.as_str() == Some(*required))
        }),
        "aggregate stub must declare every compile-back kind: {evidence}"
    );

    let manifest = std::fs::read_to_string(root.join(manifest_path)).expect("read manifest");
    assert!(manifest.contains("schema_version = \"trust.product-proof-manifest.v1\""));
    assert!(manifest.contains("status = \"blocked\""));
    assert!(manifest.contains(&format!("stage2_trustc = \"{stage2_trustc_path}\"")));
    assert!(manifest.contains(&format!("source_tarball = \"{source_tarball_path}\"")));
    assert!(
        root.join("release/evidence/product-proof/product-proof-release-certificate.json")
            .is_file()
    );
    assert!(manifest.contains("component = \"binary/decomp gates\""));
    for required in COMPILE_BACK_DIGEST_REQUIREMENTS {
        assert!(
            manifest.contains(&format!("{required}:{out_path}")),
            "manifest missing compile-back ref `{required}`:\n{manifest}"
        );
    }

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(
        !report.findings.iter().any(|finding| finding.code == "product-proof-manifest-missing")
    );
    assert!(
        !report.findings.iter().any(|finding| {
            finding.code == "product-proof-component-missing"
                && finding.message.contains("binary/decomp gates")
        }),
        "binary/decomp row should be present in skeleton: {:?}",
        report.findings
    );
    assert!(report.findings.iter().any(|finding| finding.code == "product-proof-manifest-blocked"));
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-component-blocked"
                && finding.message.contains("binary/decomp gates")
        }),
        "skeleton must remain blocked until proof evidence exists: {:?}",
        report.findings
    );
    assert!(report.evidence_refs.is_empty());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_stub_manifest_skeleton_requires_aggregate_compile_back_inputs() {
    let root = temp_root("product-proof-stub-manifest-skeleton-missing-input");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let artifact_path = "release/evidence/artifacts/root.bin";
    let out_path = "release/evidence/product-proof/root-only.json";
    let manifest_path = "release/product-proof.toml";
    let artifact = root.join(artifact_path);
    std::fs::create_dir_all(artifact.parent().expect("artifact parent"))
        .expect("create artifact dir");
    std::fs::write(&artifact, b"only one compile-back artifact\n").expect("write artifact");

    let args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence-kind",
        "compile-back-root-artifact-sha256",
        "--artifact",
        &format!("root_artifact_sha256={artifact_path}"),
        "--out",
        out_path,
        "--manifest-out",
        manifest_path,
    ]);

    assert_eq!(run_product_proof_stub_subcommand(&args), ExitCode::from(2));
    assert!(!root.join(out_path).exists());
    assert!(!root.join(manifest_path).exists());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_report_rejects_self_declared_compile_back_solver_evidence() {
    let root = temp_root("product-proof-report-self-declared-solver");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let report_path = "release/reports/product-proof-release-report.json";
    let mut runner = product_proof_runner_json();
    runner["repo_dirty"] = false.into();
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kinds": COMPILE_BACK_DIGEST_REQUIREMENTS,
        "candidate_commit": candidate,
        "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
        "runner": runner,
        "proof_results": product_proof_results_json(),
        "compile_back_artifact_digest_binding": compile_back_digest_binding(&root, "0..16"),
        "release_artifact_binding": release_artifact_binding_json(&root, candidate),
    });
    let evidence_path = write_product_proof_evidence(&root, "product-proof-pass.json", &evidence);
    commit_all(&root, "release evidence");

    let args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence",
        &evidence_path,
        "--out",
        report_path,
    ]);
    assert_eq!(run_product_proof_report_subcommand(&args), ExitCode::from(1));

    let report: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join(report_path)).expect("read release report"),
    )
    .expect("parse release report");
    let evidence_digest = file_sha256(&root.join(&evidence_path)).expect("hash evidence");

    assert_eq!(report["schema_version"], "trust.product-proof-release-artifact-report.v1");
    assert_eq!(report["status"], "blocked");
    assert_eq!(report["candidate_commit"], candidate);
    assert_eq!(report["candidate_commit_binding"]["status"], "bound");
    assert_eq!(report["product_proof_artifact"]["path"], evidence_path);
    assert_eq!(report["product_proof_artifact"]["sha256"].as_str(), Some(evidence_digest.as_str()));
    assert_eq!(report["product_proof_pass_evidence"].as_bool(), Some(false));
    assert_eq!(report["domination_admissible"].as_bool(), Some(false));
    assert_eq!(report["runner"]["implementation"], "rust");
    assert_eq!(report["runner"]["python_used"].as_bool(), Some(false));
    assert_eq!(report["ingested_evidence_runner"]["repo_dirty"].as_bool(), Some(false));
    assert_eq!(report["runner_clean_provenance"]["status"], "passed");
    assert_eq!(report["selected_image_range_check"]["status"], "passed");
    assert_eq!(report["selected_image_range_check"]["range"].as_str(), Some("0..16"));
    assert!(
        report["compile_back_evidence_kinds"]
            .as_array()
            .expect("compile-back kind checks")
            .iter()
            .all(|check| check["status"] == "passed"),
        "all compile-back kinds must be declared: {report}"
    );
    assert!(
        report["artifact_sha256_checks"]
            .as_array()
            .expect("artifact checks")
            .iter()
            .all(|check| check["status"] == "passed"),
        "all compile-back artifact hashes must be materialized: {report}"
    );
    assert!(
        report["blockers"].as_array().expect("blockers").iter().any(|blocker| {
            blocker["code"] == "product-proof-solver-evidence-unverified"
                && blocker["message"].as_str().is_some_and(|message| {
                    message.contains("self-declared runner identity")
                        && message.contains("complete ID/digest-indexed candidate obligation set")
                        && message.contains("strictly parsed transcript")
                })
        }),
        "fabricated counts plus fully materialized hashes must remain non-proof checklist material: {report}"
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_report_rejects_duplicate_json_keys() {
    let root = temp_root("product-proof-report-duplicate-json-key");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence_path = "release/evidence/product-proof-duplicate.json";
    let report_path = "release/reports/product-proof-duplicate-report.json";
    std::fs::create_dir_all(root.join("release/evidence")).expect("create evidence dir");
    std::fs::write(
        root.join(evidence_path),
        format!(
            r#"{{
  "schema_version": "trust.product-proof.v1",
  "candidate_commit": "fedcba9876543210fedcba9876543210fedcba98",
  "\u0063andidate_commit": "{candidate}"
}}"#
        ),
    )
    .expect("write duplicate-key release evidence");
    commit_all(&root, "duplicate-key release evidence");

    let args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence",
        evidence_path,
        "--out",
        report_path,
    ]);
    assert_eq!(run_product_proof_report_subcommand(&args), ExitCode::from(1));

    let report: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join(report_path)).expect("read release report"),
    )
    .expect("parse release report");
    assert_eq!(report["status"], "blocked");
    assert!(
        report["blockers"].as_array().expect("blockers").iter().any(|blocker| {
            blocker["code"] == "product-proof-release-evidence-json"
                && blocker["message"].as_str().is_some_and(|message| {
                    message.contains("duplicate object key `candidate_commit`")
                })
        }),
        "duplicate candidate bindings must fail before last-key-wins parsing: {report}"
    );
    assert_eq!(report["product_proof_pass_evidence"].as_bool(), Some(false));
    assert_eq!(report["domination_admissible"].as_bool(), Some(false));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_report_rejects_dirty_current_repo() {
    let root = temp_root("product-proof-report-dirty-current-repo");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let mut runner = product_proof_runner_json();
    runner["repo_dirty"] = false.into();
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kinds": COMPILE_BACK_DIGEST_REQUIREMENTS,
        "candidate_commit": candidate,
        "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
        "runner": runner,
        "proof_results": product_proof_results_json(),
        "compile_back_artifact_digest_binding": compile_back_digest_binding(&root, "0..16"),
    });
    let evidence_path =
        write_product_proof_evidence(&root, "product-proof-dirty-current-repo.json", &evidence);
    commit_all(&root, "release evidence");
    std::fs::write(root.join("dirty-current-repo.txt"), "dirty after evidence commit\n")
        .expect("write dirty file");
    let report_path = "release/reports/product-proof-dirty-current-repo-report.json";

    let args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence",
        &evidence_path,
        "--out",
        report_path,
    ]);
    assert_eq!(run_product_proof_report_subcommand(&args), ExitCode::from(1));

    let report: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join(report_path)).expect("read release report"),
    )
    .expect("parse release report");
    assert_eq!(report["status"], "blocked");
    assert_eq!(report["repo_dirty"].as_bool(), Some(true));
    assert_eq!(report["repo_dirty_metadata"]["available"].as_bool(), Some(true));
    assert_eq!(report["repo_dirty_metadata"]["dirty"].as_bool(), Some(true));
    assert!(
        report["blockers"]
            .as_array()
            .expect("blockers")
            .iter()
            .any(|blocker| blocker["code"] == "product-proof-release-repo-dirty"),
        "dirty current repo must block release admission: {report}"
    );
    assert_eq!(report["product_proof_pass_evidence"].as_bool(), Some(false));
    assert_eq!(report["domination_admissible"].as_bool(), Some(false));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_report_blocks_digest_bound_stub_evidence() {
    let root = temp_root("product-proof-report-stub-blocked");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let artifact_path = "release/evidence/artifacts/root.bin";
    let out_path = "release/evidence/root-stub.json";
    let report_path = "release/reports/root-stub-report.json";
    let artifact = root.join(artifact_path);
    std::fs::create_dir_all(artifact.parent().expect("artifact parent"))
        .expect("create artifact dir");
    std::fs::write(&artifact, b"digest-bound compile-back root artifact\n")
        .expect("write artifact");

    let stub_args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence-kind",
        "compile-back-root-artifact-sha256",
        "--artifact",
        &format!("root_artifact_sha256={artifact_path}"),
        "--out",
        out_path,
    ]);
    assert_eq!(run_product_proof_stub_subcommand(&stub_args), ExitCode::SUCCESS);

    let report_args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence",
        out_path,
        "--out",
        report_path,
    ]);
    assert_eq!(run_product_proof_report_subcommand(&report_args), ExitCode::from(1));

    let report: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join(report_path)).expect("read release report"),
    )
    .expect("parse release report");
    assert_eq!(report["status"], "blocked");
    assert_eq!(report["product_proof_pass_evidence"].as_bool(), Some(false));
    assert_eq!(report["domination_admissible"].as_bool(), Some(false));
    assert!(
        report["blockers"]
            .as_array()
            .expect("blockers")
            .iter()
            .any(|blocker| blocker["code"] == "product-proof-stub-blocked"),
        "stub evidence must be blocked explicitly: {report}"
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_report_rejects_dirty_runner_provenance() {
    let root = temp_root("product-proof-report-dirty-runner");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let mut runner = product_proof_runner_json();
    runner["repo_dirty"] = true.into();
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kinds": COMPILE_BACK_DIGEST_REQUIREMENTS,
        "candidate_commit": candidate,
        "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
        "runner": runner,
        "proof_results": product_proof_results_json(),
        "compile_back_artifact_digest_binding": compile_back_digest_binding(&root, "0..16"),
    });
    let evidence_path =
        write_product_proof_evidence(&root, "product-proof-dirty-runner.json", &evidence);
    let report_path = "release/reports/product-proof-dirty-runner-report.json";

    let args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence",
        &evidence_path,
        "--out",
        report_path,
    ]);
    assert_eq!(run_product_proof_report_subcommand(&args), ExitCode::from(1));

    let report: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join(report_path)).expect("read release report"),
    )
    .expect("parse release report");
    assert_eq!(report["status"], "blocked");
    assert_eq!(report["runner_clean_provenance"]["status"], "blocked");
    assert!(
        report["blockers"]
            .as_array()
            .expect("blockers")
            .iter()
            .any(|blocker| blocker["code"] == "product-proof-evidence-runner-dirty"),
        "dirty runner provenance must block release admission: {report}"
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_report_rejects_candidate_mismatch() {
    let root = temp_root("product-proof-report-candidate-mismatch");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let other_candidate = "fedcba9876543210fedcba9876543210fedcba98";
    let mut runner = product_proof_runner_json();
    runner["repo_dirty"] = false.into();
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kinds": COMPILE_BACK_DIGEST_REQUIREMENTS,
        "candidate_commit": other_candidate,
        "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
        "runner": runner,
        "proof_results": product_proof_results_json(),
        "compile_back_artifact_digest_binding": compile_back_digest_binding(&root, "0..16"),
    });
    let evidence_path =
        write_product_proof_evidence(&root, "product-proof-candidate-mismatch.json", &evidence);
    let report_path = "release/reports/product-proof-candidate-mismatch-report.json";

    let args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence",
        &evidence_path,
        "--out",
        report_path,
    ]);
    assert_eq!(run_product_proof_report_subcommand(&args), ExitCode::from(1));

    let report: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join(report_path)).expect("read release report"),
    )
    .expect("parse release report");
    assert_eq!(report["status"], "blocked");
    assert_eq!(report["candidate_commit_binding"]["status"], "blocked");
    assert!(
        report["blockers"]
            .as_array()
            .expect("blockers")
            .iter()
            .any(|blocker| blocker["code"] == "product-proof-release-candidate-mismatch"),
        "candidate mismatch must block release admission: {report}"
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_report_rejects_unbound_selected_image_digest() {
    let root = temp_root("product-proof-report-selected-image-mismatch");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let mut runner = product_proof_runner_json();
    runner["repo_dirty"] = false.into();
    let mut binding = compile_back_digest_binding(&root, "0..16");
    binding["selected_image_sha256"] = PRODUCT_PROOF_TEST_SHA256.into();
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kinds": COMPILE_BACK_DIGEST_REQUIREMENTS,
        "candidate_commit": candidate,
        "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
        "runner": runner,
        "proof_results": product_proof_results_json(),
        "compile_back_artifact_digest_binding": binding,
    });
    let evidence_path = write_product_proof_evidence(
        &root,
        "product-proof-selected-image-mismatch.json",
        &evidence,
    );
    let report_path = "release/reports/product-proof-selected-image-mismatch-report.json";

    let args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence",
        &evidence_path,
        "--out",
        report_path,
    ]);
    assert_eq!(run_product_proof_report_subcommand(&args), ExitCode::from(1));

    let report: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join(report_path)).expect("read release report"),
    )
    .expect("parse release report");
    assert_eq!(report["status"], "blocked");
    assert_eq!(report["selected_image_range_check"]["status"], "blocked");
    assert_eq!(report["selected_image_range_check"]["hash_bound"].as_bool(), Some(false));
    assert!(
        report["blockers"].as_array().expect("blockers").iter().any(|blocker| {
            blocker["code"] == "product-proof-selected-image-binding-missing"
                || blocker["code"] == "product-proof-compile-back-artifact-digest-missing"
        }),
        "selected-image hash mismatch must block release admission: {report}"
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_stub_exporter_fails_before_writing_missing_artifact() {
    let root = temp_root("product-proof-stub-missing-artifact");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let out_path = "release/evidence/missing-stub.json";

    let args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence-kind",
        "compile-back-root-artifact-sha256",
        "--artifact",
        "root_artifact_sha256=release/evidence/artifacts/missing.bin",
        "--out",
        out_path,
    ]);

    assert_eq!(run_product_proof_stub_subcommand(&args), ExitCode::from(2));
    assert!(!root.join(out_path).exists());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_stub_exporter_rejects_undigested_range_only_stub() {
    let root = temp_root("product-proof-stub-range-only");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let out_path = "release/evidence/range-stub.json";

    let args = string_args(&[
        "--repo-root",
        &root.display().to_string(),
        "--candidate-commit",
        candidate,
        "--evidence-kind",
        "compile-back-selected-image-range",
        "--selected-image-range",
        "0..16",
        "--out",
        out_path,
    ]);

    assert_eq!(run_product_proof_stub_subcommand(&args), ExitCode::from(2));
    assert!(!root.join(out_path).exists());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_rejects_compile_back_digest_binding_with_non_numeric_range() {
    let root = temp_root("product-proof-compile-back-digests-bogus-range");
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let evidence_path = root.join("release/evidence/binary-decomp.json");
    std::fs::create_dir_all(evidence_path.parent().expect("evidence parent"))
        .expect("create evidence dir");
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kinds": binary_decomp_required_evidence(),
        "candidate_commit": candidate,
        "generated_at": PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
        "runner": product_proof_runner_json(),
        "proof_results": {
            "proved": 1,
            "total": 1,
            "failed": 0,
            "unknown": 0,
            "by_solver": ["focused-product-proof-test"]
        },
        "compile_back_artifact_digest_binding": compile_back_digest_binding(&root, "bogus"),
    });
    std::fs::write(
        &evidence_path,
        serde_json::to_string_pretty(&evidence).expect("render evidence"),
    )
    .expect("write binary/decomp evidence");
    write_binary_decomp_product_proof_manifest(&root, "release/evidence/binary-decomp.json");

    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-compile-back-artifact-digest-missing"
                && finding.message.contains("selected_image_range")
        }),
        "bogus selected-image range must block compile-back digest evidence: {:?}",
        report.findings
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_evidence_classes_read_manifest_statuses() {
    let root = temp_root("product-proof-evidence-classes");
    std::fs::create_dir_all(root.join("release")).expect("create release dir");
    std::fs::write(
        root.join("release/product-proof.toml"),
        r#"
[[evidence_classes]]
class = "strict Tier-0 proof"
status = "blocked"
reason = "strict proof evidence has not been produced"
"#,
    )
    .expect("write product proof manifest");

    let classes = product_proof_evidence_classes(&root, &[]);
    let strict = classes
        .iter()
        .find(|class| class.class == "strict Tier-0 proof")
        .expect("strict proof class");
    assert_eq!(strict.status, "blocked");
    assert_eq!(strict.reason.as_deref(), Some("strict proof evidence has not been produced"));

    let native = classes
        .iter()
        .find(|class| class.class == "native proof engines")
        .expect("native proof class");
    assert_eq!(native.status, "missing_evidence");
    assert!(native.reason.is_none());

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_evidence_class_acceptance_requires_manifest_and_gate_pass() {
    let root = temp_root("product-proof-evidence-class-acceptance");
    std::fs::create_dir_all(root.join("release")).expect("create release dir");
    std::fs::write(
        root.join("release/product-proof.toml"),
        r#"
schema_version = "trust.product-proof-manifest.v1"
status = "blocked"
reason = "release evidence has not been produced"

[[evidence_classes]]
class = "strict Tier-0 proof"
status = "accepted"
reason = "declared by manifest"
"#,
    )
    .expect("write product proof manifest");

    let classes = product_proof_evidence_classes(&root, &[GateReport::pass("trust-extra")]);
    let strict = classes
        .iter()
        .find(|class| class.class == "strict Tier-0 proof")
        .expect("strict proof class");
    assert_eq!(strict.status, "blocked");
    assert_eq!(
        strict.reason.as_deref(),
        Some("top-level product-proof manifest status is not accepted")
    );

    let report =
        check_product_proof_coverage(&root, Some("0123456789abcdef0123456789abcdef01234567"), None);
    assert!(report.findings.iter().any(|finding| finding.code == "product-proof-manifest-blocked"));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_coverage_requires_top_level_manifest_status() {
    let root = temp_root("product-proof-manifest-status-missing");
    std::fs::create_dir_all(root.join("release")).expect("create release dir");
    let mut manifest = String::from(
        r#"schema_version = "trust.product-proof-manifest.v1"

"#,
    );
    for component in product_proof_component_requirements() {
        manifest.push_str("[[components]]\n");
        manifest.push_str(&format!("component = {:?}\n", component.component));
        manifest.push_str("status = \"blocked\"\n");
        manifest.push_str("reason = \"release evidence has not been produced\"\n\n");
    }
    std::fs::write(root.join("release/product-proof.toml"), manifest)
        .expect("write product proof manifest");

    let report =
        check_product_proof_coverage(&root, Some("0123456789abcdef0123456789abcdef01234567"), None);

    assert_eq!(report.status, GateStatus::Blocked);
    assert!(report.findings.iter().any(|finding| {
        finding.code == "product-proof-manifest-status-missing"
            && finding.message.contains("status = \"accepted\"")
    }));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_matrix_fails_closed_on_malformed_manifest() {
    let root = temp_root("product-proof-matrix-malformed-manifest");
    std::fs::create_dir_all(root.join("release")).expect("create release dir");
    std::fs::write(
        root.join("release/product-proof.toml"),
        "status = \"accepted\"\n[[components]\n",
    )
    .expect("write malformed product proof manifest");

    assert_product_proof_matrix_invalid_manifest(&root, "failed to parse");

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_matrix_fails_closed_on_manifest_read_error() {
    let root = temp_root("product-proof-matrix-manifest-read-error");
    std::fs::create_dir_all(root.join("release/product-proof.toml"))
        .expect("create manifest path as directory");

    assert_product_proof_matrix_invalid_manifest(&root, "failed to read");

    let _ = std::fs::remove_dir_all(root);
}

fn assert_product_proof_matrix_invalid_manifest(root: &PathBuf, reason_fragment: &str) {
    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let report = check_product_proof_coverage(root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    let parse_finding = report
        .findings
        .iter()
        .find(|finding| finding.code == "product-proof-manifest-parse")
        .expect("manifest parse/read blocker");
    assert!(
        parse_finding.message.contains(reason_fragment),
        "manifest blocker should describe {reason_fragment}: {:?}",
        report.findings
    );

    let classes = product_proof_evidence_classes(root, &[]);
    assert!(!classes.is_empty());
    assert!(classes.iter().all(|class| {
        class.status == "invalid_manifest"
            && class.reason.as_deref().is_some_and(|reason| reason.contains(reason_fragment))
    }));

    let components = product_proof_components(root, Some(candidate), None);
    assert!(!components.is_empty());
    assert!(components.iter().all(|component| component.status == "invalid_manifest"));
}

#[test]
fn product_proof_rejects_unknown_evidence_class_metadata() {
    let root = temp_root("product-proof-unknown-evidence-class");
    std::fs::create_dir_all(root.join("release")).expect("create release dir");
    std::fs::write(
        root.join("release/product-proof.toml"),
        r#"
[[evidence_classes]]
class = "made-up proof"
status = "accepted"
"#,
    )
    .expect("write product proof manifest");

    let report =
        check_product_proof_coverage(&root, Some("0123456789abcdef0123456789abcdef01234567"), None);
    assert_eq!(report.status, GateStatus::Fail);
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.code == "product-proof-evidence-class-unknown")
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_rejects_legacy_component_aliases() {
    let root = temp_root("product-proof-rejects-legacy-aliases");
    std::fs::create_dir_all(root.join("release")).expect("create release dir");
    let mut manifest = String::new();
    for component in product_proof_component_requirements() {
        let manifest_component = match component.component {
            PRODUCT_COMPONENT_TRUSTC => "trustc/rustc",
            PRODUCT_COMPONENT_TARGO => "targo/cargo",
            other => other,
        };
        manifest.push_str("[[components]]\n");
        manifest.push_str(&format!("component = {manifest_component:?}\n"));
        manifest.push_str("status = \"blocked\"\n");
        manifest.push_str("reason = \"release evidence has not been produced\"\n\n");
    }
    std::fs::write(root.join("release/product-proof.toml"), manifest)
        .expect("write product proof manifest");

    let report =
        check_product_proof_coverage(&root, Some("0123456789abcdef0123456789abcdef01234567"), None);
    assert_eq!(report.status, GateStatus::Fail);
    assert!(
        report.findings.iter().any(|finding| finding.code == "product-proof-component-missing")
    );

    let components =
        product_proof_components(&root, Some("0123456789abcdef0123456789abcdef01234567"), None);
    assert!(components.iter().any(|component| {
        component.component == PRODUCT_COMPONENT_TRUSTC && component.status == "missing_evidence"
    }));
    assert!(components.iter().any(|component| {
        component.component == PRODUCT_COMPONENT_TARGO && component.status == "missing_evidence"
    }));
    assert!(
        components.iter().all(|component| component.component != "trustc/rustc"
            && component.component != "targo/cargo")
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn product_proof_components_downgrade_unvalidated_accepted_claims() {
    let root = temp_root("product-proof-components-downgrade-unvalidated-accepted-claims");
    std::fs::create_dir_all(root.join("release")).expect("create release dir");
    let mut manifest = String::from(
        r#"schema_version = "trust.product-proof-manifest.v1"
status = "accepted"

"#,
    );
    for component in product_proof_component_requirements() {
        manifest.push_str("[[components]]\n");
        manifest.push_str(&format!("component = {:?}\n", component.component));
        if component.component == "binary/decomp gates" {
            manifest.push_str("status = \"accepted\"\n\n");
        } else {
            manifest.push_str("status = \"blocked\"\n");
            manifest.push_str("reason = \"outside focused component matrix regression test\"\n\n");
        }
    }
    std::fs::write(root.join("release/product-proof.toml"), manifest)
        .expect("write product proof manifest");

    let candidate = "0123456789abcdef0123456789abcdef01234567";
    let report = check_product_proof_coverage(&root, Some(candidate), None);
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(report.findings.iter().any(|finding| {
        finding.code == "product-proof-evidence-empty"
            && finding.message.contains("binary/decomp gates")
    }));

    let components = product_proof_components(&root, Some(candidate), None);
    let binary_decomp = components
        .iter()
        .find(|component| component.component == "binary/decomp gates")
        .expect("binary/decomp gates component");
    assert_eq!(binary_decomp.status, "missing_evidence");

    let _ = std::fs::remove_dir_all(root);
}

fn string_args(args: &[&str]) -> Vec<String> {
    args.iter().map(|arg| (*arg).to_string()).collect()
}

fn binary_decomp_required_evidence() -> Vec<&'static str> {
    product_proof_component_requirements()
        .into_iter()
        .find(|component| component.component == "binary/decomp gates")
        .expect("binary/decomp gates component")
        .required_evidence
        .to_vec()
}

fn write_binary_decomp_product_proof_manifest(root: &PathBuf, evidence_path: &str) {
    let mut manifest = String::from(
        r#"schema_version = "trust.product-proof-manifest.v1"
status = "accepted"

"#,
    );
    for component in product_proof_component_requirements() {
        manifest.push_str("[[components]]\n");
        manifest.push_str(&format!("component = {:?}\n", component.component));
        if component.component == "binary/decomp gates" {
            manifest.push_str("status = \"accepted\"\n");
            manifest.push_str("evidence = [\n");
            for evidence_kind in component.required_evidence {
                manifest
                    .push_str(&format!("  {:?},\n", format!("{evidence_kind}:{evidence_path}")));
            }
            manifest.push_str("]\n\n");
        } else {
            manifest.push_str("status = \"blocked\"\n");
            manifest.push_str("reason = \"outside focused binary/decomp digest-binding test\"\n\n");
        }
    }
    std::fs::write(root.join("release/product-proof.toml"), manifest)
        .expect("write product proof manifest");
}

fn write_trustc_identity_product_proof_manifest(root: &PathBuf, evidence_path: &str) {
    let mut manifest = String::from(
        r#"schema_version = "trust.product-proof-manifest.v1"
status = "accepted"

"#,
    );
    for component in product_proof_component_requirements() {
        manifest.push_str("[[components]]\n");
        manifest.push_str(&format!("component = {:?}\n", component.component));
        if component.component == PRODUCT_COMPONENT_TRUSTC {
            manifest.push_str("status = \"accepted\"\n");
            manifest.push_str(&format!(
                "evidence = [{:?}]\n\n",
                format!("trustc -Vv identity:{evidence_path}")
            ));
        } else {
            manifest.push_str("status = \"blocked\"\n");
            manifest
                .push_str("reason = \"outside focused trustc identity materialization test\"\n\n");
        }
    }
    std::fs::write(root.join("release/product-proof.toml"), manifest)
        .expect("write product proof manifest");
}

fn write_product_proof_evidence(
    root: &PathBuf,
    file_name: &str,
    evidence: &serde_json::Value,
) -> String {
    std::fs::create_dir_all(root.join("release/evidence")).expect("create evidence dir");
    let evidence_path = format!("release/evidence/{file_name}");
    let evidence = trusted_product_proof_evidence(root, evidence);
    std::fs::write(
        root.join(&evidence_path),
        serde_json::to_string_pretty(&evidence).expect("render evidence"),
    )
    .expect("write product proof evidence");
    evidence_path
}

fn write_single_evidence_product_proof_manifest(
    root: &PathBuf,
    focused_component: &str,
    evidence_kind: &str,
    evidence_path: &str,
) {
    let mut manifest = String::from(
        r#"schema_version = "trust.product-proof-manifest.v1"
status = "accepted"

"#,
    );
    for component in product_proof_component_requirements() {
        manifest.push_str("[[components]]\n");
        manifest.push_str(&format!("component = {:?}\n", component.component));
        if component.component == focused_component {
            manifest.push_str("status = \"accepted\"\n");
            manifest.push_str(&format!(
                "evidence = [{:?}]\n\n",
                format!("{evidence_kind}:{evidence_path}")
            ));
        } else {
            manifest.push_str("status = \"blocked\"\n");
            manifest.push_str(&format!(
                "reason = \"outside focused {evidence_kind} materialization test\"\n\n"
            ));
        }
    }
    std::fs::write(root.join("release/product-proof.toml"), manifest)
        .expect("write product proof manifest");
}

fn write_multi_evidence_product_proof_manifest(
    root: &PathBuf,
    focused_component: &str,
    evidence_kinds: &[&str],
    evidence_path: &str,
) {
    let mut manifest = String::from(
        r#"schema_version = "trust.product-proof-manifest.v1"
status = "accepted"

"#,
    );
    for component in product_proof_component_requirements() {
        manifest.push_str("[[components]]\n");
        manifest.push_str(&format!("component = {:?}\n", component.component));
        if component.component == focused_component {
            manifest.push_str("status = \"accepted\"\n");
            manifest.push_str("evidence = [\n");
            for evidence_kind in evidence_kinds {
                manifest
                    .push_str(&format!("  {:?},\n", format!("{evidence_kind}:{evidence_path}")));
            }
            manifest.push_str("]\n\n");
        } else {
            manifest.push_str("status = \"blocked\"\n");
            manifest.push_str(&format!(
                "reason = \"outside focused {focused_component} multi-evidence test\"\n\n"
            ));
        }
    }
    std::fs::write(root.join("release/product-proof.toml"), manifest)
        .expect("write product proof manifest");
}

fn product_proof_artifact_path_text() -> &'static str {
    "release/evidence/artifacts/product-proof-material.bin"
}

fn materialize_product_proof_artifact(root: &PathBuf) -> String {
    let artifact_path = root.join(product_proof_artifact_path_text());
    std::fs::create_dir_all(artifact_path.parent().expect("product-proof artifact parent"))
        .expect("create product-proof artifact parent");
    std::fs::write(&artifact_path, b"materialized product-proof fixture artifact\n")
        .expect("write product-proof artifact");
    file_sha256(&artifact_path).expect("hash product-proof artifact")
}

fn product_proof_results_json() -> serde_json::Value {
    serde_json::json!({
        "proved": 1,
        "total": 1,
        "failed": 0,
        "unknown": 0,
        "by_solver": ["focused-product-proof-test"]
    })
}

fn assert_solver_checklist_only(report: &GateReport, evidence_kind: &str) {
    assert_eq!(report.status, GateStatus::Blocked);
    assert!(
        report.findings.iter().any(|finding| {
            finding.code == "product-proof-solver-evidence-unverified"
                && finding.message.contains(evidence_kind)
                && finding.message.contains("kind-specific Rust collector/replayer")
                && finding.message.contains("exact candidate executable")
        }),
        "self-declared solver evidence must remain checklist-only for `{evidence_kind}`: {:?}",
        report.findings
    );
    assert!(
        report.evidence_refs.is_empty(),
        "unverified solver evidence must not be returned as accepted evidence: {:?}",
        report.evidence_refs
    );
}

fn trusted_product_proof_evidence(
    root: &PathBuf,
    evidence: &serde_json::Value,
) -> serde_json::Value {
    let mut evidence = evidence.clone();
    if let Some(map) = evidence.as_object_mut() {
        map.entry("generated_at".to_string())
            .or_insert_with(|| PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS.into());
        map.entry("runner".to_string()).or_insert_with(product_proof_runner_json);
        if !map.contains_key("proof_artifact_sha256") {
            let artifact_path = product_proof_artifact_path_text();
            let digest = materialize_product_proof_artifact(root);
            map.insert("proof_artifact_path".to_string(), artifact_path.into());
            map.insert("proof_artifact_sha256".to_string(), digest.into());
        }
    }
    evidence
}

fn product_proof_runner_json() -> serde_json::Value {
    serde_json::json!({
        "implementation": "rust",
        "entrypoint": "targo trust release check",
        "python_used": false,
        "tool": "targo-trust",
    })
}

fn release_artifact_binding_json(root: &PathBuf, candidate: &str) -> serde_json::Value {
    let stage2_trustc_path = materialized_stage2_trustc_path(root, candidate);
    let source_tarball_path = materialized_source_tarball_path(root, candidate);
    let stage2_trustc_digest =
        file_sha256(&root.join(&stage2_trustc_path)).expect("hash stage2 trustc fixture");
    let source_tarball_digest =
        file_sha256(&root.join(&source_tarball_path)).expect("hash source tarball fixture");
    serde_json::json!({
        "schema_version": "trust.product-proof-release-binding.v1",
        "candidate_commit": candidate,
        "stage2_trustc": {
            "name": "trustc",
            "stage": "stage2",
            "path": stage2_trustc_path,
            "sha256": stage2_trustc_digest,
            "executable": true,
            "version": "trustc 1.96.0-trust",
            "commit_hash": candidate,
            "candidate_commit": candidate,
        },
        "source_tarball": {
            "path": source_tarball_path,
            "sha256": source_tarball_digest,
            "candidate_commit": candidate,
        }
    })
}

fn materialized_stage2_trustc_path(root: &PathBuf, candidate: &str) -> String {
    let path_text = "build/host/stage2/bin/trustc";
    let path = root.join(path_text);
    std::fs::create_dir_all(path.parent().expect("stage2 trustc parent"))
        .expect("create stage2 trustc parent");
    std::fs::write(
        &path,
        format!(
            "#!/bin/sh\nif [ \"$1\" = \"-Vv\" ]; then\n  echo 'trustc 1.96.0-trust'\n  echo 'commit-hash: {candidate}'\nelse\n  echo 'trustc 1.96.0-trust'\nfi\n"
        ),
    )
    .expect("write stage2 trustc fixture");
    make_executable(&path);
    path_text.to_string()
}

fn materialized_source_tarball_path(root: &PathBuf, candidate: &str) -> String {
    let path_text = "dist/trust-src-1.96.0-trust.tar.xz";
    let path = root.join(path_text);
    std::fs::create_dir_all(path.parent().expect("source tarball parent"))
        .expect("create source tarball parent");
    let mut bytes = vec![0xfd, b'7', b'z', b'X', b'Z', 0x00];
    bytes.extend_from_slice(
        format!("materialized trust source tarball fixture for {candidate}\n").as_bytes(),
    );
    std::fs::write(&path, bytes).expect("write source tarball fixture");
    path_text.to_string()
}

#[cfg(unix)]
fn make_executable(path: &Path) {
    use std::os::unix::fs::PermissionsExt;

    let mut permissions = std::fs::metadata(path).expect("stage2 trustc metadata").permissions();
    permissions.set_mode(0o755);
    std::fs::set_permissions(path, permissions).expect("chmod stage2 trustc fixture");
}

#[cfg(not(unix))]
fn make_executable(_path: &Path) {}

fn materialized_trust_tool_identity_json(
    root: &PathBuf,
    name: &str,
    commit_hash: Option<&str>,
) -> serde_json::Value {
    let path_text = format!("release/evidence/tools/{name}");
    let path = root.join(&path_text);
    std::fs::create_dir_all(path.parent().expect("tool identity parent"))
        .expect("create tool identity parent");
    #[cfg(unix)]
    if name == "trustd" {
        let commit = commit_hash.expect("materialized trustd identity requires commit hash");
        write_native_trustd_test_file(&path, commit, false);
        let digest = file_sha256(&path).expect("hash native trustd identity fixture");
        return trust_tool_identity_json(name, &path_text, &digest, commit_hash);
    }
    let contents = format!("materialized Trust tool fixture: {name}\n");
    write_executable_test_file(&path, contents.as_bytes());
    let digest = file_sha256(&path).expect("hash tool identity fixture");
    trust_tool_identity_json(name, &path_text, &digest, commit_hash)
}

#[cfg(unix)]
fn write_native_trustd_test_file(path: &Path, commit: &str, reject_loader_env: bool) {
    assert!(
        commit.len() == 40
            && commit
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "native trustd fixture requires a canonical candidate commit"
    );
    let source_path = path.with_extension("fixture.c");
    let source = r#"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
    const char *ld = getenv("LD_LIBRARY_PATH");
    const char *dyld = getenv("DYLD_LIBRARY_PATH");
    if (__REJECT_LOADER_ENV__
        && ((ld != NULL && strstr(ld, "attacker-controlled") != NULL)
            || (dyld != NULL && strstr(dyld, "attacker-controlled") != NULL))) {
        fputs("ambient loader path inherited\n", stderr);
        return 97;
    }
    if (argc != 2 || strcmp(argv[1], "--version") != 0) {
        return 2;
    }
    puts("trustd 1.96.0-trust");
    puts("trust.identity=trustd");
    puts("trust.protocol=__PROTOCOL__");
    puts("commit-hash: __COMMIT__");
    return 0;
}
"#
    .replace(
        "__REJECT_LOADER_ENV__",
        if reject_loader_env { "1" } else { "0" },
    )
    .replace("__PROTOCOL__", trust_router::coordinator::STATUS_VERSION)
    .replace("__COMMIT__", commit);
    std::fs::write(&source_path, source).expect("write native trustd fixture source");
    let compiler = if Path::new("/usr/bin/cc").is_file() { "/usr/bin/cc" } else { "cc" };
    let mut command = std::process::Command::new(compiler);
    command
        .args(["-std=c11", "-O0", "-o"])
        .arg(path)
        .arg(&source_path)
        .env_remove("LD_LIBRARY_PATH")
        .env_remove("DYLD_LIBRARY_PATH");
    let output = command.output().expect("compile native trustd fixture");
    assert!(
        output.status.success(),
        "native trustd fixture compilation failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::remove_file(source_path).expect("remove native trustd fixture source");
}

fn materialized_version_identity_json(
    root: &PathBuf,
    candidate: &str,
    daemon_identity: serde_json::Value,
) -> serde_json::Value {
    serde_json::json!({
        "product": "Trust",
        "toolchain_alias": "trust",
        "trust_product_version": "0.1.0",
        "candidate_commit": candidate,
        "candidate_command_version": 1,
        "tools": {
            "frontend": materialized_trust_tool_identity_json(root, "targo", None),
            "extension": materialized_trust_tool_identity_json(root, "targo-trust", None),
            "compiler": materialized_trust_tool_identity_json(
                root,
                "trustc",
                Some(candidate),
            ),
            "daemon": daemon_identity,
        }
    })
}

fn candidate_daemon_from_json(root: &Path, identity: &serde_json::Value) -> BoundToolIdentity {
    let path_text = identity["path"].as_str().expect("daemon identity path");
    let path = root
        .join(path_text)
        .canonicalize()
        .expect("canonical daemon identity path");
    BoundToolIdentity {
        name: "trustd".to_string(),
        path: Some(path.display().to_string()),
        sha256: Some(identity["sha256"].as_str().expect("daemon identity digest").to_string()),
        executable: Some(true),
        version: Some(identity["version"].as_str().expect("daemon identity version").to_string()),
        commit_hash: Some(
            identity["commit_hash"].as_str().expect("daemon identity commit").to_string(),
        ),
        rust_compat_version: None,
        resolution: Some("bound-executable".to_string()),
        rejected_inherited_name: None,
        rejected_path: None,
    }
}

#[cfg(target_os = "macos")]
fn fabricated_trustd_protocol_evidence(
    root: &PathBuf,
    candidate: &str,
) -> (serde_json::Value, BoundToolIdentity) {
    let tool_identity = materialized_trust_tool_identity_json(root, "trustd", Some(candidate));
    let candidate_daemon = candidate_daemon_from_json(root, &tool_identity);
    let tool_sha256 = tool_identity["sha256"].as_str().expect("tool digest");
    let identity_response = serde_json::json!({
        "version": trust_router::coordinator::IDENTITY_VERSION,
        "protocol": trust_router::coordinator::STATUS_VERSION,
        "release": "1.96.0-trust",
        "commit": candidate,
        "executable_sha256": tool_sha256,
    });
    let status_before = serde_json::json!({
        "version": trust_router::coordinator::STATUS_VERSION,
        "budget_bytes": 1024,
        "reserved_bytes": 0,
        "free_bytes": 1024,
        "queue_depth": 0,
        "granted_total": 0,
        "released_total": 0,
        "started_at": 1,
        "active": [],
    });
    let status_reserved = serde_json::json!({
        "version": trust_router::coordinator::STATUS_VERSION,
        "budget_bytes": 1024,
        "reserved_bytes": 1,
        "free_bytes": 1023,
        "queue_depth": 0,
        "granted_total": 1,
        "released_total": 0,
        "started_at": 1,
        "active": [{
            "pid": 123,
            "bytes": 1,
            "label": "product-proof-live-smoke",
            "since_secs": 0,
            "token": 1,
        }],
    });
    let status_released = serde_json::json!({
        "version": trust_router::coordinator::STATUS_VERSION,
        "budget_bytes": 1024,
        "reserved_bytes": 0,
        "free_bytes": 1024,
        "queue_depth": 0,
        "granted_total": 1,
        "released_total": 1,
        "started_at": 1,
        "active": [],
    });
    let transcript_path = "release/evidence/trustd-protocol.transcript";
    let transcript = format!(
        "> PING\n< PONG\n> IDENTITY\n< {}\n> STATUS\n< {}\n> RESERVE 1 123 product-proof-live-smoke\n< GRANTED 1\n> STATUS\n< {}\n> RELEASE 1\n< OK\n> STATUS\n< {}\n",
        serde_json::to_string(&identity_response).expect("identity JSON"),
        serde_json::to_string(&status_before).expect("status before JSON"),
        serde_json::to_string(&status_reserved).expect("status reserved JSON"),
        serde_json::to_string(&status_released).expect("status released JSON")
    );
    std::fs::create_dir_all(root.join("release/evidence")).expect("create evidence dir");
    std::fs::write(root.join(transcript_path), transcript).expect("write transcript");
    let transcript_sha256 = file_sha256(&root.join(transcript_path)).expect("transcript digest");
    let runtime_closure =
        inspect_trustd_runtime_closure(&std::env::current_exe().expect("current test executable"))
            .expect("inspect test executable runtime closure");
    let evidence = serde_json::json!({
        "schema_version": "trust.product-proof.v1",
        "evidence_kind": "Trust daemon protocol smoke",
        "candidate_commit": candidate,
        "operational_checks": {
            "ping": true,
            "identity": true,
            "status": true,
            "reserve": true,
            "release": true,
        },
        "runtime_closure": runtime_closure,
        "tool_identity": tool_identity,
        "trustd_protocol_smoke": {
            "requests": ["PING", "IDENTITY", "STATUS", "RESERVE", "STATUS", "RELEASE", "STATUS"],
            "ping_response": "PONG",
            "reservation_bytes": 1,
            "reservation_label": "product-proof-live-smoke",
            "reservation_pid": 123,
            "reservation_token": 1,
            "identity_response": identity_response,
            "status_before": status_before,
            "status_reserved": status_reserved,
            "status_released": status_released,
            "transcript_path": transcript_path,
            "transcript_sha256": transcript_sha256,
        },
    });
    (evidence, candidate_daemon)
}

fn unmaterialized_trust_tool_identity_json(
    name: &str,
    digest: &str,
    commit_hash: Option<&str>,
) -> serde_json::Value {
    trust_tool_identity_json(name, &format!("/tmp/trust/bin/{name}"), digest, commit_hash)
}

fn trust_tool_identity_json(
    name: &str,
    path: &str,
    digest: &str,
    commit_hash: Option<&str>,
) -> serde_json::Value {
    let mut identity = serde_json::Map::new();
    identity.insert("name".to_string(), name.into());
    identity.insert("path".to_string(), path.into());
    identity.insert("sha256".to_string(), digest.into());
    identity.insert("executable".to_string(), true.into());
    identity.insert("version".to_string(), format!("{name} 1.96.0-trust").into());
    if let Some(commit_hash) = commit_hash {
        identity.insert("commit_hash".to_string(), commit_hash.into());
    }
    serde_json::Value::Object(identity)
}

fn compile_back_digest_diagnostics(digest: &str) -> Vec<String> {
    [
        "compile-back-lifted-binary-trust_ir-sha256",
        "compile-back-rust-source-sha256",
        "compile-back-reconstructed-trust_ir-sha256",
        "compile-back-refinement-artifact-sha256",
        "compile-back-root-artifact-sha256",
        "compile-back-selected-image-sha256",
    ]
    .into_iter()
    .map(|prefix| format!("{prefix}={digest}"))
    .chain(["compile-back-selected-image-range=0..16".to_string()])
    .collect()
}

fn compile_back_digest_binding(root: &PathBuf, selected_image_range: &str) -> serde_json::Value {
    let artifact_path = compile_back_artifact_path_text();
    let digest = materialize_compile_back_artifact(root);
    serde_json::json!({
        "lifted_binary_trust_ir_sha256": &digest,
        "lifted_binary_trust_ir_path": artifact_path,
        "rust_source_sha256": &digest,
        "rust_source_path": artifact_path,
        "reconstructed_trust_ir_sha256": &digest,
        "reconstructed_trust_ir_path": artifact_path,
        "refinement_artifact_sha256": &digest,
        "refinement_artifact_path": artifact_path,
        "root_artifact_sha256": &digest,
        "root_artifact_path": artifact_path,
        "selected_image_sha256": &digest,
        "selected_image_path": artifact_path,
        "selected_image_range": selected_image_range,
    })
}

fn compile_back_artifact_path_text() -> &'static str {
    "release/evidence/artifacts/compile-back-material.bin"
}

fn materialize_compile_back_artifact(root: &PathBuf) -> String {
    let artifact_path = root.join(compile_back_artifact_path_text());
    std::fs::create_dir_all(artifact_path.parent().expect("compile-back artifact parent"))
        .expect("create compile-back artifact parent");
    std::fs::write(&artifact_path, b"materialized compile-back proof artifact fixture\n")
        .expect("write compile-back artifact");
    file_sha256(&artifact_path).expect("hash compile-back artifact")
}

fn temp_root(label: &str) -> PathBuf {
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).expect("system time").as_nanos();
    let root = std::env::temp_dir()
        .join(format!("targo-trust-release-cli-{label}-{}-{nanos}", std::process::id()));
    std::fs::create_dir_all(&root).expect("create temp root");
    root.canonicalize().expect("canonical temp root")
}

fn commit_all(root: &Path, message: &str) {
    run_git(root, &["init"]);
    run_git(root, &["config", "user.email", "trust-tests@example.invalid"]);
    run_git(root, &["config", "user.name", "Trust Tests"]);
    run_git(root, &["add", "."]);
    run_git(root, &["commit", "-m", message]);
}

fn run_git(root: &Path, args: &[&str]) {
    let output = std::process::Command::new("git")
        .arg("-C")
        .arg(root)
        .args(args)
        .output()
        .unwrap_or_else(|err| panic!("run git {}: {err}", args.join(" ")));
    assert!(
        output.status.success(),
        "git {} failed\nstdout:\n{}\nstderr:\n{}",
        args.join(" "),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn test_identity_with_candidate(candidate_commit: &str) -> TrustVersionIdentity {
    TrustVersionIdentity {
        schema_version: trust_version::VERSION_SCHEMA.to_string(),
        product: "Trust".to_string(),
        toolchain_alias: "trust".to_string(),
        trust_product_version: "0.1.0".to_string(),
        trust_product_channel: trust_version::CHANNEL_RELEASE.to_string(),
        rust_upstream_version: "1.99.0".to_string(),
        bootstrap_channel: "trust".to_string(),
        rust_compat_version: "1.99.0-dev".to_string(),
        rust_compat_source: "test".to_string(),
        archive_version: "0.1.0-trust".to_string(),
        rust_alignment: trust_version::RustAlignment {
            rustc_version: "1.99.0".to_string(),
            revision: "rust-lang/rust:5e91de65d75d3c849c643f5079509b9e5985a5c0".to_string(),
            merged_on: "2026-07-08".to_string(),
        },
        candidate_commit: Some(candidate_commit.to_string()),
        commit_date: None,
        host: "test-host".to_string(),
        runner_kind: "test".to_string(),
        candidate_command: "targo trust version --json".to_string(),
        candidate_command_version: CANDIDATE_COMMAND_VERSION,
        tools: BoundTools {
            frontend: BoundToolIdentity::missing("targo"),
            extension: BoundToolIdentity::missing("targo-trust"),
            compiler: BoundToolIdentity::missing("trustc"),
            documentation: BoundToolIdentity::missing("trustdoc"),
            formatter: BoundToolIdentity::missing("trustfmt"),
            cargo_formatter: BoundToolIdentity::missing("targo-fmt"),
            tippy: BoundToolIdentity::missing("tippy"),
            targo_tippy: BoundToolIdentity::missing("targo-tippy"),
            tippy_driver: BoundToolIdentity::missing("tippy-driver"),
            analyzer: BoundToolIdentity::missing("trust-analyzer"),
            daemon: BoundToolIdentity::missing("trustd"),
            miri: BoundToolIdentity::missing("trust-miri"),
            targo_miri: BoundToolIdentity::missing("targo-miri"),
        },
        schemas: Default::default(),
        stage0: None,
        components: Vec::new(),
    }
}

fn bound_test_tool(name: &str) -> BoundToolIdentity {
    BoundToolIdentity {
        name: name.to_string(),
        path: Some(format!("/tmp/trust/bin/{name}")),
        sha256: Some("a".repeat(64)),
        executable: Some(true),
        version: Some(format!("{name} 1.96.0-trust")),
        commit_hash: matches!(name, "trustc" | "trustd").then(|| "abcdef1234567890".to_string()),
        rust_compat_version: None,
        resolution: Some("bound-executable".to_string()),
        rejected_inherited_name: None,
        rejected_path: None,
    }
}

fn bind_required_test_tools(identity: &mut TrustVersionIdentity) {
    identity.tools.frontend = bound_test_tool("targo");
    identity.tools.extension = bound_test_tool("targo-trust");
    identity.tools.compiler = bound_test_tool("trustc");
    identity.tools.documentation = bound_test_tool("trustdoc");
    identity.tools.formatter = bound_test_tool("trustfmt");
    identity.tools.cargo_formatter = bound_test_tool("targo-fmt");
    identity.tools.tippy = bound_test_tool("tippy");
    identity.tools.targo_tippy = bound_test_tool("targo-tippy");
    identity.tools.tippy_driver = bound_test_tool("tippy-driver");
    identity.tools.analyzer = bound_test_tool("trust-analyzer");
    identity.tools.daemon = bound_test_tool("trustd");
}

fn materialize_bound_required_test_tools(
    identity: &mut TrustVersionIdentity,
    sysroot: &Path,
) -> PathBuf {
    bind_required_test_tools(identity);
    let bin = sysroot.join("bin");
    std::fs::create_dir_all(&bin).expect("create canonical toolchain bin");
    for tool in [
        &mut identity.tools.frontend,
        &mut identity.tools.extension,
        &mut identity.tools.compiler,
        &mut identity.tools.documentation,
        &mut identity.tools.formatter,
        &mut identity.tools.cargo_formatter,
        &mut identity.tools.tippy,
        &mut identity.tools.targo_tippy,
        &mut identity.tools.tippy_driver,
        &mut identity.tools.analyzer,
        &mut identity.tools.daemon,
    ] {
        let path = bin.join(&tool.name);
        write_executable_test_file(&path, b"canonical Trust tool fixture\n");
        tool.sha256 = file_sha256(&path);
        tool.path = Some(path.display().to_string());
    }
    for alias in ["rustc", "cargo"] {
        write_executable_test_file(&bin.join(alias), b"canonical Trust tool fixture\n");
    }
    bin
}

fn write_executable_test_file(path: &Path, bytes: &[u8]) {
    std::fs::write(path, bytes).expect("write executable test fixture");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        let mut permissions = std::fs::metadata(path).expect("test fixture metadata").permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(path, permissions).expect("mark test fixture executable");
    }
}
