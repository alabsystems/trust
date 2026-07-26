//! `public-distribution-cull-smoke` — check named culled machinery stays absent.
//!
//! This is a negative source-tree name/path diagnostic only. It does not build
//! or inspect distribution roots, artifact manifests, checksums, signatures,
//! or installation contents, and must never satisfy canonical
//! `public-distribution` release evidence.
//!
//! Commit `734c12188e7` ("Cull obsolete scripts, release metadata, and
//! workflows") and `8c9a3d01bb2` ("Cull stale e2e gates and publication-v3
//! test wrappers") deleted the entire public-distribution promotion machinery:
//! the two CI workflows, the dscan/dpub/publication-v3 producer + validator
//! scripts, the owned-dependency / public-engine / public-mirror tooling, the
//! `release/product-proof.toml` + `release/publication-ledger.toml` promotion
//! ledgers, and the `tests/e2e_public_distribution_roots.sh` / `publication_v3_*`
//! CLI test wrappers.
//!
//! Per `docs/testing-strategy.md` this gate "needs design, not porting": there
//! is no shell gate to translate line-for-line, and that doc forbids promoting
//! fake / manual / stub evidence into a passing dimension. So this is a *real*
//! current-state property, not a rigged pass: it asserts that none of those
//! deleted artifacts have crept back into the working tree, and that no source
//! file re-introduces the forbidden machinery under an active-code location.
//!
//! Scope discipline (why this is not over-broad, and not fake-narrow):
//!
//! * The gate protects against resurrection of **executable machinery** and
//!   **release-ledger metadata** — files that carry promotion/publication
//!   authority (`.sh`/`.py`/`.yml`/`.yaml`/`.rs`/`.toml` under `scripts/`,
//!   `.github/`, `release/`, top-level `tests/*.sh`, and `*/tests/`).
//! * `release/internal-repo-versions.toml` and `release/trust-version.toml`
//!   are **deliberately not** treated as forbidden. Although `734c12188e7`
//!   deleted them, a later reviewed commit (`13916beab1d`) intentionally
//!   re-created them as the live version-CLI / release-CLI skeleton; they are
//!   referenced today by `crates/trust-release`, `crates/trust-deps`, and
//!   `targo-trust/src/release_cli/gates.rs`. Flagging live config would make
//!   this a gate rigged to *fail*, which is as dishonest as one rigged to pass.
//!   The publication ledgers the audit actually forbade — `product-proof.toml`
//!   and `publication-ledger.toml` — are asserted absent below.
//! * `tests/e2e_trust_dist_artifacts.sh` is also deliberately allowed. It was
//!   restored as the local, no-upload prepublish receipt producer and explicitly
//!   claims no hosted channel, signature, notarization, or public availability.
//!   Treating that local archive/install rehearsal as public-promotion machinery
//!   would make this diagnostic fail on the evidence path it is meant to keep
//!   distinct from publication.
//! * Inert example fixtures under `tests/fixtures/**` (static `.json` data with
//!   no executable or promotion authority, never deleted by the cull) are out
//!   of scope: they are not "scripts" and cannot promote anything. The machinery
//!   extension filter excludes `.json`, so they never trip the scan.
//!
//! A present forbidden artifact is a genuine regression in every mode, so it
//! fails the gate regardless of `policy`. `policy.strict` / `policy.release`
//! only govern the fail-closed guards (an unreadable directory or a root that
//! does not authenticate as a Trust checkout is a "cannot verify", never a
//! silent pass).

use std::fs;
use std::io;
use std::path::Path;

use anyhow::{Context, Result, bail};

use super::{GatePolicy, section};

/// Exact machinery paths deleted by the two cull commits (the public-distribution
/// subsystem subset). Each must stay absent from the working tree. The renamed
/// `tcargo-trust -> targo-trust` spellings of the CLI test wrappers are both
/// listed so a resurrection under either crate name is caught.
const FORBIDDEN_ABSENT_PATHS: &[&str] = &[
    // CI workflows.
    ".github/workflows/public-distribution.yml",
    ".github/workflows/publication-v3.yml",
    // Release-gate publication ledgers (the promotion metadata, not the live
    // version/internal-repo skeleton restored post-cull).
    "release/product-proof.toml",
    "release/publication-ledger.toml",
    // dscan / dpub / publication-v3 producer + validator scripts.
    "scripts/produce_dscan_attestation.py",
    "scripts/produce_publication_v3_draft_scaffold.py",
    "scripts/produce_publication_v3_release_inputs.py",
    "scripts/validate_dpub_publication.py",
    "scripts/validate_dscan_admission.py",
    "scripts/validate_dscan_trust_engines_report.py",
    "scripts/validate_publication_v3_admission_link.py",
    "scripts/validate_publication_v3_release_gate.py",
    "scripts/validate_publication_v3_schemas.py",
    "scripts/generate_dpub_publication_plan.py",
    // Public-engine / public-mirror / owned-dependency / product-surface tooling
    // culled in the same audit.
    "scripts/check_l45_public_mirror_permissions.py",
    "scripts/derive_public_engine_package_admission.py",
    "scripts/validate_public_engine_package_inputs.py",
    "scripts/check_owned_dependency_import_readiness.py",
    "scripts/check_owned_dependency_public_archives.py",
    "scripts/check_owned_dependency_remote_alignment.py",
    "scripts/import_owned_dependency_snapshots.py",
    "scripts/upstream_owned_dependency_matrix.py",
    "scripts/validate_owned_dependency_metadata.py",
    "scripts/trust_product_surface_audit.py",
    // Promotion shell drivers.
    "scripts/prepare_public_distribution_promotion.sh",
    "scripts/promote_public_distribution.sh",
    // e2e shell gates + publication-v3 CLI test wrappers (both crate spellings).
    "tests/e2e_public_distribution_roots.sh",
    "tests/e2e_internal_repo_public_versions.sh",
    "tcargo-trust/tests/publication_v3_release_gate_cli.rs",
    "tcargo-trust/tests/publication_v3_release_inputs_cli.rs",
    "targo-trust/tests/publication_v3_release_gate_cli.rs",
    "targo-trust/tests/publication_v3_release_inputs_cli.rs",
];

/// Directories scanned for a re-introduced machinery file, with whether the
/// walk recurses. `tests/` is scanned top-level only: the deleted e2e gates
/// lived directly under `tests/`, and recursing would drag in the 20K+-file
/// `tests/ui` / `tests/fixtures` trees (the latter is inert data, out of scope).
const SCAN_LOCATIONS: &[(&str, bool)] = &[
    ("scripts", true),
    (".github", true),
    ("release", true),
    ("targo-trust/tests", true),
    ("tcargo-trust/tests", true),
    ("tests", false),
];

/// Extensions that carry executable or release-metadata authority. `.json`
/// (example fixtures) is intentionally excluded — inert data cannot promote.
const MACHINERY_EXTENSIONS: &[&str] = &[".sh", ".py", ".yml", ".yaml", ".rs", ".toml"];

/// Basename tokens that mark the culled subsystem. Deliberately specific
/// (`publication-v3`, not bare `publication`) so live release-CLI modules such
/// as `release_cli/publication.rs` / `product_proof.rs` — which live under
/// `src/` and are never in a scan location — could not be mistaken for it.
const FORBIDDEN_NAME_TOKENS: &[&str] = &[
    "dscan",
    "dpub",
    "publication-v3",
    "publication_v3",
    "publication-ledger",
    "publication_ledger",
    "public-distribution",
    "public_distribution",
    "public-engine",
    "public_engine",
    "public-mirror",
    "public_mirror",
    "product-proof",
    "product_proof",
    "product-surface",
    "product_surface",
    "owned-dependency",
    "owned_dependency",
];

/// Upper bound on files inspected across all scan locations. The targeted
/// directories are small; a wildly larger count means we are pointed at an
/// unexpected tree and should fail closed rather than churn.
const MAX_SCANNED_FILES: usize = 50_000;

pub(super) fn run(root: &Path, policy: GatePolicy) -> Result<()> {
    section("public-distribution cull smoke (non-authoritative)");
    println!(
        "Property: the culled publication / dscan / dpub / public-distribution machinery (workflows, promotion + validation scripts, release ledgers, e2e/CLI test wrappers) stays absent."
    );
    println!("Mode: strict={} release={}", policy.strict, policy.release);

    authenticate_repo_root(root)?;

    let mut violations: Vec<String> = Vec::new();

    // 1. Every exact deleted machinery path must stay absent. A read error other
    //    than NotFound is a "cannot verify", so it fails closed.
    for relative in FORBIDDEN_ABSENT_PATHS {
        match fs::symlink_metadata(root.join(relative)) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => {
                bail!("could not determine whether {relative} is absent: {error}");
            }
            Ok(_) => {
                violations.push(format!("resurrected culled artifact: {relative}"));
            }
        }
    }

    // 2. No re-introduced machinery file under any active-code scan location.
    let mut budget = MAX_SCANNED_FILES;
    for (location, recursive) in SCAN_LOCATIONS {
        let dir = root.join(location);
        match fs::symlink_metadata(&dir) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => bail!("could not inspect scan location {location}: {error}"),
            Ok(metadata) if metadata.file_type().is_symlink() => {
                bail!("scan location {location} is a symlink; refusing to trust it");
            }
            Ok(metadata) if !metadata.file_type().is_dir() => {
                bail!("scan location {location} is not a directory");
            }
            Ok(_) => {}
        }
        scan_location(&dir, *recursive, location, &mut budget, &mut violations)?;
    }

    if !violations.is_empty() {
        violations.sort();
        violations.dedup();
        for violation in &violations {
            eprintln!("FAIL: {violation}");
        }
        bail!(
            "public-distribution cull regressed: {} forbidden artifact(s) present; the publication/dscan/dpub subsystem must remain culled",
            violations.len()
        );
    }

    println!(
        "PASS: {} exact machinery paths confirmed absent; no re-introduced machinery under {} scan location(s).",
        FORBIDDEN_ABSENT_PATHS.len(),
        SCAN_LOCATIONS.len()
    );
    println!(
        "SMOKE ONLY: canonical public-distribution remains blocked until actual distribution roots and artifacts are built and authenticated."
    );
    Ok(())
}

/// Fail closed unless `root` authenticates as a real Trust checkout. Without a
/// recognizable tree, "the artifacts are absent" would be a vacuous pass — the
/// artifacts are absent because *everything* is.
fn authenticate_repo_root(root: &Path) -> Result<()> {
    let x_py = root.join("x.py");
    if !fs::symlink_metadata(&x_py).map(|m| m.file_type().is_file()).unwrap_or(false) {
        bail!(
            "cannot verify the public-distribution cull: {} is not a Trust checkout (missing x.py)",
            root.display()
        );
    }
    let scripts = root.join("scripts");
    if !fs::symlink_metadata(&scripts).map(|m| m.file_type().is_dir()).unwrap_or(false) {
        bail!(
            "cannot verify the public-distribution cull: {} has no scripts/ directory to inspect",
            root.display()
        );
    }
    Ok(())
}

/// Walk `dir` (recursing only when asked) and record entries whose basename is
/// a machinery name. Any symlink fails closed: following it escapes the exact
/// tree, while merely pruning it would leave the hidden subtree unproved.
fn scan_location(
    dir: &Path,
    recursive: bool,
    label: &str,
    budget: &mut usize,
    violations: &mut Vec<String>,
) -> Result<()> {
    let entries =
        fs::read_dir(dir).with_context(|| format!("failed to read scan location {label}"))?;
    for entry in entries {
        let entry = entry.with_context(|| format!("failed to read an entry under {label}"))?;
        if *budget == 0 {
            bail!(
                "public-distribution scan exceeded {MAX_SCANNED_FILES} files under {label}; refusing to continue on an unexpected tree"
            );
        }
        *budget -= 1;

        let path = entry.path();
        let file_type =
            entry.file_type().with_context(|| format!("failed to inspect {}", path.display()))?;

        let name = match path.file_name().and_then(|name| name.to_str()) {
            Some(name) => name,
            None => bail!(
                "public-distribution cull scan cannot classify non-UTF-8 entry: {}",
                path.display()
            ),
        };

        if file_type.is_symlink() {
            bail!(
                "public-distribution cull scan encountered a symlink and cannot prove the subtree/name inventory: {}",
                path.display()
            );
        }

        if is_machinery_name(name) && !file_type.is_dir() {
            violations.push(format!("re-introduced machinery file: {}", path.display()));
        }

        if recursive && file_type.is_dir() {
            let child_label = format!("{label}/{name}");
            scan_location(&path, true, &child_label, budget, violations)?;
        }
    }
    Ok(())
}

/// A machinery name is a basename that both carries a machinery extension and
/// contains a forbidden subsystem token (case-insensitive).
fn is_machinery_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    let has_machinery_ext = MACHINERY_EXTENSIONS.iter().any(|ext| lower.ends_with(ext));
    if !has_machinery_ext {
        return false;
    }
    FORBIDDEN_NAME_TOKENS.iter().any(|token| lower.contains(token))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn machinery_names_are_flagged() {
        assert!(is_machinery_name("validate_dscan_admission.py"));
        assert!(is_machinery_name("produce_publication_v3_release_inputs.py"));
        assert!(is_machinery_name("public-distribution.yml"));
        assert!(is_machinery_name("publication-v3.yml"));
        assert!(is_machinery_name("prepare_public_distribution_promotion.sh"));
        assert!(is_machinery_name("publication_v3_release_gate_cli.rs"));
        assert!(is_machinery_name("product-proof.toml"));
        assert!(is_machinery_name("publication-ledger.toml"));
        assert!(is_machinery_name("generate_dpub_publication_plan.py"));
        assert!(is_machinery_name("check_owned_dependency_public_archives.py"));
        // Case-insensitive.
        assert!(is_machinery_name("Validate_DScan_Admission.PY"));
    }

    #[test]
    fn inert_and_live_files_are_not_flagged() {
        // Live release-CLI skeleton restored post-cull — must NOT be flagged.
        assert!(!is_machinery_name("internal-repo-versions.toml"));
        assert!(!is_machinery_name("trust-version.toml"));
        // Inert example fixtures are .json — excluded by the extension filter.
        assert!(!is_machinery_name("dscan-attestation.example.json"));
        assert!(!is_machinery_name("dpub-release-ledger.example.json"));
        assert!(!is_machinery_name("dscan-trust-engines.example.json"));
        // Ordinary repo files with no forbidden token.
        assert!(!is_machinery_name("lib.rs"));
        assert!(!is_machinery_name("FUNDING.yml"));
        assert!(!is_machinery_name("recreate_bootstrap.py"));
        // Bare "publication"/"product" is not a token — live release_cli modules
        // (never in a scan location) stay clear even by name.
        assert!(!is_machinery_name("publication.rs"));
    }

    #[test]
    fn exact_absent_list_has_no_live_release_config() {
        // Guard the scope decision: the live skeleton must never appear in the
        // must-be-absent list.
        assert!(!FORBIDDEN_ABSENT_PATHS.contains(&"release/internal-repo-versions.toml"));
        assert!(!FORBIDDEN_ABSENT_PATHS.contains(&"release/trust-version.toml"));
        // The forbidden publication ledgers must be present in the list.
        assert!(FORBIDDEN_ABSENT_PATHS.contains(&"release/product-proof.toml"));
        assert!(FORBIDDEN_ABSENT_PATHS.contains(&"release/publication-ledger.toml"));
    }
}
