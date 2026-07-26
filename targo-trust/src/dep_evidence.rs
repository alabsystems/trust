// The proof-aware dependency lane: the per-package evidence record `targo
// package` ships and `[trust] require_dep_evidence` reads.
//
// A Trust build knows a great deal about the crate in front of it and nothing
// at all about the 200 crates underneath it. `.trust/proof.cert` is the file
// that closes that gap by carrying, in the published tarball, the verdict
// distribution a verification run actually produced for that exact package.
//
// THREE THINGS THIS RECORD IS NOT, stated here because a file named
// `proof.cert` invites all three readings:
//
//   1. It is not a proof. It is a RECORD of a proof run — the counts, the
//      report digest, and the toolchain identity. `AUTHORITY` says so in the
//      file itself, and every consumer prints it.
//   2. It is not independently verifiable by the packaging step. `targo
//      package` is a courier: it copies bytes it cannot judge, exactly as it
//      does for `.cargo_vcs_info.json`. Judging happens on the targo-trust
//      side, where the signing chain (`trust-proof-cert`) lives.
//   3. It is not a gate by default. See `DepEvidencePolicy` for why `none` is
//      the considered default rather than an unfinished one.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::config::DepEvidencePolicy;

/// The schema tag every record carries. Consumers reject anything else rather
/// than guessing at an unknown shape.
pub(crate) const PROOF_CERT_SCHEMA: &str = "trust.package.proof-cert.v1";

/// What the record claims, stated verbatim inside the record so a reader who
/// only ever sees the JSON gets the honest reading with it.
pub(crate) const AUTHORITY: &str =
    "a publisher-recorded verdict distribution from one local verification run of this exact \
     package; not an independently checkable proof and not evidence that any consumer re-ran it";

/// The evidence file's path relative to a package root. Also its path inside
/// the published `.crate` tarball — same spelling both places, so a consumer
/// unpacking a crate finds it where a developer left it.
pub(crate) const PROOF_CERT_RELATIVE_PATH: &str = ".trust/proof.cert";

/// The evidence file for a package rooted at `package_root`.
pub(crate) fn proof_cert_path(package_root: &Path) -> PathBuf {
    package_root.join(".trust").join("proof.cert")
}

/// The verdict distribution, copied from the report rather than summarised into
/// a boolean.
///
/// Every one of these is carried separately on purpose. A single `verified:
/// true` would erase the difference between "nothing failed" and "nothing was
/// attempted", and between a clean run and one that leaned on four recorded
/// assumptions — which is precisely the difference a downstream consumer
/// deciding whether to depend on this crate needs to see.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ProofCertTotals {
    /// Obligations the run proved. A blended count: kernel-certified and
    /// solver-trusted proofs both land here, exactly as in the report.
    pub(crate) proved: usize,
    /// Obligations with a counterexample.
    pub(crate) failed: usize,
    /// Obligations that came back unknown or timed out.
    pub(crate) unknown: usize,
    /// Obligations demoted to a runtime check instead of proved statically.
    pub(crate) runtime_checked: usize,
    /// Obligations raised at all.
    pub(crate) total: usize,
    /// Ledger rows the verdict is conditional on. A nonzero count means the run
    /// assumed something it did not prove.
    pub(crate) assumptions: usize,
}

impl ProofCertTotals {
    /// Whether the recorded run is clean: something was attempted, nothing
    /// failed, nothing came back unknown, and nothing was assumed.
    ///
    /// `total == 0` is deliberately NOT clean. A package that raised no
    /// obligations has not been verified; it has been skipped, and the two must
    /// never read the same to a consumer choosing a dependency.
    pub(crate) fn is_clean(&self) -> bool {
        self.total > 0
            && self.failed == 0
            && self.unknown == 0
            && self.runtime_checked == 0
            && self.assumptions == 0
    }
}

/// The `.trust/proof.cert` document.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PackageProofCert {
    /// Always [`PROOF_CERT_SCHEMA`].
    pub(crate) schema: String,
    /// Always [`AUTHORITY`], so the honest reading travels with the bytes.
    pub(crate) authority: String,
    /// The package this record is about. Checked against the package being
    /// packaged, so a record cannot be moved between crates.
    pub(crate) package: String,
    /// The version this record is about. Checked the same way — a record from
    /// the previous release says nothing about this one.
    pub(crate) version: String,
    /// The toolchain that produced it.
    pub(crate) trust_version: String,
    /// sha256 of the canonical JSON report the totals were read from, so the
    /// record can be tied back to the run that produced it.
    pub(crate) report_sha256: String,
    /// The verdict distribution.
    pub(crate) totals: ProofCertTotals,
}

impl PackageProofCert {
    /// Build a record from a finished report.
    pub(crate) fn from_report(
        report: &trust_types::JsonProofReport,
        package: &str,
        version: &str,
        trust_version: &str,
        report_sha256: &str,
    ) -> Self {
        let summary = &report.summary;
        Self {
            schema: PROOF_CERT_SCHEMA.to_string(),
            authority: AUTHORITY.to_string(),
            package: package.to_string(),
            version: version.to_string(),
            trust_version: trust_version.to_string(),
            report_sha256: report_sha256.to_string(),
            totals: ProofCertTotals {
                proved: summary.total_proved,
                failed: summary.total_failed,
                unknown: summary.total_unknown,
                runtime_checked: summary.total_runtime_checked,
                total: summary.total_obligations,
                assumptions: report.assumptions.len(),
            },
        }
    }

    /// Parse and validate a record against the package it is supposed to
    /// describe.
    ///
    /// Both identity checks are load-bearing: a record is a claim about one
    /// name at one version, and the failure mode this prevents — shipping last
    /// release's clean record with this release's code — is the whole reason a
    /// consumer would distrust the mechanism.
    pub(crate) fn parse_for(
        bytes: &[u8],
        package: &str,
        version: &str,
    ) -> Result<Self, ProofCertError> {
        let cert: Self =
            serde_json::from_slice(bytes).map_err(|e| ProofCertError::Malformed(e.to_string()))?;
        if cert.schema != PROOF_CERT_SCHEMA {
            return Err(ProofCertError::Malformed(format!(
                "schema is {:?}, want {PROOF_CERT_SCHEMA:?}",
                cert.schema
            )));
        }
        if cert.package != package || cert.version != version {
            return Err(ProofCertError::WrongPackage {
                found: format!("{} {}", cert.package, cert.version),
                want: format!("{package} {version}"),
            });
        }
        Ok(cert)
    }

    /// The one-line summary `targo tree --proof` prints per node.
    pub(crate) fn describe(&self) -> String {
        let t = &self.totals;
        format!(
            "proved {} / {} (failed {}, unknown {}, runtime-checked {}, assumptions {})",
            t.proved, t.total, t.failed, t.unknown, t.runtime_checked, t.assumptions
        )
    }
}

/// Why a record was not usable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ProofCertError {
    /// No record for this package.
    Absent,
    /// A record exists but does not parse as this schema.
    Malformed(String),
    /// A record exists and describes a different package or version.
    WrongPackage {
        /// What the record says it describes.
        found: String,
        /// What it was asked about.
        want: String,
    },
}

impl std::fmt::Display for ProofCertError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Absent => write!(f, "no {PROOF_CERT_RELATIVE_PATH}"),
            Self::Malformed(detail) => write!(f, "{PROOF_CERT_RELATIVE_PATH} is malformed: {detail}"),
            Self::WrongPackage { found, want } => write!(
                f,
                "{PROOF_CERT_RELATIVE_PATH} describes `{found}`, not `{want}`"
            ),
        }
    }
}

/// Read a package's record, if it has one.
pub(crate) fn read_proof_cert(
    package_root: &Path,
    package: &str,
    version: &str,
) -> Result<PackageProofCert, ProofCertError> {
    let path = proof_cert_path(package_root);
    let bytes = std::fs::read(&path).map_err(|_| ProofCertError::Absent)?;
    PackageProofCert::parse_for(&bytes, package, version)
}

/// One dependency's standing under a policy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DepEvidenceFinding {
    /// The dependency.
    pub(crate) package: String,
    /// The dependency's version.
    pub(crate) version: String,
    /// Why it does not satisfy the policy.
    pub(crate) reason: String,
}

/// Judge one dependency's record against a policy.
///
/// Returns `None` when the dependency satisfies the policy. `None` under
/// [`DepEvidencePolicy::None`] is unconditional and is the point: a project
/// that has not opted in is not billed for the ecosystem's missing
/// certificates.
pub(crate) fn evaluate(
    policy: DepEvidencePolicy,
    package: &str,
    version: &str,
    cert: &Result<PackageProofCert, ProofCertError>,
) -> Option<DepEvidenceFinding> {
    let finding = |reason: String| {
        Some(DepEvidenceFinding {
            package: package.to_string(),
            version: version.to_string(),
            reason,
        })
    };
    match policy {
        DepEvidencePolicy::None => None,
        DepEvidencePolicy::Present => match cert {
            Ok(_) => None,
            Err(e) => finding(e.to_string()),
        },
        DepEvidencePolicy::Verified => match cert {
            Ok(cert) if cert.totals.is_clean() => None,
            Ok(cert) => finding(format!("recorded run is not clean: {}", cert.describe())),
            Err(e) => finding(e.to_string()),
        },
    }
}

// ───────────────────────────────────────────────────────────────────────────
// `targo trust proof-cert`
// ───────────────────────────────────────────────────────────────────────────

/// Read `[package] name` / `version` out of a manifest.
fn package_identity(manifest_path: &Path) -> Result<(String, String), String> {
    let text = std::fs::read_to_string(manifest_path)
        .map_err(|e| format!("{}: {e}", manifest_path.display()))?;
    let doc: toml::Value = text
        .parse()
        .map_err(|e| format!("{}: {e}", manifest_path.display()))?;
    let package = doc
        .get("package")
        .ok_or_else(|| format!("{} has no [package] table", manifest_path.display()))?;
    let field = |key: &str| {
        package
            .get(key)
            .and_then(toml::Value::as_str)
            .map(str::to_string)
            .ok_or_else(|| format!("{} has no literal [package] {key}", manifest_path.display()))
    };
    Ok((field("name")?, field("version")?))
}

/// Derive a record from a report bundle written by `targo trust check/report`.
///
/// # The re-read boundary
///
/// `JsonProofReport`'s own `Deserialize` downgrades every `Proved` row it reads
/// back from disk to `Unknown` and recounts the summary. That is deliberate and
/// correct: replaying a stored report for a fresh unit would be a NEW
/// proof-authority claim, and the type refuses to let a file confer one.
///
/// The consequence for this lane is the load-bearing part. A record derived
/// here can only ever describe the post-downgrade counts, so a report that
/// carried proved rows would produce a record saying it carried none. That is
/// not a useful artifact, and — worse — publishing it would make every
/// verified crate look unverified. So this refuses instead, and names the real
/// remedy: the record has to be minted by the process that HELD the proof
/// authority, inside the run, not reconstructed afterwards from its output.
///
/// What the step still does honestly is derive a record from a report with no
/// proved rows to lose — which is exactly the shape `require_dep_evidence`
/// judges under `present`, and exactly the shape that must never pass
/// `verified`.
pub(crate) fn record_from_report(
    report_json: &Path,
    manifest_path: &Path,
) -> Result<(PathBuf, PackageProofCert), String> {
    let (package, version) = package_identity(manifest_path)?;
    let bytes =
        std::fs::read(report_json).map_err(|e| format!("{}: {e}", report_json.display()))?;
    let report: trust_types::JsonProofReport = serde_json::from_slice(&bytes)
        .map_err(|e| format!("{} is not a Trust proof report: {e}", report_json.display()))?;
    // The report names the crate it verified. If that is not this package, the
    // honest answer is a refusal: a record derived from someone else's run is
    // exactly the false claim this lane exists to avoid.
    if normalize_crate_name(&report.crate_name) != normalize_crate_name(&package) {
        return Err(format!(
            "{} reports on crate `{}`, but {} declares `{package}`",
            report_json.display(),
            report.crate_name,
            manifest_path.display()
        ));
    }
    // The declared count, before the deserializer's downgrade. If it disagrees
    // with what the loaded report now says, this file's proof credit did not
    // survive being read back, and no record derived from it can be honest.
    let declared_proved = serde_json::from_slice::<serde_json::Value>(&bytes)
        .ok()
        .and_then(|v| v.pointer("/summary/total_proved").and_then(serde_json::Value::as_u64))
        .unwrap_or(0);
    if declared_proved > report.summary.total_proved as u64 {
        return Err(format!(
            "{} declares {declared_proved} proved obligations, but reading it back leaves {} — a \
             saved report carries no proof authority, so a record derived from one would \
             understate every verified crate. Mint the record inside the verification run \
             instead.",
            report_json.display(),
            report.summary.total_proved
        ));
    }
    let report_sha256 = trust_types::digest::stable_sha256_hex(&bytes);
    let cert = PackageProofCert::from_report(
        &report,
        &package,
        &version,
        &report.metadata.trust_version,
        &report_sha256,
    );
    let package_root = manifest_path
        .parent()
        .ok_or_else(|| format!("{} has no parent directory", manifest_path.display()))?;
    let path = proof_cert_path(package_root);
    let dir = path.parent().expect("the record path always has a parent");
    std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let serialized = serde_json::to_vec_pretty(&cert)
        .map_err(|e| format!("could not serialize the record: {e}"))?;
    std::fs::write(&path, serialized).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok((path, cert))
}

/// Crate names reach reports with `-` normalized to `_`; compare on the
/// normalized spelling so `my-crate` and `my_crate` are one package.
fn normalize_crate_name(name: &str) -> String {
    name.replace('-', "_")
}

/// Judge every dependency in the resolved graph against the project's
/// configured policy.
///
/// The policy comes from `[trust] require_dep_evidence` in the project's own
/// manifest — a property of the project, not of the invocation, so there is no
/// flag for it (DESIGN_PHILOSOPHY §3). Under the default `none` this walks the
/// graph and reports, which is the useful thing to be able to do before opting
/// in to something stricter.
fn check_dependencies(manifest: &Path) -> Result<(DepEvidencePolicy, Vec<DepEvidenceFinding>), String>
{
    let dir = manifest.parent().unwrap_or(Path::new("."));
    let resolved =
        crate::config::resolve_trust_config(dir, Some(manifest)).map_err(|e| e.to_string())?;
    let policy = resolved.config.require_dep_evidence;
    let args = vec!["--manifest-path".to_string(), manifest.display().to_string()];
    let deps = crate::pipeline::cargo_selection::resolve_dependencies(&args)?;
    let mut findings = Vec::new();
    for dep in deps {
        let cert = read_proof_cert(&dep.root, &dep.name, &dep.version);
        println!(
            "{} {} — {}",
            dep.name,
            dep.version,
            match &cert {
                Ok(cert) => cert.describe(),
                Err(e) => e.to_string(),
            }
        );
        if let Some(finding) = evaluate(policy, &dep.name, &dep.version, &cert) {
            findings.push(finding);
        }
    }
    Ok((policy, findings))
}

/// `targo trust proof-cert <record|show|check>`.
pub(crate) fn run_subcommand(args: &[String]) -> std::process::ExitCode {
    let usage = "usage: targo trust proof-cert record --report <report.json> [--manifest <Cargo.toml>]\n       targo trust proof-cert show [--manifest <Cargo.toml>]\n       targo trust proof-cert check [--manifest <Cargo.toml>]";
    let mut manifest: Option<PathBuf> = None;
    let mut report: Option<PathBuf> = None;
    let verb = args.first().map(String::as_str);
    let mut rest = args.iter().skip(1);
    while let Some(arg) = rest.next() {
        let mut take = |target: &mut Option<PathBuf>, name: &str| match rest.next() {
            Some(value) => {
                *target = Some(PathBuf::from(value));
                Ok(())
            }
            None => Err(format!("{name} needs a path")),
        };
        let outcome = match arg.as_str() {
            "--manifest" => take(&mut manifest, "--manifest"),
            "--report" => take(&mut report, "--report"),
            other => Err(format!("unknown argument `{other}`")),
        };
        if let Err(e) = outcome {
            eprintln!("targo trust proof-cert: {e}\n{usage}");
            return std::process::ExitCode::from(2);
        }
    }
    let manifest = manifest.unwrap_or_else(|| PathBuf::from("Cargo.toml"));

    match verb {
        Some("record") => {
            let Some(report) = report else {
                eprintln!("targo trust proof-cert record: --report is required\n{usage}");
                return std::process::ExitCode::from(2);
            };
            match record_from_report(&report, &manifest) {
                Ok((path, cert)) => {
                    println!("wrote {} — {}", path.display(), cert.describe());
                    println!("authority: {AUTHORITY}");
                    std::process::ExitCode::SUCCESS
                }
                Err(e) => {
                    eprintln!("targo trust proof-cert record: {e}");
                    std::process::ExitCode::from(2)
                }
            }
        }
        Some("show") => {
            let identity = match package_identity(&manifest) {
                Ok(identity) => identity,
                Err(e) => {
                    eprintln!("targo trust proof-cert show: {e}");
                    return std::process::ExitCode::from(2);
                }
            };
            let root = manifest.parent().unwrap_or(Path::new("."));
            match read_proof_cert(root, &identity.0, &identity.1) {
                Ok(cert) => {
                    println!("{} {} — {}", cert.package, cert.version, cert.describe());
                    println!("authority: {AUTHORITY}");
                    std::process::ExitCode::SUCCESS
                }
                Err(e) => {
                    eprintln!("targo trust proof-cert show: {e}");
                    std::process::ExitCode::from(1)
                }
            }
        }
        Some("check") => match check_dependencies(&manifest) {
            Ok((policy, findings)) if findings.is_empty() => {
                println!("dependency evidence policy `{}`: satisfied", policy.name());
                std::process::ExitCode::SUCCESS
            }
            Ok((policy, findings)) => {
                for finding in &findings {
                    eprintln!(
                        "targo trust proof-cert: {} {} does not satisfy `{}`: {}",
                        finding.package,
                        finding.version,
                        policy.name(),
                        finding.reason
                    );
                }
                std::process::ExitCode::from(1)
            }
            Err(e) => {
                eprintln!("targo trust proof-cert check: {e}");
                std::process::ExitCode::from(2)
            }
        },
        _ => {
            eprintln!("{usage}");
            std::process::ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cert(proved: usize, failed: usize, unknown: usize, assumptions: usize) -> PackageProofCert {
        PackageProofCert {
            schema: PROOF_CERT_SCHEMA.to_string(),
            authority: AUTHORITY.to_string(),
            package: "widget".to_string(),
            version: "1.2.3".to_string(),
            trust_version: "0.1.0".to_string(),
            report_sha256: "0".repeat(64),
            totals: ProofCertTotals {
                proved,
                failed,
                unknown,
                runtime_checked: 0,
                total: proved + failed + unknown,
                assumptions,
            },
        }
    }

    #[test]
    fn the_default_policy_bills_nobody() {
        // The ecosystem has no certificates. Under the default that must not be
        // a finding, or the first `targo build` against crates.io fails closed
        // on 200 innocent packages.
        let absent = Err(ProofCertError::Absent);
        assert_eq!(evaluate(DepEvidencePolicy::None, "serde", "1.0.0", &absent), None);
        assert!(evaluate(DepEvidencePolicy::Present, "serde", "1.0.0", &absent).is_some());
    }

    #[test]
    fn present_asks_for_a_record_and_verified_asks_it_to_be_clean() {
        let dirty = Ok(cert(10, 1, 0, 0));
        assert_eq!(evaluate(DepEvidencePolicy::Present, "widget", "1.2.3", &dirty), None);
        let finding = evaluate(DepEvidencePolicy::Verified, "widget", "1.2.3", &dirty).unwrap();
        assert!(finding.reason.contains("not clean"), "{}", finding.reason);
    }

    #[test]
    fn an_assumption_is_not_a_clean_run() {
        // The row that makes this worth carrying separately: everything proved,
        // but the verdict rests on an assumption the run did not discharge.
        let assumed = Ok(cert(10, 0, 0, 1));
        assert!(evaluate(DepEvidencePolicy::Verified, "widget", "1.2.3", &assumed).is_some());
    }

    #[test]
    fn a_package_that_raised_no_obligations_is_not_verified() {
        let nothing = Ok(cert(0, 0, 0, 0));
        assert!(!nothing.as_ref().unwrap().totals.is_clean());
        assert!(evaluate(DepEvidencePolicy::Verified, "widget", "1.2.3", &nothing).is_some());
    }

    #[test]
    fn a_record_cannot_be_moved_between_packages_or_versions() {
        let bytes = serde_json::to_vec(&cert(1, 0, 0, 0)).unwrap();
        assert!(PackageProofCert::parse_for(&bytes, "widget", "1.2.3").is_ok());
        // Last release's clean record, shipped with this release's code.
        let err = PackageProofCert::parse_for(&bytes, "widget", "1.2.4").unwrap_err();
        assert!(matches!(err, ProofCertError::WrongPackage { .. }), "{err}");
        let err = PackageProofCert::parse_for(&bytes, "gadget", "1.2.3").unwrap_err();
        assert!(matches!(err, ProofCertError::WrongPackage { .. }), "{err}");
    }

    #[test]
    fn an_unknown_schema_is_refused_rather_than_guessed_at() {
        let mut value: serde_json::Value = serde_json::to_value(cert(1, 0, 0, 0)).unwrap();
        value["schema"] = serde_json::json!("trust.package.proof-cert.v99");
        let err =
            PackageProofCert::parse_for(value.to_string().as_bytes(), "widget", "1.2.3").unwrap_err();
        assert!(matches!(err, ProofCertError::Malformed(_)), "{err}");
    }

    #[test]
    fn the_record_carries_its_own_honest_reading() {
        let bytes = serde_json::to_vec(&cert(1, 0, 0, 0)).unwrap();
        let text = String::from_utf8(bytes).unwrap();
        assert!(text.contains("not an independently checkable proof"), "{text}");
    }

    #[test]
    fn a_record_is_derived_from_a_report_for_the_same_crate() {
        let dir = tempfile::tempdir().unwrap();
        let manifest = dir.path().join("Cargo.toml");
        std::fs::write(
            &manifest,
            "[package]\nname = \"widget\"\nversion = \"1.2.3\"\nedition = \"2024\"\n",
        )
        .unwrap();
        let report_path = dir.path().join("report.json");
        std::fs::write(&report_path, minimal_report("widget", 0)).unwrap();

        let (path, cert) = record_from_report(&report_path, &manifest).unwrap();
        assert!(path.ends_with(PROOF_CERT_RELATIVE_PATH));
        assert_eq!(cert.package, "widget");
        assert_eq!(cert.version, "1.2.3");
        assert_eq!(cert.totals.proved, 0);
        // The digest ties the record to the exact report bytes on disk.
        let bytes = std::fs::read(&report_path).unwrap();
        assert_eq!(cert.report_sha256, trust_types::digest::stable_sha256_hex(&bytes));
        // And the file that lands is the file `targo package` will validate.
        let round_trip =
            read_proof_cert(dir.path(), "widget", "1.2.3").expect("the written record parses");
        assert_eq!(round_trip, cert);
    }

    #[test]
    fn a_report_whose_proof_credit_did_not_survive_reloading_is_refused() {
        // The boundary this lane runs into: `JsonProofReport` downgrades every
        // deserialized `Proved` row, on purpose. A record derived from such a
        // file would say "0 proved" about a crate that proved everything, so
        // refusing beats publishing it.
        let dir = tempfile::tempdir().unwrap();
        let manifest = dir.path().join("Cargo.toml");
        std::fs::write(&manifest, "[package]\nname = \"widget\"\nversion = \"1.2.3\"\n").unwrap();
        let report_path = dir.path().join("report.json");
        std::fs::write(&report_path, minimal_report("widget", 2)).unwrap();
        let err = record_from_report(&report_path, &manifest).unwrap_err();
        assert!(err.contains("carries no proof authority"), "{err}");
        assert!(!proof_cert_path(dir.path()).exists());
    }

    #[test]
    fn a_report_for_another_crate_never_becomes_this_crates_record() {
        let dir = tempfile::tempdir().unwrap();
        let manifest = dir.path().join("Cargo.toml");
        std::fs::write(&manifest, "[package]\nname = \"widget\"\nversion = \"1.2.3\"\n").unwrap();
        let report_path = dir.path().join("report.json");
        std::fs::write(&report_path, minimal_report("gadget", 0)).unwrap();
        let err = record_from_report(&report_path, &manifest).unwrap_err();
        assert!(err.contains("reports on crate `gadget`"), "{err}");
        assert!(!proof_cert_path(dir.path()).exists(), "a refused record must not be written");
    }

    #[test]
    fn a_hyphenated_package_matches_its_underscored_report_name() {
        let dir = tempfile::tempdir().unwrap();
        let manifest = dir.path().join("Cargo.toml");
        std::fs::write(&manifest, "[package]\nname = \"my-widget\"\nversion = \"0.1.0\"\n")
            .unwrap();
        let report_path = dir.path().join("report.json");
        std::fs::write(&report_path, minimal_report("my_widget", 0)).unwrap();
        let (_, cert) = record_from_report(&report_path, &manifest).unwrap();
        assert_eq!(cert.package, "my-widget");
    }

    /// A report declaring `proved` proved obligations and nothing else, in the
    /// shape `JsonProofReport` deserializes.
    fn minimal_report(crate_name: &str, proved: usize) -> String {
        serde_json::json!({
            "metadata": {
                "schema_version": "trust.report.v1",
                "trust_version": "0.1.0",
                "timestamp": "2026-07-24T00:00:00Z",
                "total_time_ms": 1,
            },
            "crate_name": crate_name,
            "summary": {
                "functions_analyzed": 1,
                "functions_verified": usize::from(proved > 0),
                "functions_with_violations": 0,
                "functions_inconclusive": 0,
                "total_obligations": proved,
                "total_proved": proved,
                "total_failed": 0,
                "total_unknown": 0,
                "verdict": if proved > 0 { "Verified" } else { "NoObligations" },
            },
            "functions": [],
            "hardened": null,
            "assumptions": [],
        })
        .to_string()
    }

    #[test]
    fn the_relative_path_matches_the_constructed_one() {
        // The tarball entry and the on-disk file have to be the same spelling,
        // or a consumer unpacking a crate looks in the wrong place.
        let built = proof_cert_path(Path::new("/pkg"));
        assert!(built.ends_with(PROOF_CERT_RELATIVE_PATH));
    }
}
