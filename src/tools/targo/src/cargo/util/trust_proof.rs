//! Trust: ship a package's verification record in the `.crate` tarball.
//!
//! The schema is owned by `targo-trust/src/dep_evidence.rs`; this module is
//! deliberately not a second definition of it. Packaging is a courier job — it
//! copies bytes it has no standing to judge, exactly as it does for
//! `.cargo_vcs_info.json` — so the only questions asked here are the two a
//! courier can answer: does the document say it is this schema, and does it say
//! it is about this package at this version. Everything else (what the counts
//! mean, whether the signature checks out, whether the run was clean) belongs
//! to `targo trust`, which has the crates for it.
//!
//! Two properties this has to keep, or Trust crates stop being publishable:
//!
//! * **Additive.** No record, no file, no error, no warning. The overwhelming
//!   majority of packages — including every third-party crate a Trust user
//!   depends on — will never have one.
//! * **Ignorable.** An extra path in the tarball that no consumer reads. A
//!   registry that has never heard of Trust unpacks it and ignores it, the same
//!   way it ignores `.cargo_vcs_info.json`.
//!
//! The one thing it must NOT do is ship a record that says something false. A
//! document that is present but does not parse, or that describes a different
//! crate, is a hard packaging error rather than a skipped file: a stale clean
//! record shipped alongside changed code is worse than no record at all, and
//! silence would be how that happens.

use crate::CargoResult;
use crate::core::Package;
use anyhow::bail;
use std::path::Path;

/// The record's path, both on disk under the package root and inside the
/// tarball. One spelling, so a consumer unpacking a crate finds it where a
/// developer left it.
pub const TRUST_PROOF_CERT_FILE: &str = ".trust/proof.cert";

/// The schema tag written by `targo-trust`'s `dep_evidence::PROOF_CERT_SCHEMA`.
const TRUST_PROOF_CERT_SCHEMA: &str = "trust.package.proof-cert.v1";

/// Read and courier-check the package's record.
///
/// `Ok(None)` is the ordinary case: nothing to ship.
pub fn read_proof_cert(pkg: &Package) -> CargoResult<Option<Vec<u8>>> {
    let path = pkg.root().join(TRUST_PROOF_CERT_FILE);
    if !path.is_file() {
        return Ok(None);
    }
    let bytes = std::fs::read(&path)?;
    check_proof_cert(
        &bytes,
        &pkg.name().to_string(),
        &pkg.version().to_string(),
        &path,
    )?;
    Ok(Some(bytes))
}

fn check_proof_cert(
    bytes: &[u8],
    name: &str,
    version: &str,
    path: &Path,
) -> CargoResult<()> {
    let value: serde_json::Value = match serde_json::from_slice(bytes) {
        Ok(value) => value,
        Err(e) => bail!("{} is not valid JSON: {e}", path.display()),
    };
    let schema = value.get("schema").and_then(|v| v.as_str());
    if schema != Some(TRUST_PROOF_CERT_SCHEMA) {
        bail!(
            "{} declares schema {:?}, expected {TRUST_PROOF_CERT_SCHEMA:?}",
            path.display(),
            schema.unwrap_or("<missing>")
        );
    }
    let cert_name = value.get("package").and_then(|v| v.as_str()).unwrap_or_default();
    let cert_version = value.get("version").and_then(|v| v.as_str()).unwrap_or_default();
    if cert_name != name || cert_version != version {
        bail!(
            "{} describes `{cert_name} {cert_version}`, but this package is `{name} {version}`; \
             re-run `targo trust check` to record evidence for this version",
            path.display()
        );
    }
    Ok(())
}

/// One line of dependency proof standing, for `targo tree --proof`.
///
/// A registry dependency's package root is its unpacked source directory, so a
/// crate that shipped the record in its tarball has it here. Reading is
/// display-only: `tree` reports what each dependency claims and judges none of
/// it. `[trust] require_dep_evidence` is where a project says what it will
/// accept, and `targo trust` is what enforces that.
pub fn describe_proof_cert(pkg: &Package) -> String {
    let name = pkg.name().to_string();
    let version = pkg.version().to_string();
    let path = pkg.root().join(TRUST_PROOF_CERT_FILE);
    let Ok(bytes) = std::fs::read(&path) else {
        return "no proof record".to_string();
    };
    if let Err(e) = check_proof_cert(&bytes, &name, &version, &path) {
        // A record that does not describe this package is worse than none: say
        // so rather than folding it into "no proof record".
        return format!("unusable proof record ({e})");
    }
    let Ok(value) = serde_json::from_slice::<serde_json::Value>(&bytes) else {
        return "unusable proof record".to_string();
    };
    let count = |key: &str| value.pointer(&format!("/totals/{key}")).and_then(|v| v.as_u64());
    match (
        count("proved"),
        count("total"),
        count("failed"),
        count("unknown"),
        count("assumptions"),
    ) {
        (Some(proved), Some(total), Some(failed), Some(unknown), Some(assumptions)) => format!(
            "recorded: proved {proved}/{total}, failed {failed}, unknown {unknown}, \
             assumptions {assumptions}"
        ),
        _ => "unusable proof record (totals missing)".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cert_json(schema: &str, name: &str, version: &str) -> Vec<u8> {
        serde_json::json!({
            "schema": schema,
            "authority": "a publisher-recorded verdict distribution",
            "package": name,
            "version": version,
            "totals": { "proved": 3, "failed": 0, "unknown": 0, "runtime_checked": 0, "total": 3, "assumptions": 0 },
        })
        .to_string()
        .into_bytes()
    }

    #[test]
    fn a_matching_record_passes() {
        let bytes = cert_json(TRUST_PROOF_CERT_SCHEMA, "widget", "1.2.3");
        assert!(check_proof_cert(&bytes, "widget", "1.2.3", Path::new("p")).is_ok());
    }

    #[test]
    fn last_releases_record_is_a_packaging_error() {
        // The failure this exists to prevent: a clean record from 1.2.3 riding
        // along in the 1.2.4 tarball.
        let bytes = cert_json(TRUST_PROOF_CERT_SCHEMA, "widget", "1.2.3");
        let err = check_proof_cert(&bytes, "widget", "1.2.4", Path::new("p")).unwrap_err();
        assert!(err.to_string().contains("but this package is"), "{err}");
    }

    #[test]
    fn another_crates_record_is_a_packaging_error() {
        let bytes = cert_json(TRUST_PROOF_CERT_SCHEMA, "gadget", "1.2.3");
        let err = check_proof_cert(&bytes, "widget", "1.2.3", Path::new("p")).unwrap_err();
        assert!(err.to_string().contains("describes `gadget 1.2.3`"), "{err}");
    }

    #[test]
    fn an_unreadable_record_fails_rather_than_shipping() {
        let err = check_proof_cert(b"{", "widget", "1.2.3", Path::new("p")).unwrap_err();
        assert!(err.to_string().contains("not valid JSON"), "{err}");
        let bytes = cert_json("trust.package.proof-cert.v99", "widget", "1.2.3");
        let err = check_proof_cert(&bytes, "widget", "1.2.3", Path::new("p")).unwrap_err();
        assert!(err.to_string().contains("declares schema"), "{err}");
    }
}
