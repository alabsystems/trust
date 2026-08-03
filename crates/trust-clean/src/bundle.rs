// trust-clean/bundle.rs: Project-level proof certificate bundles
//
// Bundles group one or more proof certificates with minimal metadata so the
// project can persist `.trust-cert`-style artifacts without committing to a
// CLI or report format yet.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fs;
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::TrustProofCertificate;
use crate::error::CertificateError;

/// Current bundle format version.
pub const TRUST_CERT_BUNDLE_FORMAT_VERSION: u32 = 1;

/// Minimal metadata for a project-level certificate bundle.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrustProofCertificateBundleMetadata {
    pub project: String,
    pub format_version: u32,
}

/// A project-level bundle of one or more proof certificates.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrustProofCertificateBundle {
    pub metadata: TrustProofCertificateBundleMetadata,
    pub certificates: Vec<TrustProofCertificate>,
}

impl TrustProofCertificateBundle {
    /// Build a validated bundle for a project.
    pub fn new(
        project: impl Into<String>,
        certificates: Vec<TrustProofCertificate>,
    ) -> Result<Self, CertificateError> {
        let project = project.into();
        if certificates.is_empty() {
            return Err(CertificateError::EmptyCertificateBundle { project });
        }

        Ok(Self {
            metadata: TrustProofCertificateBundleMetadata {
                project,
                format_version: TRUST_CERT_BUNDLE_FORMAT_VERSION,
            },
            certificates,
        })
    }

    /// Convenience constructor for a single certificate.
    pub fn single(project: impl Into<String>, certificate: TrustProofCertificate) -> Self {
        Self {
            metadata: TrustProofCertificateBundleMetadata {
                project: project.into(),
                format_version: TRUST_CERT_BUNDLE_FORMAT_VERSION,
            },
            certificates: vec![certificate],
        }
    }

    /// Returns the project name.
    #[must_use]
    pub fn project(&self) -> &str {
        &self.metadata.project
    }

    /// Returns the number of certificates in the bundle.
    #[must_use]
    pub fn len(&self) -> usize {
        self.certificates.len()
    }

    /// Returns true when the bundle contains no certificates.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.certificates.is_empty()
    }

    /// Returns an iterator over the contained certificates.
    pub fn iter(&self) -> impl Iterator<Item = &TrustProofCertificate> {
        self.certificates.iter()
    }

    /// Serialize the bundle to bincode bytes.
    pub fn to_bytes(&self) -> Result<Vec<u8>, CertificateError> {
        bincode::serialize(self)
            .map_err(|e| CertificateError::BundleSerializationFailed { reason: e.to_string() })
    }

    /// Deserialize a bundle from bincode bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, CertificateError> {
        let bundle: Self = bincode::deserialize(bytes)
            .map_err(|e| CertificateError::BundleSerializationFailed { reason: e.to_string() })?;

        bundle.validate()
    }

    /// Write the bundle to a `.trust-cert`-style file.
    pub fn write_to_path(&self, path: impl AsRef<Path>) -> Result<(), CertificateError> {
        let path = path.as_ref();
        let bytes = self.to_bytes()?;
        fs::write(path, bytes).map_err(|e| CertificateError::BundleIoFailed {
            path: path.display().to_string(),
            reason: e.to_string(),
        })
    }

    /// Read a bundle from a `.trust-cert`-style file.
    pub fn read_from_path(path: impl AsRef<Path>) -> Result<Self, CertificateError> {
        let path = path.as_ref();
        let bytes = fs::read(path).map_err(|e| CertificateError::BundleIoFailed {
            path: path.display().to_string(),
            reason: e.to_string(),
        })?;
        Self::from_bytes(&bytes)
    }

    fn validate(self) -> Result<Self, CertificateError> {
        if self.certificates.is_empty() {
            return Err(CertificateError::EmptyCertificateBundle {
                project: self.metadata.project,
            });
        }

        Ok(self)
    }
}

/// Serialize a bundle to bytes.
pub fn serialize_certificate_bundle(
    bundle: &TrustProofCertificateBundle,
) -> Result<Vec<u8>, CertificateError> {
    bundle.to_bytes()
}

/// Deserialize a bundle from bytes.
pub fn deserialize_certificate_bundle(
    bytes: &[u8],
) -> Result<TrustProofCertificateBundle, CertificateError> {
    TrustProofCertificateBundle::from_bytes(bytes)
}

/// Write a bundle to disk.
pub fn write_certificate_bundle(
    path: impl AsRef<Path>,
    bundle: &TrustProofCertificateBundle,
) -> Result<(), CertificateError> {
    bundle.write_to_path(path)
}

/// Read a bundle from disk.
pub fn read_certificate_bundle(
    path: impl AsRef<Path>,
) -> Result<TrustProofCertificateBundle, CertificateError> {
    TrustProofCertificateBundle::read_from_path(path)
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    fn sample_vc(name: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: name.into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    fn sample_cert(name: &str) -> TrustProofCertificate {
        let vc = sample_vc(name, Formula::Bool(false));
        let result = VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        crate::certificate::generate_certificate_unchecked(
            &vc,
            &result,
            vec![0xCA, 0xFE],
            "trust-wp 0.1.0",
        )
        .expect("certificate")
    }

    #[test]
    fn bundle_rejects_empty_constructor() {
        let err = TrustProofCertificateBundle::new("project-a", vec![])
            .expect_err("empty bundle should be rejected");
        assert!(matches!(err, CertificateError::EmptyCertificateBundle { .. }));
    }

    #[test]
    fn bundle_roundtrips_through_bytes() {
        let bundle = TrustProofCertificateBundle::new(
            "project-a",
            vec![sample_cert("one"), sample_cert("two")],
        )
        .expect("bundle");

        let bytes = bundle.to_bytes().expect("serialize");
        let recovered = TrustProofCertificateBundle::from_bytes(&bytes).expect("deserialize");

        assert_eq!(bundle.project(), recovered.project());
        assert_eq!(bundle.metadata.format_version, recovered.metadata.format_version);
        assert_eq!(bundle.len(), recovered.len());
        assert_eq!(bundle.certificates[0].prover, recovered.certificates[0].prover);
        assert_eq!(bundle.certificates[1].proof_term, recovered.certificates[1].proof_term);
    }

    #[test]
    fn bundle_roundtrips_through_file() {
        let bundle = TrustProofCertificateBundle::single("project-b", sample_cert("single"));
        let path = std::env::temp_dir().join(format!(
            "trust-clean-bundle-{}-{}.trust-cert",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));

        bundle.write_to_path(&path).expect("write");
        let recovered = TrustProofCertificateBundle::read_from_path(&path).expect("read");
        let _ = fs::remove_file(&path);

        assert_eq!(bundle.project(), recovered.project());
        assert_eq!(bundle.len(), recovered.len());
        assert_eq!(bundle.certificates[0].vc_fingerprint, recovered.certificates[0].vc_fingerprint);
    }

    #[test]
    fn free_function_helpers_match_methods() {
        let bundle = TrustProofCertificateBundle::single("project-c", sample_cert("helper"));
        let bytes = serialize_certificate_bundle(&bundle).expect("serialize");
        let recovered = deserialize_certificate_bundle(&bytes).expect("deserialize");

        assert_eq!(bundle.project(), recovered.project());
        assert_eq!(bundle.certificates[0].canonical_vc, recovered.certificates[0].canonical_vc);
    }
}
