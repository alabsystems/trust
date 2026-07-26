// trust-clean/certification/result.rs: CertificationResult enum
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::TrustProofCertificate;

/// Trust: Result of clean certification attempt.
///
/// Separate from `VerificationResult` — this is a post-processing outcome.
/// The original verification result is not modified; certification is layered on top.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum CertificationResult {
    /// Trust: clean kernel confirmed the proof — upgrades Trusted -> Certified.
    Certified {
        /// The certificate produced by clean verification.
        certificate: TrustProofCertificate,
        /// clean kernel verification time in milliseconds.
        time_ms: u64,
    },
    /// Trust: Certificate was produced but NOT kernel-verified.
    ///
    /// The proof term was stored but clean did not confirm it. This covers:
    /// - `certify_unchecked()` (caller explicitly requested no kernel check)
    /// - `certify_from_solver_proof()` fallback (kernel rejected, unchecked fallback used)
    ///
    /// Trusted certificates cannot enable codegen check elision.
    Trusted {
        /// The certificate produced WITHOUT clean kernel verification.
        certificate: TrustProofCertificate,
        /// Time spent producing the certificate, in milliseconds.
        time_ms: u64,
    },
    /// Trust: clean could not verify the proof term.
    Rejected {
        /// Why clean rejected the proof.
        reason: String,
        /// Time spent before rejection, in milliseconds.
        time_ms: u64,
    },
    /// Trust: Certification was not attempted (wrong result type or no proof term).
    Skipped {
        /// Why certification was skipped.
        reason: String,
    },
}

impl CertificationResult {
    /// Returns `true` if the result is `Certified`.
    #[must_use]
    pub fn is_certified(&self) -> bool {
        matches!(self, CertificationResult::Certified { .. })
    }

    /// Returns `true` if the result is `Trusted` (certificate exists but NOT kernel-verified).
    #[must_use]
    pub fn is_trusted(&self) -> bool {
        matches!(self, CertificationResult::Trusted { .. })
    }

    /// Returns `true` if the result is `Rejected`.
    #[must_use]
    pub fn is_rejected(&self) -> bool {
        matches!(self, CertificationResult::Rejected { .. })
    }

    /// Returns `true` if certification was skipped (not attempted).
    #[must_use]
    pub fn is_skipped(&self) -> bool {
        matches!(self, CertificationResult::Skipped { .. })
    }
}
