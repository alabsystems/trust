// trust-proof-cert error types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use thiserror::Error;

/// Errors that can occur while building, serializing, or validating proof certificates.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum CertError {
    #[error("invalid certificate: {reason}")]
    InvalidCertificate { reason: String },
    #[error("chain integrity failure at step {step}: {reason}")]
    ChainIntegrityFailure { step: usize, reason: String },
    #[error(
        "stale certificate for function `{function}`: expected hash {expected_hash}, actual hash {actual_hash}"
    )]
    StaleCertificate { function: String, expected_hash: String, actual_hash: String },
    #[error("serialization failed: {reason}")]
    SerializationFailed { reason: String },
    #[error("verification failed: {reason}")]
    VerificationFailed { reason: String },
    #[error("IO error: {reason}")]
    IoError { reason: String },
    #[error("store error: {reason}")]
    StoreError { reason: String },
    #[error("chain validation failed: {reason}")]
    ChainValidationFailed { reason: String },
}

impl From<std::io::Error> for CertError {
    fn from(e: std::io::Error) -> Self {
        CertError::IoError { reason: e.to_string() }
    }
}
