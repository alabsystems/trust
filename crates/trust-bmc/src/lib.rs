// dead_code audit: crate-level suppression removed
// trust-bmc: tRustc integration boundary for trust_mc safety verifier
//
// Target contract architecture:
// designs/2026-04-25-trust-contracts-first-class-target.md.
// Exposes trust-mc's core analysis as a library API that Trust can call directly
// instead of shelling out to the CLI binary.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! # trust-bmc
//!
//! Integration boundary for the trust_mc safety verifier. This crate provides:
//!
//! - **High-level API**: `verify_function` for end-to-end BMC/CHC/PDR verification
//! - **Low-level API**: `encode_function` for MIR-to-ay encoding without solving
//! - **Optional re-exports**: `BmcVc`, `ChcVc`, `Violation`, `PropertyKind`
//!   from `trust_mc_core` behind `trust-mc-core-types`
//! - **Configuration**: `TrustMcConfig`, `DiagConfig` for controlling verification behavior
//! - **Results**: `TrustMcResult`, `Verdict`, `TrustMcProofMode`, `TypedCounterexample`
//!   for structured output
//!
//! ## Architecture
//!
//! ```text
//! Trust compiler pass (TyCtxt, DefId)
//!          |
//!          v
//!   trust-bmc  (this crate)
//!          |
//!          +--[trust-build]---> trust_mc codegen_ay in-process over tRustc MIR
//!          |
//!          +--[default]-------> compatibility subprocess bridge
//!          |
//!          v
//!     TrustMcResult { verdict, counterexample, proof_certificate, violations, proof_mode }
//! ```
//!
//! ## Feature Flags
//!
//! - `trust-build`: Enables direct tRustc `TyCtxt` integration. Target builds
//!   must use this path so proof strength can distinguish ordinary bounded
//!   BMC, finite acyclic BMC, and CHC/PDR.

mod config;
mod error;
// Sealed-authority S3 (2026-07-17 blueprint): gate-side CHC/PDR invariant
// replay oracle. Library-only — rides the trust-mc-native-solver feature so it
// sees the same patched ay-chc package trust-mc-driver's native lane uses,
// with no rustc-private linkage. No in-tree consumer calls it yet (S3 wires it
// into trust_verify's recheck pass).
#[cfg(feature = "trust-mc-native-solver")]
pub mod replay_oracle;
mod result;
mod subprocess;
#[cfg(not(feature = "trust-mc-core-types"))]
mod verifier_api_stub;
#[cfg(feature = "trust-mc-core-types")]
mod verifier_api;
#[cfg(not(feature = "trust-mc-core-types"))]
use verifier_api_stub as verifier_api;

pub use config::{DiagConfig, TrustMcConfig};
pub use error::TrustMcLibError;
pub use result::{
    DiagLevel, DiagnosticMessage, EncodingContext, NativeEncodingArtifact, NativeEncodingKind,
    TraceStep, TrustMcProofMode, TrustMcProofProvenance, TrustMcPropertyKind, TrustMcResult,
    TypedCounterexample, TypedValue, Verdict, ViolationInfo,
};
pub use subprocess::SubprocessBackend;
pub use verifier_api::{
    TRUST_MC_FULL_VERIFICATION_VERDICT_METADATA_KEY, TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY,
    TRUST_MC_TYPED_CHC_BINDING_SCHEMA, TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA,
    TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY,
    TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY, TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY,
    TrustMcVerifierApiAdapter, is_trust_mc_owned_obligation_kind,
    trust_mc_owned_obligation_kinds,
};
#[cfg(feature = "trust-mc-core-types")]
pub use verifier_api::{
    TrustMcChcPdrProofEvidence, TrustMcChcPdrProofKind, TrustMcChcPdrStats,
    TrustMcDiagnosticOnlyEvidence, TrustMcEvidenceHash, TrustMcEvidenceHashError,
    TrustMcFullProofEvidenceMetadata, TrustMcFullVerificationArtifact,
    TrustMcFullVerificationArtifactKind, TrustMcFullVerificationProblemKind,
    TrustMcNativeFullVerifierEvidence, TrustMcNativeTypedChcObligationMetadata,
    TrustMcProofCheckStatus, TrustMcProofReplayCheckStatus, TrustMcProofReplayStatus,
};
#[cfg(feature = "trust-mc-core-types")]
pub use verifier_api::trust_mc_full_verification_verdict_metadata_entry;
#[cfg(feature = "trust-mc-native-solver")]
pub use verifier_api::{
    FreshExactDirectChcPdrBundleSeal, FreshExactDirectChcPdrDispatch,
    FreshExactDirectChcPdrReceipt,
    TrustMcNativeTypedChcPdrProofTransport, TrustMcNativeTypedProofArtifactRef,
    TrustMcNativeTypedProofStatus, TrustMcNativeTypedProofStrength,
};
#[cfg(feature = "trust-mc-native-trust-ir-bundle")]
pub use verifier_api::NativeTrustIrBundleEvidenceWithFreshReceipts;
// Additional re-exports for lower-level access. These are feature-gated so
// default consumers do not depend on trust-mc-core as part of trust-bmc's
// public API while the implementation split is staged.
#[cfg(feature = "trust-mc-core-types")]
pub use trust_mc_core::{
    ArtifactMetadata, BmcQuery, ChcPdrProofEvidence, ChcPdrProofKind, ChcPdrStats, ChcQuery,
    Constraints, Decl, DiagnosticOnlyEvidence, EvidenceHash, FullProofEvidence,
    FullProofEvidenceMetadata, FullVerificationArtifact, FullVerificationArtifactKind,
    FullVerificationProblemKind, FullVerificationVerdict, HarnessId, MirDerivedChcPdrObligation,
    MirObligationKind, ObligationOrigin, ProofGradeVerdict, PropertyId, SourceLocation, VcArtifact,
    VerificationMode,
};
// Trust: Re-export trust_mc_core types for consumers that need the VC IR directly.
// These are the types from the trust_mc repo's core crate, providing BMC/CHC
// verification condition containers, violation descriptors, and property kinds.
#[cfg(feature = "trust-mc-core-types")]
pub use trust_mc_core::{BmcVc, ChcVc, PropertyKind, Violation};

/// Verify a function using trust-mc's safety/reachability engine.
///
/// This is the high-level entry point matching the Pipeline v2 design:
/// ```text
/// let result = trust_bmc::verify_function(tcx, def_id, config);
/// ```
///
/// In compatibility builds, this delegates to the subprocess backend. Target
/// tRustc builds must call trust-mc's `codegen_ay` directly in-process and report
/// whether the proof is ordinary bounded BMC, finite acyclic BMC, or unbounded
/// CHC/PDR evidence.
///
/// # Arguments
///
/// * `function_name` - The fully qualified function name to verify
/// * `smtlib_script` - The SMT-LIB2 script encoding the verification condition
/// * `config` - Verification configuration (timeout, depth, diagnostics)
///
/// # Errors
///
/// Returns `TrustMcLibError` if the subprocess fails to spawn or produces
/// unparseable output.
pub fn verify_function(
    function_name: &str,
    smtlib_script: &str,
    config: &TrustMcConfig,
) -> Result<TrustMcResult, TrustMcLibError> {
    #[cfg(feature = "trust-mc-native")]
    {
        return verify_function_native(function_name, smtlib_script, config);
    }

    #[cfg(not(feature = "trust-mc-native"))]
    {
        ensure_smtlib_bmc_mode(config)?;
        let backend = SubprocessBackend::new(config);
        backend.verify(function_name, smtlib_script)
    }
}

/// Encode a function's MIR into verification conditions without solving.
///
/// This is the lower-level API from the Pipeline v2 design (Challenge 7):
/// returns the ay encoding context, local variable mappings, and base
/// constraint set. Callers can compose additional constraints before solving.
///
/// In compatibility builds, this returns an `EncodingContext` with the SMT-LIB2
/// script and metadata. Target tRustc builds return ay `Expr` trees and solver
/// context directly.
///
/// # Arguments
///
/// * `function_name` - The fully qualified function name to encode
/// * `smtlib_script` - The SMT-LIB2 script encoding the function
/// * `config` - Encoding configuration
///
/// # Errors
///
/// Returns `TrustMcLibError` if encoding fails.
pub fn encode_function(
    function_name: &str,
    smtlib_script: &str,
    config: &TrustMcConfig,
) -> Result<EncodingContext, TrustMcLibError> {
    #[cfg(feature = "trust-mc-native")]
    {
        return encode_function_native(function_name, smtlib_script, config);
    }

    #[cfg(not(feature = "trust-mc-native"))]
    {
        ensure_smtlib_bmc_mode(config)?;
        if config.proof_mode == TrustMcProofMode::Bmc {
            Ok(EncodingContext::from_smtlib(
                function_name.to_string(),
                smtlib_script.to_string(),
                config.bmc_depth,
            ))
        } else {
            Ok(EncodingContext::from_smtlib_with_provenance(
                function_name.to_string(),
                smtlib_script.to_string(),
                local_provenance(config.proof_mode, config.bmc_depth, "trust-bmc-subprocess"),
                None,
            ))
        }
    }
}

#[cfg(not(feature = "trust-mc-native"))]
fn ensure_smtlib_bmc_mode(config: &TrustMcConfig) -> Result<(), TrustMcLibError> {
    match config.proof_mode {
        TrustMcProofMode::Bmc | TrustMcProofMode::FiniteAcyclicBmc => Ok(()),
        TrustMcProofMode::Chc | TrustMcProofMode::PdrIc3 => Err(TrustMcLibError::ConfigError {
            reason: format!(
                "SMT-LIB compatibility mode supports only BMC and finite acyclic BMC; {:?} requires native CHC/PDR support",
                config.proof_mode
            ),
        }),
    }
}

#[cfg(not(feature = "trust-mc-native"))]
fn local_provenance(
    proof_mode: TrustMcProofMode,
    bmc_depth: u32,
    producer: impl Into<String>,
) -> TrustMcProofProvenance {
    match proof_mode {
        TrustMcProofMode::Bmc => TrustMcProofProvenance::bmc(bmc_depth, producer),
        TrustMcProofMode::FiniteAcyclicBmc => {
            TrustMcProofProvenance::finite_acyclic_bmc(bmc_depth, producer)
        }
        TrustMcProofMode::Chc | TrustMcProofMode::PdrIc3 => {
            TrustMcProofProvenance::unbounded(proof_mode, producer)
        }
    }
}

#[cfg(feature = "trust-mc-native")]
fn encode_function_native(
    function_name: &str,
    smtlib_script: &str,
    config: &TrustMcConfig,
) -> Result<EncodingContext, TrustMcLibError> {
    let request = trust_mc_compiler::NativeEncodeRequest::new(
        function_name,
        function_name,
        trust_mc_compiler::NativeInput::SmtLib { script: smtlib_script.to_string() },
        to_compiler_proof_mode(config.proof_mode),
    )
    .with_bmc_depth(config.bmc_depth);

    let encoded = trust_mc_compiler::encode_native(request).map_err(map_native_encode_error)?;
    let provenance = from_compiler_provenance(encoded.provenance)?;
    let native_artifact = NativeEncodingArtifact {
        obligation_id: encoded.obligation_id,
        function_name: encoded.function_name,
        kind: from_compiler_vc_kind(encoded.kind)?,
        payload: encoded.payload,
        provenance: provenance.clone(),
    };

    Ok(EncodingContext::from_smtlib_with_provenance(
        function_name.to_string(),
        smtlib_script.to_string(),
        provenance,
        Some(native_artifact),
    ))
}

#[cfg(feature = "trust-mc-native")]
fn verify_function_native(
    function_name: &str,
    smtlib_script: &str,
    config: &TrustMcConfig,
) -> Result<TrustMcResult, TrustMcLibError> {
    use std::time::{Duration, Instant};

    let start = Instant::now();
    let context = encode_function_native(function_name, smtlib_script, config)?;
    let artifact =
        context.native_artifact.clone().ok_or_else(|| TrustMcLibError::EncodingError {
            reason: String::from("native encode did not return an artifact"),
        })?;

    let request = trust_mc_driver::NativeSolveRequest::new(to_driver_artifact(artifact)?)
        .with_timeout(Duration::from_millis(config.timeout_ms))
        .with_proof_certificate(config.produce_proofs);
    let solved = trust_mc_driver::solve_native(request).map_err(map_native_solve_error)?;
    let elapsed = start.elapsed().as_millis() as u64;
    let proof_provenance = from_driver_provenance(solved.provenance)?;
    let diagnostics = native_diagnostics(solved.diagnostics, &config.diagnostics);

    Ok(TrustMcResult {
        verdict: from_driver_verdict(solved.verdict),
        counterexample: None,
        proof_certificate: solved.proof_certificate,
        violations: Vec::new(),
        proof_mode: proof_provenance.proof_mode,
        proof_provenance: Some(proof_provenance.clone()),
        time_ms: elapsed,
        diagnostics,
        bmc_depth: proof_provenance.bmc_depth.unwrap_or(config.bmc_depth),
        function_name: function_name.to_string(),
    })
}

#[cfg(feature = "trust-mc-native")]
fn to_compiler_proof_mode(mode: TrustMcProofMode) -> trust_mc_compiler::NativeProofMode {
    match mode {
        TrustMcProofMode::Bmc => trust_mc_compiler::NativeProofMode::Bmc,
        TrustMcProofMode::FiniteAcyclicBmc => trust_mc_compiler::NativeProofMode::FiniteAcyclicBmc,
        TrustMcProofMode::Chc => trust_mc_compiler::NativeProofMode::Chc,
        TrustMcProofMode::PdrIc3 => trust_mc_compiler::NativeProofMode::PdrIc3,
    }
}

#[cfg(feature = "trust-mc-native")]
fn from_compiler_proof_mode(
    mode: trust_mc_compiler::NativeProofMode,
) -> Result<TrustMcProofMode, TrustMcLibError> {
    match mode {
        trust_mc_compiler::NativeProofMode::Bmc => Ok(TrustMcProofMode::Bmc),
        trust_mc_compiler::NativeProofMode::FiniteAcyclicBmc => {
            Ok(TrustMcProofMode::FiniteAcyclicBmc)
        }
        trust_mc_compiler::NativeProofMode::Chc => Ok(TrustMcProofMode::Chc),
        trust_mc_compiler::NativeProofMode::PdrIc3 => Ok(TrustMcProofMode::PdrIc3),
        _ => Err(TrustMcLibError::EncodingError {
            reason: String::from("unrecognized native compiler proof mode"),
        }),
    }
}

#[cfg(feature = "trust-mc-native")]
fn from_compiler_provenance(
    provenance: trust_mc_compiler::NativeProofProvenance,
) -> Result<TrustMcProofProvenance, TrustMcLibError> {
    Ok(TrustMcProofProvenance {
        proof_mode: from_compiler_proof_mode(provenance.proof_mode)?,
        bmc_depth: provenance.bmc_depth,
        finite_acyclic: provenance.finite_acyclic,
        producer: provenance.producer,
    })
}

#[cfg(feature = "trust-mc-native")]
fn from_compiler_vc_kind(
    kind: trust_mc_compiler::NativeVcKind,
) -> Result<NativeEncodingKind, TrustMcLibError> {
    match kind {
        trust_mc_compiler::NativeVcKind::Bmc => Ok(NativeEncodingKind::Bmc),
        trust_mc_compiler::NativeVcKind::Chc => Ok(NativeEncodingKind::Chc),
        _ => Err(TrustMcLibError::EncodingError {
            reason: String::from("unrecognized native compiler artifact kind"),
        }),
    }
}

#[cfg(feature = "trust-mc-native")]
fn to_driver_artifact(
    artifact: NativeEncodingArtifact,
) -> Result<trust_mc_driver::NativeEncodedArtifact, TrustMcLibError> {
    Ok(trust_mc_driver::NativeEncodedArtifact::new(
        artifact.obligation_id,
        artifact.function_name,
        match artifact.kind {
            NativeEncodingKind::Bmc => trust_mc_driver::NativeVcKind::Bmc,
            NativeEncodingKind::Chc => trust_mc_driver::NativeVcKind::Chc,
        },
        artifact.payload,
        to_driver_provenance(&artifact.provenance)?,
    ))
}

#[cfg(feature = "trust-mc-native")]
fn to_driver_provenance(
    provenance: &TrustMcProofProvenance,
) -> Result<trust_mc_driver::NativeProofProvenance, TrustMcLibError> {
    let mut native = match provenance.proof_mode {
        TrustMcProofMode::Bmc => {
            trust_mc_driver::NativeProofProvenance::bmc(required_bmc_depth(provenance, "BMC")?)
        }
        TrustMcProofMode::FiniteAcyclicBmc => {
            trust_mc_driver::NativeProofProvenance::finite_acyclic_bmc(required_bmc_depth(
                provenance,
                "finite acyclic BMC",
            )?)
        }
        TrustMcProofMode::Chc => {
            trust_mc_driver::NativeProofProvenance::unbounded(trust_mc_driver::NativeProofMode::Chc)
        }
        TrustMcProofMode::PdrIc3 => trust_mc_driver::NativeProofProvenance::unbounded(
            trust_mc_driver::NativeProofMode::PdrIc3,
        ),
    };
    native.bmc_depth = provenance.bmc_depth;
    native.finite_acyclic = provenance.finite_acyclic;
    native.producer = provenance.producer.clone();
    Ok(native)
}

#[cfg(feature = "trust-mc-native")]
fn required_bmc_depth(
    provenance: &TrustMcProofProvenance,
    proof_mode: &str,
) -> Result<u32, TrustMcLibError> {
    provenance.bmc_depth.ok_or_else(|| TrustMcLibError::EncodingError {
        reason: format!("native {proof_mode} provenance is missing bmc_depth"),
    })
}

#[cfg(feature = "trust-mc-native")]
fn from_driver_provenance(
    provenance: trust_mc_driver::NativeProofProvenance,
) -> Result<TrustMcProofProvenance, TrustMcLibError> {
    let proof_mode = match provenance.proof_mode {
        trust_mc_driver::NativeProofMode::Bmc => TrustMcProofMode::Bmc,
        trust_mc_driver::NativeProofMode::FiniteAcyclicBmc => TrustMcProofMode::FiniteAcyclicBmc,
        trust_mc_driver::NativeProofMode::Chc => TrustMcProofMode::Chc,
        trust_mc_driver::NativeProofMode::PdrIc3 => TrustMcProofMode::PdrIc3,
        _ => {
            return Err(TrustMcLibError::ParseError {
                reason: String::from("unrecognized native driver proof mode"),
            });
        }
    };

    Ok(TrustMcProofProvenance {
        proof_mode,
        bmc_depth: provenance.bmc_depth,
        finite_acyclic: provenance.finite_acyclic,
        producer: provenance.producer,
    })
}

#[cfg(feature = "trust-mc-native")]
fn from_driver_verdict(verdict: trust_mc_driver::NativeSolverVerdict) -> Verdict {
    match verdict {
        trust_mc_driver::NativeSolverVerdict::Proved => Verdict::Proved,
        trust_mc_driver::NativeSolverVerdict::Failed => Verdict::Failed,
        trust_mc_driver::NativeSolverVerdict::Unknown { reason } => Verdict::Unknown { reason },
        trust_mc_driver::NativeSolverVerdict::Timeout => Verdict::Timeout,
        _ => Verdict::Unknown { reason: String::from("unrecognized native solver verdict") },
    }
}

#[cfg(feature = "trust-mc-native")]
fn native_diagnostics(
    diagnostics: Vec<String>,
    diag_config: &DiagConfig,
) -> Vec<result::DiagnosticMessage> {
    if *diag_config == DiagConfig::Passthrough {
        for diagnostic in &diagnostics {
            eprintln!("{diagnostic}");
        }
    }

    if *diag_config != DiagConfig::Capture {
        return Vec::new();
    }

    diagnostics
        .into_iter()
        .map(|message| result::DiagnosticMessage {
            level: result::DiagLevel::Note,
            message,
            location: None,
        })
        .collect()
}

#[cfg(feature = "trust-mc-native")]
fn map_native_encode_error(error: trust_mc_compiler::NativeEncodeError) -> TrustMcLibError {
    match error {
        trust_mc_compiler::NativeEncodeError::Unsupported(unsupported) => {
            TrustMcLibError::ConfigError {
                reason: format!("unsupported native encode: {}", unsupported.reason),
            }
        }
        trust_mc_compiler::NativeEncodeError::InvalidInput { field, detail } => {
            TrustMcLibError::EncodingError {
                reason: format!("invalid native encode input `{field}`: {detail}"),
            }
        }
        other => TrustMcLibError::EncodingError {
            reason: format!("unrecognized native encode error: {other}"),
        },
    }
}

#[cfg(feature = "trust-mc-native")]
fn map_native_solve_error(error: trust_mc_driver::NativeSolveError) -> TrustMcLibError {
    match error {
        trust_mc_driver::NativeSolveError::Unsupported(unsupported) => {
            TrustMcLibError::ConfigError {
                reason: format!("unsupported native solve: {}", unsupported.reason),
            }
        }
        trust_mc_driver::NativeSolveError::InvalidInput { field, detail } => {
            TrustMcLibError::ParseError {
                reason: format!("invalid native solve input `{field}`: {detail}"),
            }
        }
        other => TrustMcLibError::ParseError {
            reason: format!("unrecognized native solve error: {other}"),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const UNSAT_SCRIPT: &str = "(set-logic QF_LIA)\n(assert false)\n(check-sat)\n";

    fn config_error_reason(error: TrustMcLibError) -> String {
        match error {
            TrustMcLibError::ConfigError { reason } => reason,
            other => panic!("expected configuration error, got {other:?}"),
        }
    }

    #[test]
    fn encode_function_preserves_bounded_bmc_provenance() {
        let config = TrustMcConfig::new().with_bmc_depth(7).with_proof_mode(TrustMcProofMode::Bmc);

        let context =
            encode_function("crate::harness", UNSAT_SCRIPT, &config).expect("BMC should encode");

        assert_eq!(context.proof_mode, TrustMcProofMode::Bmc);
        assert_eq!(context.bmc_depth, 7);
        assert_eq!(context.proof_provenance.proof_mode, TrustMcProofMode::Bmc);
        assert_eq!(context.proof_provenance.bmc_depth, Some(7));
        assert!(!context.proof_provenance.finite_acyclic);

        let strength = context.proof_mode.to_proof_strength(context.bmc_depth);
        assert!(strength.is_bounded());
        assert_eq!(strength.bounded_depth(), Some(7));
    }

    #[test]
    fn encode_function_preserves_finite_acyclic_provenance() {
        let config = TrustMcConfig::new()
            .with_bmc_depth(9)
            .with_proof_mode(TrustMcProofMode::FiniteAcyclicBmc);

        let context = encode_function("crate::harness", UNSAT_SCRIPT, &config)
            .expect("finite acyclic BMC SMT-LIB should encode");

        assert_eq!(context.proof_mode, TrustMcProofMode::FiniteAcyclicBmc);
        assert_eq!(context.bmc_depth, 9);
        assert!(context.proof_provenance.finite_acyclic);
        assert_eq!(context.proof_provenance.bmc_depth, Some(9));
    }

    #[cfg(not(feature = "trust-mc-native"))]
    #[test]
    fn compatibility_smtlib_rejects_chc_and_pdr_without_native_support() {
        for proof_mode in [TrustMcProofMode::Chc, TrustMcProofMode::PdrIc3] {
            let config = TrustMcConfig::new().with_proof_mode(proof_mode);

            let encode_reason = config_error_reason(
                encode_function("crate::harness", UNSAT_SCRIPT, &config)
                    .expect_err("CHC/PDR SMT-LIB compatibility encoding must fail closed"),
            );
            assert!(encode_reason.contains("SMT-LIB compatibility mode"));
            assert!(encode_reason.contains(&format!("{proof_mode:?}")));

            let verify_reason = config_error_reason(
                verify_function("crate::harness", UNSAT_SCRIPT, &config)
                    .expect_err("CHC/PDR SMT-LIB compatibility solving must fail closed"),
            );
            assert!(verify_reason.contains("SMT-LIB compatibility mode"));
            assert!(verify_reason.contains(&format!("{proof_mode:?}")));
        }
    }

    #[test]
    fn verify_function_rejects_chc_smtlib_without_downgrading() {
        let config = TrustMcConfig::new().with_proof_mode(TrustMcProofMode::Chc);
        let err = verify_function("crate::harness", UNSAT_SCRIPT, &config)
            .expect_err("CHC SMT-LIB must not silently run as BMC");

        assert!(matches!(err, TrustMcLibError::ConfigError { .. }));
    }

    #[cfg(feature = "trust-mc-native")]
    #[test]
    fn native_smtlib_chc_and_pdr_reach_native_before_failing_closed() {
        for proof_mode in [TrustMcProofMode::Chc, TrustMcProofMode::PdrIc3] {
            let config = TrustMcConfig::new().with_proof_mode(proof_mode);

            let encode_reason = config_error_reason(
                encode_function("crate::harness", UNSAT_SCRIPT, &config)
                    .expect_err("CHC/PDR native SMT-LIB encoding must fail closed"),
            );
            assert!(encode_reason.contains("unsupported native encode"));
            assert!(encode_reason.contains("smtlib_non_bmc_not_native_yet"));
            assert!(!encode_reason.contains("SMT-LIB compatibility mode"));

            let verify_reason = config_error_reason(
                verify_function("crate::harness", UNSAT_SCRIPT, &config)
                    .expect_err("CHC/PDR native SMT-LIB solving must fail closed"),
            );
            assert!(verify_reason.contains("unsupported native encode"));
            assert!(verify_reason.contains("smtlib_non_bmc_not_native_yet"));
            assert!(!verify_reason.contains("SMT-LIB compatibility mode"));
        }
    }

    #[cfg(feature = "trust-mc-native")]
    #[test]
    fn encode_function_uses_native_artifact_when_enabled() {
        let config = TrustMcConfig::new().with_bmc_depth(4);
        let context =
            encode_function("crate::harness", UNSAT_SCRIPT, &config).expect("native encode");

        let artifact = context.native_artifact.expect("native artifact should be present");
        assert_eq!(artifact.kind, NativeEncodingKind::Bmc);
        assert_eq!(artifact.provenance.proof_mode, TrustMcProofMode::Bmc);
        assert_eq!(artifact.provenance.bmc_depth, Some(4));
    }

    #[cfg(all(feature = "trust-mc-native", feature = "trust-mc-native-solver"))]
    #[test]
    fn verify_function_uses_native_solver_when_enabled() {
        let config = TrustMcConfig::new().with_bmc_depth(4);
        let result =
            verify_function("crate::harness", UNSAT_SCRIPT, &config).expect("native solve");

        assert_eq!(result.verdict, Verdict::Proved);
        assert_eq!(result.proof_mode, TrustMcProofMode::Bmc);
        assert_eq!(result.bmc_depth, 4);
        assert_eq!(
            result.proof_provenance.as_ref().map(|provenance| provenance.bmc_depth),
            Some(Some(4))
        );
    }
}
