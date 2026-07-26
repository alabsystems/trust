// trust-bmc result types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Result types for trust_mc verification.
//!
//! `TrustMcResult` is the primary output type, containing the verdict,
//! optional counterexample, proof certificate, and violation details.
//!
//! Target tRustc integration must preserve the trust_mc proof mode. Ordinary BMC is
//! bounded; finite acyclic BMC is complete only when the frontend proves the
//! explored transition system has no cycles; CHC/PDR proof is inductive/
//! unbounded safety evidence.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// The outcome of a trust_mc verification run.
///
/// Matches the `TrustMcResult` signature from the Pipeline v2 design
/// (designs/2026-04-14-verification-pipeline-v2.md, section 3.2.1).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrustMcResult {
    /// The verification verdict.
    pub verdict: Verdict,

    /// Concrete counterexample if the property was falsified.
    pub counterexample: Option<TypedCounterexample>,

    /// Proof certificate bytes if the property was proved and
    /// `TrustMcConfig::produce_proofs` was enabled.
    pub proof_certificate: Option<Vec<u8>>,

    /// Detailed violation information from the solver.
    pub violations: Vec<ViolationInfo>,

    /// The trust_mc proof mode that produced this result.
    #[serde(default)]
    pub proof_mode: TrustMcProofMode,

    /// Provenance carried by the native encode/solve path.
    #[serde(default)]
    pub proof_provenance: Option<TrustMcProofProvenance>,

    /// Wall-clock time for the verification in milliseconds.
    pub time_ms: u64,

    /// Diagnostic messages captured during verification
    /// (populated when `DiagConfig::Capture` is used).
    pub diagnostics: Vec<DiagnosticMessage>,

    /// The BMC depth used for this verification when the proof mode is bounded.
    pub bmc_depth: u32,

    /// The function that was verified.
    pub function_name: String,
}

impl TrustMcResult {
    /// Returns `true` if the property was proved to hold.
    #[must_use]
    pub fn is_proved(&self) -> bool {
        matches!(self.verdict, Verdict::Proved)
    }

    /// Returns `true` if a counterexample was found.
    #[must_use]
    pub fn is_failed(&self) -> bool {
        matches!(self.verdict, Verdict::Failed)
    }

    /// Returns `true` if the result is inconclusive.
    #[must_use]
    pub fn is_unknown(&self) -> bool {
        matches!(self.verdict, Verdict::Unknown { .. })
    }

    /// Convert to a `trust_types::VerificationResult` for the router.
    #[must_use]
    pub fn to_verification_result(&self) -> trust_types::VerificationResult {
        match &self.verdict {
            Verdict::Proved => trust_types::VerificationResult::Proved {
                solver: "trust-mc-lib".into(),
                time_ms: self.time_ms,
                strength: self.proof_mode.to_proof_strength(self.bmc_depth),
                proof_certificate: self.proof_certificate.clone(),
                solver_warnings: None,
                native_proof_envelope: None,
            },
            Verdict::Failed => {
                let cex = self.counterexample.as_ref().map(|tc| {
                    let assignments: Vec<(String, trust_types::CounterexampleValue)> = tc
                        .variables
                        .iter()
                        .map(|(name, value)| (name.clone(), typed_value_to_cex_value(value)))
                        .collect();
                    trust_types::Counterexample::new(assignments)
                });
                trust_types::VerificationResult::Failed {
                    solver: "trust-mc-lib".into(),
                    time_ms: self.time_ms,
                    counterexample: cex,
                }
            }
            Verdict::Unknown { reason } => trust_types::VerificationResult::Unknown {
                solver: "trust-mc-lib".into(),
                time_ms: self.time_ms,
                reason: reason.clone(),
            },
            Verdict::Timeout => trust_types::VerificationResult::Timeout {
                solver: "trust-mc-lib".into(),
                timeout_ms: self.time_ms,
            },
        }
    }
}

/// The trust_mc proof engine/mode that produced a result.
///
/// Ordinary BMC is bounded by `TrustMcResult::bmc_depth`; finite acyclic BMC is a
/// complete finite proof only when the producer proved the explored transition
/// system is acyclic; CHC and PDR/IC3 are unbounded safety proofs when they
/// return `Verdict::Proved`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum TrustMcProofMode {
    /// Bounded model checking.
    #[default]
    Bmc,

    /// BMC over a finite acyclic transition system.
    ///
    /// Producers must use this only when the BMC unrolling is exhaustive
    /// because the analyzed state graph has no cycles. Use [`Self::Bmc`] for
    /// ordinary depth-bounded BMC.
    FiniteAcyclicBmc,

    /// Constrained Horn Clause solving.
    Chc,

    /// Property-directed reachability / IC3.
    PdrIc3,
}

/// Provenance for proof strength and native artifact auditing.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustMcProofProvenance {
    /// Proof mode the artifact/result is intended to support.
    pub proof_mode: TrustMcProofMode,
    /// BMC depth when the proof mode is BMC-shaped.
    pub bmc_depth: Option<u32>,
    /// Whether the producer established a finite acyclic transition system.
    pub finite_acyclic: bool,
    /// Human-readable producer component.
    pub producer: String,
}

impl TrustMcProofProvenance {
    /// Create provenance for ordinary bounded BMC.
    #[must_use]
    pub fn bmc(depth: u32, producer: impl Into<String>) -> Self {
        Self {
            proof_mode: TrustMcProofMode::Bmc,
            bmc_depth: Some(depth),
            finite_acyclic: false,
            producer: producer.into(),
        }
    }

    /// Create provenance for exhaustive finite acyclic BMC.
    #[must_use]
    pub fn finite_acyclic_bmc(depth: u32, producer: impl Into<String>) -> Self {
        Self {
            proof_mode: TrustMcProofMode::FiniteAcyclicBmc,
            bmc_depth: Some(depth),
            finite_acyclic: true,
            producer: producer.into(),
        }
    }

    /// Create provenance for an unsupported/unbounded native mode.
    #[must_use]
    pub fn unbounded(proof_mode: TrustMcProofMode, producer: impl Into<String>) -> Self {
        Self { proof_mode, bmc_depth: None, finite_acyclic: false, producer: producer.into() }
    }
}

impl TrustMcProofMode {
    /// Convert this mode into Trust's proof-strength model.
    #[must_use]
    pub fn to_proof_strength(self, bmc_depth: u32) -> trust_types::ProofStrength {
        match self {
            Self::Bmc => trust_types::ProofStrength::bounded(u64::from(bmc_depth)),
            Self::FiniteAcyclicBmc => trust_types::ProofStrength {
                reasoning: trust_types::ReasoningKind::ExhaustiveFinite(u64::from(bmc_depth)),
                assurance: trust_types::AssuranceLevel::Sound,
            },
            Self::Chc => trust_types::ProofStrength::chc_spacer(),
            Self::PdrIc3 => trust_types::ProofStrength::pdr(),
        }
    }

    /// Returns true when the mode provides only bounded proof strength.
    #[must_use]
    pub fn is_bounded(self) -> bool {
        matches!(self, Self::Bmc)
    }

    /// Returns true when BMC was exhaustive because the transition system is finite and acyclic.
    #[must_use]
    pub fn is_finite_acyclic_bmc(self) -> bool {
        matches!(self, Self::FiniteAcyclicBmc)
    }
}

#[cfg(feature = "trust-mc-core-types")]
impl From<trust_mc_core::VerificationMode> for TrustMcProofMode {
    fn from(mode: trust_mc_core::VerificationMode) -> Self {
        match mode {
            trust_mc_core::VerificationMode::Bmc => Self::Bmc,
            trust_mc_core::VerificationMode::Chc => Self::Chc,
        }
    }
}

/// Convert a `TypedValue` to a `trust_types::CounterexampleValue`.
fn typed_value_to_cex_value(value: &TypedValue) -> trust_types::CounterexampleValue {
    match value {
        TypedValue::Bool(b) => trust_types::CounterexampleValue::Bool(*b),
        TypedValue::Int(n) => trust_types::CounterexampleValue::Int(*n),
        TypedValue::Uint(n) => trust_types::CounterexampleValue::Uint(*n),
        TypedValue::BitVec { value, .. } => trust_types::CounterexampleValue::Uint(*value),
        TypedValue::String(s) => {
            trust_types::CounterexampleValue::Uint(s.parse::<u128>().unwrap_or(0))
        }
    }
}

/// The verification verdict.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Verdict {
    /// The property was proved for the reported proof mode.
    Proved,

    /// A counterexample was found (SAT).
    Failed,

    /// The result is inconclusive.
    Unknown {
        /// Reason the result is inconclusive (e.g., bound exhaustion).
        reason: String,
    },

    /// The solver timed out.
    Timeout,
}

/// A typed counterexample from the solver.
///
/// Contains concrete variable assignments that demonstrate a property violation.
/// Unlike the text-based `Counterexample` in `trust-types`, these values retain
/// their SMT sorts (bitvector width, signedness, etc.).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypedCounterexample {
    /// Variable assignments mapping names to typed values.
    pub variables: BTreeMap<String, TypedValue>,

    /// Multi-step execution trace if the counterexample involves loops or
    /// step-indexed variables.
    pub trace: Option<Vec<TraceStep>>,

    /// The violated property kinds from this counterexample.
    pub violated_properties: Vec<TrustMcPropertyKind>,
}

impl TypedCounterexample {
    /// Create a new counterexample with the given variable assignments.
    pub fn new(variables: BTreeMap<String, TypedValue>) -> Self {
        Self { variables, trace: None, violated_properties: Vec::new() }
    }

    /// Add a trace to this counterexample.
    #[must_use]
    pub fn with_trace(mut self, trace: Vec<TraceStep>) -> Self {
        self.trace = Some(trace);
        self
    }

    /// Add violated property information.
    #[must_use]
    pub fn with_violations(mut self, properties: Vec<TrustMcPropertyKind>) -> Self {
        self.violated_properties = properties;
        self
    }
}

/// Local property classification for trust-mc results.
///
/// This intentionally mirrors trust-mc-core's property categories without
/// exposing trust-mc-core in the default trust-bmc public API.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TrustMcPropertyKind {
    /// User-written assertion.
    Assertion,
    /// Assumption.
    Assumption,
    /// Cover statement.
    Cover,
    /// Arithmetic overflow check.
    ArithmeticOverflow,
    /// Division by zero check.
    DivisionByZero,
    /// Array bounds check.
    OutOfBounds,
    /// Null pointer dereference check.
    NullPointer,
    /// Memory safety check.
    MemorySafety,
    /// Pointer offset overflow check.
    PointerOverflow,
    /// Unreachable code check.
    Unreachable,
    /// Panic handler reached.
    Panic,
    /// Undefined behavior check.
    UndefinedBehavior,
    /// Contract precondition.
    Precondition,
    /// Contract postcondition.
    Postcondition,
    /// Loop invariant.
    LoopInvariant,
    /// Other/unclassified check.
    Other,
}

#[cfg(feature = "trust-mc-core-types")]
impl From<trust_mc_core::PropertyKind> for TrustMcPropertyKind {
    fn from(kind: trust_mc_core::PropertyKind) -> Self {
        match kind {
            trust_mc_core::PropertyKind::Assertion => Self::Assertion,
            trust_mc_core::PropertyKind::Assumption => Self::Assumption,
            trust_mc_core::PropertyKind::Cover => Self::Cover,
            trust_mc_core::PropertyKind::ArithmeticOverflow => Self::ArithmeticOverflow,
            trust_mc_core::PropertyKind::DivisionByZero => Self::DivisionByZero,
            trust_mc_core::PropertyKind::OutOfBounds => Self::OutOfBounds,
            trust_mc_core::PropertyKind::NullPointer => Self::NullPointer,
            trust_mc_core::PropertyKind::MemorySafety => Self::MemorySafety,
            trust_mc_core::PropertyKind::PointerOverflow => Self::PointerOverflow,
            trust_mc_core::PropertyKind::Unreachable => Self::Unreachable,
            trust_mc_core::PropertyKind::Panic => Self::Panic,
            trust_mc_core::PropertyKind::UndefinedBehavior => Self::UndefinedBehavior,
            trust_mc_core::PropertyKind::Precondition => Self::Precondition,
            trust_mc_core::PropertyKind::Postcondition => Self::Postcondition,
            trust_mc_core::PropertyKind::LoopInvariant => Self::LoopInvariant,
            trust_mc_core::PropertyKind::Other => Self::Other,
        }
    }
}

#[cfg(feature = "trust-mc-core-types")]
impl From<TrustMcPropertyKind> for trust_mc_core::PropertyKind {
    fn from(kind: TrustMcPropertyKind) -> Self {
        match kind {
            TrustMcPropertyKind::Assertion => Self::Assertion,
            TrustMcPropertyKind::Assumption => Self::Assumption,
            TrustMcPropertyKind::Cover => Self::Cover,
            TrustMcPropertyKind::ArithmeticOverflow => Self::ArithmeticOverflow,
            TrustMcPropertyKind::DivisionByZero => Self::DivisionByZero,
            TrustMcPropertyKind::OutOfBounds => Self::OutOfBounds,
            TrustMcPropertyKind::NullPointer => Self::NullPointer,
            TrustMcPropertyKind::MemorySafety => Self::MemorySafety,
            TrustMcPropertyKind::PointerOverflow => Self::PointerOverflow,
            TrustMcPropertyKind::Unreachable => Self::Unreachable,
            TrustMcPropertyKind::Panic => Self::Panic,
            TrustMcPropertyKind::UndefinedBehavior => Self::UndefinedBehavior,
            TrustMcPropertyKind::Precondition => Self::Precondition,
            TrustMcPropertyKind::Postcondition => Self::Postcondition,
            TrustMcPropertyKind::LoopInvariant => Self::LoopInvariant,
            TrustMcPropertyKind::Other => Self::Other,
        }
    }
}

/// A typed value from the solver model.
///
/// Preserves the SMT sort information that text-based counterexamples lose.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TypedValue {
    /// Boolean value.
    Bool(bool),
    /// Signed integer.
    Int(i128),
    /// Unsigned integer.
    Uint(u128),
    /// Bitvector with explicit width.
    BitVec {
        /// The bitvector value.
        value: u128,
        /// Width in bits.
        width: u32,
    },
    /// String representation for complex values.
    String(String),
}

/// A step in a multi-step counterexample trace.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceStep {
    /// Step index (0-based).
    pub step: u32,
    /// Variable assignments at this step.
    pub assignments: BTreeMap<String, TypedValue>,
    /// Program point (basic block or line number) if available.
    pub program_point: Option<String>,
}

/// A diagnostic message from trust_mc during verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiagnosticMessage {
    /// Severity level.
    pub level: DiagLevel,
    /// The message text.
    pub message: String,
    /// Source location if available.
    pub location: Option<String>,
}

/// Diagnostic severity level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DiagLevel {
    /// Error diagnostic.
    Error,
    /// Warning diagnostic.
    Warning,
    /// Note/info diagnostic.
    Note,
}

/// Information about a specific violation found during verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ViolationInfo {
    /// The kind of property that was violated.
    pub kind: TrustMcPropertyKind,
    /// Human-readable description of the violation.
    pub message: String,
    /// Source location if available.
    pub location: Option<String>,
}

/// Encoding context from `encode_function`.
///
/// In Phase 1 (subprocess mode), this contains the SMT-LIB2 script and metadata.
/// In Phase 2 (trust-build / direct mode), this will contain ay `Context`,
/// local variable mappings (`MirLocal -> ay::Expr`), and the base constraint set.
#[derive(Debug, Clone)]
pub struct EncodingContext {
    /// The function being encoded.
    pub function_name: String,

    /// The SMT-LIB2 script representing the encoding.
    pub smtlib_script: String,

    /// BMC depth used for the encoding.
    pub bmc_depth: u32,

    /// Requested proof mode for this encoding.
    pub proof_mode: TrustMcProofMode,

    /// Provenance attached to this encoding.
    pub proof_provenance: TrustMcProofProvenance,

    /// Variable declarations extracted from the script.
    pub variable_names: Vec<String>,

    /// Native encoded artifact when the trust_mc native facade is enabled.
    pub native_artifact: Option<NativeEncodingArtifact>,
}

/// Opaque native artifact captured from trust-mc-compiler's native facade.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeEncodingArtifact {
    /// Stable obligation identifier.
    pub obligation_id: String,
    /// Function or harness name.
    pub function_name: String,
    /// Artifact kind.
    pub kind: NativeEncodingKind,
    /// Opaque payload for trust-mc-driver.
    pub payload: Vec<u8>,
    /// Encoding provenance.
    pub provenance: TrustMcProofProvenance,
}

/// Native artifact kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeEncodingKind {
    /// Bounded model checking artifact.
    Bmc,
    /// Constrained Horn Clause artifact.
    Chc,
}

impl EncodingContext {
    /// Create an encoding context from an SMT-LIB2 script.
    pub(crate) fn from_smtlib(
        function_name: String,
        smtlib_script: String,
        bmc_depth: u32,
    ) -> Self {
        Self::from_smtlib_with_provenance(
            function_name,
            smtlib_script,
            TrustMcProofProvenance::bmc(bmc_depth, "trust-bmc-subprocess"),
            None,
        )
    }

    /// Create an encoding context from SMT-LIB2 plus explicit provenance.
    pub(crate) fn from_smtlib_with_provenance(
        function_name: String,
        smtlib_script: String,
        proof_provenance: TrustMcProofProvenance,
        native_artifact: Option<NativeEncodingArtifact>,
    ) -> Self {
        // Extract variable names from declare-const lines
        let variable_names = smtlib_script
            .lines()
            .filter_map(|line| {
                let trimmed = line.trim();
                if trimmed.starts_with("(declare-const ") {
                    let rest = trimmed.strip_prefix("(declare-const ")?;
                    let name_end = rest.find(|c: char| c.is_whitespace())?;
                    Some(rest[..name_end].to_string())
                } else {
                    None
                }
            })
            .collect();

        let bmc_depth = proof_provenance.bmc_depth.unwrap_or(0);
        let proof_mode = proof_provenance.proof_mode;

        Self {
            function_name,
            smtlib_script,
            bmc_depth,
            proof_mode,
            proof_provenance,
            variable_names,
            native_artifact,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn proved_result(proof_mode: TrustMcProofMode, bmc_depth: u32) -> TrustMcResult {
        TrustMcResult {
            verdict: Verdict::Proved,
            counterexample: None,
            proof_certificate: None,
            violations: Vec::new(),
            proof_mode,
            proof_provenance: Some(match proof_mode {
                TrustMcProofMode::Bmc => TrustMcProofProvenance::bmc(bmc_depth, "test"),
                TrustMcProofMode::FiniteAcyclicBmc => {
                    TrustMcProofProvenance::finite_acyclic_bmc(bmc_depth, "test")
                }
                TrustMcProofMode::Chc | TrustMcProofMode::PdrIc3 => {
                    TrustMcProofProvenance::unbounded(proof_mode, "test")
                }
            }),
            time_ms: 7,
            diagnostics: Vec::new(),
            bmc_depth,
            function_name: "test_fn".to_string(),
        }
    }

    #[test]
    fn bmc_proved_maps_to_bounded_strength() {
        let result = proved_result(TrustMcProofMode::Bmc, 12).to_verification_result();

        let trust_types::VerificationResult::Proved { strength, .. } = result else {
            panic!("expected proved result");
        };
        assert_eq!(strength, trust_types::ProofStrength::bounded(12));
        assert_eq!(strength.bounded_depth(), Some(12));
    }

    #[test]
    fn finite_acyclic_bmc_proved_maps_to_complete_finite_strength() {
        let result = proved_result(TrustMcProofMode::FiniteAcyclicBmc, 12).to_verification_result();

        let trust_types::VerificationResult::Proved { strength, .. } = result else {
            panic!("expected proved result");
        };
        assert_eq!(
            strength,
            trust_types::ProofStrength {
                reasoning: trust_types::ReasoningKind::ExhaustiveFinite(12),
                assurance: trust_types::AssuranceLevel::Sound,
            }
        );
        assert!(!strength.is_bounded());
    }

    #[test]
    fn chc_proved_maps_to_unbounded_chc_strength() {
        let result = proved_result(TrustMcProofMode::Chc, 12).to_verification_result();

        let trust_types::VerificationResult::Proved { strength, .. } = result else {
            panic!("expected proved result");
        };
        assert_eq!(strength, trust_types::ProofStrength::chc_spacer());
        assert!(!strength.is_bounded());
    }

    #[test]
    fn pdr_ic3_proved_maps_to_unbounded_pdr_strength() {
        let result = proved_result(TrustMcProofMode::PdrIc3, 12).to_verification_result();

        let trust_types::VerificationResult::Proved { strength, .. } = result else {
            panic!("expected proved result");
        };
        assert_eq!(strength, trust_types::ProofStrength::pdr());
        assert!(!strength.is_bounded());
    }

    #[cfg(feature = "trust-mc-core-types")]
    #[test]
    fn trust_mc_core_modes_convert_to_local_proof_modes() {
        assert_eq!(
            TrustMcProofMode::from(trust_mc_core::VerificationMode::Bmc),
            TrustMcProofMode::Bmc
        );
        assert_eq!(
            TrustMcProofMode::from(trust_mc_core::VerificationMode::Chc),
            TrustMcProofMode::Chc
        );
    }

    #[cfg(feature = "trust-mc-core-types")]
    #[test]
    fn trust_mc_core_property_kinds_convert_to_local_result_kinds() {
        let pairs = [
            (trust_mc_core::PropertyKind::Assertion, TrustMcPropertyKind::Assertion),
            (trust_mc_core::PropertyKind::Assumption, TrustMcPropertyKind::Assumption),
            (trust_mc_core::PropertyKind::Cover, TrustMcPropertyKind::Cover),
            (
                trust_mc_core::PropertyKind::ArithmeticOverflow,
                TrustMcPropertyKind::ArithmeticOverflow,
            ),
            (
                trust_mc_core::PropertyKind::DivisionByZero,
                TrustMcPropertyKind::DivisionByZero,
            ),
            (trust_mc_core::PropertyKind::OutOfBounds, TrustMcPropertyKind::OutOfBounds),
            (trust_mc_core::PropertyKind::NullPointer, TrustMcPropertyKind::NullPointer),
            (trust_mc_core::PropertyKind::MemorySafety, TrustMcPropertyKind::MemorySafety),
            (
                trust_mc_core::PropertyKind::PointerOverflow,
                TrustMcPropertyKind::PointerOverflow,
            ),
            (trust_mc_core::PropertyKind::Unreachable, TrustMcPropertyKind::Unreachable),
            (trust_mc_core::PropertyKind::Panic, TrustMcPropertyKind::Panic),
            (
                trust_mc_core::PropertyKind::UndefinedBehavior,
                TrustMcPropertyKind::UndefinedBehavior,
            ),
            (trust_mc_core::PropertyKind::Precondition, TrustMcPropertyKind::Precondition),
            (trust_mc_core::PropertyKind::Postcondition, TrustMcPropertyKind::Postcondition),
            (trust_mc_core::PropertyKind::LoopInvariant, TrustMcPropertyKind::LoopInvariant),
            (trust_mc_core::PropertyKind::Other, TrustMcPropertyKind::Other),
        ];

        for (core, local) in pairs {
            assert_eq!(TrustMcPropertyKind::from(core), local);
            assert_eq!(trust_mc_core::PropertyKind::from(local), core);
        }
    }

    #[test]
    fn only_ordinary_bmc_reports_bounded_mode() {
        assert!(TrustMcProofMode::Bmc.is_bounded());
        assert!(!TrustMcProofMode::FiniteAcyclicBmc.is_bounded());
        assert!(TrustMcProofMode::FiniteAcyclicBmc.is_finite_acyclic_bmc());
        assert!(!TrustMcProofMode::Chc.is_bounded());
        assert!(!TrustMcProofMode::PdrIc3.is_bounded());
    }
}
