//! trust-wasm-bridge: trust-types/trust-ir → WebAssembly.
//!
//! Two paths live here:
//!
//! - [`binary`] — a binary `.wasm` lowering front door for already-closed
//!   `VerifiableFunction`/trust-ir inputs. It is not a Rust linker and is not
//!   used by `rustc_codegen_trust_cg` for linked crates.
//! - The WAT-text helpers below intentionally accept only a tiny, auditable
//!   subset of `trust_types::VerifiableFunction` (a single straight-line block
//!   returning a simple integer expression from constants, parameters, local
//!   copies, and add/sub), rejecting everything else fail-closed with
//!   validation records and an unsupported ledger. They exist for
//!   inspection/audit, not production emission.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![forbid(unsafe_code)]
#![allow(clippy::module_name_repetitions)]

pub mod binary;
pub use binary::{
    WasmCompileError, compile_functions_to_wasm, compile_trust_ir_module_to_wasm,
};

use std::collections::HashMap;

use thiserror::Error;
use trust_ir::Module as TrustIrModule;
use trust_ir::dialect::{AttrValue, DialectInst};
use trust_ir::inst::Inst;
use trust_types::{
    BinOp, BinaryOrigin, ConstValue, DecompileTarget, Formula, Operand, Place,
    ProofCertificateStatus, ReconstructionCandidateKind, ReconstructionValidationDirection,
    ReconstructionValidationDirectionRecord, ReconstructionValidationEvidence,
    ReconstructionValidationRecord, ReconstructionValidationStatus, ReplayStatus, Rvalue, Sort,
    SourceSpan, Statement, Terminator, TrustLevel, Ty, UnsupportedLedger, UnsupportedRecord,
    VerifiableFunction, infer_sort, stable_sha256_hex,
};

const STAGE: &str = "trust-wasm-bridge";
const SUBSET: &str = "wasm-simple-integer-or-unit-return";
const SYMBOLIC_FORMULA_DIALECT: &str = "trust_symbolic";
const SYMBOLIC_FORMULA_OP: &str = "formula";
const SYMBOLIC_FORMULA_ATTR_SCHEMA: &str = "schema";
const SYMBOLIC_FORMULA_ATTR_JSON: &str = "formula_json";
const SYMBOLIC_FORMULA_ATTR_SMTLIB: &str = "formula.smtlib2";
const SYMBOLIC_FORMULA_ATTR_SORT: &str = "formula.sort";
const SYMBOLIC_FORMULA_ATTR_DEBUG: &str = "formula.debug";
const SYMBOLIC_FORMULA_SCHEMA: &str = "trust-types.Formula@1";
const BINARY_PROVENANCE_DIALECT: &str = "trust_binary";
const BINARY_PROVENANCE_OP: &str = "provenance";
const BINARY_PROVENANCE_ATTR_SCHEMA: &str = "schema";
const BINARY_PROVENANCE_ATTR_SOURCE: &str = "source";
const BINARY_PROVENANCE_ATTR_BINARY_PATH: &str = "binary_path";
const BINARY_PROVENANCE_ATTR_FUNCTION_ENTRY: &str = "function_entry";
const BINARY_PROVENANCE_ATTR_INSTRUCTION_ADDRESS: &str = "instruction_address";
const BINARY_PROVENANCE_ATTR_INSTRUCTION_SIZE: &str = "instruction_size";
const BINARY_PROVENANCE_ATTR_ENCODING: &str = "encoding";
const BINARY_PROVENANCE_ATTR_INSTRUCTION_BYTES: &str = "instruction_bytes";
const BINARY_PROVENANCE_ATTR_TARGET_SEMANTICS_CONSUMED: &str = "target_semantics_consumed";
const BINARY_PROVENANCE_SCHEMA: &str = "trust-types.BinaryProvenance@1";
const PROOF_METADATA_DIALECT: &str = "trust_proof";
const CHECKED_CERTIFICATE_OP: &str = "checked_certificate";
const PROOF_REPLAY_OP: &str = "proof_replay";
const UNSUPPORTED_LEDGER_OP: &str = "unsupported_ledger";
const PROOF_METADATA_ATTR_SCHEMA: &str = "schema";
const PROOF_METADATA_ATTR_SOURCE: &str = "source";
const PROOF_METADATA_ATTR_STATUS_JSON: &str = "status_json";
const PROOF_METADATA_ATTR_CHECKER: &str = "checker";
const PROOF_METADATA_ATTR_FORMAT: &str = "format";
const PROOF_METADATA_ATTR_SHA256: &str = "sha256";
const PROOF_METADATA_ATTR_CERTIFICATE_CHECKED: &str = "certificate_checked";
const PROOF_METADATA_ATTR_REPLAY_STATUS: &str = "replay_status";
const PROOF_METADATA_ATTR_ARTIFACT_SHA256: &str = "artifact_sha256";
const PROOF_METADATA_ATTR_EXACT_REPLAY_CHECKED: &str = "exact_replay_checked";
const PROOF_METADATA_ATTR_UNSUPPORTED_RECORDS: &str = "unsupported_records";
const PROOF_METADATA_ATTR_VERIFICATION_UNSUPPORTED: &str = "verification_unsupported";
const PROOF_METADATA_ATTR_TARGET_SEMANTICS_CONSUMED: &str = "target_semantics_consumed";
const CHECKED_CERTIFICATE_SCHEMA: &str = "trust-types.CheckedCertificate@1";
const PROOF_REPLAY_SCHEMA: &str = "trust-types.ProofReplay@1";
const UNSUPPORTED_LEDGER_SCHEMA: &str = "trust-types.UnsupportedLedger@1";
const WASM_TARGET_SEMANTIC_CONSUMER: &str = "trust-wasm-bridge::target-semantic-consumption-gate";
const WASM_BOUNDED_EMPTY_TARGET_CONSUMED_CODE: &str = "bounded-empty-wasm-target-consumed";

/// Wasm-specific validation gate for converted binary-derived TrustIr.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmTargetValidationStatus {
    /// WAT was emitted for inspection, but the target artifact is rejected
    /// until refinement metadata and checked proof evidence are attached.
    InspectableRejected,
    /// No inspectable WAT was emitted.
    Rejected,
}

/// Explicit blocker keeping a Wasm conversion below proof grade.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmValidationBlocker {
    /// Stable machine-readable blocker code.
    pub code: String,
    /// Human-readable explanation.
    pub detail: String,
}

/// Symbolic formula carried through conversion metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmSymbolicFormula {
    /// Function containing the symbolic operand.
    pub function: String,
    /// Source TrustIr block id.
    pub block: usize,
    /// Statement index within the source block.
    pub statement_index: usize,
    /// Operand role within the statement/rvalue.
    pub operand: String,
    /// Original symbolic formula from lifted binary TrustIr.
    pub formula: Formula,
    /// Inferred SMT sort for the formula, serialized as SMT-LIB2 text.
    pub sort: String,
    /// Bit-vector width when the inferred sort is a fixed-width machine value.
    pub bit_width: Option<u32>,
}

/// Bridge-owned Wasm target-semantic consumption decision for one proof input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmTargetSemanticConsumptionEvidence {
    /// Component that made the authoritative consumption decision.
    pub consumer: String,
    /// True only when this bridge has target-owned evidence that semantics consumed the input.
    pub target_semantics_consumed: bool,
    /// Untrusted canonical metadata claim, preserved for audit but never accepted as authority.
    pub input_claimed_target_semantics_consumed: Option<bool>,
    /// Stable machine-readable rejection or acceptance code.
    pub code: String,
    /// Human-readable explanation of the decision.
    pub detail: String,
}

/// Binary provenance carried into the Wasm target proof-consumer gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmProvenanceEvidence {
    /// Function associated with this provenance record.
    pub function: String,
    /// Source of the provenance record inside the conversion pipeline.
    pub source: String,
    /// Source TrustIr block id, when the record comes from a statement span.
    pub block: Option<usize>,
    /// Statement index, when the record comes from a statement span.
    pub statement_index: Option<usize>,
    /// Original machine-code origin.
    pub origin: BinaryOrigin,
    /// Bridge-owned target-semantic consumption decision for this provenance.
    pub target_semantic_consumption: WasmTargetSemanticConsumptionEvidence,
    /// False until executable Wasm target semantics consume this provenance.
    pub target_semantics_consumed: bool,
}

/// Checked certificate metadata carried into the Wasm target proof-consumer gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmCheckedCertificateEvidence {
    /// Function associated with this checked certificate record.
    pub function: String,
    /// Source of the certificate metadata inside the conversion pipeline.
    pub source: String,
    /// Source TrustIr block id, when the record comes from canonical TrustIr.
    pub block: Option<usize>,
    /// Statement index, when the record comes from canonical TrustIr.
    pub statement_index: Option<usize>,
    /// Canonical trust-types certificate status parsed from conversion metadata.
    pub certificate: ProofCertificateStatus,
    /// Bridge-owned target-semantic consumption decision for this certificate.
    pub target_semantic_consumption: WasmTargetSemanticConsumptionEvidence,
    /// False until executable Wasm target semantics consume this certificate.
    pub target_semantics_consumed: bool,
}

/// Proof replay metadata carried into the Wasm target proof-consumer gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmProofReplayEvidence {
    /// Function associated with this replay record.
    pub function: String,
    /// Source of the replay metadata inside the conversion pipeline.
    pub source: String,
    /// Source TrustIr block id, when the record comes from canonical TrustIr.
    pub block: Option<usize>,
    /// Statement index, when the record comes from canonical TrustIr.
    pub statement_index: Option<usize>,
    /// Canonical trust-types replay status parsed from conversion metadata.
    pub replay: ReplayStatus,
    /// Replay artifact digest, when conversion metadata carried one.
    pub artifact_sha256: Option<String>,
    /// True only when metadata claims exact replay was checked.
    pub exact_replay_checked: bool,
    /// Bridge-owned target-semantic consumption decision for this replay record.
    pub target_semantic_consumption: WasmTargetSemanticConsumptionEvidence,
    /// False until executable Wasm target semantics consume this replay record.
    pub target_semantics_consumed: bool,
}

/// Unsupported-ledger elimination evidence carried into the Wasm target proof-consumer gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmUnsupportedLedgerEvidence {
    /// Function associated with this unsupported-ledger record.
    pub function: String,
    /// Source of the ledger metadata inside the conversion pipeline.
    pub source: String,
    /// Source TrustIr block id, when the record comes from canonical TrustIr.
    pub block: Option<usize>,
    /// Statement index, when the record comes from canonical TrustIr.
    pub statement_index: Option<usize>,
    /// Number of unsupported ledger records visible to this target consumer.
    pub unsupported_records: usize,
    /// Binary verification unsupported counter visible to this target consumer.
    pub verification_unsupported: usize,
    /// True only when visible unsupported ledger/counter evidence is empty.
    pub unsupported_ledger_eliminated: bool,
    /// Bridge-owned target-semantic consumption decision for this ledger evidence.
    pub target_semantic_consumption: WasmTargetSemanticConsumptionEvidence,
    /// False until executable Wasm target semantics consume this evidence.
    pub target_semantics_consumed: bool,
}

/// Wasm target proof-consumer acceptance state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmProofConsumerStatus {
    /// Wasm target semantics consumed every carried proof input.
    Accepted,
    /// At least one proof input is absent or has not been consumed by target semantics.
    Rejected,
}

/// One proof-consumer input and its target-acceptance decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmProofConsumerRecord {
    /// Input class, such as `target_semantics`, `symbolic_formula`,
    /// `checked_certificate`, or `proof_replay`.
    pub kind: String,
    /// Stable record identifier for diagnostics and JSON callers.
    pub identifier: String,
    /// True only after Wasm target semantics consumed this input.
    pub accepted: bool,
    /// Human-readable explanation for the decision.
    pub detail: String,
}

/// One canonical proof input bound to the Wasm target output artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmProofBindingInput {
    /// Input class, such as `canonical_trust_ir_formula`, `binary_provenance`,
    /// `checked_certificate`, or `proof_replay`.
    pub kind: String,
    /// Stable input identifier for diagnostics and JSON callers.
    pub identifier: String,
    /// Canonical source namespace for the proof input.
    pub canonical_source: String,
    /// Target artifact this input is meant to justify.
    pub target_output: String,
    /// True only after executable Wasm semantics consumed this input/output edge.
    pub consumed_by_target_semantics: bool,
    /// Human-readable binding detail.
    pub detail: String,
}

/// Bridge-owned proof binding artifact tying Wasm output to proof inputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmTargetProofBinding {
    /// Target semantic domain for this binding.
    pub target: String,
    /// Stable description of the target output artifact.
    pub target_output: String,
    /// Digest of the lifted TrustIr artifact that produced the Wasm target output.
    pub lifted_trust_ir_artifact_digest: Option<String>,
    /// Digest claim consumed by the target proof-consumer binding.
    pub bound_lifted_trust_ir_artifact_digest: Option<String>,
    /// True only when the bound digest exactly matches the lifted TrustIr artifact digest.
    pub lifted_trust_ir_artifact_digest_matched: bool,
    /// Aggregate binding state.
    pub status: WasmProofConsumerStatus,
    /// True only after executable Wasm semantics consumed all binding edges.
    pub target_semantics_consumed: bool,
    /// Canonical TrustIr/provenance/certificate/replay inputs bound to the output.
    pub inputs: Vec<WasmProofBindingInput>,
    /// Machine-readable blockers explaining a rejected binding.
    pub blockers: Vec<WasmValidationBlocker>,
}

/// Wasm-specific source/target refinement row consumed by the proof-consumer gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmRefinementMetadataEvidence {
    /// Narrow slice shape this metadata describes.
    pub slice: String,
    /// Canonical source namespace for the source-side slice.
    pub source: String,
    /// Source TrustIr function.
    pub source_function: String,
    /// Source TrustIr block, when the metadata is statement-bound.
    pub source_block: Option<usize>,
    /// Source TrustIr statement, when the metadata is statement-bound.
    pub source_statement_index: Option<usize>,
    /// Source obligation formula serialized as SMT-LIB2 when available.
    pub source_formula: Option<String>,
    /// Target semantic domain.
    pub target: String,
    /// Stable target output identifier.
    pub target_output: String,
    /// Target Wasm operation or empty-output marker.
    pub target_operation: String,
    /// Forward source-to-target relation summary.
    pub forward_relation: String,
    /// Reverse target-to-source relation summary.
    pub reverse_relation: String,
    /// True only after the Wasm target proof-consumer validates the row.
    pub bidirectional_refinement_consumed: bool,
    /// Stable machine-readable acceptance/rejection code.
    pub code: String,
    /// Human-readable explanation of the decision.
    pub detail: String,
}

/// Explicit Wasm proof-consumer evidence derived from conversion metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmProofConsumerEvidence {
    /// Target semantic domain for this proof-consumer gate.
    pub target: String,
    /// Aggregate proof-consumer status.
    pub status: WasmProofConsumerStatus,
    /// True only after executable Wasm target semantics consumed the carried inputs.
    pub target_semantics_consumed: bool,
    /// Per-input acceptance/rejection records.
    pub records: Vec<WasmProofConsumerRecord>,
    /// Bridge-owned binding artifact for the target output and proof inputs.
    pub binding: WasmTargetProofBinding,
    /// Structured target-refinement evidence visible to proof-grade residual gates.
    pub refinement_metadata_evidence: Vec<WasmRefinementMetadataEvidence>,
    /// Machine-readable blockers explaining a rejected aggregate status.
    pub blockers: Vec<WasmValidationBlocker>,
    /// Residual proof-grade blockers not cleared by target semantic consumption.
    pub proof_grade_blockers: Vec<WasmValidationBlocker>,
}

impl WasmProofConsumerEvidence {
    /// True when Wasm target proof consumption is still rejected.
    #[must_use]
    pub fn is_rejected(&self) -> bool {
        self.status == WasmProofConsumerStatus::Rejected
    }
}

/// Conversion error category for the fail-closed Wasm subset.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum WasmBridgeError {
    /// No lifted TrustIr function was supplied to the converter.
    #[error("missing lifted TrustIr function")]
    MissingLiftedTrustIr,
    /// The function is not one straight-line block ending in `Return`.
    #[error("unsupported control flow: {0}")]
    UnsupportedControlFlow(String),
    /// The function return type cannot be represented in this first Wasm slice.
    #[error("unsupported return type: {0}")]
    UnsupportedReturnType(String),
    /// The body does not reduce to a simple integer return.
    #[error("unsupported return value: {0}")]
    UnsupportedReturnValue(String),
    /// A statement outside the constant-return subset was encountered.
    #[error("unsupported statement: {0}")]
    UnsupportedStatement(String),
    /// Canonical TrustIr text could not be parsed.
    #[error("invalid canonical TrustIr: {0}")]
    InvalidCanonicalTrustIr(String),
    /// Canonical TrustIr contains symbolic formulas that require proof semantics.
    #[error("symbolic formula requires proof-grade Wasm semantics: {0}")]
    SymbolicFormulaRequiresProof(String),
    /// Canonical TrustIr cannot be lowered by this first Wasm bridge slice.
    #[error("unsupported canonical TrustIr: {0}")]
    UnsupportedCanonicalTrustIr(String),
}

impl WasmBridgeError {
    fn feature(&self) -> String {
        self.to_string()
    }
}

/// Result of converting one or more lifted TrustIr functions to WAT text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmConversion {
    /// WAT text when every requested function fit the accepted subset.
    pub wat: Option<String>,
    /// Lowercase SHA-256 over the lifted TrustIr artifact that produced this conversion.
    pub lifted_trust_ir_artifact_digest: Option<String>,
    /// Lowercase SHA-256 that the target proof-consumer binding claims to consume.
    pub bound_lifted_trust_ir_artifact_digest: Option<String>,
    /// Aggregate syntactic subset validation status for this conversion request.
    pub validation: ReconstructionValidationStatus,
    /// Wasm target validation gate status.
    pub wasm_validation: WasmTargetValidationStatus,
    /// Trust level for the emitted WAT or rejection.
    pub trust_level: TrustLevel,
    /// Target-specific blockers that must be resolved before proof-grade use.
    pub validation_blockers: Vec<WasmValidationBlocker>,
    /// Symbolic formulas preserved from lifted TrustIr operands where present.
    pub symbolic_formulas: Vec<WasmSymbolicFormula>,
    /// Binary provenance preserved for target proof consumers.
    pub provenance_evidence: Vec<WasmProvenanceEvidence>,
    /// Checked certificate metadata preserved for target proof consumers.
    pub checked_certificate_evidence: Vec<WasmCheckedCertificateEvidence>,
    /// Proof replay metadata preserved for target proof consumers.
    pub proof_replay_evidence: Vec<WasmProofReplayEvidence>,
    /// Unsupported-ledger elimination metadata preserved for target proof consumers.
    pub unsupported_ledger_evidence: Vec<WasmUnsupportedLedgerEvidence>,
    /// Per-function structured validation records.
    pub validation_records: Vec<ReconstructionValidationRecord>,
    /// Unsupported ledger populated on every rejection.
    pub unsupported: UnsupportedLedger,
    /// Human-readable diagnostics.
    pub diagnostics: Vec<String>,
}

impl WasmConversion {
    /// True when the conversion can be consumed as proof-grade output.
    #[must_use]
    pub fn is_accepted(&self) -> bool {
        let proof_consumer = self.target_proof_consumer_evidence();
        self.wat.is_some()
            && self.validation == ReconstructionValidationStatus::Validated
            && self.wasm_validation == WasmTargetValidationStatus::InspectableRejected
            && self.validation_blockers.is_empty()
            && self.unsupported.is_empty()
            && self.trust_level == TrustLevel::ProofGrade
            && proof_consumer.status == WasmProofConsumerStatus::Accepted
            && proof_consumer.target_semantics_consumed
            && proof_consumer.blockers.is_empty()
    }

    /// True when WAT text was emitted for inspection even though proof-grade
    /// target validation is still blocked.
    #[must_use]
    pub fn is_inspectable(&self) -> bool {
        self.wat.is_some()
            && self.wasm_validation == WasmTargetValidationStatus::InspectableRejected
    }

    /// Explicit proof-consumer evidence for symbolic formulas, checked
    /// certificates, and replay metadata carried by this conversion.
    #[must_use]
    pub fn target_proof_consumer_evidence(&self) -> WasmProofConsumerEvidence {
        build_wasm_proof_consumer_evidence(self)
    }
}

/// Convert a single lifted TrustIr function to a WAT module.
#[must_use]
pub fn convert_function_to_wat(function: &VerifiableFunction) -> WasmConversion {
    convert_functions_to_wat(std::slice::from_ref(function))
}

/// Convert lifted TrustIr functions to one WAT module, failing closed if any
/// function is outside the accepted subset.
#[must_use]
pub fn convert_functions_to_wat(functions: &[VerifiableFunction]) -> WasmConversion {
    if functions.is_empty() {
        return rejected_conversion(None, WasmBridgeError::MissingLiftedTrustIr);
    }

    let lifted_trust_ir_artifact_digest = lifted_trust_ir_artifact_digest_for_functions(functions);
    let mut rendered = Vec::with_capacity(functions.len());
    let mut records = Vec::with_capacity(functions.len());
    let mut symbolic_formulas = Vec::new();
    let mut provenance_evidence = Vec::new();
    let checked_certificate_evidence = Vec::new();
    let proof_replay_evidence = Vec::new();
    let unsupported_ledger_evidence = Vec::new();
    let mut diagnostics = vec![
        format!("subset={SUBSET}"),
        "validation is syntactic subset validation only; Wasm target gate rejects until proof metadata is available".to_string(),
    ];

    for function in functions {
        symbolic_formulas.extend(collect_symbolic_formulas(function));
        let function_provenance = collect_function_provenance_evidence(function);
        diagnostics.extend(function_provenance.iter().map(wasm_provenance_evidence_detail));
        provenance_evidence.extend(function_provenance);
        match lower_function(function) {
            Ok(lowered) => {
                rendered.push(lowered.wat);
                records.push(accepted_record(function));
            }
            Err(error) => {
                let mut conversion = rejected_conversion(Some(function), error);
                records.append(&mut conversion.validation_records);
                diagnostics.append(&mut conversion.diagnostics);
                return WasmConversion {
                    wat: None,
                    lifted_trust_ir_artifact_digest,
                    bound_lifted_trust_ir_artifact_digest: None,
                    validation: ReconstructionValidationStatus::Failed,
                    wasm_validation: WasmTargetValidationStatus::Rejected,
                    trust_level: TrustLevel::Rejected,
                    validation_blockers: conversion.validation_blockers,
                    symbolic_formulas,
                    provenance_evidence,
                    checked_certificate_evidence,
                    proof_replay_evidence,
                    unsupported_ledger_evidence,
                    validation_records: records,
                    unsupported: conversion.unsupported,
                    diagnostics,
                };
            }
        }
    }

    WasmConversion {
        wat: Some(format!("(module\n{}\n)\n", rendered.join(""))),
        lifted_trust_ir_artifact_digest,
        bound_lifted_trust_ir_artifact_digest: None,
        validation: ReconstructionValidationStatus::Validated,
        wasm_validation: WasmTargetValidationStatus::InspectableRejected,
        trust_level: TrustLevel::Rejected,
        validation_blockers: inspectable_validation_blockers(
            &provenance_evidence,
            &checked_certificate_evidence,
            &proof_replay_evidence,
            &unsupported_ledger_evidence,
        ),
        symbolic_formulas,
        provenance_evidence,
        checked_certificate_evidence,
        proof_replay_evidence,
        unsupported_ledger_evidence,
        validation_records: records,
        unsupported: UnsupportedLedger::default(),
        diagnostics,
    }
}

fn lifted_trust_ir_artifact_digest_for_functions(functions: &[VerifiableFunction]) -> Option<String> {
    serde_json::to_vec(functions).ok().map(|bytes| stable_sha256_hex(&bytes))
}

/// Build the standard fail-closed result used when a decompiler function has no
/// lifted TrustIr body to feed into this bridge.
#[must_use]
pub fn reject_missing_lifted_trust_ir(function_name: Option<&str>) -> WasmConversion {
    rejected_conversion_parts(
        function_name.map(str::to_string),
        None,
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        WasmBridgeError::MissingLiftedTrustIr,
    )
}

/// Parse canonical TrustIr text for a downstream Wasm conversion.
///
/// This entrypoint is intentionally fail-closed for symbolic formulas: the
/// formula dialect op is preserved as structured conversion metadata and
/// surfaced as blockers/evidence instead of being translated to Wasm `undef`.
#[must_use]
pub fn convert_canonical_trust_ir_to_wat(canonical_trust_ir: &str) -> WasmConversion {
    match trust_ir::parser::parse_module(canonical_trust_ir) {
        Ok(module) => {
            let mut conversion = convert_trust_ir_module_to_wat(&module);
            conversion.lifted_trust_ir_artifact_digest =
                Some(stable_sha256_hex(canonical_trust_ir.as_bytes()));
            conversion
        }
        Err(err) => rejected_conversion_parts(
            None,
            None,
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            WasmBridgeError::InvalidCanonicalTrustIr(err.to_string()),
        ),
    }
}

/// Convert an already parsed canonical TrustIr module to a Wasm conversion result.
#[must_use]
pub fn convert_trust_ir_module_to_wat(module: &TrustIrModule) -> WasmConversion {
    let symbolic_metadata = collect_trust_ir_symbolic_formulas(module);
    let mut provenance_evidence = collect_trust_ir_provenance_evidence(module);
    let mut checked_certificate_evidence = collect_trust_ir_checked_certificate_evidence(module);
    let mut proof_replay_evidence = collect_trust_ir_proof_replay_evidence(module);
    let mut unsupported_ledger_evidence = collect_trust_ir_unsupported_ledger_evidence(module);
    apply_bounded_empty_target_consumption_to_canonical_evidence(
        module,
        &symbolic_metadata,
        &mut checked_certificate_evidence,
        &mut proof_replay_evidence,
        &mut provenance_evidence,
        &mut unsupported_ledger_evidence,
    );
    if !symbolic_metadata.is_empty() {
        return rejected_symbolic_trust_ir_conversion(
            module,
            symbolic_metadata,
            provenance_evidence,
            checked_certificate_evidence,
            proof_replay_evidence,
            unsupported_ledger_evidence,
        );
    }

    rejected_conversion_parts(
        None,
        provenance_evidence.first().map(|entry| entry.origin.clone()),
        Vec::new(),
        provenance_evidence,
        checked_certificate_evidence,
        proof_replay_evidence,
        unsupported_ledger_evidence,
        WasmBridgeError::UnsupportedCanonicalTrustIr(
            "TrustIr-to-Wasm lowering currently requires the lifted trust-types body".to_string(),
        ),
    )
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LoweredFunction {
    wat: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum WasmExpr {
    Const(i128),
    Param(usize),
    Add(Box<WasmExpr>, Box<WasmExpr>),
    Sub(Box<WasmExpr>, Box<WasmExpr>),
}

impl WasmExpr {
    fn is_const_expr(&self) -> bool {
        match self {
            WasmExpr::Const(_) => true,
            WasmExpr::Param(_) => false,
            WasmExpr::Add(lhs, rhs) | WasmExpr::Sub(lhs, rhs) => {
                lhs.is_const_expr() && rhs.is_const_expr()
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LoweredBody {
    params: Vec<WasmParam>,
    value: WasmExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LoweredFunctionKind {
    Result { wasm_ty: &'static str, body: LoweredBody },
    Unit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct WasmParam {
    local: usize,
    wasm_ty: &'static str,
}

fn lower_function(function: &VerifiableFunction) -> Result<LoweredFunction, WasmBridgeError> {
    let block = match function.body.blocks.as_slice() {
        [block] if matches!(block.terminator, Terminator::Return) => block,
        [] => {
            return Err(WasmBridgeError::UnsupportedControlFlow(
                "function body has no basic blocks".to_string(),
            ));
        }
        [_] => {
            return Err(WasmBridgeError::UnsupportedControlFlow(
                "single block does not end in Return".to_string(),
            ));
        }
        blocks => {
            return Err(WasmBridgeError::UnsupportedControlFlow(format!(
                "expected one return block, found {} blocks",
                blocks.len()
            )));
        }
    };

    let lowered = match &function.body.return_ty {
        Ty::Unit => LoweredFunctionKind::Unit,
        _ => {
            let wasm_ty = wasm_result_type(&function.body.return_ty)?;
            LoweredFunctionKind::Result {
                wasm_ty,
                body: simple_return_body(function, block.stmts.as_slice(), wasm_ty)?,
            }
        }
    };
    let symbol = wat_symbol(&function.name);
    let export = wat_string(&function.name);
    let wat = match lowered {
        LoweredFunctionKind::Result { wasm_ty, body } => {
            let params = render_params(&body.params);
            let instructions = render_expr(&body.value, wasm_ty)?.join("\n");
            format!(
                "  (func ${symbol}{params} (result {wasm_ty})\n{instructions})\n  (export \"{export}\" (func ${symbol}))\n"
            )
        }
        LoweredFunctionKind::Unit => {
            format!("  (func ${symbol})\n  (export \"{export}\" (func ${symbol}))\n")
        }
    };

    Ok(LoweredFunction { wat })
}

fn wasm_result_type(ty: &Ty) -> Result<&'static str, WasmBridgeError> {
    match ty {
        Ty::Int { width, .. } | Ty::Bv(width) if *width <= 32 => Ok("i32"),
        Ty::Int { width, .. } | Ty::Bv(width) if *width <= 64 => Ok("i64"),
        other => Err(WasmBridgeError::UnsupportedReturnType(format!("{other:?}"))),
    }
}

fn simple_return_body(
    function: &VerifiableFunction,
    stmts: &[Statement],
    wasm_ty: &'static str,
) -> Result<LoweredBody, WasmBridgeError> {
    let mut locals: HashMap<usize, WasmExpr> = HashMap::new();
    let mut params = Vec::with_capacity(function.body.arg_count);

    for local in 1..=function.body.arg_count {
        let Some(decl) = function.body.locals.iter().find(|decl| decl.index == local) else {
            return Err(WasmBridgeError::UnsupportedReturnValue(format!(
                "argument local _{local} has no declaration"
            )));
        };
        let param_ty = wasm_result_type(&decl.ty).map_err(|_| {
            WasmBridgeError::UnsupportedReturnValue(format!(
                "argument local _{local} has unsupported type {:?}",
                decl.ty
            ))
        })?;
        if param_ty != wasm_ty {
            return Err(WasmBridgeError::UnsupportedReturnValue(format!(
                "argument local _{local} type {param_ty} does not match result type {wasm_ty}"
            )));
        }
        locals.insert(local, WasmExpr::Param(local));
        params.push(WasmParam { local, wasm_ty: param_ty });
    }

    for stmt in stmts {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            return Err(WasmBridgeError::UnsupportedStatement(format!("{stmt:?}")));
        };
        if !place.projections.is_empty() {
            return Err(WasmBridgeError::UnsupportedStatement(format!(
                "assignment to projected place {:?}",
                place.projections
            )));
        }

        let value = match rvalue {
            Rvalue::Use(operand) => operand_expr(operand, &locals)?,
            Rvalue::BinaryOp(BinOp::Add, lhs, rhs) => binary_expr(BinOp::Add, lhs, rhs, &locals)?,
            Rvalue::BinaryOp(BinOp::Sub, lhs, rhs) => binary_expr(BinOp::Sub, lhs, rhs, &locals)?,
            other => {
                return Err(WasmBridgeError::UnsupportedStatement(format!(
                    "unsupported rvalue {other:?}"
                )));
            }
        };

        locals.insert(place.local, value);
    }

    let value = locals.get(&0).cloned().ok_or_else(|| {
        WasmBridgeError::UnsupportedReturnValue("return place _0 was not assigned".to_string())
    })?;

    Ok(LoweredBody { params, value })
}

fn binary_expr(
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    locals: &HashMap<usize, WasmExpr>,
) -> Result<WasmExpr, WasmBridgeError> {
    let lhs = operand_expr(lhs, locals)?;
    let rhs = operand_expr(rhs, locals)?;
    if !lhs.is_const_expr() && !rhs.is_const_expr() {
        return Err(WasmBridgeError::UnsupportedStatement(format!(
            "{op:?} requires at least one constant operand"
        )));
    }

    match op {
        BinOp::Add => Ok(WasmExpr::Add(Box::new(lhs), Box::new(rhs))),
        BinOp::Sub => Ok(WasmExpr::Sub(Box::new(lhs), Box::new(rhs))),
        other => {
            Err(WasmBridgeError::UnsupportedStatement(format!("unsupported binary op {other:?}")))
        }
    }
}

fn operand_expr(
    operand: &Operand,
    locals: &HashMap<usize, WasmExpr>,
) -> Result<WasmExpr, WasmBridgeError> {
    match operand {
        Operand::Constant(ConstValue::Int(value)) => Ok(WasmExpr::Const(*value)),
        Operand::Constant(ConstValue::Uint(value, _)) => {
            let value = i128::try_from(*value).map_err(|_| {
                WasmBridgeError::UnsupportedReturnValue(format!(
                    "unsigned constant {value} is outside i128"
                ))
            })?;
            Ok(WasmExpr::Const(value))
        }
        Operand::Copy(place) | Operand::Move(place) => local_expr(place, locals),
        other => {
            Err(WasmBridgeError::UnsupportedReturnValue(format!("unsupported operand {other:?}")))
        }
    }
}

fn local_expr(
    place: &Place,
    locals: &HashMap<usize, WasmExpr>,
) -> Result<WasmExpr, WasmBridgeError> {
    if !place.projections.is_empty() {
        return Err(WasmBridgeError::UnsupportedReturnValue(format!(
            "projected local copy {:?}",
            place.projections
        )));
    }
    locals.get(&place.local).cloned().ok_or_else(|| {
        WasmBridgeError::UnsupportedReturnValue(format!(
            "local _{} is not a known simple integer expression",
            place.local
        ))
    })
}

fn render_params(params: &[WasmParam]) -> String {
    params
        .iter()
        .map(|param| format!(" (param ${} {})", param_symbol(param.local), param.wasm_ty))
        .collect()
}

fn render_expr(expr: &WasmExpr, wasm_ty: &str) -> Result<Vec<String>, WasmBridgeError> {
    let mut lines = Vec::new();
    render_expr_into(expr, wasm_ty, &mut lines)?;
    Ok(lines)
}

fn render_expr_into(
    expr: &WasmExpr,
    wasm_ty: &str,
    lines: &mut Vec<String>,
) -> Result<(), WasmBridgeError> {
    match expr {
        WasmExpr::Const(value) => {
            let literal = wasm_literal(*value, wasm_ty)?;
            lines.push(format!("    {wasm_ty}.const {literal}"));
        }
        WasmExpr::Param(local) => {
            lines.push(format!("    local.get ${}", param_symbol(*local)));
        }
        WasmExpr::Add(lhs, rhs) => {
            render_expr_into(lhs, wasm_ty, lines)?;
            render_expr_into(rhs, wasm_ty, lines)?;
            lines.push(format!("    {wasm_ty}.add"));
        }
        WasmExpr::Sub(lhs, rhs) => {
            render_expr_into(lhs, wasm_ty, lines)?;
            render_expr_into(rhs, wasm_ty, lines)?;
            lines.push(format!("    {wasm_ty}.sub"));
        }
    }
    Ok(())
}

fn wasm_literal(value: i128, wasm_ty: &str) -> Result<String, WasmBridgeError> {
    match wasm_ty {
        "i32" => i32::try_from(value).map(|value| value.to_string()).map_err(|_| {
            WasmBridgeError::UnsupportedReturnValue(format!("{value} does not fit i32"))
        }),
        "i64" => i64::try_from(value).map(|value| value.to_string()).map_err(|_| {
            WasmBridgeError::UnsupportedReturnValue(format!("{value} does not fit i64"))
        }),
        other => Err(WasmBridgeError::UnsupportedReturnType(other.to_string())),
    }
}

fn accepted_record(function: &VerifiableFunction) -> ReconstructionValidationRecord {
    ReconstructionValidationRecord {
        target: DecompileTarget::Wasm,
        function: Some(function.name.clone()),
        lifted_function: Some(function.name.clone()),
        reconstructed_function: Some(function.name.clone()),
        candidate: ReconstructionCandidateKind::Other(SUBSET.to_string()),
        status: ReconstructionValidationStatus::Validated,
        trust_level: TrustLevel::Rejected,
        forward: Some(validation_direction(
            ReconstructionValidationDirection::LiftedToOutput,
            ReconstructionValidationStatus::Validated,
        )),
        reverse: Some(validation_direction(
            ReconstructionValidationDirection::OutputToLifted,
            ReconstructionValidationStatus::Validated,
        )),
        evidence: vec![
            ReconstructionValidationEvidence::Other(
                "StrictWasmSimpleIntegerOrUnitReturnSubset".to_string(),
            ),
            ReconstructionValidationEvidence::NoCheckedProofCertificate,
            ReconstructionValidationEvidence::Other("NoProofReplayMetadata".to_string()),
            ReconstructionValidationEvidence::NoBinaryProofObligation,
        ],
        diagnostics: vec![
            "Wasm text emitted for simple integer or no-result unit return subset inspection"
                .to_string(),
            "validated means subset shape checked; target validation remains rejected".to_string(),
            "trust level is Rejected until checked proof/refinement metadata exists".to_string(),
        ],
    }
}

fn validation_record_proof_metadata_evidence(
    checked_certificate_evidence: &[WasmCheckedCertificateEvidence],
    proof_replay_evidence: &[WasmProofReplayEvidence],
    unsupported_ledger_evidence: &[WasmUnsupportedLedgerEvidence],
) -> Vec<ReconstructionValidationEvidence> {
    let mut evidence = Vec::new();
    if checked_certificate_evidence.is_empty() {
        evidence.push(ReconstructionValidationEvidence::NoCheckedProofCertificate);
    } else {
        evidence.push(ReconstructionValidationEvidence::Other(format!(
            "CheckedProofCertificateMetadataPreserved:{}",
            checked_certificate_evidence.len()
        )));
        for entry in checked_certificate_evidence {
            evidence.push(ReconstructionValidationEvidence::Other(format!(
                "checked_certificate.identifier={}",
                wasm_checked_certificate_identifier(entry)
            )));
            evidence.push(ReconstructionValidationEvidence::Other(format!(
                "checked_certificate.target_semantics_consumed={}",
                entry.target_semantics_consumed
            )));
        }
    }

    if proof_replay_evidence.is_empty() {
        evidence.push(ReconstructionValidationEvidence::Other("NoProofReplayMetadata".to_string()));
    } else {
        evidence.push(ReconstructionValidationEvidence::Other(format!(
            "ProofReplayMetadataPreserved:{}",
            proof_replay_evidence.len()
        )));
        for entry in proof_replay_evidence {
            evidence.push(ReconstructionValidationEvidence::Other(format!(
                "proof_replay.identifier={}",
                wasm_proof_replay_identifier(entry)
            )));
            evidence.push(ReconstructionValidationEvidence::Other(format!(
                "proof_replay.target_semantics_consumed={}",
                entry.target_semantics_consumed
            )));
        }
    }

    if unsupported_ledger_evidence.is_empty() {
        evidence.push(ReconstructionValidationEvidence::Other(
            "NoUnsupportedLedgerEliminationMetadata".to_string(),
        ));
    } else {
        evidence.push(ReconstructionValidationEvidence::Other(format!(
            "UnsupportedLedgerEliminationMetadataPreserved:{}",
            unsupported_ledger_evidence.len()
        )));
        for entry in unsupported_ledger_evidence {
            evidence.push(ReconstructionValidationEvidence::Other(format!(
                "unsupported_ledger.identifier={}",
                wasm_unsupported_ledger_identifier(entry)
            )));
            evidence.push(ReconstructionValidationEvidence::Other(format!(
                "unsupported_ledger.eliminated={}",
                entry.unsupported_ledger_eliminated
            )));
            evidence.push(ReconstructionValidationEvidence::Other(format!(
                "unsupported_ledger.target_semantics_consumed={}",
                entry.target_semantics_consumed
            )));
        }
    }
    evidence
}

fn rejected_conversion(
    function: Option<&VerifiableFunction>,
    error: WasmBridgeError,
) -> WasmConversion {
    let function_name = function.map(|function| function.name.clone());
    let origin = function.and_then(|function| origin_from_span(&function.span));
    let symbolic_formulas = function.map_or_else(Vec::new, collect_symbolic_formulas);
    let provenance_evidence = function.map_or_else(Vec::new, collect_function_provenance_evidence);
    rejected_conversion_parts(
        function_name,
        origin,
        symbolic_formulas,
        provenance_evidence,
        Vec::new(),
        Vec::new(),
        Vec::new(),
        error,
    )
}

#[allow(clippy::too_many_arguments)] // rejected-conversion record captures every evidence slot for the wasm boundary
fn rejected_conversion_parts(
    function_name: Option<String>,
    origin: Option<BinaryOrigin>,
    symbolic_formulas: Vec<WasmSymbolicFormula>,
    provenance_evidence: Vec<WasmProvenanceEvidence>,
    checked_certificate_evidence: Vec<WasmCheckedCertificateEvidence>,
    proof_replay_evidence: Vec<WasmProofReplayEvidence>,
    unsupported_ledger_evidence: Vec<WasmUnsupportedLedgerEvidence>,
    error: WasmBridgeError,
) -> WasmConversion {
    let mut evidence = vec![ReconstructionValidationEvidence::RejectedUnsupported];
    evidence.extend(validation_record_proof_metadata_evidence(
        &checked_certificate_evidence,
        &proof_replay_evidence,
        &unsupported_ledger_evidence,
    ));
    evidence.push(ReconstructionValidationEvidence::NoBinaryProofObligation);
    let record = ReconstructionValidationRecord {
        target: DecompileTarget::Wasm,
        function: function_name.clone(),
        lifted_function: function_name.clone(),
        reconstructed_function: None,
        candidate: ReconstructionCandidateKind::Other(SUBSET.to_string()),
        status: ReconstructionValidationStatus::Failed,
        trust_level: TrustLevel::Rejected,
        forward: Some(validation_direction(
            ReconstructionValidationDirection::LiftedToOutput,
            ReconstructionValidationStatus::Failed,
        )),
        reverse: None,
        evidence,
        diagnostics: vec![
            error.to_string(),
            "Wasm conversion rejected fail-closed".to_string(),
            "no Wasm text emitted; not proof-grade".to_string(),
        ],
    };

    let unsupported = UnsupportedLedger {
        records: vec![UnsupportedRecord {
            stage: STAGE.to_string(),
            architecture: Some("wasm32".to_string()),
            origin,
            opcode: None,
            operand: function_name.clone(),
            feature: error.feature(),
        }],
    };
    let mut validation_blockers = rejected_blockers(
        &error,
        &provenance_evidence,
        &checked_certificate_evidence,
        &proof_replay_evidence,
        &unsupported_ledger_evidence,
    );
    validation_blockers.extend(unsupported_ledger_blockers(&unsupported));

    WasmConversion {
        wat: None,
        lifted_trust_ir_artifact_digest: None,
        bound_lifted_trust_ir_artifact_digest: None,
        validation: ReconstructionValidationStatus::Failed,
        wasm_validation: WasmTargetValidationStatus::Rejected,
        trust_level: TrustLevel::Rejected,
        validation_blockers,
        symbolic_formulas,
        provenance_evidence: provenance_evidence.clone(),
        checked_certificate_evidence: checked_certificate_evidence.clone(),
        proof_replay_evidence: proof_replay_evidence.clone(),
        unsupported_ledger_evidence: unsupported_ledger_evidence.clone(),
        validation_records: vec![record],
        unsupported,
        diagnostics: vec![
            format!("subset={SUBSET}"),
            "Wasm conversion rejected fail-closed".to_string(),
        ]
        .into_iter()
        .chain(provenance_evidence.iter().map(wasm_provenance_evidence_detail))
        .chain(checked_certificate_evidence.iter().map(wasm_checked_certificate_detail))
        .chain(proof_replay_evidence.iter().map(wasm_proof_replay_detail))
        .chain(unsupported_ledger_evidence.iter().map(wasm_unsupported_ledger_detail))
        .collect(),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CanonicalSymbolicFormula {
    function: String,
    block: usize,
    statement_index: usize,
    result_tys: String,
    formula: Option<Formula>,
    schema: Option<String>,
    json: Option<String>,
    smtlib: Option<String>,
    sort: Option<String>,
    inferred_sort: Option<String>,
    bit_width: Option<u32>,
    debug: Option<String>,
    parse_error: Option<String>,
    schema_errors: Vec<String>,
}

fn rejected_symbolic_trust_ir_conversion(
    module: &TrustIrModule,
    symbolic_metadata: Vec<CanonicalSymbolicFormula>,
    provenance_evidence: Vec<WasmProvenanceEvidence>,
    checked_certificate_evidence: Vec<WasmCheckedCertificateEvidence>,
    proof_replay_evidence: Vec<WasmProofReplayEvidence>,
    unsupported_ledger_evidence: Vec<WasmUnsupportedLedgerEvidence>,
) -> WasmConversion {
    let symbolic_formulas = symbolic_metadata
        .iter()
        .filter_map(|entry| {
            entry.formula.clone().map(|formula| WasmSymbolicFormula {
                function: entry.function.clone(),
                block: entry.block,
                statement_index: entry.statement_index,
                operand: "dialect_op".to_string(),
                sort: entry.inferred_sort.clone().unwrap_or_else(|| "unknown".to_string()),
                bit_width: entry.bit_width,
                formula,
            })
        })
        .collect::<Vec<_>>();
    let detail = symbolic_formula_summary(&symbolic_metadata);
    let error = WasmBridgeError::SymbolicFormulaRequiresProof(detail.clone());
    let unsupported = UnsupportedLedger {
        records: symbolic_metadata
            .iter()
            .map(|entry| UnsupportedRecord {
                stage: STAGE.to_string(),
                architecture: Some("wasm32".to_string()),
                origin: None,
                opcode: Some(format!("{}.{}", SYMBOLIC_FORMULA_DIALECT, SYMBOLIC_FORMULA_OP)),
                operand: Some(format!(
                    "{}::bb{}::stmt{}",
                    entry.function, entry.block, entry.statement_index
                )),
                feature: error.feature(),
            })
            .collect(),
    };
    let mut validation_blockers = rejected_blockers(
        &error,
        &provenance_evidence,
        &checked_certificate_evidence,
        &proof_replay_evidence,
        &unsupported_ledger_evidence,
    );
    validation_blockers.splice(0..0, symbolic_formula_blockers(&symbolic_metadata));
    validation_blockers.splice(0..0, symbolic_formula_schema_blockers(&symbolic_metadata));
    validation_blockers.extend(unsupported_ledger_blockers(&unsupported));
    let validation_records = symbolic_trust_ir_validation_records(
        &symbolic_metadata,
        &checked_certificate_evidence,
        &proof_replay_evidence,
        &unsupported_ledger_evidence,
    );
    let mut diagnostics = vec![
        format!("subset={SUBSET}"),
        format!("canonical TrustIr module={}", module.name),
        "Wasm conversion rejected fail-closed".to_string(),
        "symbolic formula dialect metadata preserved; not lowered to Wasm undef".to_string(),
    ];
    diagnostics.extend(symbolic_metadata.iter().map(symbolic_formula_detail));
    diagnostics.extend(provenance_evidence.iter().map(wasm_provenance_evidence_detail));
    diagnostics.extend(checked_certificate_evidence.iter().map(wasm_checked_certificate_detail));
    diagnostics.extend(proof_replay_evidence.iter().map(wasm_proof_replay_detail));
    diagnostics.extend(unsupported_ledger_evidence.iter().map(wasm_unsupported_ledger_detail));

    WasmConversion {
        wat: None,
        lifted_trust_ir_artifact_digest: None,
        bound_lifted_trust_ir_artifact_digest: None,
        validation: ReconstructionValidationStatus::Failed,
        wasm_validation: WasmTargetValidationStatus::Rejected,
        trust_level: TrustLevel::Rejected,
        validation_blockers,
        symbolic_formulas,
        provenance_evidence,
        checked_certificate_evidence,
        proof_replay_evidence,
        unsupported_ledger_evidence,
        validation_records,
        unsupported,
        diagnostics,
    }
}

fn symbolic_trust_ir_validation_records(
    symbolic_metadata: &[CanonicalSymbolicFormula],
    checked_certificate_evidence: &[WasmCheckedCertificateEvidence],
    proof_replay_evidence: &[WasmProofReplayEvidence],
    unsupported_ledger_evidence: &[WasmUnsupportedLedgerEvidence],
) -> Vec<ReconstructionValidationRecord> {
    let mut functions = Vec::<String>::new();
    for entry in symbolic_metadata {
        if !functions.iter().any(|function| function == &entry.function) {
            functions.push(entry.function.clone());
        }
    }

    functions
        .into_iter()
        .map(|function| {
            let function_metadata = symbolic_metadata
                .iter()
                .filter(|entry| entry.function == function)
                .collect::<Vec<_>>();
            let mut evidence = vec![
                ReconstructionValidationEvidence::RejectedUnsupported,
                ReconstructionValidationEvidence::Other(
                    "PreservedCanonicalTrustIrSymbolicFormula".to_string(),
                ),
            ];
            evidence.extend(validation_record_proof_metadata_evidence(
                checked_certificate_evidence,
                proof_replay_evidence,
                unsupported_ledger_evidence,
            ));
            evidence.push(ReconstructionValidationEvidence::NoBinaryProofObligation);
            for entry in &function_metadata {
                if let Some(schema) = &entry.schema {
                    evidence.push(ReconstructionValidationEvidence::Other(format!(
                        "formula.schema={schema}"
                    )));
                }
                if let Some(sort) = &entry.sort {
                    evidence.push(ReconstructionValidationEvidence::Other(format!(
                        "formula.sort={sort}"
                    )));
                }
                if let Some(inferred_sort) = &entry.inferred_sort {
                    evidence.push(ReconstructionValidationEvidence::Other(format!(
                        "formula.inferred_sort={inferred_sort}"
                    )));
                }
                if let Some(bit_width) = entry.bit_width {
                    evidence.push(ReconstructionValidationEvidence::Other(format!(
                        "formula.bit_width={bit_width}"
                    )));
                }
                if let Some(smtlib) = &entry.smtlib {
                    evidence.push(ReconstructionValidationEvidence::Other(format!(
                        "formula.smtlib2={smtlib}"
                    )));
                }
                for error in &entry.schema_errors {
                    evidence.push(ReconstructionValidationEvidence::Other(format!(
                        "formula.schema_error={error}"
                    )));
                }
            }

            ReconstructionValidationRecord {
                target: DecompileTarget::Wasm,
                function: Some(function.clone()),
                lifted_function: Some(function.clone()),
                reconstructed_function: None,
                candidate: ReconstructionCandidateKind::Other("canonical-trust_ir-to-wasm".to_string()),
                status: ReconstructionValidationStatus::Failed,
                trust_level: TrustLevel::Rejected,
                forward: Some(validation_direction(
                    ReconstructionValidationDirection::LiftedToOutput,
                    ReconstructionValidationStatus::Failed,
                )),
                reverse: None,
                evidence,
                diagnostics: function_metadata
                    .into_iter()
                    .map(symbolic_formula_detail)
                    .chain(std::iter::once(
                        "canonical TrustIr symbolic formula preserved as blocker/evidence".to_string(),
                    ))
                    .collect(),
            }
        })
        .collect()
}

fn symbolic_formula_blockers(
    symbolic_metadata: &[CanonicalSymbolicFormula],
) -> Vec<WasmValidationBlocker> {
    vec![validation_blocker(
        "preserved-symbolic-formula",
        &format!(
            "{} symbolic formula(s) preserved in canonical TrustIr metadata; Wasm proof must consume formula JSON/SMT-LIB instead of replacing the value with Undef. {}",
            symbolic_metadata.len(),
            symbolic_formula_summary(symbolic_metadata)
        ),
    )]
}

fn symbolic_formula_schema_blockers(
    symbolic_metadata: &[CanonicalSymbolicFormula],
) -> Vec<WasmValidationBlocker> {
    let errors = symbolic_metadata
        .iter()
        .flat_map(|entry| {
            entry.schema_errors.iter().map(move |error| {
                format!(
                    "{}::bb{}::stmt{}: {error}",
                    entry.function, entry.block, entry.statement_index
                )
            })
        })
        .collect::<Vec<_>>();
    if errors.is_empty() {
        Vec::new()
    } else {
        vec![validation_blocker(
            "invalid-symbolic-formula-schema",
            &format!(
                "canonical TrustIr symbolic formula metadata failed schema validation: {}",
                errors.join("; ")
            ),
        )]
    }
}

fn symbolic_formula_summary(symbolic_metadata: &[CanonicalSymbolicFormula]) -> String {
    symbolic_metadata
        .first()
        .map(symbolic_formula_detail)
        .unwrap_or_else(|| "no symbolic formula metadata".to_string())
}

fn symbolic_formula_detail(entry: &CanonicalSymbolicFormula) -> String {
    let mut parts = vec![
        format!("function={}", entry.function),
        format!("block={}", entry.block),
        format!("statement_index={}", entry.statement_index),
        format!("result_tys={}", entry.result_tys),
    ];
    if let Some(schema) = &entry.schema {
        parts.push(format!("schema={schema}"));
    }
    if let Some(sort) = &entry.sort {
        parts.push(format!("sort={sort}"));
    }
    if let Some(inferred_sort) = &entry.inferred_sort {
        parts.push(format!("inferred_sort={inferred_sort}"));
    }
    if let Some(bit_width) = entry.bit_width {
        parts.push(format!("bit_width={bit_width}"));
    }
    if let Some(smtlib) = &entry.smtlib {
        parts.push(format!("smtlib={smtlib}"));
    }
    if let Some(json) = &entry.json {
        parts.push(format!("formula_json={json}"));
    }
    if let Some(debug) = &entry.debug {
        parts.push(format!("debug={debug}"));
    }
    if let Some(parse_error) = &entry.parse_error {
        parts.push(format!("formula_json_error={parse_error}"));
    }
    for error in &entry.schema_errors {
        parts.push(format!("formula_schema_error={error}"));
    }
    parts.join("; ")
}

fn collect_trust_ir_symbolic_formulas(module: &TrustIrModule) -> Vec<CanonicalSymbolicFormula> {
    let mut formulas = Vec::new();
    for function in &module.functions {
        for block in &function.blocks {
            for (statement_index, node) in block.body.iter().enumerate() {
                let Inst::DialectOp(op) = &node.inst else {
                    continue;
                };
                if op.dialect != SYMBOLIC_FORMULA_DIALECT || op.op != SYMBOLIC_FORMULA_OP {
                    continue;
                }
                formulas.push(canonical_symbolic_formula(
                    &function.name,
                    block.id.as_usize(),
                    statement_index,
                    op,
                ));
            }
        }
    }
    formulas
}

fn collect_trust_ir_provenance_evidence(module: &TrustIrModule) -> Vec<WasmProvenanceEvidence> {
    let mut evidence = Vec::new();
    for function in &module.functions {
        for block in &function.blocks {
            for (statement_index, node) in block.body.iter().enumerate() {
                let Inst::DialectOp(op) = &node.inst else {
                    continue;
                };
                if op.dialect != BINARY_PROVENANCE_DIALECT || op.op != BINARY_PROVENANCE_OP {
                    continue;
                }
                if let Some(entry) = trust_ir_provenance_evidence(
                    &function.name,
                    block.id.as_usize(),
                    statement_index,
                    op,
                ) {
                    evidence.push(entry);
                }
            }
        }
    }
    evidence
}

fn collect_trust_ir_checked_certificate_evidence(
    module: &TrustIrModule,
) -> Vec<WasmCheckedCertificateEvidence> {
    let mut evidence = Vec::new();
    for function in &module.functions {
        for block in &function.blocks {
            for (statement_index, node) in block.body.iter().enumerate() {
                let Inst::DialectOp(op) = &node.inst else {
                    continue;
                };
                if op.dialect != PROOF_METADATA_DIALECT || op.op != CHECKED_CERTIFICATE_OP {
                    continue;
                }
                if let Some(entry) = trust_ir_checked_certificate_evidence(
                    &function.name,
                    block.id.as_usize(),
                    statement_index,
                    op,
                ) {
                    evidence.push(entry);
                }
            }
        }
    }
    evidence
}

fn collect_trust_ir_proof_replay_evidence(module: &TrustIrModule) -> Vec<WasmProofReplayEvidence> {
    let mut evidence = Vec::new();
    for function in &module.functions {
        for block in &function.blocks {
            for (statement_index, node) in block.body.iter().enumerate() {
                let Inst::DialectOp(op) = &node.inst else {
                    continue;
                };
                if op.dialect != PROOF_METADATA_DIALECT || op.op != PROOF_REPLAY_OP {
                    continue;
                }
                if let Some(entry) = trust_ir_proof_replay_evidence(
                    &function.name,
                    block.id.as_usize(),
                    statement_index,
                    op,
                ) {
                    evidence.push(entry);
                }
            }
        }
    }
    evidence
}

fn collect_trust_ir_unsupported_ledger_evidence(
    module: &TrustIrModule,
) -> Vec<WasmUnsupportedLedgerEvidence> {
    let mut evidence = Vec::new();
    for function in &module.functions {
        for block in &function.blocks {
            for (statement_index, node) in block.body.iter().enumerate() {
                let Inst::DialectOp(op) = &node.inst else {
                    continue;
                };
                if op.dialect != PROOF_METADATA_DIALECT || op.op != UNSUPPORTED_LEDGER_OP {
                    continue;
                }
                if let Some(entry) = trust_ir_unsupported_ledger_evidence(
                    &function.name,
                    block.id.as_usize(),
                    statement_index,
                    op,
                ) {
                    evidence.push(entry);
                }
            }
        }
    }
    evidence
}

fn trust_ir_provenance_evidence(
    function: &str,
    block: usize,
    statement_index: usize,
    op: &DialectInst,
) -> Option<WasmProvenanceEvidence> {
    let schema = attr_string(op, BINARY_PROVENANCE_ATTR_SCHEMA)?;
    if schema != BINARY_PROVENANCE_SCHEMA {
        return None;
    }
    let instruction_address = attr_u64(op, BINARY_PROVENANCE_ATTR_INSTRUCTION_ADDRESS)?;
    let instruction_bytes = attr_hex_bytes(op, BINARY_PROVENANCE_ATTR_INSTRUCTION_BYTES)?;
    if instruction_bytes.is_empty() {
        return None;
    }

    let instruction_size = attr_u64(op, BINARY_PROVENANCE_ATTR_INSTRUCTION_SIZE)
        .and_then(|value| u8::try_from(value).ok())
        .or_else(|| u8::try_from(instruction_bytes.len()).ok());
    let source = trust_ir_provenance_source(attr_string(op, BINARY_PROVENANCE_ATTR_SOURCE));
    let target_semantic_consumption = wasm_target_semantic_consumption_evidence(attr_bool(
        op,
        BINARY_PROVENANCE_ATTR_TARGET_SEMANTICS_CONSUMED,
    ));
    let target_semantics_consumed = target_semantic_consumption.target_semantics_consumed;

    Some(WasmProvenanceEvidence {
        function: function.to_string(),
        source,
        block: Some(block),
        statement_index: Some(statement_index),
        origin: BinaryOrigin {
            binary_path: attr_string(op, BINARY_PROVENANCE_ATTR_BINARY_PATH),
            function_entry: attr_u64(op, BINARY_PROVENANCE_ATTR_FUNCTION_ENTRY),
            instruction_address,
            instruction_size,
            encoding: attr_u64(op, BINARY_PROVENANCE_ATTR_ENCODING)
                .and_then(|value| u32::try_from(value).ok()),
            instruction_bytes,
            source: Some(SourceSpan::binary_address(instruction_address)),
        },
        target_semantic_consumption,
        target_semantics_consumed,
    })
}

fn trust_ir_checked_certificate_evidence(
    function: &str,
    block: usize,
    statement_index: usize,
    op: &DialectInst,
) -> Option<WasmCheckedCertificateEvidence> {
    let schema = attr_string(op, PROOF_METADATA_ATTR_SCHEMA)?;
    if schema != CHECKED_CERTIFICATE_SCHEMA {
        return None;
    }
    let certificate = proof_certificate_status_from_attrs(op)?;
    let target_semantic_consumption = wasm_target_semantic_consumption_evidence(attr_bool(
        op,
        PROOF_METADATA_ATTR_TARGET_SEMANTICS_CONSUMED,
    ));
    let target_semantics_consumed = target_semantic_consumption.target_semantics_consumed;

    Some(WasmCheckedCertificateEvidence {
        function: function.to_string(),
        source: proof_metadata_source(
            CHECKED_CERTIFICATE_OP,
            attr_string(op, PROOF_METADATA_ATTR_SOURCE),
        ),
        block: Some(block),
        statement_index: Some(statement_index),
        certificate,
        target_semantic_consumption,
        target_semantics_consumed,
    })
}

fn trust_ir_proof_replay_evidence(
    function: &str,
    block: usize,
    statement_index: usize,
    op: &DialectInst,
) -> Option<WasmProofReplayEvidence> {
    let schema = attr_string(op, PROOF_METADATA_ATTR_SCHEMA)?;
    if schema != PROOF_REPLAY_SCHEMA {
        return None;
    }
    let replay = replay_status_from_attrs(op)?;
    let target_semantic_consumption = wasm_target_semantic_consumption_evidence(attr_bool(
        op,
        PROOF_METADATA_ATTR_TARGET_SEMANTICS_CONSUMED,
    ));
    let target_semantics_consumed = target_semantic_consumption.target_semantics_consumed;

    Some(WasmProofReplayEvidence {
        function: function.to_string(),
        source: proof_metadata_source(PROOF_REPLAY_OP, attr_string(op, PROOF_METADATA_ATTR_SOURCE)),
        block: Some(block),
        statement_index: Some(statement_index),
        replay,
        artifact_sha256: non_empty_attr_string(op, PROOF_METADATA_ATTR_ARTIFACT_SHA256),
        exact_replay_checked: attr_bool(op, PROOF_METADATA_ATTR_EXACT_REPLAY_CHECKED)
            .unwrap_or(false),
        target_semantic_consumption,
        target_semantics_consumed,
    })
}

fn trust_ir_unsupported_ledger_evidence(
    function: &str,
    block: usize,
    statement_index: usize,
    op: &DialectInst,
) -> Option<WasmUnsupportedLedgerEvidence> {
    let schema = attr_string(op, PROOF_METADATA_ATTR_SCHEMA)?;
    if schema != UNSUPPORTED_LEDGER_SCHEMA {
        return None;
    }
    let unsupported_records = attr_u64(op, PROOF_METADATA_ATTR_UNSUPPORTED_RECORDS)
        .and_then(|value| usize::try_from(value).ok())
        .unwrap_or(usize::MAX);
    let verification_unsupported = attr_u64(op, PROOF_METADATA_ATTR_VERIFICATION_UNSUPPORTED)
        .and_then(|value| usize::try_from(value).ok())
        .unwrap_or(0);
    let target_semantic_consumption = wasm_target_semantic_consumption_evidence(attr_bool(
        op,
        PROOF_METADATA_ATTR_TARGET_SEMANTICS_CONSUMED,
    ));
    let target_semantics_consumed = target_semantic_consumption.target_semantics_consumed;

    Some(WasmUnsupportedLedgerEvidence {
        function: function.to_string(),
        source: proof_metadata_source(
            UNSUPPORTED_LEDGER_OP,
            attr_string(op, PROOF_METADATA_ATTR_SOURCE),
        ),
        block: Some(block),
        statement_index: Some(statement_index),
        unsupported_records,
        verification_unsupported,
        unsupported_ledger_eliminated: unsupported_records == 0 && verification_unsupported == 0,
        target_semantic_consumption,
        target_semantics_consumed,
    })
}

fn proof_certificate_status_from_attrs(op: &DialectInst) -> Option<ProofCertificateStatus> {
    if let Some(json) = attr_string(op, PROOF_METADATA_ATTR_STATUS_JSON) {
        return serde_json::from_str::<ProofCertificateStatus>(&json).ok();
    }

    let checked = attr_bool(op, PROOF_METADATA_ATTR_CERTIFICATE_CHECKED).unwrap_or(false);
    let checker = non_empty_attr_string(op, PROOF_METADATA_ATTR_CHECKER);
    let format = non_empty_attr_string(op, PROOF_METADATA_ATTR_FORMAT);
    let sha256 = non_empty_attr_string(op, PROOF_METADATA_ATTR_SHA256);

    if checked {
        Some(ProofCertificateStatus::Checked { checker: checker?, format: format?, sha256 })
    } else if let Some(format) = format {
        Some(ProofCertificateStatus::Present { format, sha256, artifact_path: None })
    } else {
        Some(ProofCertificateStatus::Unavailable {
            reason: Some(
                "canonical checked-certificate metadata was present but incomplete".to_string(),
            ),
        })
    }
}

fn replay_status_from_attrs(op: &DialectInst) -> Option<ReplayStatus> {
    if let Some(json) = attr_string(op, PROOF_METADATA_ATTR_STATUS_JSON) {
        return serde_json::from_str::<ReplayStatus>(&json).ok();
    }
    attr_string(op, PROOF_METADATA_ATTR_REPLAY_STATUS).and_then(|status| match status.as_str() {
        "not_attempted" | "not-attempted" | "NotAttempted" => Some(ReplayStatus::NotAttempted),
        "replayed" | "Replayed" => Some(ReplayStatus::Replayed),
        "spurious" | "Spurious" => Some(ReplayStatus::Spurious),
        "failed" | "Failed" => Some(ReplayStatus::Failed),
        _ => None,
    })
}

fn canonical_symbolic_formula(
    function: &str,
    block: usize,
    statement_index: usize,
    op: &DialectInst,
) -> CanonicalSymbolicFormula {
    let json = attr_string(op, SYMBOLIC_FORMULA_ATTR_JSON);
    let schema = attr_string(op, SYMBOLIC_FORMULA_ATTR_SCHEMA);
    let smtlib = attr_string(op, SYMBOLIC_FORMULA_ATTR_SMTLIB);
    let sort = attr_string(op, SYMBOLIC_FORMULA_ATTR_SORT);
    let (formula, parse_error) = match json.as_deref() {
        Some(json) => match serde_json::from_str::<Formula>(json) {
            Ok(formula) => (Some(formula), None),
            Err(err) => (None, Some(err.to_string())),
        },
        None => (None, Some("missing formula_json attr".to_string())),
    };
    let formula_schema = formula.as_ref().map(symbolic_formula_schema);
    let inferred_sort = formula_schema.as_ref().map(|schema| schema.sort.clone());
    let bit_width = formula_schema.as_ref().and_then(|schema| schema.bit_width);
    let mut schema_errors = symbolic_formula_schema_errors(
        schema.as_deref(),
        sort.as_deref(),
        smtlib.as_deref(),
        formula_schema.as_ref(),
    );
    if let Some(parse_error) = &parse_error {
        schema_errors.push(format!("formula_json parse error: {parse_error}"));
    }

    CanonicalSymbolicFormula {
        function: function.to_string(),
        block,
        statement_index,
        result_tys: result_tys_label(op),
        formula,
        schema,
        json,
        smtlib,
        sort,
        inferred_sort,
        bit_width,
        debug: attr_string(op, SYMBOLIC_FORMULA_ATTR_DEBUG),
        parse_error,
        schema_errors,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SymbolicFormulaSchema {
    sort: String,
    bit_width: Option<u32>,
    smtlib: String,
}

fn symbolic_formula_schema(formula: &Formula) -> SymbolicFormulaSchema {
    let sort = infer_sort(formula);
    SymbolicFormulaSchema {
        sort: sort.to_smtlib(),
        bit_width: sort_bit_width(&sort),
        smtlib: formula.to_smtlib(),
    }
}

fn sort_bit_width(sort: &Sort) -> Option<u32> {
    match sort {
        Sort::BitVec(width) => Some(*width),
        Sort::Bool | Sort::Int | Sort::Array(_, _) => None,
        #[allow(unreachable_patterns)]
        _ => None,
    }
}

fn symbolic_formula_schema_errors(
    schema: Option<&str>,
    sort: Option<&str>,
    smtlib: Option<&str>,
    formula_schema: Option<&SymbolicFormulaSchema>,
) -> Vec<String> {
    let mut errors = Vec::new();
    match schema {
        Some(SYMBOLIC_FORMULA_SCHEMA) => {}
        Some(other) => errors
            .push(format!("unsupported schema `{other}`; expected `{SYMBOLIC_FORMULA_SCHEMA}`")),
        None => errors.push(format!("missing schema attr `{SYMBOLIC_FORMULA_SCHEMA}`")),
    }

    if let Some(formula_schema) = formula_schema {
        match sort {
            Some(sort) if sort == formula_schema.sort => {}
            Some(sort) => errors.push(format!(
                "formula.sort `{sort}` does not match inferred sort `{}`",
                formula_schema.sort
            )),
            None => errors.push(format!("missing `{SYMBOLIC_FORMULA_ATTR_SORT}` attr")),
        }

        match smtlib {
            Some(smtlib) if smtlib == formula_schema.smtlib => {}
            Some(smtlib) => errors.push(format!(
                "formula.smtlib2 `{smtlib}` does not match parsed formula `{}`",
                formula_schema.smtlib
            )),
            None => errors.push(format!("missing `{SYMBOLIC_FORMULA_ATTR_SMTLIB}` attr")),
        }
    }

    errors
}

fn attr_string(op: &DialectInst, name: &str) -> Option<String> {
    op.attr(name).and_then(AttrValue::as_str).map(str::to_string)
}

fn non_empty_attr_string(op: &DialectInst, name: &str) -> Option<String> {
    attr_string(op, name).and_then(|value| {
        let trimmed = value.trim();
        if trimmed.is_empty() { None } else { Some(trimmed.to_string()) }
    })
}

fn attr_u64(op: &DialectInst, name: &str) -> Option<u64> {
    attr_string(op, name).and_then(|value| parse_canonical_u64(&value))
}

fn attr_bool(op: &DialectInst, name: &str) -> Option<bool> {
    attr_string(op, name).and_then(|value| match value.trim() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    })
}

fn attr_hex_bytes(op: &DialectInst, name: &str) -> Option<Vec<u8>> {
    attr_string(op, name).and_then(|value| parse_canonical_hex_bytes(&value))
}

fn result_tys_label(op: &DialectInst) -> String {
    if op.result_tys.is_empty() {
        "()".to_string()
    } else {
        op.result_tys.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ")
    }
}

fn parse_canonical_u64(value: &str) -> Option<u64> {
    let trimmed = value.trim();
    trimmed
        .strip_prefix("0x")
        .or_else(|| trimmed.strip_prefix("0X"))
        .map_or_else(|| trimmed.parse().ok(), |hex| u64::from_str_radix(hex, 16).ok())
}

fn parse_canonical_hex_bytes(value: &str) -> Option<Vec<u8>> {
    let normalized = value
        .trim()
        .strip_prefix("0x")
        .or_else(|| value.trim().strip_prefix("0X"))
        .unwrap_or_else(|| value.trim())
        .chars()
        .filter(|ch| !ch.is_ascii_whitespace() && *ch != '_' && *ch != ':')
        .collect::<String>();
    if normalized.is_empty() || normalized.len() % 2 != 0 {
        return None;
    }
    (0..normalized.len())
        .step_by(2)
        .map(|idx| u8::from_str_radix(&normalized[idx..idx + 2], 16).ok())
        .collect()
}

fn trust_ir_provenance_source(source: Option<String>) -> String {
    let base = format!("{BINARY_PROVENANCE_DIALECT}.{BINARY_PROVENANCE_OP}");
    match source {
        Some(source) if !source.is_empty() => format!("canonical-trust_ir.{base}:{source}"),
        _ => format!("canonical-trust_ir.{base}"),
    }
}

fn proof_metadata_source(op: &str, source: Option<String>) -> String {
    let base = format!("{PROOF_METADATA_DIALECT}.{op}");
    match source {
        Some(source) if !source.is_empty() => format!("canonical-trust_ir.{base}:{source}"),
        _ => format!("canonical-trust_ir.{base}"),
    }
}

fn proof_metadata_blockers(
    checked_certificate_evidence: &[WasmCheckedCertificateEvidence],
    proof_replay_evidence: &[WasmProofReplayEvidence],
    unsupported_ledger_evidence: &[WasmUnsupportedLedgerEvidence],
) -> Vec<WasmValidationBlocker> {
    let mut blockers = vec![
        validation_blocker(
            "missing-target-semantic-validation",
            "Wasm text has not been validated against executable Wasm target semantics",
        ),
        validation_blocker(
            "missing-refinement-metadata",
            "Wasm text has no bidirectional refinement metadata tying it to lifted TrustIr",
        ),
        validation_blocker(
            "missing-binary-proof-obligation",
            "Wasm conversion has not discharged machine-code proof obligations",
        ),
    ];
    blockers.extend(wasm_checked_certificate_blockers(checked_certificate_evidence));
    blockers.extend(wasm_proof_replay_blockers(proof_replay_evidence));
    blockers.extend(wasm_unsupported_ledger_blockers(unsupported_ledger_evidence));
    blockers
}

fn inspectable_validation_blockers(
    provenance_evidence: &[WasmProvenanceEvidence],
    checked_certificate_evidence: &[WasmCheckedCertificateEvidence],
    proof_replay_evidence: &[WasmProofReplayEvidence],
    unsupported_ledger_evidence: &[WasmUnsupportedLedgerEvidence],
) -> Vec<WasmValidationBlocker> {
    let mut blockers = proof_metadata_blockers(
        checked_certificate_evidence,
        proof_replay_evidence,
        unsupported_ledger_evidence,
    );
    blockers.extend(wasm_provenance_target_blockers(provenance_evidence));
    blockers
}

fn rejected_blockers(
    error: &WasmBridgeError,
    provenance_evidence: &[WasmProvenanceEvidence],
    checked_certificate_evidence: &[WasmCheckedCertificateEvidence],
    proof_replay_evidence: &[WasmProofReplayEvidence],
    unsupported_ledger_evidence: &[WasmUnsupportedLedgerEvidence],
) -> Vec<WasmValidationBlocker> {
    let mut blockers = vec![validation_blocker("unsupported-wasm-subset", &error.to_string())];
    blockers.extend(proof_metadata_blockers(
        checked_certificate_evidence,
        proof_replay_evidence,
        unsupported_ledger_evidence,
    ));
    blockers.extend(wasm_provenance_target_blockers(provenance_evidence));
    blockers
}

fn wasm_provenance_target_blockers(
    provenance_evidence: &[WasmProvenanceEvidence],
) -> Vec<WasmValidationBlocker> {
    if provenance_evidence.is_empty() {
        vec![validation_blocker(
            "missing-binary-provenance",
            "Wasm target proof consumer has no binary provenance metadata tying output back to machine instructions",
        )]
    } else if provenance_evidence.iter().all(|entry| {
        wasm_target_semantic_consumption_is_bridge_owned(&entry.target_semantic_consumption)
    }) {
        Vec::new()
    } else {
        vec![validation_blocker(
            "binary-provenance-not-consumed-by-target-semantics",
            &format!(
                "{} binary provenance record(s) are preserved but not consumed by Wasm target semantics; authoritative consumed state is bridge-owned by {WASM_TARGET_SEMANTIC_CONSUMER}, and any canonical target_semantics_consumed attr is treated as an untrusted input claim",
                provenance_evidence.len()
            ),
        )]
    }
}

fn wasm_checked_certificate_blockers(
    checked_certificate_evidence: &[WasmCheckedCertificateEvidence],
) -> Vec<WasmValidationBlocker> {
    if checked_certificate_evidence.is_empty() {
        return vec![validation_blocker(
            "missing-checked-proof-certificate",
            "Wasm conversion has no checked proof certificate for the emitted text",
        )];
    }

    let mut blockers = Vec::new();
    if !checked_certificate_evidence.iter().all(|entry| {
        wasm_target_semantic_consumption_is_bridge_owned(&entry.target_semantic_consumption)
    }) {
        blockers.push(validation_blocker(
            "checked-certificate-not-consumed-by-target-semantics",
            &format!(
                "{} checked certificate metadata record(s) are preserved but not consumed by Wasm target semantics; authoritative consumed state is bridge-owned by {WASM_TARGET_SEMANTIC_CONSUMER}",
                checked_certificate_evidence.len()
            ),
        ));
    }
    if !checked_certificate_evidence
        .iter()
        .any(|entry| checked_certificate_has_canonical_identity(&entry.certificate))
    {
        blockers.push(validation_blocker(
            "checked-proof-certificate-incomplete",
            "checked certificate metadata is present, but no checked certificate record carries checker, format, and sha256 identity",
        ));
    }
    blockers
}

fn wasm_proof_replay_blockers(
    proof_replay_evidence: &[WasmProofReplayEvidence],
) -> Vec<WasmValidationBlocker> {
    if proof_replay_evidence.is_empty() {
        return vec![validation_blocker(
            "missing-proof-replay-metadata",
            "Wasm conversion has no replay metadata tying proof results to the emitted text",
        )];
    }

    let mut blockers = Vec::new();
    if !proof_replay_evidence.iter().all(|entry| {
        wasm_target_semantic_consumption_is_bridge_owned(&entry.target_semantic_consumption)
    }) {
        blockers.push(validation_blocker(
            "proof-replay-not-consumed-by-target-semantics",
            &format!(
                "{} proof replay metadata record(s) are preserved but not consumed by Wasm target semantics; authoritative consumed state is bridge-owned by {WASM_TARGET_SEMANTIC_CONSUMER}",
                proof_replay_evidence.len()
            ),
        ));
    }
    if !proof_replay_evidence
        .iter()
        .any(|entry| entry.replay == ReplayStatus::Replayed && entry.exact_replay_checked)
    {
        blockers.push(validation_blocker(
            "proof-replay-incomplete",
            "proof replay metadata is present, but no record carries ReplayStatus::Replayed with exact replay checked",
        ));
    }
    blockers
}

fn wasm_unsupported_ledger_blockers(
    unsupported_ledger_evidence: &[WasmUnsupportedLedgerEvidence],
) -> Vec<WasmValidationBlocker> {
    if unsupported_ledger_evidence.is_empty() {
        return vec![validation_blocker(
            "missing-unsupported-ledger-evidence",
            "Wasm target proof consumer has no unsupported-ledger elimination evidence",
        )];
    }

    let mut blockers = Vec::new();
    if !unsupported_ledger_evidence.iter().all(|entry| {
        wasm_target_semantic_consumption_is_bridge_owned(&entry.target_semantic_consumption)
    }) {
        blockers.push(validation_blocker(
            "unsupported-ledger-not-consumed-by-target-semantics",
            &format!(
                "{} unsupported-ledger evidence record(s) are preserved but not consumed by Wasm target semantics; authoritative consumed state is bridge-owned by {WASM_TARGET_SEMANTIC_CONSUMER}",
                unsupported_ledger_evidence.len()
            ),
        ));
    }
    if !unsupported_ledger_evidence.iter().all(is_unsupported_ledger_eliminated_evidence) {
        blockers.push(validation_blocker(
            "unsupported-ledger-not-eliminated",
            "unsupported-ledger evidence is present, but at least one record has non-empty unsupported records or unsupported verification counters",
        ));
    }
    blockers
}

fn checked_certificate_has_canonical_identity(status: &ProofCertificateStatus) -> bool {
    matches!(
        status,
        ProofCertificateStatus::Checked { checker, format, sha256: Some(sha256) }
            if !checker.trim().is_empty()
                && !format.trim().is_empty()
                && !sha256.trim().is_empty()
    )
}

fn validation_blocker(code: &str, detail: &str) -> WasmValidationBlocker {
    WasmValidationBlocker { code: code.to_string(), detail: detail.to_string() }
}

fn unsupported_ledger_blockers(unsupported: &UnsupportedLedger) -> Vec<WasmValidationBlocker> {
    if unsupported.records.is_empty() {
        return Vec::new();
    }

    let features = unsupported
        .records
        .iter()
        .take(3)
        .map(|record| record.feature.as_str())
        .collect::<Vec<_>>()
        .join("; ");
    let remaining = unsupported.records.len().saturating_sub(3);
    let summary = if remaining == 0 { features } else { format!("{features}; {remaining} more") };

    vec![validation_blocker(
        "unsupported-ledger-not-empty",
        &format!(
            "{} unsupported ledger record(s) remain in the Wasm conversion; proof-grade acceptance requires unsupported-ledger elimination before target evidence can be accepted: {summary}",
            unsupported.records.len()
        ),
    )]
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BoundedWasmTargetConsumption {
    accepted: bool,
    detail: String,
    blockers: Vec<WasmValidationBlocker>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NonEmptyScalarTargetBinding {
    function: String,
    formula_value: bool,
    target_operation: &'static str,
    formula_identifier: String,
    provenance_identifier: String,
    checked_certificate_identifier: String,
    proof_replay_identifier: String,
    unsupported_ledger_identifier: String,
    proof_identity: String,
}

fn wasm_target_consumption(conversion: &WasmConversion) -> BoundedWasmTargetConsumption {
    let bounded_consumption = wasm_bounded_empty_target_consumption(conversion);
    if bounded_consumption.accepted {
        return bounded_consumption;
    }

    let scalar_consumption = wasm_non_empty_scalar_target_consumption(conversion);
    if scalar_consumption.accepted {
        return scalar_consumption;
    }

    let mut blockers = bounded_consumption.blockers;
    blockers.extend(scalar_consumption.blockers);
    BoundedWasmTargetConsumption {
        accepted: false,
        detail:
            "no bridge-owned Wasm target proof-consumer slice accepted the conversion proof inputs"
                .to_string(),
        blockers,
    }
}

fn apply_bounded_empty_target_consumption_to_canonical_evidence(
    module: &TrustIrModule,
    symbolic_metadata: &[CanonicalSymbolicFormula],
    checked_certificate_evidence: &mut [WasmCheckedCertificateEvidence],
    proof_replay_evidence: &mut [WasmProofReplayEvidence],
    provenance_evidence: &mut [WasmProvenanceEvidence],
    unsupported_ledger_evidence: &mut [WasmUnsupportedLedgerEvidence],
) {
    if !trust_ir_module_is_bounded_empty_metadata_slice(module) {
        return;
    }

    let consumption = wasm_bounded_empty_target_consumption_candidate(
        "wat:blocked:no-emitted-module",
        symbolic_metadata,
        checked_certificate_evidence,
        proof_replay_evidence,
        provenance_evidence,
        unsupported_ledger_evidence,
    );
    if !consumption.accepted {
        return;
    }

    for entry in provenance_evidence {
        entry.target_semantic_consumption =
            wasm_bounded_empty_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
    for entry in checked_certificate_evidence {
        entry.target_semantic_consumption =
            wasm_bounded_empty_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
    for entry in proof_replay_evidence {
        entry.target_semantic_consumption =
            wasm_bounded_empty_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
    for entry in unsupported_ledger_evidence {
        entry.target_semantic_consumption =
            wasm_bounded_empty_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
}

fn wasm_bounded_empty_target_consumption(
    conversion: &WasmConversion,
) -> BoundedWasmTargetConsumption {
    let target_output = wasm_target_output_identifier(conversion);
    let symbolic_metadata = symbolic_formulas_to_bounded_metadata(&conversion.symbolic_formulas);
    wasm_bounded_empty_target_consumption_impl(
        &target_output,
        &symbolic_metadata,
        &conversion.checked_certificate_evidence,
        &conversion.proof_replay_evidence,
        &conversion.provenance_evidence,
        &conversion.unsupported_ledger_evidence,
        true,
    )
}

fn wasm_bounded_empty_target_consumption_candidate(
    target_output: &str,
    symbolic_metadata: &[CanonicalSymbolicFormula],
    checked_certificate_evidence: &[WasmCheckedCertificateEvidence],
    proof_replay_evidence: &[WasmProofReplayEvidence],
    provenance_evidence: &[WasmProvenanceEvidence],
    unsupported_ledger_evidence: &[WasmUnsupportedLedgerEvidence],
) -> BoundedWasmTargetConsumption {
    wasm_bounded_empty_target_consumption_impl(
        target_output,
        symbolic_metadata,
        checked_certificate_evidence,
        proof_replay_evidence,
        provenance_evidence,
        unsupported_ledger_evidence,
        false,
    )
}

fn wasm_bounded_empty_target_consumption_impl(
    target_output: &str,
    symbolic_metadata: &[CanonicalSymbolicFormula],
    checked_certificate_evidence: &[WasmCheckedCertificateEvidence],
    proof_replay_evidence: &[WasmProofReplayEvidence],
    provenance_evidence: &[WasmProvenanceEvidence],
    unsupported_ledger_evidence: &[WasmUnsupportedLedgerEvidence],
    require_bridge_consumed_marker: bool,
) -> BoundedWasmTargetConsumption {
    let mut blockers = Vec::new();

    if target_output != "wat:blocked:no-emitted-module" {
        blockers.push(validation_blocker(
            "bounded-empty-slice-target-not-empty",
            "bounded Wasm target proof-consumer slice only applies when no WAT module was emitted",
        ));
    }

    if symbolic_metadata.is_empty() {
        blockers.push(validation_blocker(
            "bounded-empty-slice-missing-trivial-formula",
            "bounded Wasm target proof-consumer slice requires canonical trust_symbolic.formula metadata for the trivial Bool(true) obligation",
        ));
    } else if !symbolic_metadata.iter().all(is_bounded_empty_trivial_formula_metadata) {
        blockers.push(validation_blocker(
            "bounded-empty-slice-nontrivial-formula",
            "bounded Wasm target proof-consumer slice rejects nontrivial, malformed, or non-canonical formula metadata",
        ));
    }

    if provenance_evidence.is_empty() {
        blockers.push(validation_blocker(
            "bounded-empty-slice-missing-noop-provenance",
            "bounded Wasm target proof-consumer slice requires canonical binary provenance for a recognized no-op instruction",
        ));
    } else if !provenance_evidence.iter().all(is_bounded_empty_noop_provenance) {
        blockers.push(validation_blocker(
            "bounded-empty-slice-non-noop-provenance",
            "bounded Wasm target proof-consumer slice rejects provenance that is non-canonical, lacks exact bytes, or does not identify a recognized no-op instruction",
        ));
    }

    if checked_certificate_evidence.is_empty() {
        blockers.push(validation_blocker(
            "bounded-empty-slice-missing-checked-certificate",
            "bounded Wasm target proof-consumer slice requires canonical checked-certificate metadata with checker, format, and sha256 identity",
        ));
    } else if !checked_certificate_evidence.iter().all(is_bounded_empty_checked_certificate) {
        blockers.push(validation_blocker(
            "bounded-empty-slice-incomplete-checked-certificate",
            "bounded Wasm target proof-consumer slice rejects checked-certificate metadata that is non-canonical or lacks checked identity",
        ));
    }

    if proof_replay_evidence.is_empty() {
        blockers.push(validation_blocker(
            "bounded-empty-slice-missing-exact-replay",
            "bounded Wasm target proof-consumer slice requires canonical proof replay metadata with ReplayStatus::Replayed and exact replay checked",
        ));
    } else if !proof_replay_evidence.iter().all(is_bounded_empty_exact_replay) {
        blockers.push(validation_blocker(
            "bounded-empty-slice-incomplete-exact-replay",
            "bounded Wasm target proof-consumer slice rejects replay metadata that is non-canonical, not replayed, missing an artifact digest, or not exact",
        ));
    }

    if unsupported_ledger_evidence.is_empty() {
        blockers.push(validation_blocker(
            "bounded-empty-slice-missing-unsupported-ledger",
            "bounded Wasm target proof-consumer slice requires canonical unsupported-ledger elimination evidence",
        ));
    } else if !unsupported_ledger_evidence.iter().all(is_unsupported_ledger_eliminated_evidence) {
        blockers.push(validation_blocker(
            "bounded-empty-slice-unsupported-ledger-not-eliminated",
            "bounded Wasm target proof-consumer slice rejects non-empty unsupported ledgers or unsupported verification counters",
        ));
    }

    if require_bridge_consumed_marker
        && blockers.is_empty()
        && !bounded_empty_evidence_is_bridge_consumed(
            checked_certificate_evidence,
            proof_replay_evidence,
            provenance_evidence,
            unsupported_ledger_evidence,
        )
    {
        blockers.push(validation_blocker(
            "bounded-empty-slice-not-bridge-consumed",
            "bounded Wasm target proof-consumer slice requires target-specific bridge-owned Wasm consumption stamped after canonical empty/no-op source-shape validation",
        ));
    }

    let accepted = blockers.is_empty();
    BoundedWasmTargetConsumption {
        accepted,
        detail: if accepted {
            "Wasm target proof consumer accepted the bounded empty/no-op slice: no WAT module emitted, every formula is Bool(true), binary provenance identifies only recognized no-op bytes, checked certificate plus exact replay metadata are canonical, and unsupported-ledger evidence is eliminated"
                .to_string()
        } else {
            "bounded empty/no-op Wasm target proof-consumer slice did not apply".to_string()
        },
        blockers,
    }
}

fn trust_ir_module_is_bounded_empty_metadata_slice(module: &TrustIrModule) -> bool {
    let [function] = module.functions.as_slice() else {
        return false;
    };
    let [block] = function.blocks.as_slice() else {
        return false;
    };
    if block.body.is_empty()
        || !matches!(block.body.last().map(|node| &node.inst), Some(Inst::Return { .. }))
    {
        return false;
    }

    block.body[..block.body.len() - 1]
        .iter()
        .all(|node| matches!(&node.inst, Inst::DialectOp(op) if is_bounded_empty_metadata_op(op)))
}

fn is_bounded_empty_metadata_op(op: &DialectInst) -> bool {
    matches!(
        (op.dialect.as_str(), op.op.as_str()),
        (SYMBOLIC_FORMULA_DIALECT, SYMBOLIC_FORMULA_OP)
            | (BINARY_PROVENANCE_DIALECT, BINARY_PROVENANCE_OP)
            | (PROOF_METADATA_DIALECT, CHECKED_CERTIFICATE_OP)
            | (PROOF_METADATA_DIALECT, PROOF_REPLAY_OP)
            | (PROOF_METADATA_DIALECT, UNSUPPORTED_LEDGER_OP)
    )
}

fn symbolic_formulas_to_bounded_metadata(
    formulas: &[WasmSymbolicFormula],
) -> Vec<CanonicalSymbolicFormula> {
    formulas
        .iter()
        .map(|formula| {
            let json = serde_json::to_string(&formula.formula).ok();
            CanonicalSymbolicFormula {
                function: formula.function.clone(),
                block: formula.block,
                statement_index: formula.statement_index,
                result_tys: formula.sort.clone(),
                formula: Some(formula.formula.clone()),
                schema: Some(SYMBOLIC_FORMULA_SCHEMA.to_string()),
                json,
                smtlib: Some(formula.formula.to_smtlib()),
                sort: Some(formula.sort.clone()),
                inferred_sort: Some(formula.sort.clone()),
                bit_width: formula.bit_width,
                debug: None,
                parse_error: None,
                schema_errors: Vec::new(),
            }
        })
        .collect()
}

fn bounded_empty_evidence_is_bridge_consumed(
    checked_certificate_evidence: &[WasmCheckedCertificateEvidence],
    proof_replay_evidence: &[WasmProofReplayEvidence],
    provenance_evidence: &[WasmProvenanceEvidence],
    unsupported_ledger_evidence: &[WasmUnsupportedLedgerEvidence],
) -> bool {
    checked_certificate_evidence.iter().all(|entry| {
        wasm_bounded_empty_target_semantic_consumption_is_bridge_owned(
            &entry.target_semantic_consumption,
        )
    }) && proof_replay_evidence.iter().all(|entry| {
        wasm_bounded_empty_target_semantic_consumption_is_bridge_owned(
            &entry.target_semantic_consumption,
        )
    }) && provenance_evidence.iter().all(|entry| {
        wasm_bounded_empty_target_semantic_consumption_is_bridge_owned(
            &entry.target_semantic_consumption,
        )
    }) && unsupported_ledger_evidence.iter().all(|entry| {
        wasm_bounded_empty_target_semantic_consumption_is_bridge_owned(
            &entry.target_semantic_consumption,
        )
    })
}

fn wasm_target_semantic_consumption_is_bridge_owned(
    evidence: &WasmTargetSemanticConsumptionEvidence,
) -> bool {
    evidence.target_semantics_consumed
        && evidence.consumer == WASM_TARGET_SEMANTIC_CONSUMER
        && evidence.code == WASM_BOUNDED_EMPTY_TARGET_CONSUMED_CODE
}

fn wasm_bounded_empty_target_semantic_consumption_is_bridge_owned(
    evidence: &WasmTargetSemanticConsumptionEvidence,
) -> bool {
    evidence.target_semantics_consumed
        && evidence.consumer == WASM_TARGET_SEMANTIC_CONSUMER
        && evidence.code == WASM_BOUNDED_EMPTY_TARGET_CONSUMED_CODE
}

fn is_bounded_empty_trivial_formula_metadata(entry: &CanonicalSymbolicFormula) -> bool {
    matches!(entry.formula, Some(Formula::Bool(true)))
        && matches!(entry.result_tys.as_str(), "bool" | "Bool")
        && entry.schema.as_deref() == Some(SYMBOLIC_FORMULA_SCHEMA)
        && entry.sort.as_deref() == Some("Bool")
        && entry.inferred_sort.as_deref() == Some("Bool")
        && entry.smtlib.as_deref() == Some("true")
        && entry.parse_error.is_none()
        && entry.schema_errors.is_empty()
}

fn is_bounded_empty_noop_provenance(entry: &WasmProvenanceEvidence) -> bool {
    entry.source.starts_with("canonical-trust_ir.trust_binary.provenance")
        && !entry.origin.instruction_bytes.is_empty()
        && entry
            .origin
            .instruction_size
            .is_none_or(|size| usize::from(size) == entry.origin.instruction_bytes.len())
        && is_recognized_noop_instruction_bytes(&entry.origin.instruction_bytes)
}

fn is_recognized_noop_instruction_bytes(bytes: &[u8]) -> bool {
    matches!(bytes, [0x90] | [0x66, 0x90] | [0x0f, 0x1f, 0x00] | [0x1f, 0x20, 0x03, 0xd5])
}

fn is_bounded_empty_checked_certificate(entry: &WasmCheckedCertificateEvidence) -> bool {
    entry.source.starts_with("canonical-trust_ir.trust_proof.checked_certificate")
        && checked_certificate_has_canonical_identity(&entry.certificate)
}

fn is_bounded_empty_exact_replay(entry: &WasmProofReplayEvidence) -> bool {
    entry.source.starts_with("canonical-trust_ir.trust_proof.proof_replay")
        && entry.replay == ReplayStatus::Replayed
        && entry.exact_replay_checked
        && entry.artifact_sha256.as_deref().is_some_and(|sha256| !sha256.trim().is_empty())
}

fn is_unsupported_ledger_eliminated_evidence(entry: &WasmUnsupportedLedgerEvidence) -> bool {
    entry.unsupported_ledger_eliminated
        && entry.unsupported_records == 0
        && entry.verification_unsupported == 0
}

fn wasm_refinement_metadata_evidence(
    conversion: &WasmConversion,
    target_consumption: &BoundedWasmTargetConsumption,
    target_output: &str,
) -> Vec<WasmRefinementMetadataEvidence> {
    if !target_consumption.accepted {
        return Vec::new();
    }

    if target_output == "wat:blocked:no-emitted-module" {
        return wasm_bounded_empty_refinement_metadata(conversion, target_output);
    }

    let Some(wat) = conversion.wat.as_deref() else {
        return Vec::new();
    };
    wasm_non_empty_scalar_refinement_metadata(conversion, wat, target_output)
}

fn wasm_bounded_empty_refinement_metadata(
    conversion: &WasmConversion,
    target_output: &str,
) -> Vec<WasmRefinementMetadataEvidence> {
    let [formula] = conversion.symbolic_formulas.as_slice() else {
        return Vec::new();
    };
    if formula.formula != Formula::Bool(true)
        || formula.sort != "Bool"
        || formula.bit_width.is_some()
    {
        return Vec::new();
    }

    vec![WasmRefinementMetadataEvidence {
        slice: "bounded-empty-noop".to_string(),
        source: "canonical-trust_ir".to_string(),
        source_function: formula.function.clone(),
        source_block: Some(formula.block),
        source_statement_index: Some(formula.statement_index),
        source_formula: Some(formula.formula.to_smtlib()),
        target: "wasm".to_string(),
        target_output: target_output.to_string(),
        target_operation: "no-emitted-wat".to_string(),
        forward_relation:
            "canonical Bool(true) plus no-op provenance refines the empty Wasm output slice"
                .to_string(),
        reverse_relation:
            "empty Wasm output slice preserves only the canonical Bool(true) no-op obligation"
                .to_string(),
        bidirectional_refinement_consumed: true,
        code: "bounded-empty-noop-wasm-refinement-consumed".to_string(),
        detail: format!(
            "Wasm target proof consumer accepted bounded empty/no-op refinement for {}::bb{}::stmt{} and empty WAT output",
            formula.function, formula.block, formula.statement_index
        ),
    }]
}

fn wasm_non_empty_scalar_refinement_metadata(
    conversion: &WasmConversion,
    wat: &str,
    target_output: &str,
) -> Vec<WasmRefinementMetadataEvidence> {
    let Ok(binding) = exact_non_empty_scalar_target_binding(conversion, wat) else {
        return Vec::new();
    };
    let Some(target_bool) = wat_single_i32_const_bool_result(wat) else {
        return Vec::new();
    };
    let Some(formula) = exact_bool_formula(&conversion.symbolic_formulas, target_bool) else {
        return Vec::new();
    };

    vec![WasmRefinementMetadataEvidence {
        slice: "non-empty-scalar-bool".to_string(),
        source: "lifted-trust_ir".to_string(),
        source_function: formula.function.clone(),
        source_block: Some(formula.block),
        source_statement_index: Some(formula.statement_index),
        source_formula: Some(formula.formula.to_smtlib()),
        target: "wasm".to_string(),
        target_output: target_output.to_string(),
        target_operation: binding.target_operation.to_string(),
        forward_relation: format!(
            "lifted TrustIr {} refines emitted Wasm {}",
            formula.formula.to_smtlib(),
            binding.target_operation
        ),
        reverse_relation: format!(
            "emitted Wasm {} preserves only lifted TrustIr {}",
            binding.target_operation,
            formula.formula.to_smtlib()
        ),
        bidirectional_refinement_consumed: true,
        code: "non-empty-scalar-wasm-refinement-consumed".to_string(),
        detail: format!(
            "Wasm target proof consumer accepted non-empty scalar refinement for {} using {} and proof identity {}",
            binding.formula_identifier, binding.target_operation, binding.proof_identity
        ),
    }]
}

fn wasm_refinement_proof_grade_blockers(
    target_semantics_consumed: bool,
    refinement_metadata_evidence: &[WasmRefinementMetadataEvidence],
) -> Vec<WasmValidationBlocker> {
    if refinement_metadata_evidence.is_empty() {
        let mut blockers = vec![validation_blocker(
            "missing-refinement-metadata",
            "Wasm target proof consumer has no bidirectional refinement metadata tying emitted target semantics to lifted TrustIr",
        )];
        blockers.push(if target_semantics_consumed {
            validation_blocker(
                "binary-proof-obligation-pending-refinement-metadata",
                "Wasm target proof consumer consumed carried proof inputs, but proof-grade remains closed until bidirectional refinement metadata binds that consumed obligation to lifted TrustIr",
            )
        } else {
            validation_blocker(
                "missing-binary-proof-obligation",
                "Wasm conversion has no bridge-consumed metadata for machine-code proof obligations",
            )
        });
        return blockers;
    }

    if refinement_metadata_evidence.iter().all(|entry| entry.bidirectional_refinement_consumed) {
        Vec::new()
    } else {
        vec![
            validation_blocker(
                "refinement-metadata-not-consumed",
                "Wasm target proof consumer has structured refinement metadata, but no bridge-owned bidirectional refinement consumer has consumed the forward and reverse relation",
            ),
            validation_blocker(
                "binary-proof-obligation-pending-refinement-consumption",
                "Wasm target proof consumer consumed carried proof inputs, and structured refinement metadata is present, but proof-grade remains closed until that metadata is consumed",
            ),
        ]
    }
}

fn append_unique_wasm_blockers(
    target: &mut Vec<WasmValidationBlocker>,
    source: &[WasmValidationBlocker],
) {
    for blocker in source {
        if !target.iter().any(|existing| existing.code == blocker.code) {
            target.push(blocker.clone());
        }
    }
}

fn build_wasm_proof_consumer_evidence(conversion: &WasmConversion) -> WasmProofConsumerEvidence {
    let target_consumption = wasm_target_consumption(conversion);
    let target_semantics_consumed = target_consumption.accepted;
    let target_output = wasm_target_output_identifier(conversion);
    let refinement_metadata_evidence =
        wasm_refinement_metadata_evidence(conversion, &target_consumption, &target_output);
    let mut records = vec![WasmProofConsumerRecord {
        kind: "target_semantics".to_string(),
        identifier: "wasm32".to_string(),
        accepted: target_semantics_consumed,
        detail: if target_semantics_consumed {
            target_consumption.detail.clone()
        } else {
            "executable Wasm target semantics have not consumed conversion proof inputs".to_string()
        },
    }];

    records.extend(conversion.symbolic_formulas.iter().map(|formula| WasmProofConsumerRecord {
        kind: "symbolic_formula".to_string(),
        identifier: format!(
            "{}::bb{}::stmt{}::{}",
            formula.function, formula.block, formula.statement_index, formula.operand
        ),
        accepted: target_semantics_consumed,
        detail: if target_semantics_consumed {
            format!(
                "formula sort={} bit_width={} was consumed by bridge-owned Wasm target proof-consumer evidence: {}",
                formula.sort,
                formula
                    .bit_width
                    .map(|width| width.to_string())
                    .unwrap_or_else(|| "none".to_string()),
                target_consumption.detail
            )
        } else {
            "symbolic formula JSON/SMT-LIB/sort metadata is preserved, but Wasm target semantics have not consumed it".to_string()
        },
    }));

    if conversion.provenance_evidence.is_empty() {
        records.push(WasmProofConsumerRecord {
            kind: "binary_provenance".to_string(),
            identifier: "missing".to_string(),
            accepted: false,
            detail: "no binary provenance metadata was carried into the Wasm target proof consumer"
                .to_string(),
        });
    } else {
        records.extend(conversion.provenance_evidence.iter().map(|entry| {
            WasmProofConsumerRecord {
                kind: "binary_provenance".to_string(),
                identifier: wasm_provenance_identifier(entry),
                accepted: target_semantics_consumed
                    || wasm_target_semantic_consumption_is_bridge_owned(
                        &entry.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "binary provenance source={} address=0x{:x} bytes={} was consumed by bridge-owned Wasm target proof-consumer evidence: {}",
                        entry.source,
                        entry.origin.instruction_address,
                        entry.origin.instruction_bytes.len(),
                        target_consumption.detail
                    )
                } else {
                    format!(
                        "binary provenance source={} address=0x{:x} bytes={} is preserved, but Wasm target semantics have not consumed it; bridge-owned consumer {} rejected target-semantic consumption: {}",
                        entry.source,
                        entry.origin.instruction_address,
                        entry.origin.instruction_bytes.len(),
                        entry.target_semantic_consumption.consumer,
                        entry.target_semantic_consumption.detail
                    )
                },
            }
        }));
    }

    if conversion.checked_certificate_evidence.is_empty() {
        records.push(WasmProofConsumerRecord {
            kind: "checked_certificate".to_string(),
            identifier: "missing".to_string(),
            accepted: false,
            detail:
                "no checked certificate metadata was carried into the Wasm target proof consumer"
                    .to_string(),
        });
    } else {
        records.extend(conversion.checked_certificate_evidence.iter().map(|entry| {
            WasmProofConsumerRecord {
                kind: "checked_certificate".to_string(),
                identifier: wasm_checked_certificate_identifier(entry),
                accepted: target_semantics_consumed
                    || wasm_target_semantic_consumption_is_bridge_owned(
                        &entry.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "{} was consumed by bridge-owned Wasm target proof-consumer evidence: {}",
                        checked_certificate_label(&entry.certificate),
                        target_consumption.detail
                    )
                } else {
                    format!(
                        "{} is preserved, but Wasm target semantics have not consumed it; bridge-owned consumer {} rejected target-semantic consumption: {}",
                        checked_certificate_label(&entry.certificate),
                        entry.target_semantic_consumption.consumer,
                        entry.target_semantic_consumption.detail
                    )
                },
            }
        }));
    }

    if conversion.proof_replay_evidence.is_empty() {
        records.push(WasmProofConsumerRecord {
            kind: "proof_replay".to_string(),
            identifier: "missing".to_string(),
            accepted: false,
            detail: "no proof replay metadata was carried into the Wasm target proof consumer"
                .to_string(),
        });
    } else {
        records.extend(conversion.proof_replay_evidence.iter().map(|entry| {
            WasmProofConsumerRecord {
                kind: "proof_replay".to_string(),
                identifier: wasm_proof_replay_identifier(entry),
                accepted: target_semantics_consumed
                    || wasm_target_semantic_consumption_is_bridge_owned(
                        &entry.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "proof replay status={:?} exact_replay_checked={} artifact_sha256={} was consumed by bridge-owned Wasm target proof-consumer evidence: {}",
                        entry.replay,
                        entry.exact_replay_checked,
                        entry.artifact_sha256.as_deref().unwrap_or("none"),
                        target_consumption.detail
                    )
                } else {
                    format!(
                        "proof replay status={:?} exact_replay_checked={} artifact_sha256={} is preserved, but Wasm target semantics have not consumed it; bridge-owned consumer {} rejected target-semantic consumption: {}",
                        entry.replay,
                        entry.exact_replay_checked,
                        entry.artifact_sha256.as_deref().unwrap_or("none"),
                        entry.target_semantic_consumption.consumer,
                        entry.target_semantic_consumption.detail
                    )
                },
            }
        }));
    }

    if conversion.unsupported_ledger_evidence.is_empty() {
        records.push(WasmProofConsumerRecord {
            kind: "unsupported_ledger".to_string(),
            identifier: "missing".to_string(),
            accepted: false,
            detail:
                "no unsupported-ledger elimination evidence was carried into the Wasm target proof consumer"
                    .to_string(),
        });
    } else {
        records.extend(conversion.unsupported_ledger_evidence.iter().map(|entry| {
            WasmProofConsumerRecord {
                kind: "unsupported_ledger".to_string(),
                identifier: wasm_unsupported_ledger_identifier(entry),
                accepted: target_semantics_consumed
                    || wasm_target_semantic_consumption_is_bridge_owned(
                        &entry.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "unsupported ledger eliminated={} records={} verification_unsupported={} was consumed by bridge-owned Wasm target proof-consumer evidence: {}",
                        entry.unsupported_ledger_eliminated,
                        entry.unsupported_records,
                        entry.verification_unsupported,
                        target_consumption.detail
                    )
                } else {
                    format!(
                        "unsupported ledger eliminated={} records={} verification_unsupported={} is preserved, but Wasm target semantics have not consumed it; bridge-owned consumer {} rejected target-semantic consumption: {}",
                        entry.unsupported_ledger_eliminated,
                        entry.unsupported_records,
                        entry.verification_unsupported,
                        entry.target_semantic_consumption.consumer,
                        entry.target_semantic_consumption.detail
                    )
                },
            }
        }));
    }

    if refinement_metadata_evidence.is_empty() {
        records.push(WasmProofConsumerRecord {
            kind: "target_refinement".to_string(),
            identifier: "missing".to_string(),
            accepted: false,
            detail:
                "no bidirectional Wasm refinement metadata was carried into the target proof consumer"
                    .to_string(),
        });
    } else {
        records.extend(refinement_metadata_evidence.iter().map(|entry| {
            WasmProofConsumerRecord {
                kind: "target_refinement".to_string(),
                identifier: wasm_refinement_metadata_identifier(entry),
                accepted: entry.bidirectional_refinement_consumed,
                detail: if entry.bidirectional_refinement_consumed {
                    format!(
                        "bidirectional refinement metadata slice={} source={} target_output={} target_operation={} was consumed with code {}",
                        entry.slice,
                        entry.source,
                        entry.target_output,
                        entry.target_operation,
                        entry.code
                    )
                } else {
                    format!(
                        "bidirectional refinement metadata slice={} source={} target_output={} remains rejected: {}",
                        entry.slice, entry.source, entry.target_output, entry.detail
                    )
                },
            }
        }));
    }

    let mut blockers = wasm_proof_consumer_blockers(conversion, &target_consumption);
    let proof_grade_blockers = wasm_refinement_proof_grade_blockers(
        target_semantics_consumed,
        &refinement_metadata_evidence,
    );
    append_unique_wasm_blockers(&mut blockers, &proof_grade_blockers);

    let status = if target_semantics_consumed && blockers.is_empty() {
        WasmProofConsumerStatus::Accepted
    } else {
        WasmProofConsumerStatus::Rejected
    };
    let binding = build_wasm_target_proof_binding(
        &target_output,
        status,
        target_semantics_consumed,
        conversion,
        &target_consumption,
        &refinement_metadata_evidence,
        &blockers,
    );

    WasmProofConsumerEvidence {
        target: "wasm".to_string(),
        status,
        target_semantics_consumed,
        records,
        binding,
        refinement_metadata_evidence,
        blockers,
        proof_grade_blockers,
    }
}

fn build_wasm_target_proof_binding(
    target_output: &str,
    status: WasmProofConsumerStatus,
    target_semantics_consumed: bool,
    conversion: &WasmConversion,
    target_consumption: &BoundedWasmTargetConsumption,
    refinement_metadata_evidence: &[WasmRefinementMetadataEvidence],
    blockers: &[WasmValidationBlocker],
) -> WasmTargetProofBinding {
    let mut inputs = Vec::new();

    inputs.extend(conversion.symbolic_formulas.iter().map(|formula| {
        WasmProofBindingInput {
            kind: "canonical_trust_ir_formula".to_string(),
            identifier: format!(
                "{}::bb{}::stmt{}::{}",
                formula.function, formula.block, formula.statement_index, formula.operand
            ),
            canonical_source: format!("{SYMBOLIC_FORMULA_DIALECT}.{SYMBOLIC_FORMULA_OP}"),
            target_output: target_output.to_string(),
            consumed_by_target_semantics: target_semantics_consumed,
            detail: if target_semantics_consumed {
                format!(
                    "formula sort={} bit_width={} is bound to {target_output} and consumed by bridge-owned Wasm target proof-consumer evidence: {}",
                    formula.sort,
                    formula
                        .bit_width
                        .map(|width| width.to_string())
                        .unwrap_or_else(|| "none".to_string()),
                    target_consumption.detail
                )
            } else {
                format!(
                    "formula sort={} bit_width={} is bound to {target_output}, but executable Wasm semantics have not consumed the edge",
                    formula.sort,
                    formula
                        .bit_width
                        .map(|width| width.to_string())
                        .unwrap_or_else(|| "none".to_string())
                )
            },
        }
    }));

    if conversion.provenance_evidence.is_empty() {
        inputs.push(WasmProofBindingInput {
            kind: "binary_provenance".to_string(),
            identifier: "missing".to_string(),
            canonical_source: format!("{BINARY_PROVENANCE_DIALECT}.{BINARY_PROVENANCE_OP}"),
            target_output: target_output.to_string(),
            consumed_by_target_semantics: false,
            detail: "no canonical binary provenance input is available to bind to the Wasm output"
                .to_string(),
        });
    } else {
        inputs.extend(conversion.provenance_evidence.iter().map(|entry| {
            WasmProofBindingInput {
                kind: "binary_provenance".to_string(),
                identifier: wasm_provenance_identifier(entry),
                canonical_source: format!("{BINARY_PROVENANCE_DIALECT}.{BINARY_PROVENANCE_OP}"),
                target_output: target_output.to_string(),
                consumed_by_target_semantics: target_semantics_consumed
                    || wasm_target_semantic_consumption_is_bridge_owned(
                        &entry.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "provenance source={} address=0x{:x} bytes={} is bound to {target_output} and consumed by bridge-owned Wasm target proof-consumer evidence: {}",
                        entry.source,
                        entry.origin.instruction_address,
                        entry.origin.instruction_bytes.len(),
                        target_consumption.detail
                    )
                } else {
                    format!(
                        "provenance source={} address=0x{:x} bytes={} is bound to {target_output}, but executable Wasm semantics have not consumed it",
                        entry.source,
                        entry.origin.instruction_address,
                        entry.origin.instruction_bytes.len()
                    )
                },
            }
        }));
    }

    if conversion.checked_certificate_evidence.is_empty() {
        inputs.push(WasmProofBindingInput {
            kind: "checked_certificate".to_string(),
            identifier: "missing".to_string(),
            canonical_source: "checked-certificate".to_string(),
            target_output: target_output.to_string(),
            consumed_by_target_semantics: false,
            detail: "no checked certificate input is available to bind to the Wasm output"
                .to_string(),
        });
    } else {
        inputs.extend(conversion.checked_certificate_evidence.iter().map(|entry| {
            WasmProofBindingInput {
                kind: "checked_certificate".to_string(),
                identifier: wasm_checked_certificate_identifier(entry),
                canonical_source: format!("{PROOF_METADATA_DIALECT}.{CHECKED_CERTIFICATE_OP}"),
                target_output: target_output.to_string(),
                consumed_by_target_semantics: target_semantics_consumed
                    || wasm_target_semantic_consumption_is_bridge_owned(
                        &entry.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "{} is bound to {target_output} and consumed by bridge-owned Wasm target proof-consumer evidence: {}",
                        checked_certificate_label(&entry.certificate),
                        target_consumption.detail
                    )
                } else {
                    format!(
                        "{} is bound to {target_output}, but executable Wasm semantics have not consumed the edge",
                        checked_certificate_label(&entry.certificate)
                    )
                },
            }
        }));
    }

    if conversion.proof_replay_evidence.is_empty() {
        inputs.push(WasmProofBindingInput {
            kind: "proof_replay".to_string(),
            identifier: "missing".to_string(),
            canonical_source: "proof-replay".to_string(),
            target_output: target_output.to_string(),
            consumed_by_target_semantics: false,
            detail: "no proof replay input is available to bind to the Wasm output".to_string(),
        });
    } else {
        inputs.extend(conversion.proof_replay_evidence.iter().map(|entry| {
            WasmProofBindingInput {
                kind: "proof_replay".to_string(),
                identifier: wasm_proof_replay_identifier(entry),
                canonical_source: format!("{PROOF_METADATA_DIALECT}.{PROOF_REPLAY_OP}"),
                target_output: target_output.to_string(),
                consumed_by_target_semantics: target_semantics_consumed
                    || wasm_target_semantic_consumption_is_bridge_owned(
                        &entry.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "proof replay status={:?} exact_replay_checked={} artifact_sha256={} is bound to {target_output} and consumed by bridge-owned Wasm target proof-consumer evidence: {}",
                        entry.replay,
                        entry.exact_replay_checked,
                        entry.artifact_sha256.as_deref().unwrap_or("none"),
                        target_consumption.detail
                    )
                } else {
                    format!(
                        "proof replay status={:?} exact_replay_checked={} artifact_sha256={} is bound to {target_output}, but executable Wasm semantics have not consumed the edge",
                        entry.replay,
                        entry.exact_replay_checked,
                        entry.artifact_sha256.as_deref().unwrap_or("none")
                    )
                },
            }
        }));
    }

    if conversion.unsupported_ledger_evidence.is_empty() {
        inputs.push(WasmProofBindingInput {
            kind: "unsupported_ledger".to_string(),
            identifier: "missing".to_string(),
            canonical_source: format!("{PROOF_METADATA_DIALECT}.{UNSUPPORTED_LEDGER_OP}"),
            target_output: target_output.to_string(),
            consumed_by_target_semantics: false,
            detail:
                "no unsupported-ledger elimination input is available to bind to the Wasm output"
                    .to_string(),
        });
    } else {
        inputs.extend(conversion.unsupported_ledger_evidence.iter().map(|entry| {
            WasmProofBindingInput {
                kind: "unsupported_ledger".to_string(),
                identifier: wasm_unsupported_ledger_identifier(entry),
                canonical_source: format!("{PROOF_METADATA_DIALECT}.{UNSUPPORTED_LEDGER_OP}"),
                target_output: target_output.to_string(),
                consumed_by_target_semantics: target_semantics_consumed
                    || wasm_target_semantic_consumption_is_bridge_owned(
                        &entry.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "unsupported ledger eliminated={} records={} verification_unsupported={} is bound to {target_output} and consumed by bridge-owned Wasm target proof-consumer evidence: {}",
                        entry.unsupported_ledger_eliminated,
                        entry.unsupported_records,
                        entry.verification_unsupported,
                        target_consumption.detail
                    )
                } else {
                    format!(
                        "unsupported ledger eliminated={} records={} verification_unsupported={} is bound to {target_output}, but executable Wasm semantics have not consumed the edge",
                        entry.unsupported_ledger_eliminated,
                        entry.unsupported_records,
                        entry.verification_unsupported
                    )
                },
            }
        }));
    }

    if refinement_metadata_evidence.is_empty() {
        inputs.push(WasmProofBindingInput {
            kind: "target_refinement".to_string(),
            identifier: "missing".to_string(),
            canonical_source: "bidirectional-refinement".to_string(),
            target_output: target_output.to_string(),
            consumed_by_target_semantics: false,
            detail: "no bidirectional refinement metadata input is available to bind lifted TrustIr to the Wasm output"
                .to_string(),
        });
    } else {
        inputs.extend(refinement_metadata_evidence.iter().map(|entry| {
            WasmProofBindingInput {
                kind: "target_refinement".to_string(),
                identifier: wasm_refinement_metadata_identifier(entry),
                canonical_source: entry.source.clone(),
                target_output: target_output.to_string(),
                consumed_by_target_semantics: entry.bidirectional_refinement_consumed,
                detail: if entry.bidirectional_refinement_consumed {
                    format!(
                        "bidirectional refinement slice={} binds {}::bb{}::stmt{} to {target_output} target_operation={} and is consumed by the Wasm proof-consumer gate",
                        entry.slice,
                        entry.source_function,
                        entry
                            .source_block
                            .map(|block| block.to_string())
                            .unwrap_or_else(|| "none".to_string()),
                        entry
                            .source_statement_index
                            .map(|stmt| stmt.to_string())
                            .unwrap_or_else(|| "none".to_string()),
                        entry.target_operation
                    )
                } else {
                    format!(
                        "bidirectional refinement slice={} is bound to {target_output}, but the Wasm proof-consumer gate has not consumed it: {}",
                        entry.slice, entry.detail
                    )
                },
            }
        }));
    }

    WasmTargetProofBinding {
        target: "wasm".to_string(),
        target_output: target_output.to_string(),
        lifted_trust_ir_artifact_digest: conversion.lifted_trust_ir_artifact_digest.clone(),
        bound_lifted_trust_ir_artifact_digest: conversion.bound_lifted_trust_ir_artifact_digest.clone(),
        lifted_trust_ir_artifact_digest_matched: wasm_lifted_trust_ir_artifact_digest_matches(conversion),
        status,
        target_semantics_consumed,
        inputs,
        blockers: blockers.to_vec(),
    }
}

fn wasm_target_output_identifier(conversion: &WasmConversion) -> String {
    match &conversion.wat {
        Some(wat) => {
            let mut functions = conversion
                .validation_records
                .iter()
                .filter_map(|record| record.function.clone())
                .collect::<Vec<_>>();
            functions.sort();
            functions.dedup();
            format!(
                "wat:emitted:bytes={}:functions={}",
                wat.len(),
                if functions.is_empty() { "unknown".to_string() } else { functions.join("|") }
            )
        }
        None => "wat:blocked:no-emitted-module".to_string(),
    }
}

fn wasm_refinement_metadata_identifier(entry: &WasmRefinementMetadataEvidence) -> String {
    let source_block = entry
        .source_block
        .map(|block| format!("bb{block}"))
        .unwrap_or_else(|| "bbnone".to_string());
    let source_statement = entry
        .source_statement_index
        .map(|statement| format!("stmt{statement}"))
        .unwrap_or_else(|| "stmtnone".to_string());
    format!(
        "{}::{}::{}::{}::{}::{}",
        entry.slice,
        entry.source,
        entry.source_function,
        source_block,
        source_statement,
        entry.target_operation
    )
}

fn wasm_proof_consumer_blockers(
    conversion: &WasmConversion,
    target_consumption: &BoundedWasmTargetConsumption,
) -> Vec<WasmValidationBlocker> {
    let mut blockers = unsupported_ledger_blockers(&conversion.unsupported);
    blockers.extend(wasm_lifted_trust_ir_artifact_digest_blockers(conversion));
    if target_consumption.accepted {
        return blockers;
    }

    blockers.push(validation_blocker(
        "target-semantics-not-consumed",
        "Wasm target semantics have not consumed symbolic formula, checked-certificate, replay, or binary-provenance metadata",
    ));

    blockers.extend(target_consumption.blockers.clone());

    if !conversion.symbolic_formulas.is_empty() {
        let symbolic_metadata =
            symbolic_formulas_to_bounded_metadata(&conversion.symbolic_formulas);
        blockers.push(validation_blocker(
            "symbolic-formula-not-consumed-by-target-semantics",
            &format!(
                "{} symbolic formula metadata record(s) are preserved but not consumed by Wasm target semantics; bridge-owned consumer {WASM_TARGET_SEMANTIC_CONSUMER} has not consumed formula JSON/SMT-LIB/sort metadata: {}",
                conversion.symbolic_formulas.len(),
                symbolic_formula_summary(&symbolic_metadata)
            ),
        ));
    }

    blockers.extend(wasm_provenance_target_blockers(&conversion.provenance_evidence));
    blockers.extend(wasm_checked_certificate_blockers(&conversion.checked_certificate_evidence));
    blockers.extend(wasm_proof_replay_blockers(&conversion.proof_replay_evidence));
    blockers.extend(wasm_unsupported_ledger_blockers(&conversion.unsupported_ledger_evidence));

    blockers
}

fn wasm_lifted_trust_ir_artifact_digest_matches(conversion: &WasmConversion) -> bool {
    matches!(
        (
            conversion.lifted_trust_ir_artifact_digest.as_deref(),
            conversion.bound_lifted_trust_ir_artifact_digest.as_deref(),
        ),
        (Some(lifted), Some(bound))
            if is_canonical_sha256_hex(lifted) && lifted == bound
    )
}

fn wasm_lifted_trust_ir_artifact_digest_blockers(
    conversion: &WasmConversion,
) -> Vec<WasmValidationBlocker> {
    let lifted = conversion.lifted_trust_ir_artifact_digest.as_deref().map(str::trim);
    let bound = conversion.bound_lifted_trust_ir_artifact_digest.as_deref().map(str::trim);

    let Some(lifted) = lifted.filter(|digest| !digest.is_empty()) else {
        return vec![validation_blocker(
            "lifted-trust_ir-artifact-digest-missing",
            "Wasm target proof-consumer binding requires the lifted TrustIr artifact SHA-256 digest that produced the target output",
        )];
    };
    let Some(bound) = bound.filter(|digest| !digest.is_empty()) else {
        if is_canonical_sha256_hex(lifted) {
            return vec![validation_blocker(
                "bound-lifted-trust_ir-artifact-digest-missing",
                "Wasm target proof-consumer binding did not carry the lifted TrustIr artifact SHA-256 digest it consumed",
            )];
        }
        return vec![validation_blocker(
            "lifted-trust_ir-artifact-digest-noncanonical",
            "Wasm target proof-consumer binding requires lowercase canonical SHA-256 digests for both the lifted TrustIr artifact and the consumed binding digest",
        )];
    };

    if !is_canonical_sha256_hex(lifted) || !is_canonical_sha256_hex(bound) {
        return vec![validation_blocker(
            "lifted-trust_ir-artifact-digest-noncanonical",
            "Wasm target proof-consumer binding requires lowercase canonical SHA-256 digests for both the lifted TrustIr artifact and the consumed binding digest",
        )];
    }

    if lifted == bound {
        Vec::new()
    } else {
        vec![validation_blocker(
            "lifted-trust_ir-artifact-digest-mismatch",
            &format!(
                "Wasm target proof-consumer binding consumed lifted TrustIr artifact digest {bound}, but the conversion was produced from lifted TrustIr artifact digest {lifted}"
            ),
        )]
    }
}

fn is_canonical_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value
            .as_bytes()
            .iter()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
}

fn wasm_scalar_target_consumer_blockers(conversion: &WasmConversion) -> Vec<WasmValidationBlocker> {
    match conversion.wat.as_deref() {
        Some(wat) => wasm_non_empty_scalar_target_consumer_blockers(conversion, wat),
        None if !conversion.symbolic_formulas.is_empty() => vec![validation_blocker(
            "no-emitted-scalar-wasm-target-op-binding",
            "Wasm scalar proof consumer preserved canonical formula metadata, but this bridge emitted no WAT target operation to bind against it; only the bounded empty/no-op metadata slice is currently consumable without emitted Wasm",
        )],
        None => Vec::new(),
    }
}

fn wasm_non_empty_scalar_target_consumption(
    conversion: &WasmConversion,
) -> BoundedWasmTargetConsumption {
    let Some(wat) = conversion.wat.as_deref() else {
        return BoundedWasmTargetConsumption {
            accepted: false,
            detail: "non-empty scalar Wasm target proof-consumer slice did not apply because no WAT module was emitted"
                .to_string(),
            blockers: wasm_scalar_target_consumer_blockers(conversion),
        };
    };

    match exact_non_empty_scalar_target_binding(conversion, wat) {
        Ok(binding) => BoundedWasmTargetConsumption {
            accepted: true,
            detail: format!(
                "Wasm target proof consumer accepted the non-empty scalar slice: emitted {} target output is exactly bound to {}={}, {}, {}, {}, and {} for function {} with proof identity {}",
                binding.target_operation,
                binding.formula_identifier,
                binding.formula_value,
                binding.provenance_identifier,
                binding.checked_certificate_identifier,
                binding.proof_replay_identifier,
                binding.unsupported_ledger_identifier,
                binding.function,
                binding.proof_identity
            ),
            blockers: Vec::new(),
        },
        Err(blockers) => BoundedWasmTargetConsumption {
            accepted: false,
            detail: "non-empty scalar Wasm target proof-consumer slice did not apply".to_string(),
            blockers: unavailable_non_empty_scalar_blockers(blockers),
        },
    }
}

fn wasm_non_empty_scalar_target_consumer_blockers(
    conversion: &WasmConversion,
    wat: &str,
) -> Vec<WasmValidationBlocker> {
    match exact_non_empty_scalar_target_binding(conversion, wat) {
        Ok(_) => Vec::new(),
        Err(blockers) => unavailable_non_empty_scalar_blockers(blockers),
    }
}

fn unavailable_non_empty_scalar_blockers(
    blockers: Vec<WasmValidationBlocker>,
) -> Vec<WasmValidationBlocker> {
    if blockers.is_empty() {
        return blockers;
    }

    let mut blockers = blockers;
    blockers.insert(0, validation_blocker(
        "non-empty-scalar-wasm-target-consumer-unavailable",
        "Wasm target proof consumer observed emitted WAT output, but the bridge-owned non-empty scalar consumer did not accept it; accepted shape requires exactly one boolean i32.const operation, one matching canonical Bool formula, one checked certificate identity, one exact replay identity, one matching no-op provenance, and unsupported-ledger elimination evidence",
    ));
    blockers
}

fn exact_non_empty_scalar_target_binding(
    conversion: &WasmConversion,
    wat: &str,
) -> Result<NonEmptyScalarTargetBinding, Vec<WasmValidationBlocker>> {
    let mut blockers = Vec::new();
    let target_bool = wat_single_i32_const_bool_result(wat);
    if target_bool.is_none() {
        blockers.push(validation_blocker(
            "missing-scalar-formula-target-op-binding",
            "non-empty scalar Wasm proof consumption currently requires exactly one emitted i32.const 0 or i32.const 1 result operation as the target side of a Bool formula binding",
        ));
    }

    let formula = target_bool
        .and_then(|target_bool| exact_bool_formula(&conversion.symbolic_formulas, target_bool));
    if formula.is_none() {
        let detail = match target_bool {
            Some(true) => {
                "emitted WAT contains an i32.const 1 result operation, but the conversion carries no exactly matching canonical Bool(true) formula metadata to bind to that target op"
            }
            Some(false) => {
                "emitted WAT contains an i32.const 0 result operation, but the conversion carries no exactly matching canonical Bool(false) formula metadata to bind to that target op"
            }
            None => {
                "emitted WAT has no single boolean i32.const result operation, so the conversion has no target op that can be bound to canonical Bool(true) or Bool(false) formula metadata"
            }
        };
        blockers.push(validation_blocker("missing-scalar-formula-target-op-binding", detail));
    }

    let checked_certificate_candidates = conversion
        .checked_certificate_evidence
        .iter()
        .filter(|entry| checked_certificate_has_canonical_identity(&entry.certificate))
        .collect::<Vec<_>>();
    let checked_certificate = (conversion.checked_certificate_evidence.len() == 1
        && checked_certificate_candidates.len() == 1)
        .then(|| checked_certificate_candidates[0]);
    if checked_certificate_candidates.is_empty() {
        blockers.push(validation_blocker(
            "non-empty-scalar-checked-certificate-identity-missing",
            "non-empty scalar Wasm proof consumption requires checked certificate metadata with checker, format, and sha256 identity",
        ));
    }

    let proof_replay_candidates = conversion
        .proof_replay_evidence
        .iter()
        .filter(|entry| has_replay_grade_artifact_identity(entry))
        .collect::<Vec<_>>();
    let proof_replay = (conversion.proof_replay_evidence.len() == 1
        && proof_replay_candidates.len() == 1)
        .then(|| proof_replay_candidates[0]);
    if proof_replay_candidates.is_empty() {
        blockers.push(validation_blocker(
            "non-empty-scalar-replay-artifact-identity-missing",
            "non-empty scalar Wasm proof consumption requires ReplayStatus::Replayed, exact replay checked, and a replay-grade artifact SHA-256 identity bound to emitted WAT",
        ));
    }

    let proof_identity = checked_certificate
        .zip(proof_replay)
        .and_then(|(certificate, replay)| scalar_proof_metadata_identity(certificate, replay));
    if proof_identity.is_none() {
        push_unique_blocker(
            &mut blockers,
            "non-empty-scalar-proof-metadata-identity-mismatch",
            "non-empty scalar Wasm proof consumption requires exactly one checked certificate and exactly one exact replay record for the same solver/proof metadata identity",
        );
    }

    let provenance = match (formula, proof_identity.as_deref()) {
        (Some(formula), Some(proof_identity)) => {
            exact_scalar_noop_provenance(&conversion.provenance_evidence, formula, proof_identity)
        }
        (Some(formula), None) => {
            exact_scalar_source_statement_noop_provenance(&conversion.provenance_evidence, formula)
        }
        (None, _) => None,
    };
    if provenance.is_none() {
        push_unique_blocker(
            &mut blockers,
            "non-empty-scalar-binary-provenance-missing",
            "non-empty scalar Wasm proof consumption requires exact no-op binary provenance for the scalar source statement or matching proof dispatch",
        );
    }

    let unsupported_ledger_eliminated = conversion
        .unsupported_ledger_evidence
        .iter()
        .filter(|entry| is_unsupported_ledger_eliminated_evidence(entry))
        .collect::<Vec<_>>();
    if conversion.unsupported_ledger_evidence.is_empty() {
        blockers.push(validation_blocker(
            "non-empty-scalar-unsupported-ledger-evidence-missing",
            "non-empty scalar Wasm proof consumption requires unsupported-ledger elimination evidence",
        ));
    } else if unsupported_ledger_eliminated.len() != conversion.unsupported_ledger_evidence.len() {
        blockers.push(validation_blocker(
            "non-empty-scalar-unsupported-ledger-not-eliminated",
            "non-empty scalar Wasm proof consumption requires empty unsupported ledgers and zero unsupported verification counters",
        ));
    }

    if blockers.is_empty() {
        let formula = formula.expect("blockers empty only when formula exists");
        let target_bool = target_bool.expect("blockers empty only when target bool exists");
        let checked_certificate =
            checked_certificate.expect("blockers empty only when checked certificate exists");
        let proof_replay = proof_replay.expect("blockers empty only when proof replay exists");
        let provenance = provenance.expect("blockers empty only when provenance exists");
        let proof_identity =
            proof_identity.expect("blockers empty only when proof identity exists");
        let unsupported_ledger_identifier = unsupported_ledger_eliminated
            .iter()
            .map(|entry| wasm_unsupported_ledger_identifier(entry))
            .collect::<Vec<_>>()
            .join("|");
        Ok(NonEmptyScalarTargetBinding {
            function: formula.function.clone(),
            formula_value: target_bool,
            target_operation: if target_bool { "i32.const 1" } else { "i32.const 0" },
            formula_identifier: format!(
                "{}::bb{}::stmt{}::{}",
                formula.function, formula.block, formula.statement_index, formula.operand
            ),
            provenance_identifier: wasm_provenance_identifier(provenance),
            checked_certificate_identifier: wasm_checked_certificate_identifier(
                checked_certificate,
            ),
            proof_replay_identifier: wasm_proof_replay_identifier(proof_replay),
            unsupported_ledger_identifier,
            proof_identity,
        })
    } else {
        Err(blockers)
    }
}

fn push_unique_blocker(blockers: &mut Vec<WasmValidationBlocker>, code: &str, detail: &str) {
    if !blockers.iter().any(|blocker| blocker.code == code) {
        blockers.push(validation_blocker(code, detail));
    }
}

fn wat_single_i32_const_bool_result(wat: &str) -> Option<bool> {
    let semantic_ops = wat
        .lines()
        .map(str::trim)
        .filter(|line| {
            !line.is_empty()
                && !line.starts_with("(module")
                && !line.starts_with("(func ")
                && !line.starts_with("(export ")
                && *line != ")"
        })
        .map(|line| line.trim_end_matches(')').trim())
        .collect::<Vec<_>>();
    match semantic_ops.as_slice() {
        ["i32.const 1"] => Some(true),
        ["i32.const 0"] => Some(false),
        _ => None,
    }
}

fn exact_bool_formula(
    formulas: &[WasmSymbolicFormula],
    expected: bool,
) -> Option<&WasmSymbolicFormula> {
    match formulas {
        [formula]
            if formula.formula == Formula::Bool(expected)
                && formula.sort == "Bool"
                && formula.bit_width.is_none()
                && formula.operand == "use" =>
        {
            Some(formula)
        }
        _ => None,
    }
}

fn has_replay_grade_artifact_identity(entry: &WasmProofReplayEvidence) -> bool {
    entry.replay == ReplayStatus::Replayed
        && entry.exact_replay_checked
        && entry.artifact_sha256.as_deref().is_some_and(|sha256| !sha256.trim().is_empty())
}

fn scalar_proof_metadata_identity(
    certificate: &WasmCheckedCertificateEvidence,
    replay: &WasmProofReplayEvidence,
) -> Option<String> {
    let function = certificate.function.trim();
    if function.is_empty() || certificate.function != replay.function {
        return None;
    }

    let certificate_source = metadata_source_identity(&certificate.source);
    let replay_source = metadata_source_identity(&replay.source);
    if certificate_source.is_empty() || certificate_source != replay_source {
        return None;
    }

    Some(format!("{function}:{certificate_source}"))
}

fn metadata_source_identity(source: &str) -> &str {
    source.split_once(':').map_or(source, |(_, identity)| identity).trim()
}

fn exact_scalar_noop_provenance<'a>(
    provenance_evidence: &'a [WasmProvenanceEvidence],
    formula: &WasmSymbolicFormula,
    proof_identity: &str,
) -> Option<&'a WasmProvenanceEvidence> {
    let proof_source_identity =
        proof_identity.split_once(':').map_or(proof_identity, |(_, identity)| identity);
    let matches = provenance_evidence
        .iter()
        .filter(|entry| {
            entry.function == formula.function
                && is_exact_noop_provenance(entry)
                && (entry.block == Some(formula.block)
                    && entry.statement_index == Some(formula.statement_index)
                    || metadata_source_identity(&entry.source) == proof_source_identity)
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [entry] => Some(*entry),
        _ => None,
    }
}

fn exact_scalar_source_statement_noop_provenance<'a>(
    provenance_evidence: &'a [WasmProvenanceEvidence],
    formula: &WasmSymbolicFormula,
) -> Option<&'a WasmProvenanceEvidence> {
    let matches = provenance_evidence
        .iter()
        .filter(|entry| {
            entry.function == formula.function
                && is_exact_noop_provenance(entry)
                && entry.block == Some(formula.block)
                && entry.statement_index == Some(formula.statement_index)
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [entry] => Some(*entry),
        _ => None,
    }
}

fn is_exact_noop_provenance(entry: &WasmProvenanceEvidence) -> bool {
    entry.origin.binary_path.as_deref().is_some_and(|binary_path| !binary_path.trim().is_empty())
        && entry.origin.function_entry.is_some()
        && entry
            .origin
            .instruction_size
            .is_some_and(|size| usize::from(size) == entry.origin.instruction_bytes.len())
        && entry.origin.encoding.is_some()
        && is_recognized_noop_instruction_bytes(&entry.origin.instruction_bytes)
}

fn validation_direction(
    direction: ReconstructionValidationDirection,
    status: ReconstructionValidationStatus,
) -> ReconstructionValidationDirectionRecord {
    ReconstructionValidationDirectionRecord {
        direction,
        status,
        vc_count: 0,
        counterexamples: 0,
        proof_certificates: 0,
        diagnostics: vec![
            "syntactic subset check only; no solver VC, checked proof certificate, or proof replay metadata"
                .to_string(),
        ],
    }
}

fn origin_from_span(span: &SourceSpan) -> Option<BinaryOrigin> {
    span.binary_address_value().map(|instruction_address| BinaryOrigin {
        instruction_address,
        source: Some(span.clone()),
        ..Default::default()
    })
}

fn wasm_target_semantic_consumption_evidence(
    input_claimed_target_semantics_consumed: Option<bool>,
) -> WasmTargetSemanticConsumptionEvidence {
    let claim_detail = match input_claimed_target_semantics_consumed {
        Some(true) => {
            "canonical input claimed target_semantics_consumed=true; claim is preserved only as untrusted metadata"
        }
        Some(false) => {
            "canonical input claimed target_semantics_consumed=false; claim is preserved only as untrusted metadata"
        }
        None => "no canonical target_semantics_consumed claim was present",
    };

    WasmTargetSemanticConsumptionEvidence {
        consumer: WASM_TARGET_SEMANTIC_CONSUMER.to_string(),
        target_semantics_consumed: false,
        input_claimed_target_semantics_consumed,
        code: "no-wasm-target-semantic-consumer".to_string(),
        detail: format!(
            "{claim_detail}; no bridge-owned executable Wasm target semantic consumer has consumed binary provenance, symbolic formula, checked-certificate, replay, or unsupported-ledger evidence"
        ),
    }
}

fn wasm_bounded_empty_target_semantic_consumption_evidence(
    detail: &str,
) -> WasmTargetSemanticConsumptionEvidence {
    WasmTargetSemanticConsumptionEvidence {
        consumer: WASM_TARGET_SEMANTIC_CONSUMER.to_string(),
        target_semantics_consumed: true,
        input_claimed_target_semantics_consumed: None,
        code: WASM_BOUNDED_EMPTY_TARGET_CONSUMED_CODE.to_string(),
        detail: detail.to_string(),
    }
}

fn collect_symbolic_formulas(function: &VerifiableFunction) -> Vec<WasmSymbolicFormula> {
    let mut formulas = Vec::new();
    for block in &function.body.blocks {
        for (statement_index, statement) in block.stmts.iter().enumerate() {
            match statement {
                Statement::Assign { rvalue, .. } => {
                    collect_rvalue_symbolics(
                        &function.name,
                        block.id.0,
                        statement_index,
                        rvalue,
                        &mut formulas,
                    );
                }
                Statement::Intrinsic { args, .. }
                | Statement::Unsupported { operands: args, .. } => {
                    for (arg_index, operand) in args.iter().enumerate() {
                        collect_operand_symbolic(
                            &function.name,
                            block.id.0,
                            statement_index,
                            &format!("arg{arg_index}"),
                            operand,
                            &mut formulas,
                        );
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::SetDiscriminant { .. }
                | Statement::Deinit { .. }
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                _ => {}
            }
        }
    }
    formulas
}

fn collect_function_provenance_evidence(
    function: &VerifiableFunction,
) -> Vec<WasmProvenanceEvidence> {
    let mut evidence = Vec::new();
    if let Some(origin) = origin_from_span(&function.span) {
        evidence.push(WasmProvenanceEvidence {
            function: function.name.clone(),
            source: "lifted.function_span".to_string(),
            block: None,
            statement_index: None,
            origin,
            target_semantic_consumption: wasm_target_semantic_consumption_evidence(None),
            target_semantics_consumed: false,
        });
    }

    for block in &function.body.blocks {
        for (statement_index, statement) in block.stmts.iter().enumerate() {
            let Statement::Assign { span, .. } = statement else {
                continue;
            };
            if let Some(origin) = origin_from_span(span) {
                evidence.push(WasmProvenanceEvidence {
                    function: function.name.clone(),
                    source: format!("lifted.bb{}.stmt{}", block.id.0, statement_index),
                    block: Some(block.id.0),
                    statement_index: Some(statement_index),
                    origin,
                    target_semantic_consumption: wasm_target_semantic_consumption_evidence(None),
                    target_semantics_consumed: false,
                });
            }
        }
    }
    evidence
}

fn wasm_provenance_identifier(entry: &WasmProvenanceEvidence) -> String {
    match (entry.block, entry.statement_index) {
        (Some(block), Some(statement_index)) => format!(
            "{}::bb{}::stmt{}::{}::0x{:x}",
            entry.function, block, statement_index, entry.source, entry.origin.instruction_address
        ),
        _ => format!(
            "{}::{}::0x{:x}",
            entry.function, entry.source, entry.origin.instruction_address
        ),
    }
}

fn wasm_checked_certificate_identifier(entry: &WasmCheckedCertificateEvidence) -> String {
    let suffix = match &entry.certificate {
        ProofCertificateStatus::Checked { checker, format, sha256 } => {
            format!("{checker}:{format}:{}", sha256.as_deref().unwrap_or("missing-sha256"))
        }
        ProofCertificateStatus::Present { format, sha256, .. } => {
            format!("present:{format}:{}", sha256.as_deref().unwrap_or("missing-sha256"))
        }
        ProofCertificateStatus::Unavailable { .. } => "unavailable".to_string(),
        ProofCertificateStatus::Rejected { checker, .. } => {
            format!("rejected:{}", checker.as_deref().unwrap_or("unknown-checker"))
        }
        ProofCertificateStatus::NotRequested => "not-requested".to_string(),
        _ => "unknown-certificate-status".to_string(),
    };
    match (entry.block, entry.statement_index) {
        (Some(block), Some(statement_index)) => {
            format!("{}::bb{}::stmt{}::{suffix}", entry.function, block, statement_index)
        }
        _ => format!("{}::{}::{suffix}", entry.function, entry.source),
    }
}

fn wasm_proof_replay_identifier(entry: &WasmProofReplayEvidence) -> String {
    let suffix = format!(
        "{:?}:{}:{}",
        entry.replay,
        if entry.exact_replay_checked { "exact" } else { "not-exact" },
        entry.artifact_sha256.as_deref().unwrap_or("missing-artifact-sha256")
    );
    match (entry.block, entry.statement_index) {
        (Some(block), Some(statement_index)) => {
            format!("{}::bb{}::stmt{}::{suffix}", entry.function, block, statement_index)
        }
        _ => format!("{}::{}::{suffix}", entry.function, entry.source),
    }
}

fn wasm_unsupported_ledger_identifier(entry: &WasmUnsupportedLedgerEvidence) -> String {
    let suffix = format!(
        "records={}:verification_unsupported={}:eliminated={}",
        entry.unsupported_records,
        entry.verification_unsupported,
        entry.unsupported_ledger_eliminated
    );
    match (entry.block, entry.statement_index) {
        (Some(block), Some(statement_index)) => {
            format!("{}::bb{}::stmt{}::{suffix}", entry.function, block, statement_index)
        }
        _ => format!("{}::{}::{suffix}", entry.function, entry.source),
    }
}

fn wasm_provenance_evidence_detail(entry: &WasmProvenanceEvidence) -> String {
    let mut parts = vec![
        format!("binary_provenance.function={}", entry.function),
        format!("binary_provenance.source={}", entry.source),
        format!("binary_provenance.instruction_address=0x{:x}", entry.origin.instruction_address),
        format!("binary_provenance.target_semantics_consumed={}", entry.target_semantics_consumed),
        format!(
            "binary_provenance.consumption.consumer={}",
            entry.target_semantic_consumption.consumer
        ),
        format!("binary_provenance.consumption.code={}", entry.target_semantic_consumption.code),
        format!(
            "binary_provenance.consumption.target_semantics_consumed={}",
            entry.target_semantic_consumption.target_semantics_consumed
        ),
    ];
    if let Some(claim) = entry.target_semantic_consumption.input_claimed_target_semantics_consumed {
        parts.push(format!("binary_provenance.input_claim.target_semantics_consumed={claim}"));
    }
    if let Some(block) = entry.block {
        parts.push(format!("binary_provenance.block={block}"));
    }
    if let Some(statement_index) = entry.statement_index {
        parts.push(format!("binary_provenance.statement_index={statement_index}"));
    }
    if let Some(function_entry) = entry.origin.function_entry {
        parts.push(format!("binary_provenance.function_entry=0x{function_entry:x}"));
    }
    if let Some(instruction_size) = entry.origin.instruction_size {
        parts.push(format!("binary_provenance.instruction_size={instruction_size}"));
    }
    if let Some(encoding) = entry.origin.encoding {
        parts.push(format!("binary_provenance.encoding=0x{encoding:x}"));
    }
    if !entry.origin.instruction_bytes.is_empty() {
        parts.push(format!(
            "binary_provenance.instruction_bytes={}",
            hex_bytes(&entry.origin.instruction_bytes)
        ));
    }
    parts.join("; ")
}

fn wasm_checked_certificate_detail(entry: &WasmCheckedCertificateEvidence) -> String {
    let mut parts = vec![
        format!("checked_certificate.function={}", entry.function),
        format!("checked_certificate.source={}", entry.source),
        format!("checked_certificate.status={}", checked_certificate_label(&entry.certificate)),
        format!(
            "checked_certificate.target_semantics_consumed={}",
            entry.target_semantics_consumed
        ),
        format!(
            "checked_certificate.consumption.consumer={}",
            entry.target_semantic_consumption.consumer
        ),
        format!("checked_certificate.consumption.code={}", entry.target_semantic_consumption.code),
        format!(
            "checked_certificate.consumption.target_semantics_consumed={}",
            entry.target_semantic_consumption.target_semantics_consumed
        ),
    ];
    if let Some(claim) = entry.target_semantic_consumption.input_claimed_target_semantics_consumed {
        parts.push(format!("checked_certificate.input_claim.target_semantics_consumed={claim}"));
    }
    if let Some(block) = entry.block {
        parts.push(format!("checked_certificate.block={block}"));
    }
    if let Some(statement_index) = entry.statement_index {
        parts.push(format!("checked_certificate.statement_index={statement_index}"));
    }
    parts.join("; ")
}

fn wasm_proof_replay_detail(entry: &WasmProofReplayEvidence) -> String {
    let mut parts = vec![
        format!("proof_replay.function={}", entry.function),
        format!("proof_replay.source={}", entry.source),
        format!("proof_replay.status={:?}", entry.replay),
        format!("proof_replay.exact_replay_checked={}", entry.exact_replay_checked),
        format!("proof_replay.target_semantics_consumed={}", entry.target_semantics_consumed),
        format!("proof_replay.consumption.consumer={}", entry.target_semantic_consumption.consumer),
        format!("proof_replay.consumption.code={}", entry.target_semantic_consumption.code),
        format!(
            "proof_replay.consumption.target_semantics_consumed={}",
            entry.target_semantic_consumption.target_semantics_consumed
        ),
    ];
    if let Some(artifact_sha256) = &entry.artifact_sha256 {
        parts.push(format!("proof_replay.artifact_sha256={artifact_sha256}"));
    }
    if let Some(claim) = entry.target_semantic_consumption.input_claimed_target_semantics_consumed {
        parts.push(format!("proof_replay.input_claim.target_semantics_consumed={claim}"));
    }
    if let Some(block) = entry.block {
        parts.push(format!("proof_replay.block={block}"));
    }
    if let Some(statement_index) = entry.statement_index {
        parts.push(format!("proof_replay.statement_index={statement_index}"));
    }
    parts.join("; ")
}

fn wasm_unsupported_ledger_detail(entry: &WasmUnsupportedLedgerEvidence) -> String {
    let mut parts = vec![
        format!("unsupported_ledger.function={}", entry.function),
        format!("unsupported_ledger.source={}", entry.source),
        format!("unsupported_ledger.records={}", entry.unsupported_records),
        format!("unsupported_ledger.verification_unsupported={}", entry.verification_unsupported),
        format!("unsupported_ledger.eliminated={}", entry.unsupported_ledger_eliminated),
        format!("unsupported_ledger.target_semantics_consumed={}", entry.target_semantics_consumed),
        format!(
            "unsupported_ledger.consumption.consumer={}",
            entry.target_semantic_consumption.consumer
        ),
        format!("unsupported_ledger.consumption.code={}", entry.target_semantic_consumption.code),
        format!(
            "unsupported_ledger.consumption.target_semantics_consumed={}",
            entry.target_semantic_consumption.target_semantics_consumed
        ),
    ];
    if let Some(block) = entry.block {
        parts.push(format!("unsupported_ledger.block={block}"));
    }
    if let Some(statement_index) = entry.statement_index {
        parts.push(format!("unsupported_ledger.statement_index={statement_index}"));
    }
    if let Some(claim) = entry.target_semantic_consumption.input_claimed_target_semantics_consumed {
        parts.push(format!("unsupported_ledger.input_claim.target_semantics_consumed={claim}"));
    }
    parts.join("; ")
}

fn checked_certificate_label(status: &ProofCertificateStatus) -> String {
    match status {
        ProofCertificateStatus::Checked { checker, format, sha256 } => format!(
            "checked certificate checker={checker} format={format} sha256={}",
            sha256.as_deref().unwrap_or("none")
        ),
        ProofCertificateStatus::Present { format, sha256, artifact_path } => format!(
            "unchecked certificate format={format} sha256={} artifact_path={}",
            sha256.as_deref().unwrap_or("none"),
            artifact_path.as_deref().unwrap_or("none")
        ),
        ProofCertificateStatus::Unavailable { reason } => {
            format!("unavailable certificate reason={}", reason.as_deref().unwrap_or("unspecified"))
        }
        ProofCertificateStatus::Rejected { checker, reason } => format!(
            "rejected certificate checker={} reason={reason}",
            checker.as_deref().unwrap_or("unknown")
        ),
        ProofCertificateStatus::NotRequested => "certificate not requested".to_string(),
        _ => "unknown certificate status".to_string(),
    }
}

fn hex_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect::<Vec<_>>().join("")
}

fn collect_rvalue_symbolics(
    function: &str,
    block: usize,
    statement_index: usize,
    rvalue: &Rvalue,
    formulas: &mut Vec<WasmSymbolicFormula>,
) {
    match rvalue {
        Rvalue::Use(operand) => {
            collect_operand_symbolic(function, block, statement_index, "use", operand, formulas);
        }
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            collect_operand_symbolic(function, block, statement_index, "lhs", lhs, formulas);
            collect_operand_symbolic(function, block, statement_index, "rhs", rhs, formulas);
        }
        Rvalue::UnaryOp(_, operand) | Rvalue::Cast(operand, _) | Rvalue::Repeat(operand, _) => {
            collect_operand_symbolic(
                function,
                block,
                statement_index,
                "operand",
                operand,
                formulas,
            );
        }
        Rvalue::Aggregate(_, operands) | Rvalue::Unsupported { operands, .. } => {
            for (operand_index, operand) in operands.iter().enumerate() {
                collect_operand_symbolic(
                    function,
                    block,
                    statement_index,
                    &format!("operand{operand_index}"),
                    operand,
                    formulas,
                );
            }
        }
        Rvalue::Ref { .. }
        | Rvalue::Discriminant(_)
        | Rvalue::Len(_)
        | Rvalue::AddressOf(_, _)
        | Rvalue::CopyForDeref(_) => {}
        _ => {}
    }
}

fn collect_operand_symbolic(
    function: &str,
    block: usize,
    statement_index: usize,
    operand: &str,
    value: &Operand,
    formulas: &mut Vec<WasmSymbolicFormula>,
) {
    if let Operand::Symbolic(formula) = value {
        let formula_schema = symbolic_formula_schema(formula);
        formulas.push(WasmSymbolicFormula {
            function: function.to_string(),
            block,
            statement_index,
            operand: operand.to_string(),
            formula: formula.clone(),
            sort: formula_schema.sort,
            bit_width: formula_schema.bit_width,
        });
    }
}

fn wat_symbol(name: &str) -> String {
    let mut symbol = String::new();
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() || matches!(ch, '_' | '.' | ':' | '-') {
            symbol.push(ch);
        } else {
            symbol.push('_');
        }
    }
    if symbol.is_empty() { "function".to_string() } else { symbol }
}

fn param_symbol(local: usize) -> String {
    format!("p{local}")
}

fn wat_string(name: &str) -> String {
    let mut escaped = String::new();
    for ch in name.chars() {
        match ch {
            '"' => escaped.push_str("\\22"),
            '\\' => escaped.push_str("\\5c"),
            ch if ch.is_ascii_graphic() || ch == ' ' => escaped.push(ch),
            _ => escaped.push('_'),
        }
    }
    escaped
}
