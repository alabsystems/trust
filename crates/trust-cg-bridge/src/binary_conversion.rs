//! Safe binary-derived TrustIr to trust_cg LIR conversion.
//!
//! This module is intentionally a narrow contract layer. Binary lifting and
//! Rust reconstruction are not proof-grade here; this pass only lowers a
//! binary-derived TrustIr candidate into structurally validated trust_cg LIR and
//! carries explicit diagnostics about that provenance.

use trust_cg_lower::function::Function as LirFunction;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type as LirType;
use trust_types::{
    BinaryOrigin, DecompiledFunction, Formula, Operand, ProofCertificateStatus,
    ReconstructionValidationStatus, ReplayStatus, Rvalue, SolverDispatchRecord, Sort, Statement,
    Terminator, TrustLevel, Ty, VerifiableFunction, infer_sort,
};

use crate::validation::{ValidationError, validate_lir};
use crate::{BridgeError, lower_to_lir};

const DIAGNOSTIC_TARGET: &str = "target=trust_cg-lir";
const DIAGNOSTIC_SOURCE: &str = "source=binary-derived-trust_ir";
const DIAGNOSTIC_CANONICAL_SOURCE: &str = "source=canonical-trust_ir";
const DIAGNOSTIC_NOT_PROOF_GRADE: &str = "not-proof-grade";
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
const PROOF_METADATA_ATTR_TARGET_SEMANTICS_CONSUMED: &str = "target_semantics_consumed";
const PROOF_METADATA_ATTR_UNSUPPORTED_RECORDS: &str = "unsupported_records";
const PROOF_METADATA_ATTR_VERIFICATION_UNSUPPORTED: &str = "verification_unsupported";
const CHECKED_CERTIFICATE_SCHEMA: &str = "trust-types.CheckedCertificate@1";
const PROOF_REPLAY_SCHEMA: &str = "trust-types.ProofReplay@1";
const UNSUPPORTED_LEDGER_SCHEMA: &str = "trust-types.UnsupportedLedger@1";
const CHECKED_CERTIFICATE_AUDIT_METADATA_PREFIX: &str = "checked-certificate.audit.";
const CHECKED_CERTIFICATE_READBACK_METADATA_PREFIX: &str = "checked-certificate.readback.";
const TRUST_CG_TARGET_SEMANTIC_CONSUMER: &str = "trust-cg-bridge::target-semantic-consumption-gate";
const TRUST_CG_REFINEMENT_METADATA_CONSUMER: &str =
    "trust-cg-bridge::bidirectional-refinement-consumption-gate";
const TRUST_CG_BOUNDED_EMPTY_TARGET_CONSUMED_CODE: &str = "bounded-empty-trust_cg-target-consumed";
const TRUST_CG_SCALAR_TARGET_CONSUMED_CODE: &str = "scalar-bool-true-trust_cg-target-consumed";
const SCALAR_BOOL_TRUE_REFINEMENT_FORWARD: &str =
    "lifted TrustIr local0 = Symbolic(Bool(true)) refines trust_cg Iconst(B1, 1)";
const SCALAR_BOOL_TRUE_REFINEMENT_REVERSE: &str =
    "trust-cg Iconst(B1, 1) result refines the lifted TrustIr Bool(true) obligation";
const BOUNDED_EMPTY_NOOP_REFINEMENT_FORWARD: &str =
    "canonical Bool(true) plus no-op provenance refines the empty trust_cg output slice";
const BOUNDED_EMPTY_NOOP_REFINEMENT_REVERSE: &str =
    "empty trust_cg output slice preserves only the canonical Bool(true) no-op obligation";
const MISSING_REFINEMENT_METADATA_BLOCKER: &str = "missing-refinement-metadata";
const UNCONSUMED_REFINEMENT_METADATA_BLOCKER: &str = "refinement-metadata-not-consumed";
const MISSING_BINARY_PROOF_OBLIGATION_BLOCKER: &str = "missing-binary-proof-obligation";
const BINARY_PROOF_OBLIGATION_PENDING_REFINEMENT_BLOCKER: &str =
    "binary-proof-obligation-pending-refinement-metadata";
const BINARY_PROOF_OBLIGATION_PENDING_REFINEMENT_CONSUMPTION_BLOCKER: &str =
    "binary-proof-obligation-pending-refinement-consumption";

/// trust-cg-specific validation gate for binary-derived conversions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryTrustCgValidationStatus {
    /// LIR was emitted and structurally checked, but target validation rejects
    /// it until refinement metadata and checked proof evidence are attached.
    InspectableRejected,
    /// No trust_cg LIR was emitted because a target-specific proof blocker must
    /// be consumed before the adapter may translate the source.
    Rejected,
}

/// Explicit blocker keeping binary-derived trust_cg conversion below proof grade.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgValidationBlocker {
    /// Stable machine-readable blocker code.
    pub code: String,
    /// Human-readable explanation.
    pub detail: String,
}

/// Symbolic formula carried through conversion metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgSymbolicFormula {
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

/// Structured symbolic formula evidence preserved during trust_cg conversion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgSymbolicFormulaEvidence {
    /// Function containing the symbolic formula metadata.
    pub function: String,
    /// Source TrustIr block id.
    pub block: usize,
    /// Statement or instruction index within the source block.
    pub statement_index: usize,
    /// Operand role or canonical TrustIr source.
    pub operand: String,
    /// Result type metadata attached to a canonical TrustIr dialect op.
    pub result_tys: Option<String>,
    /// Parsed trust-types formula when JSON metadata was valid.
    pub formula: Option<Formula>,
    /// Round-trippable trust-types Formula JSON payload.
    pub formula_json: Option<String>,
    /// SMT-LIB2 formula text carried by canonical TrustIr metadata.
    pub smtlib: Option<String>,
    /// Sort text carried by canonical TrustIr metadata.
    pub sort: Option<String>,
    /// Sort inferred from the parsed formula.
    pub inferred_sort: Option<String>,
    /// Bit-vector width when the inferred sort is fixed-width.
    pub bit_width: Option<u32>,
    /// Formula schema metadata carried by canonical TrustIr.
    pub schema: Option<String>,
    /// Debug AST rendering carried by canonical TrustIr.
    pub debug: Option<String>,
    /// Formula JSON parse error, if metadata could not be consumed.
    pub parse_error: Option<String>,
    /// Schema/sort/SMT consistency errors surfaced as blockers.
    pub schema_errors: Vec<String>,
    /// Bridge-owned target-semantic consumption decision for this formula.
    pub target_semantic_consumption: BinaryTrustCgTargetSemanticConsumptionEvidence,
    /// False until trust_cg target semantic validation consumes this formula.
    pub target_semantics_consumed: bool,
}

/// Checked certificate metadata preserved for later trust_cg target proof consumers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgCheckedCertificateEvidence {
    /// Stable dispatch/canonical identifier carrying the certificate metadata.
    pub dispatch_id: String,
    /// Function associated with the certified VC, when available.
    pub function: Option<String>,
    /// Source of the certificate metadata inside the conversion pipeline.
    pub source: String,
    /// Source TrustIr block id, when the record comes from canonical TrustIr.
    pub block: Option<usize>,
    /// Statement index, when the record comes from canonical TrustIr.
    pub statement_index: Option<usize>,
    /// Binary-origin metadata bound to the certified VC, when available.
    pub origin: Option<BinaryOrigin>,
    /// Canonical trust-types certificate status parsed from conversion metadata.
    pub certificate: ProofCertificateStatus,
    /// Checker identity from [`ProofCertificateStatus::Checked`].
    pub checker: String,
    /// Checked proof certificate format.
    pub format: String,
    /// Checked certificate digest, when supplied by the certificate pipeline.
    pub sha256: Option<String>,
    /// Replay/readback status for the certified dispatch.
    pub replay: ReplayStatus,
    /// Certificate audit/readback diagnostics preserved verbatim for consumers.
    pub audit_readback_metadata: Vec<String>,
    /// Bridge-owned target-semantic consumption decision for this certificate.
    pub target_semantic_consumption: BinaryTrustCgTargetSemanticConsumptionEvidence,
    /// False until trust_cg target semantic validation consumes this evidence.
    pub target_semantics_consumed: bool,
}

/// Proof replay metadata preserved for later trust_cg target proof consumers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgProofReplayEvidence {
    /// Stable dispatch/canonical identifier carrying the replay metadata.
    pub dispatch_id: String,
    /// Function associated with the replay record, when available.
    pub function: Option<String>,
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
    pub target_semantic_consumption: BinaryTrustCgTargetSemanticConsumptionEvidence,
    /// False until trust_cg target semantic validation consumes this replay record.
    pub target_semantics_consumed: bool,
}

/// Unsupported-ledger elimination evidence preserved for trust_cg proof consumers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgUnsupportedLedgerEvidence {
    /// Stable source of the unsupported-ledger evidence.
    pub source: String,
    /// Function associated with the ledger evidence, when available.
    pub function: Option<String>,
    /// Source TrustIr block id, when the record comes from canonical TrustIr.
    pub block: Option<usize>,
    /// Statement index, when the record comes from canonical TrustIr.
    pub statement_index: Option<usize>,
    /// Number of unsupported ledger records visible to this target consumer.
    pub unsupported_records: usize,
    /// Binary verification unsupported counter visible to this target consumer.
    pub verification_unsupported: usize,
    /// True only when the visible unsupported ledger/counter evidence is empty.
    pub unsupported_ledger_eliminated: bool,
    /// Bridge-owned target-semantic consumption decision for this ledger evidence.
    pub target_semantic_consumption: BinaryTrustCgTargetSemanticConsumptionEvidence,
    /// False until trust_cg target semantic validation consumes this evidence.
    pub target_semantics_consumed: bool,
}

/// Bridge-owned trust_cg target-semantic consumption decision for one proof input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgTargetSemanticConsumptionEvidence {
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

/// Bridge-owned bidirectional refinement consumption state for one metadata row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgRefinementConsumptionEvidence {
    /// Component that must consume the structured refinement relation.
    pub consumer: String,
    /// True only when a bridge-owned bidirectional refinement consumer accepted this row.
    pub bidirectional_refinement_consumed: bool,
    /// Stable machine-readable rejection or acceptance code.
    pub code: String,
    /// Human-readable explanation of the decision.
    pub detail: String,
}

/// Structured trust_cg refinement metadata for a narrow source/target slice.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgRefinementMetadataEvidence {
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
    /// Source obligation formula, serialized as SMT-LIB2 when available.
    pub source_formula: Option<String>,
    /// Target semantic domain.
    pub target: String,
    /// Stable target output identifier.
    pub target_output: String,
    /// Target trust_cg function, when LIR was emitted.
    pub target_function: Option<String>,
    /// Target trust_cg block, when LIR was emitted.
    pub target_block: Option<usize>,
    /// Target trust_cg SSA result, when the slice binds to one result.
    pub target_result: Option<u32>,
    /// Forward source-to-target relation summary.
    pub forward_relation: String,
    /// Reverse target-to-source relation summary.
    pub reverse_relation: String,
    /// Bridge-owned bidirectional refinement consumption decision.
    pub bidirectional_consumption: BinaryTrustCgRefinementConsumptionEvidence,
    /// False until the bidirectional refinement consumer accepts this row.
    pub bidirectional_refinement_consumed: bool,
}

/// Binary provenance carried into the trust_cg target proof-consumer gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgProvenanceEvidence {
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
    pub target_semantic_consumption: BinaryTrustCgTargetSemanticConsumptionEvidence,
    /// False until trust_cg target semantic validation consumes this provenance.
    pub target_semantics_consumed: bool,
}

/// trust_cg target proof-consumer acceptance state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryTrustCgProofConsumerStatus {
    /// trust-cg target semantics consumed every carried proof input.
    Accepted,
    /// At least one proof input is absent or has not been consumed by target semantics.
    Rejected,
}

/// One proof-consumer input and its target-acceptance decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgProofConsumerRecord {
    /// Input class, such as `target_semantics`, `symbolic_formula`,
    /// `checked_certificate`, or `proof_replay`.
    pub kind: String,
    /// Stable record identifier for diagnostics and JSON callers.
    pub identifier: String,
    /// True only after trust-cg target semantics consumed this input.
    pub accepted: bool,
    /// Human-readable explanation for the decision.
    pub detail: String,
}

/// One canonical proof input bound to the target output artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgProofBindingInput {
    /// Input class, such as `canonical_trust_ir_formula`, `binary_provenance`,
    /// `checked_certificate`, or `proof_replay`.
    pub kind: String,
    /// Stable input identifier for diagnostics and JSON callers.
    pub identifier: String,
    /// Canonical source namespace for the proof input.
    pub canonical_source: String,
    /// Target artifact this input is meant to justify.
    pub target_output: String,
    /// True only after trust-cg target semantics consumed this input/output edge.
    pub consumed_by_target_semantics: bool,
    /// Human-readable binding detail.
    pub detail: String,
}

/// Bridge-owned proof binding artifact tying target output to proof inputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgTargetProofBinding {
    /// Target semantic domain for this binding.
    pub target: String,
    /// Stable description of the target output artifact.
    pub target_output: String,
    /// Aggregate binding state.
    pub status: BinaryTrustCgProofConsumerStatus,
    /// True only after trust-cg target semantics have consumed all binding edges.
    pub target_semantics_consumed: bool,
    /// Canonical TrustIr/provenance/certificate/replay inputs bound to the output.
    pub inputs: Vec<BinaryTrustCgProofBindingInput>,
    /// Machine-readable blockers explaining a rejected binding.
    pub blockers: Vec<BinaryTrustCgValidationBlocker>,
}

/// Explicit trust_cg proof-consumer evidence derived from carried conversion metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryTrustCgProofConsumerEvidence {
    /// Target semantic domain for this proof-consumer gate.
    pub target: String,
    /// Aggregate proof-consumer status.
    pub status: BinaryTrustCgProofConsumerStatus,
    /// True only after trust-cg target semantics have consumed the carried inputs.
    pub target_semantics_consumed: bool,
    /// Per-input acceptance/rejection records.
    pub records: Vec<BinaryTrustCgProofConsumerRecord>,
    /// Bridge-owned binding artifact for the target output and proof inputs.
    pub binding: BinaryTrustCgTargetProofBinding,
    /// Structured refinement metadata visible to proof-grade residual gates.
    pub refinement_metadata_evidence: Vec<BinaryTrustCgRefinementMetadataEvidence>,
    /// Machine-readable blockers explaining a rejected aggregate status.
    pub blockers: Vec<BinaryTrustCgValidationBlocker>,
    /// Residual proof-grade blockers not cleared by target semantic consumption.
    pub proof_grade_blockers: Vec<BinaryTrustCgValidationBlocker>,
}

impl BinaryTrustCgProofConsumerEvidence {
    /// True when trust_cg target proof consumption is still rejected.
    #[must_use]
    pub fn is_rejected(&self) -> bool {
        self.status == BinaryTrustCgProofConsumerStatus::Rejected
    }
}

/// Result of lowering binary-derived TrustIr into trust_cg LIR.
#[derive(Debug, Clone)]
pub struct BinaryTrustCgConversion {
    /// Structurally validated trust_cg LIR produced from the lifted TrustIr.
    pub lir: LirFunction,
    /// Structural LIR validation status for the emitted inspectable artifact.
    pub structural_validation: ReconstructionValidationStatus,
    /// trust_cg target validation gate status.
    pub trust_cg_validation: BinaryTrustCgValidationStatus,
    /// Trust level for this conversion artifact. Binary-derived conversion is
    /// rejected as proof evidence until refinement/proof metadata is available.
    pub trust_level: TrustLevel,
    /// Target-specific blockers that must be resolved before proof-grade use.
    pub validation_blockers: Vec<BinaryTrustCgValidationBlocker>,
    /// Symbolic formulas preserved from lifted TrustIr operands where present.
    pub symbolic_formulas: Vec<BinaryTrustCgSymbolicFormula>,
    /// Structured formula metadata/evidence preserved for proof consumers.
    pub symbolic_formula_evidence: Vec<BinaryTrustCgSymbolicFormulaEvidence>,
    /// Checked certificate audit/readback metadata preserved for proof consumers.
    pub checked_certificate_evidence: Vec<BinaryTrustCgCheckedCertificateEvidence>,
    /// Proof replay metadata preserved for proof consumers.
    pub proof_replay_evidence: Vec<BinaryTrustCgProofReplayEvidence>,
    /// Binary provenance preserved for target proof consumers.
    pub provenance_evidence: Vec<BinaryTrustCgProvenanceEvidence>,
    /// Unsupported-ledger elimination evidence preserved for target proof consumers.
    pub unsupported_ledger_evidence: Vec<BinaryTrustCgUnsupportedLedgerEvidence>,
    /// Structured refinement metadata for narrow bridge-owned slices.
    pub refinement_metadata_evidence: Vec<BinaryTrustCgRefinementMetadataEvidence>,
    /// Semantic candidate TrustIr slice used as the lowering source.
    ///
    /// For this contract the reconstructed candidate is exactly the lifted
    /// binary TrustIr clone. No Rust reconstruction validation is implied.
    pub reconstructed_trust_ir: VerifiableFunction,
    /// Stable provenance and trust diagnostics for downstream reports.
    pub diagnostics: Vec<String>,
}

impl BinaryTrustCgConversion {
    /// Explicit proof-consumer evidence for symbolic formulas, checked
    /// certificates, and replay metadata carried by this conversion.
    #[must_use]
    pub fn target_proof_consumer_evidence(&self) -> BinaryTrustCgProofConsumerEvidence {
        let lir = std::slice::from_ref(&self.lir);
        let scalar_consumption = trust_cg_scalar_bool_true_target_consumption(
            &self.reconstructed_trust_ir,
            &self.lir,
            &self.symbolic_formula_evidence,
            &self.checked_certificate_evidence,
            &self.proof_replay_evidence,
            &self.provenance_evidence,
            &self.unsupported_ledger_evidence,
        );
        let refinement_metadata_evidence = if scalar_consumption.accepted {
            consume_binary_scalar_refinement_metadata(
                &self.reconstructed_trust_ir,
                &self.lir,
                &self.symbolic_formula_evidence,
                &self.refinement_metadata_evidence,
            )
        } else {
            pending_refinement_metadata_evidence(
                &self.refinement_metadata_evidence,
                "trust-cg target proof consumer has not accepted this slice, so bidirectional refinement metadata remains unconsumed",
            )
        };
        let target_output = trust_cg_target_output_identifier(lir);
        build_trust_cg_proof_consumer_evidence(TrustCgProofConsumerEvidenceInput {
            target_output: &target_output,
            symbolic_formula_evidence: &self.symbolic_formula_evidence,
            checked_certificate_evidence: &self.checked_certificate_evidence,
            proof_replay_evidence: &self.proof_replay_evidence,
            provenance_evidence: &self.provenance_evidence,
            unsupported_ledger_evidence: &self.unsupported_ledger_evidence,
            refinement_metadata_evidence: &refinement_metadata_evidence,
            scalar_consumption: &scalar_consumption,
        })
    }
}

/// Result of converting canonical TrustIr text/module into trust_cg LIR.
#[derive(Debug, Clone)]
pub struct CanonicalTrustCgConversion {
    /// Structurally validated trust_cg LIR functions, when conversion was safe to
    /// run. Empty when canonical symbolic formula metadata blocks lowering.
    pub lir: Vec<LirFunction>,
    /// Structural LIR validation status for emitted functions.
    pub structural_validation: ReconstructionValidationStatus,
    /// trust_cg target validation gate status.
    pub trust_cg_validation: BinaryTrustCgValidationStatus,
    /// Trust level for this conversion artifact.
    pub trust_level: TrustLevel,
    /// Target-specific blockers that must be resolved before proof-grade use.
    pub validation_blockers: Vec<BinaryTrustCgValidationBlocker>,
    /// Parsed symbolic formulas preserved from canonical TrustIr metadata.
    pub symbolic_formulas: Vec<BinaryTrustCgSymbolicFormula>,
    /// Structured formula metadata/evidence preserved for proof consumers.
    pub symbolic_formula_evidence: Vec<BinaryTrustCgSymbolicFormulaEvidence>,
    /// Binary provenance preserved for target proof consumers.
    pub provenance_evidence: Vec<BinaryTrustCgProvenanceEvidence>,
    /// Checked certificate metadata preserved for proof consumers.
    pub checked_certificate_evidence: Vec<BinaryTrustCgCheckedCertificateEvidence>,
    /// Proof replay metadata preserved for proof consumers.
    pub proof_replay_evidence: Vec<BinaryTrustCgProofReplayEvidence>,
    /// Unsupported-ledger elimination evidence preserved for proof consumers.
    pub unsupported_ledger_evidence: Vec<BinaryTrustCgUnsupportedLedgerEvidence>,
    /// Structured refinement metadata for narrow bridge-owned slices.
    pub refinement_metadata_evidence: Vec<BinaryTrustCgRefinementMetadataEvidence>,
    /// Stable provenance and trust diagnostics for downstream reports.
    pub diagnostics: Vec<String>,
}

impl CanonicalTrustCgConversion {
    /// Explicit proof-consumer evidence for symbolic formulas carried by this
    /// canonical TrustIr conversion attempt.
    #[must_use]
    pub fn target_proof_consumer_evidence(&self) -> BinaryTrustCgProofConsumerEvidence {
        let scalar_consumption = TrustCgScalarTargetConsumption::not_applicable();
        let target_output = trust_cg_target_output_identifier(&self.lir);
        let bounded_consumption = trust_cg_bounded_empty_target_consumption(
            &target_output,
            &self.symbolic_formula_evidence,
            &self.checked_certificate_evidence,
            &self.proof_replay_evidence,
            &self.provenance_evidence,
            &self.unsupported_ledger_evidence,
        );
        let refinement_metadata_evidence = if bounded_consumption.accepted {
            consume_canonical_bounded_empty_refinement_metadata(
                &target_output,
                &self.symbolic_formula_evidence,
                &self.provenance_evidence,
                &self.refinement_metadata_evidence,
            )
        } else {
            pending_refinement_metadata_evidence(
                &self.refinement_metadata_evidence,
                "trust-cg target proof consumer has not accepted this slice, so bidirectional refinement metadata remains unconsumed",
            )
        };
        build_trust_cg_proof_consumer_evidence(TrustCgProofConsumerEvidenceInput {
            target_output: &target_output,
            symbolic_formula_evidence: &self.symbolic_formula_evidence,
            checked_certificate_evidence: &self.checked_certificate_evidence,
            proof_replay_evidence: &self.proof_replay_evidence,
            provenance_evidence: &self.provenance_evidence,
            unsupported_ledger_evidence: &self.unsupported_ledger_evidence,
            refinement_metadata_evidence: &refinement_metadata_evidence,
            scalar_consumption: &scalar_consumption,
        })
    }
}

/// Errors from the safe binary-derived TrustIr to trust_cg LIR conversion contract.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum BinaryTrustCgConversionError {
    /// A decompiled function did not carry lifted binary TrustIr to lower.
    #[error("decompiled function `{function}` has no lifted binary TrustIr")]
    MissingLiftedTrustIr { function: String },

    /// Existing MIR-to-LIR lowering failed.
    #[error("failed to lower binary-derived TrustIr to trust_cg LIR: {0}")]
    Lowering(#[from] BridgeError),

    /// Existing LIR structural validation rejected the lowered function.
    #[error("lowered trust_cg LIR failed structural validation: {0:?}")]
    Validation(Vec<ValidationError>),

    /// Canonical TrustIr text could not be parsed.
    #[error("failed to parse canonical TrustIr for trust_cg conversion: {0}")]
    CanonicalTrustIrParse(String),

    /// Canonical TrustIr adapter lowering failed.
    #[error("failed to lower canonical TrustIr to trust_cg LIR: {0}")]
    CanonicalTrustIrLowering(String),
}

/// Lower a decompiled binary function's lifted TrustIr into validated trust_cg LIR.
pub fn lower_binary_decompiled_function_to_lir(
    function: &DecompiledFunction,
) -> Result<BinaryTrustCgConversion, BinaryTrustCgConversionError> {
    let lifted = function.lifted.as_ref().ok_or_else(|| {
        BinaryTrustCgConversionError::MissingLiftedTrustIr { function: function.name.clone() }
    })?;
    let mut conversion = lower_binary_trust_ir_to_lir(lifted)?;
    attach_checked_certificate_evidence(&mut conversion, function);
    Ok(conversion)
}

/// Lower binary-derived TrustIr into validated trust_cg LIR.
///
/// The returned `reconstructed_trust_ir` is a clone of the lifted TrustIr semantic
/// candidate. This function does not certify the binary, the lift, or any Rust
/// reconstruction as proof-grade.
pub fn lower_binary_trust_ir_to_lir(
    lifted_trust_ir: &VerifiableFunction,
) -> Result<BinaryTrustCgConversion, BinaryTrustCgConversionError> {
    let lir = lower_to_lir(lifted_trust_ir)?;
    validate_lir(&lir).map_err(BinaryTrustCgConversionError::Validation)?;
    let symbolic_formula_evidence = collect_symbolic_formula_evidence(lifted_trust_ir);
    let symbolic_formulas = symbolic_formulas_from_evidence(&symbolic_formula_evidence);
    let provenance_evidence = collect_function_provenance_evidence(lifted_trust_ir);
    let unsupported_ledger_evidence = Vec::new();
    let refinement_metadata_evidence = collect_binary_scalar_refinement_metadata(
        lifted_trust_ir,
        &lir,
        &symbolic_formula_evidence,
    );
    let mut validation_blockers = binary_conversion_validation_blockers();
    replace_binary_provenance_blockers(&mut validation_blockers, &provenance_evidence);
    replace_unsupported_ledger_blockers(&mut validation_blockers, &unsupported_ledger_evidence);
    replace_residual_proof_grade_blockers(
        &mut validation_blockers,
        binary_proof_obligation_residual_state(false, &refinement_metadata_evidence),
    );
    let mut diagnostics = binary_conversion_diagnostics();
    set_binary_proof_obligation_state_diagnostic(
        &mut diagnostics,
        binary_proof_obligation_residual_state(false, &refinement_metadata_evidence),
    );
    diagnostics.extend(symbolic_formula_evidence.iter().map(symbolic_formula_evidence_detail));
    diagnostics.extend(provenance_evidence.iter().map(binary_provenance_evidence_detail));
    diagnostics
        .extend(refinement_metadata_evidence.iter().map(refinement_metadata_evidence_detail));

    Ok(BinaryTrustCgConversion {
        lir,
        structural_validation: ReconstructionValidationStatus::Validated,
        trust_cg_validation: BinaryTrustCgValidationStatus::InspectableRejected,
        trust_level: TrustLevel::Rejected,
        validation_blockers,
        symbolic_formulas,
        symbolic_formula_evidence,
        checked_certificate_evidence: Vec::new(),
        proof_replay_evidence: Vec::new(),
        provenance_evidence,
        unsupported_ledger_evidence,
        refinement_metadata_evidence,
        reconstructed_trust_ir: lifted_trust_ir.clone(),
        diagnostics,
    })
}

/// Lower canonical TrustIr text into trust_cg LIR, surfacing symbolic formula
/// dialect metadata as proof blockers before the adapter can translate it.
pub fn lower_canonical_trust_ir_to_lir(
    canonical_trust_ir: &str,
) -> Result<CanonicalTrustCgConversion, BinaryTrustCgConversionError> {
    let mut symbolic_formula_evidence =
        collect_canonical_symbolic_formula_evidence(canonical_trust_ir);
    let mut provenance_evidence = collect_canonical_binary_provenance_evidence(canonical_trust_ir);
    let mut checked_certificate_evidence =
        collect_canonical_checked_certificate_evidence(canonical_trust_ir);
    let mut proof_replay_evidence = collect_canonical_proof_replay_evidence(canonical_trust_ir);
    let mut unsupported_ledger_evidence =
        collect_canonical_unsupported_ledger_evidence(canonical_trust_ir);
    apply_bounded_empty_target_consumption_to_canonical_evidence(
        canonical_trust_ir,
        &mut symbolic_formula_evidence,
        &mut checked_certificate_evidence,
        &mut proof_replay_evidence,
        &mut provenance_evidence,
        &mut unsupported_ledger_evidence,
    );
    let mut refinement_metadata_evidence = collect_canonical_bounded_empty_refinement_metadata(
        canonical_trust_ir,
        &symbolic_formula_evidence,
        &provenance_evidence,
    );
    if trust_cg_bounded_empty_target_consumption(
        "trust_cg-lir:blocked:no-emitted-functions",
        &symbolic_formula_evidence,
        &checked_certificate_evidence,
        &proof_replay_evidence,
        &provenance_evidence,
        &unsupported_ledger_evidence,
    )
    .accepted
    {
        refinement_metadata_evidence = consume_canonical_bounded_empty_refinement_metadata(
            "trust_cg-lir:blocked:no-emitted-functions",
            &symbolic_formula_evidence,
            &provenance_evidence,
            &refinement_metadata_evidence,
        );
    }
    if !symbolic_formula_evidence.is_empty()
        || !provenance_evidence.is_empty()
        || !checked_certificate_evidence.is_empty()
        || !proof_replay_evidence.is_empty()
        || !unsupported_ledger_evidence.is_empty()
    {
        let mut validation_blockers = binary_conversion_validation_blockers();
        if !symbolic_formula_evidence.is_empty() {
            validation_blockers.extend(symbolic_formula_blockers(&symbolic_formula_evidence));
            validation_blockers
                .extend(symbolic_formula_schema_blockers(&symbolic_formula_evidence));
        }
        replace_binary_provenance_blockers(&mut validation_blockers, &provenance_evidence);
        replace_proof_metadata_blockers(
            &mut validation_blockers,
            &checked_certificate_evidence,
            &proof_replay_evidence,
        );
        replace_unsupported_ledger_blockers(&mut validation_blockers, &unsupported_ledger_evidence);
        let binary_obligation_state = canonical_binary_proof_obligation_residual_state(
            &symbolic_formula_evidence,
            &checked_certificate_evidence,
            &proof_replay_evidence,
            &provenance_evidence,
            &unsupported_ledger_evidence,
            &refinement_metadata_evidence,
        );
        replace_residual_proof_grade_blockers(&mut validation_blockers, binary_obligation_state);
        let mut diagnostics = canonical_conversion_diagnostics(&symbolic_formula_evidence);
        diagnostics.push(binary_proof_obligation_state_diagnostic(binary_obligation_state));
        diagnostics.extend(provenance_evidence.iter().map(binary_provenance_evidence_detail));
        diagnostics
            .extend(checked_certificate_evidence.iter().map(checked_certificate_evidence_detail));
        diagnostics.extend(proof_replay_evidence.iter().map(proof_replay_evidence_detail));
        diagnostics
            .extend(unsupported_ledger_evidence.iter().map(unsupported_ledger_evidence_detail));
        diagnostics
            .extend(refinement_metadata_evidence.iter().map(refinement_metadata_evidence_detail));
        return Ok(CanonicalTrustCgConversion {
            lir: Vec::new(),
            structural_validation: ReconstructionValidationStatus::Failed,
            trust_cg_validation: BinaryTrustCgValidationStatus::Rejected,
            trust_level: TrustLevel::Rejected,
            validation_blockers,
            symbolic_formulas: symbolic_formulas_from_evidence(&symbolic_formula_evidence),
            symbolic_formula_evidence,
            provenance_evidence,
            checked_certificate_evidence,
            proof_replay_evidence,
            unsupported_ledger_evidence,
            refinement_metadata_evidence,
            diagnostics,
        });
    }

    Err(BinaryTrustCgConversionError::CanonicalTrustIrLowering(
        "canonical TrustIr text contained no trust_symbolic.formula metadata for this preservation path"
            .to_string(),
    ))
}

fn binary_conversion_validation_blockers() -> Vec<BinaryTrustCgValidationBlocker> {
    let mut blockers = vec![
        validation_blocker(
            "missing-target-semantic-validation",
            "trust-cg LIR has not been validated against trust-cg target semantics",
        ),
        validation_blocker(
            "missing-checked-proof-certificate",
            "trust-cg conversion has no checked proof certificate for the emitted artifact",
        ),
        validation_blocker(
            "missing-unsupported-ledger-evidence",
            "trust-cg conversion has no unsupported-ledger elimination evidence for the emitted artifact",
        ),
    ];
    blockers.extend(residual_proof_grade_blockers_for(
        BinaryProofObligationResidualState::MissingMetadata,
    ));
    blockers
}

fn ensure_residual_proof_grade_blockers_for(
    blockers: &mut Vec<BinaryTrustCgValidationBlocker>,
    binary_obligation_state: BinaryProofObligationResidualState,
) {
    for blocker in residual_proof_grade_blockers_for(binary_obligation_state) {
        if !blockers.iter().any(|existing| existing.code == blocker.code) {
            blockers.push(blocker);
        }
    }
}

fn replace_residual_proof_grade_blockers(
    blockers: &mut Vec<BinaryTrustCgValidationBlocker>,
    binary_obligation_state: BinaryProofObligationResidualState,
) {
    blockers.retain(|blocker| {
        !matches!(
            blocker.code.as_str(),
            MISSING_REFINEMENT_METADATA_BLOCKER
                | UNCONSUMED_REFINEMENT_METADATA_BLOCKER
                | MISSING_BINARY_PROOF_OBLIGATION_BLOCKER
                | BINARY_PROOF_OBLIGATION_PENDING_REFINEMENT_BLOCKER
                | BINARY_PROOF_OBLIGATION_PENDING_REFINEMENT_CONSUMPTION_BLOCKER
        )
    });
    ensure_residual_proof_grade_blockers_for(blockers, binary_obligation_state);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BinaryProofObligationResidualState {
    MissingMetadata,
    RefinementMetadataPresentPendingProof,
    TargetConsumedPendingRefinement,
    TargetConsumedPendingRefinementConsumption,
    Discharged,
}

fn residual_proof_grade_blockers_for(
    binary_obligation_state: BinaryProofObligationResidualState,
) -> Vec<BinaryTrustCgValidationBlocker> {
    if binary_obligation_state == BinaryProofObligationResidualState::Discharged {
        return Vec::new();
    }

    vec![
        refinement_metadata_residual_blocker(binary_obligation_state),
        binary_proof_obligation_residual_blocker(binary_obligation_state),
    ]
}

fn refinement_metadata_residual_blocker(
    state: BinaryProofObligationResidualState,
) -> BinaryTrustCgValidationBlocker {
    match state {
        BinaryProofObligationResidualState::MissingMetadata
        | BinaryProofObligationResidualState::TargetConsumedPendingRefinement => {
            validation_blocker(
                MISSING_REFINEMENT_METADATA_BLOCKER,
                "trust-cg LIR has no bidirectional refinement metadata tying it to lifted TrustIr",
            )
        }
        BinaryProofObligationResidualState::RefinementMetadataPresentPendingProof
        | BinaryProofObligationResidualState::TargetConsumedPendingRefinementConsumption => {
            validation_blocker(
                UNCONSUMED_REFINEMENT_METADATA_BLOCKER,
                "trust-cg LIR has structured refinement metadata for a narrow source/target slice, but no bridge-owned bidirectional refinement consumer has consumed the forward and reverse relation",
            )
        }
        BinaryProofObligationResidualState::Discharged => {
            unreachable!("discharged residual states have no refinement metadata blocker")
        }
    }
}

fn binary_proof_obligation_residual_blocker(
    state: BinaryProofObligationResidualState,
) -> BinaryTrustCgValidationBlocker {
    match state {
        BinaryProofObligationResidualState::MissingMetadata
        | BinaryProofObligationResidualState::RefinementMetadataPresentPendingProof => {
            validation_blocker(
                MISSING_BINARY_PROOF_OBLIGATION_BLOCKER,
                "trust-cg conversion has no bridge-consumed metadata for machine-code proof obligations",
            )
        }
        BinaryProofObligationResidualState::TargetConsumedPendingRefinement => validation_blocker(
            BINARY_PROOF_OBLIGATION_PENDING_REFINEMENT_BLOCKER,
            "trust-cg target proof consumer consumed the carried binary proof inputs for this narrow slice, but proof-grade remains closed until bidirectional refinement metadata binds that consumed obligation to the lifted TrustIr",
        ),
        BinaryProofObligationResidualState::TargetConsumedPendingRefinementConsumption => {
            validation_blocker(
                BINARY_PROOF_OBLIGATION_PENDING_REFINEMENT_CONSUMPTION_BLOCKER,
                "trust-cg target proof consumer consumed the carried binary proof inputs for this narrow slice, and structured refinement metadata is present, but proof-grade remains closed until the bidirectional refinement consumer consumes that metadata",
            )
        }
        BinaryProofObligationResidualState::Discharged => {
            unreachable!("discharged residual states have no binary proof-obligation blocker")
        }
    }
}

fn binary_proof_obligation_state_diagnostic(state: BinaryProofObligationResidualState) -> String {
    let label = match state {
        BinaryProofObligationResidualState::MissingMetadata => "missing-metadata",
        BinaryProofObligationResidualState::RefinementMetadataPresentPendingProof => {
            "refinement-metadata-present-pending-proof"
        }
        BinaryProofObligationResidualState::TargetConsumedPendingRefinement => {
            "target-consumed-pending-refinement"
        }
        BinaryProofObligationResidualState::TargetConsumedPendingRefinementConsumption => {
            "target-consumed-pending-refinement-consumption"
        }
        BinaryProofObligationResidualState::Discharged => "discharged",
    };
    format!("binary_proof_obligation.state={label}")
}

fn binary_proof_obligation_residual_state(
    target_semantics_consumed: bool,
    refinement_metadata_evidence: &[BinaryTrustCgRefinementMetadataEvidence],
) -> BinaryProofObligationResidualState {
    if refinement_metadata_evidence.is_empty() {
        return if target_semantics_consumed {
            BinaryProofObligationResidualState::TargetConsumedPendingRefinement
        } else {
            BinaryProofObligationResidualState::MissingMetadata
        };
    }

    let refinement_consumed =
        refinement_metadata_evidence.iter().all(|entry| entry.bidirectional_refinement_consumed);
    match (target_semantics_consumed, refinement_consumed) {
        (true, true) => BinaryProofObligationResidualState::Discharged,
        (true, false) => {
            BinaryProofObligationResidualState::TargetConsumedPendingRefinementConsumption
        }
        (false, _) => BinaryProofObligationResidualState::RefinementMetadataPresentPendingProof,
    }
}

fn set_binary_proof_obligation_state_diagnostic(
    diagnostics: &mut Vec<String>,
    state: BinaryProofObligationResidualState,
) {
    diagnostics.retain(|diagnostic| !diagnostic.starts_with("binary_proof_obligation.state="));
    diagnostics.push(binary_proof_obligation_state_diagnostic(state));
}

fn validation_blocker(code: &str, detail: &str) -> BinaryTrustCgValidationBlocker {
    BinaryTrustCgValidationBlocker { code: code.to_string(), detail: detail.to_string() }
}

fn append_unique_validation_blockers(
    target: &mut Vec<BinaryTrustCgValidationBlocker>,
    source: &[BinaryTrustCgValidationBlocker],
) {
    for blocker in source {
        if !target.iter().any(|existing| existing.code == blocker.code) {
            target.push(blocker.clone());
        }
    }
}

fn binary_conversion_diagnostics() -> Vec<String> {
    vec![
        DIAGNOSTIC_TARGET.to_string(),
        DIAGNOSTIC_SOURCE.to_string(),
        DIAGNOSTIC_NOT_PROOF_GRADE.to_string(),
        "trust_cg-validation=inspectable-rejected".to_string(),
        binary_proof_obligation_state_diagnostic(
            BinaryProofObligationResidualState::MissingMetadata,
        ),
    ]
}

fn canonical_symbolic_formula_diagnostics(
    evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
) -> Vec<String> {
    let mut diagnostics = vec![
        DIAGNOSTIC_TARGET.to_string(),
        DIAGNOSTIC_CANONICAL_SOURCE.to_string(),
        DIAGNOSTIC_NOT_PROOF_GRADE.to_string(),
        "trust_cg-validation=rejected".to_string(),
        "canonical TrustIr symbolic formula dialect metadata preserved as trust_cg blocker/evidence; not converted to Undef".to_string(),
    ];
    diagnostics.extend(evidence.iter().map(symbolic_formula_evidence_detail));
    diagnostics
}

fn canonical_conversion_diagnostics(
    evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
) -> Vec<String> {
    if evidence.is_empty() {
        vec![
            DIAGNOSTIC_TARGET.to_string(),
            DIAGNOSTIC_CANONICAL_SOURCE.to_string(),
            DIAGNOSTIC_NOT_PROOF_GRADE.to_string(),
            "trust_cg-validation=rejected".to_string(),
            "canonical TrustIr binary provenance metadata preserved as trust_cg blocker/evidence; target semantics have not consumed it".to_string(),
        ]
    } else {
        canonical_symbolic_formula_diagnostics(evidence)
    }
}

fn symbolic_formulas_from_evidence(
    evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
) -> Vec<BinaryTrustCgSymbolicFormula> {
    evidence
        .iter()
        .filter_map(|entry| {
            entry.formula.as_ref().map(|formula| {
                let formula_schema = symbolic_formula_schema(formula);
                BinaryTrustCgSymbolicFormula {
                    function: entry.function.clone(),
                    block: entry.block,
                    statement_index: entry.statement_index,
                    operand: entry.operand.clone(),
                    formula: formula.clone(),
                    sort: entry.inferred_sort.clone().unwrap_or(formula_schema.sort),
                    bit_width: entry.bit_width.or(formula_schema.bit_width),
                }
            })
        })
        .collect()
}

fn symbolic_formula_blockers(
    evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
) -> Vec<BinaryTrustCgValidationBlocker> {
    if evidence.is_empty() {
        return Vec::new();
    }

    vec![validation_blocker(
        "preserved-symbolic-formula",
        &format!(
            "{} symbolic formula(s) preserved in canonical TrustIr metadata; trust_cg proof must consume formula JSON/SMT-LIB/sort metadata instead of replacing the value with Undef. {}",
            evidence.len(),
            symbolic_formula_summary(evidence)
        ),
    )]
}

fn symbolic_formula_schema_blockers(
    evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
) -> Vec<BinaryTrustCgValidationBlocker> {
    let errors = evidence
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

fn symbolic_formula_summary(evidence: &[BinaryTrustCgSymbolicFormulaEvidence]) -> String {
    evidence
        .first()
        .map(symbolic_formula_evidence_detail)
        .unwrap_or_else(|| "no symbolic formula metadata".to_string())
}

fn attach_checked_certificate_evidence(
    conversion: &mut BinaryTrustCgConversion,
    function: &DecompiledFunction,
) {
    let previous_provenance_len = conversion.provenance_evidence.len();
    merge_provenance_evidence(
        &mut conversion.provenance_evidence,
        collect_decompiled_provenance_evidence(function),
    );
    replace_binary_provenance_blockers(
        &mut conversion.validation_blockers,
        &conversion.provenance_evidence,
    );
    conversion.diagnostics.extend(
        conversion.provenance_evidence[previous_provenance_len..]
            .iter()
            .map(binary_provenance_evidence_detail),
    );

    let unsupported_ledger_evidence = collect_decompiled_unsupported_ledger_evidence(function);
    replace_unsupported_ledger_blockers(
        &mut conversion.validation_blockers,
        &unsupported_ledger_evidence,
    );
    conversion
        .diagnostics
        .extend(unsupported_ledger_evidence.iter().map(unsupported_ledger_evidence_detail));
    conversion.unsupported_ledger_evidence = unsupported_ledger_evidence;

    let evidence = collect_checked_certificate_evidence(function);
    let replay_evidence = collect_proof_replay_evidence(function);
    if evidence.is_empty() && replay_evidence.is_empty() {
        return;
    }

    replace_proof_metadata_blockers(
        &mut conversion.validation_blockers,
        &evidence,
        &replay_evidence,
    );
    if !evidence.is_empty() {
        conversion.validation_blockers.extend(checked_certificate_target_consumer_blockers(
            &evidence,
            &conversion.symbolic_formula_evidence,
        ));
    }
    conversion.diagnostics.extend(evidence.iter().map(checked_certificate_evidence_detail));
    conversion.diagnostics.extend(replay_evidence.iter().map(proof_replay_evidence_detail));
    conversion.checked_certificate_evidence = evidence;
    conversion.proof_replay_evidence = replay_evidence;
    apply_scalar_target_consumption_to_binary_evidence(conversion);
}

fn apply_scalar_target_consumption_to_binary_evidence(conversion: &mut BinaryTrustCgConversion) {
    let consumption = trust_cg_scalar_bool_true_target_consumption(
        &conversion.reconstructed_trust_ir,
        &conversion.lir,
        &conversion.symbolic_formula_evidence,
        &conversion.checked_certificate_evidence,
        &conversion.proof_replay_evidence,
        &conversion.provenance_evidence,
        &conversion.unsupported_ledger_evidence,
    );
    if !consumption.accepted {
        return;
    }

    for entry in &mut conversion.symbolic_formula_evidence {
        entry.target_semantic_consumption =
            trust_cg_scalar_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
    for entry in &mut conversion.provenance_evidence {
        entry.target_semantic_consumption =
            trust_cg_scalar_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
    for entry in &mut conversion.checked_certificate_evidence {
        entry.target_semantic_consumption =
            trust_cg_scalar_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
    for entry in &mut conversion.proof_replay_evidence {
        entry.target_semantic_consumption =
            trust_cg_scalar_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
    for entry in &mut conversion.unsupported_ledger_evidence {
        entry.target_semantic_consumption =
            trust_cg_scalar_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
    conversion.refinement_metadata_evidence = consume_binary_scalar_refinement_metadata(
        &conversion.reconstructed_trust_ir,
        &conversion.lir,
        &conversion.symbolic_formula_evidence,
        &conversion.refinement_metadata_evidence,
    );

    conversion.validation_blockers.retain(|blocker| {
        !matches!(
            blocker.code.as_str(),
            "missing-target-semantic-validation"
                | "binary-provenance-not-consumed-by-target-semantics"
                | "checked-certificate-not-consumed-by-target-semantics"
                | "proof-replay-not-consumed-by-target-semantics"
                | "unsupported-ledger-not-consumed-by-target-semantics"
        )
    });
    replace_residual_proof_grade_blockers(
        &mut conversion.validation_blockers,
        binary_proof_obligation_residual_state(true, &conversion.refinement_metadata_evidence),
    );
    set_binary_proof_obligation_state_diagnostic(
        &mut conversion.diagnostics,
        binary_proof_obligation_residual_state(true, &conversion.refinement_metadata_evidence),
    );
    conversion
        .diagnostics
        .extend(conversion.symbolic_formula_evidence.iter().map(symbolic_formula_evidence_detail));
    conversion
        .diagnostics
        .extend(conversion.provenance_evidence.iter().map(binary_provenance_evidence_detail));
    conversion.diagnostics.extend(
        conversion.checked_certificate_evidence.iter().map(checked_certificate_evidence_detail),
    );
    conversion
        .diagnostics
        .extend(conversion.proof_replay_evidence.iter().map(proof_replay_evidence_detail));
    conversion.diagnostics.extend(
        conversion.unsupported_ledger_evidence.iter().map(unsupported_ledger_evidence_detail),
    );
    replace_refinement_metadata_diagnostics(
        &mut conversion.diagnostics,
        &conversion.refinement_metadata_evidence,
    );
}

fn collect_checked_certificate_evidence(
    function: &DecompiledFunction,
) -> Vec<BinaryTrustCgCheckedCertificateEvidence> {
    function
        .verification
        .solver_dispatch
        .iter()
        .filter_map(checked_certificate_evidence_from_dispatch)
        .collect()
}

fn checked_certificate_evidence_from_dispatch(
    dispatch: &SolverDispatchRecord,
) -> Option<BinaryTrustCgCheckedCertificateEvidence> {
    match &dispatch.certificate {
        ProofCertificateStatus::Checked { checker, format, sha256 } => {
            Some(BinaryTrustCgCheckedCertificateEvidence {
                dispatch_id: dispatch.id.clone(),
                function: dispatch.function.clone(),
                source: format!("solver_dispatch:{}", dispatch.id),
                block: None,
                statement_index: None,
                origin: dispatch.origin.clone(),
                certificate: dispatch.certificate.clone(),
                checker: checker.clone(),
                format: format.clone(),
                sha256: sha256.clone(),
                replay: dispatch.replay,
                audit_readback_metadata: checked_certificate_audit_readback_metadata(
                    &dispatch.diagnostics,
                ),
                target_semantic_consumption: trust_cg_target_semantic_consumption_evidence(None),
                target_semantics_consumed: false,
            })
        }
        _ => None,
    }
}

fn collect_proof_replay_evidence(
    function: &DecompiledFunction,
) -> Vec<BinaryTrustCgProofReplayEvidence> {
    function
        .verification
        .solver_dispatch
        .iter()
        .map(|dispatch| BinaryTrustCgProofReplayEvidence {
            dispatch_id: dispatch.id.clone(),
            function: dispatch.function.clone(),
            source: format!("solver_dispatch:{}", dispatch.id),
            block: None,
            statement_index: None,
            replay: dispatch.replay,
            artifact_sha256: dispatch_replay_artifact_sha256(dispatch),
            exact_replay_checked: dispatch.replay == ReplayStatus::Replayed,
            target_semantic_consumption: trust_cg_target_semantic_consumption_evidence(None),
            target_semantics_consumed: false,
        })
        .collect()
}

fn dispatch_replay_artifact_sha256(dispatch: &SolverDispatchRecord) -> Option<String> {
    let identity = dispatch.replay_artifact_digest_identity()?;
    if !identity.digest_identity_allows_replay() {
        return None;
    }
    identity.root_artifact_digest.as_ref().map(|digest| digest.value.clone())
}

fn collect_decompiled_unsupported_ledger_evidence(
    function: &DecompiledFunction,
) -> Vec<BinaryTrustCgUnsupportedLedgerEvidence> {
    let unsupported_records =
        function.unsupported.records.len() + function.verification.unsupported_ledger.records.len();
    let verification_unsupported = function.verification.unsupported;
    vec![BinaryTrustCgUnsupportedLedgerEvidence {
        source: "decompiled.unsupported_ledger".to_string(),
        function: Some(function.name.clone()),
        block: None,
        statement_index: None,
        unsupported_records,
        verification_unsupported,
        unsupported_ledger_eliminated: unsupported_records == 0 && verification_unsupported == 0,
        target_semantic_consumption: trust_cg_target_semantic_consumption_evidence(None),
        target_semantics_consumed: false,
    }]
}

fn checked_certificate_audit_readback_metadata(diagnostics: &[String]) -> Vec<String> {
    diagnostics
        .iter()
        .filter(|diagnostic| {
            diagnostic.starts_with(CHECKED_CERTIFICATE_AUDIT_METADATA_PREFIX)
                || diagnostic.starts_with(CHECKED_CERTIFICATE_READBACK_METADATA_PREFIX)
        })
        .cloned()
        .collect()
}

fn checked_certificate_target_consumer_blockers(
    certificate_evidence: &[BinaryTrustCgCheckedCertificateEvidence],
    symbolic_formula_evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
) -> Vec<BinaryTrustCgValidationBlocker> {
    let symbolic_schema_records =
        symbolic_formula_evidence.iter().filter(|entry| entry.schema.is_some()).count();
    vec![validation_blocker(
        "checked-certificate-not-consumed-by-target-semantics",
        &format!(
            "{} checked certificate audit/readback metadata record(s) preserved with {} symbolic formula schema metadata record(s); trust_cg target semantic validation has not consumed them together, so proof-grade remains closed.",
            certificate_evidence.len(),
            symbolic_schema_records
        ),
    )]
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BoundedTrustCgTargetConsumption {
    accepted: bool,
    detail: String,
    blockers: Vec<BinaryTrustCgValidationBlocker>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TrustCgScalarTargetConsumption {
    accepted: bool,
    detail: String,
    blockers: Vec<BinaryTrustCgValidationBlocker>,
}

impl TrustCgScalarTargetConsumption {
    fn not_applicable() -> Self {
        Self { accepted: false, detail: String::new(), blockers: Vec::new() }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ScalarBoolTrueSourceShape {
    function: String,
    block: usize,
    statement_index: usize,
}

fn apply_bounded_empty_target_consumption_to_canonical_evidence(
    canonical_trust_ir: &str,
    symbolic_formula_evidence: &mut [BinaryTrustCgSymbolicFormulaEvidence],
    checked_certificate_evidence: &mut [BinaryTrustCgCheckedCertificateEvidence],
    proof_replay_evidence: &mut [BinaryTrustCgProofReplayEvidence],
    provenance_evidence: &mut [BinaryTrustCgProvenanceEvidence],
    unsupported_ledger_evidence: &mut [BinaryTrustCgUnsupportedLedgerEvidence],
) {
    if !canonical_trust_ir_is_bounded_empty_metadata_slice(canonical_trust_ir) {
        return;
    }

    let consumption = trust_cg_bounded_empty_target_consumption_candidate(
        "trust_cg-lir:blocked:no-emitted-functions",
        symbolic_formula_evidence,
        checked_certificate_evidence,
        proof_replay_evidence,
        provenance_evidence,
        unsupported_ledger_evidence,
    );
    if !consumption.accepted {
        return;
    }

    for entry in symbolic_formula_evidence {
        entry.target_semantic_consumption =
            trust_cg_bounded_empty_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
    for entry in provenance_evidence {
        entry.target_semantic_consumption =
            trust_cg_bounded_empty_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
    for entry in checked_certificate_evidence {
        entry.target_semantic_consumption =
            trust_cg_bounded_empty_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
    for entry in proof_replay_evidence {
        entry.target_semantic_consumption =
            trust_cg_bounded_empty_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
    for entry in unsupported_ledger_evidence {
        entry.target_semantic_consumption =
            trust_cg_bounded_empty_target_semantic_consumption_evidence(&consumption.detail);
        entry.target_semantics_consumed = true;
    }
}

fn canonical_binary_proof_obligation_residual_state(
    symbolic_formula_evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
    checked_certificate_evidence: &[BinaryTrustCgCheckedCertificateEvidence],
    proof_replay_evidence: &[BinaryTrustCgProofReplayEvidence],
    provenance_evidence: &[BinaryTrustCgProvenanceEvidence],
    unsupported_ledger_evidence: &[BinaryTrustCgUnsupportedLedgerEvidence],
    refinement_metadata_evidence: &[BinaryTrustCgRefinementMetadataEvidence],
) -> BinaryProofObligationResidualState {
    let target_semantics_consumed = trust_cg_bounded_empty_target_consumption(
        "trust_cg-lir:blocked:no-emitted-functions",
        symbolic_formula_evidence,
        checked_certificate_evidence,
        proof_replay_evidence,
        provenance_evidence,
        unsupported_ledger_evidence,
    )
    .accepted;
    binary_proof_obligation_residual_state(target_semantics_consumed, refinement_metadata_evidence)
}

fn trust_cg_bounded_empty_target_consumption(
    target_output: &str,
    symbolic_formula_evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
    checked_certificate_evidence: &[BinaryTrustCgCheckedCertificateEvidence],
    proof_replay_evidence: &[BinaryTrustCgProofReplayEvidence],
    provenance_evidence: &[BinaryTrustCgProvenanceEvidence],
    unsupported_ledger_evidence: &[BinaryTrustCgUnsupportedLedgerEvidence],
) -> BoundedTrustCgTargetConsumption {
    trust_cg_bounded_empty_target_consumption_impl(
        target_output,
        symbolic_formula_evidence,
        checked_certificate_evidence,
        proof_replay_evidence,
        provenance_evidence,
        unsupported_ledger_evidence,
        true,
    )
}

fn trust_cg_bounded_empty_target_consumption_candidate(
    target_output: &str,
    symbolic_formula_evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
    checked_certificate_evidence: &[BinaryTrustCgCheckedCertificateEvidence],
    proof_replay_evidence: &[BinaryTrustCgProofReplayEvidence],
    provenance_evidence: &[BinaryTrustCgProvenanceEvidence],
    unsupported_ledger_evidence: &[BinaryTrustCgUnsupportedLedgerEvidence],
) -> BoundedTrustCgTargetConsumption {
    trust_cg_bounded_empty_target_consumption_impl(
        target_output,
        symbolic_formula_evidence,
        checked_certificate_evidence,
        proof_replay_evidence,
        provenance_evidence,
        unsupported_ledger_evidence,
        false,
    )
}

fn trust_cg_bounded_empty_target_consumption_impl(
    target_output: &str,
    symbolic_formula_evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
    checked_certificate_evidence: &[BinaryTrustCgCheckedCertificateEvidence],
    proof_replay_evidence: &[BinaryTrustCgProofReplayEvidence],
    provenance_evidence: &[BinaryTrustCgProvenanceEvidence],
    unsupported_ledger_evidence: &[BinaryTrustCgUnsupportedLedgerEvidence],
    require_bridge_consumed_marker: bool,
) -> BoundedTrustCgTargetConsumption {
    let mut blockers = Vec::new();

    if target_output != "trust_cg-lir:blocked:no-emitted-functions" {
        blockers.push(validation_blocker(
            "bounded-empty-slice-target-not-empty",
            "bounded trust_cg target proof-consumer slice only applies when no trust_cg LIR functions were emitted",
        ));
    }

    if symbolic_formula_evidence.is_empty() {
        blockers.push(validation_blocker(
            "bounded-empty-slice-missing-trivial-formula",
            "bounded trust_cg target proof-consumer slice requires canonical trust_symbolic.formula metadata for the trivial Bool(true) obligation",
        ));
    } else if !symbolic_formula_evidence.iter().all(is_bounded_empty_trivial_formula_evidence) {
        blockers.push(validation_blocker(
            "bounded-empty-slice-nontrivial-formula",
            "bounded trust_cg target proof-consumer slice rejects nontrivial, malformed, or non-canonical formula metadata",
        ));
    }

    if provenance_evidence.is_empty() {
        blockers.push(validation_blocker(
            "bounded-empty-slice-missing-noop-provenance",
            "bounded trust_cg target proof-consumer slice requires canonical binary provenance for a recognized no-op instruction",
        ));
    } else if !provenance_evidence.iter().all(is_bounded_empty_noop_provenance) {
        blockers.push(validation_blocker(
            "bounded-empty-slice-non-noop-provenance",
            "bounded trust_cg target proof-consumer slice rejects provenance that is non-canonical, lacks exact bytes, or does not identify a recognized no-op instruction",
        ));
    }

    if checked_certificate_evidence.is_empty() {
        blockers.push(validation_blocker(
            "bounded-empty-slice-missing-checked-certificate",
            "bounded trust_cg target proof-consumer slice requires canonical checked-certificate metadata with checker, format, and sha256 identity",
        ));
    } else if !checked_certificate_evidence.iter().all(is_bounded_empty_checked_certificate) {
        blockers.push(validation_blocker(
            "bounded-empty-slice-incomplete-checked-certificate",
            "bounded trust_cg target proof-consumer slice rejects checked-certificate metadata that is non-canonical or lacks checked identity",
        ));
    }

    if proof_replay_evidence.is_empty() {
        blockers.push(validation_blocker(
            "bounded-empty-slice-missing-exact-replay",
            "bounded trust_cg target proof-consumer slice requires canonical proof replay metadata with ReplayStatus::Replayed and exact replay checked",
        ));
    } else if !proof_replay_evidence.iter().all(is_bounded_empty_exact_replay) {
        blockers.push(validation_blocker(
            "bounded-empty-slice-incomplete-exact-replay",
            "bounded trust_cg target proof-consumer slice rejects replay metadata that is non-canonical, not replayed, missing an artifact digest, or not exact",
        ));
    }

    if unsupported_ledger_evidence.is_empty() {
        blockers.push(validation_blocker(
            "bounded-empty-slice-missing-unsupported-ledger",
            "bounded trust_cg target proof-consumer slice requires canonical unsupported-ledger elimination evidence",
        ));
    } else if !unsupported_ledger_evidence.iter().all(is_unsupported_ledger_eliminated_evidence) {
        blockers.push(validation_blocker(
            "bounded-empty-slice-unsupported-ledger-not-eliminated",
            "bounded trust_cg target proof-consumer slice rejects non-empty unsupported ledgers or unsupported verification counters",
        ));
    }

    if require_bridge_consumed_marker
        && blockers.is_empty()
        && !bounded_empty_evidence_is_bridge_consumed(
            symbolic_formula_evidence,
            checked_certificate_evidence,
            proof_replay_evidence,
            provenance_evidence,
            unsupported_ledger_evidence,
        )
    {
        blockers.push(validation_blocker(
            "bounded-empty-slice-not-bridge-consumed",
            "bounded trust-cg target proof-consumer slice requires target-specific bridge-owned trust-cg consumption stamped after canonical empty/no-op source-shape validation",
        ));
    }

    let accepted = blockers.is_empty();
    BoundedTrustCgTargetConsumption {
        accepted,
        detail: if accepted {
            "trust-cg target proof consumer accepted the bounded empty/no-op slice: no LIR functions emitted, every formula is Bool(true), binary provenance identifies only recognized no-op bytes, checked certificate plus exact replay metadata are canonical, and unsupported-ledger evidence is empty"
                .to_string()
        } else {
            "bounded empty/no-op trust_cg target proof-consumer slice did not apply".to_string()
        },
        blockers,
    }
}

fn canonical_trust_ir_is_bounded_empty_metadata_slice(canonical_trust_ir: &str) -> bool {
    let mut saw_block = false;
    let mut saw_statement = false;

    for line in canonical_trust_ir.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty()
            || trimmed.starts_with(';')
            || trimmed.starts_with("module ")
            || canonical_function_name(trimmed).is_some()
            || trimmed == "}"
        {
            continue;
        }
        if canonical_block_id(trimmed).is_some() {
            saw_block = true;
            continue;
        }
        if !saw_block {
            return false;
        }

        saw_statement = true;
        if trimmed.starts_with("ret ") {
            continue;
        }
        if trimmed.contains(&symbolic_formula_dialect_op_text())
            || trimmed
                .contains(&format!("dialect_op {BINARY_PROVENANCE_DIALECT}.{BINARY_PROVENANCE_OP}"))
            || trimmed
                .contains(&format!("dialect_op {PROOF_METADATA_DIALECT}.{CHECKED_CERTIFICATE_OP}"))
            || trimmed.contains(&format!("dialect_op {PROOF_METADATA_DIALECT}.{PROOF_REPLAY_OP}"))
            || trimmed
                .contains(&format!("dialect_op {PROOF_METADATA_DIALECT}.{UNSUPPORTED_LEDGER_OP}"))
        {
            continue;
        }

        return false;
    }

    saw_block && saw_statement
}

fn bounded_empty_evidence_is_bridge_consumed(
    symbolic_formula_evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
    checked_certificate_evidence: &[BinaryTrustCgCheckedCertificateEvidence],
    proof_replay_evidence: &[BinaryTrustCgProofReplayEvidence],
    provenance_evidence: &[BinaryTrustCgProvenanceEvidence],
    unsupported_ledger_evidence: &[BinaryTrustCgUnsupportedLedgerEvidence],
) -> bool {
    symbolic_formula_evidence.iter().all(|entry| {
        trust_cg_bounded_empty_target_semantic_consumption_is_bridge_owned(
            &entry.target_semantic_consumption,
        )
    }) && checked_certificate_evidence.iter().all(|entry| {
        trust_cg_bounded_empty_target_semantic_consumption_is_bridge_owned(
            &entry.target_semantic_consumption,
        )
    }) && proof_replay_evidence.iter().all(|entry| {
        trust_cg_bounded_empty_target_semantic_consumption_is_bridge_owned(
            &entry.target_semantic_consumption,
        )
    }) && provenance_evidence.iter().all(|entry| {
        trust_cg_bounded_empty_target_semantic_consumption_is_bridge_owned(
            &entry.target_semantic_consumption,
        )
    }) && unsupported_ledger_evidence.iter().all(|entry| {
        trust_cg_bounded_empty_target_semantic_consumption_is_bridge_owned(
            &entry.target_semantic_consumption,
        )
    })
}

fn trust_cg_target_semantic_consumption_is_bridge_owned(
    evidence: &BinaryTrustCgTargetSemanticConsumptionEvidence,
) -> bool {
    evidence.target_semantics_consumed
        && evidence.consumer == TRUST_CG_TARGET_SEMANTIC_CONSUMER
        && matches!(
            evidence.code.as_str(),
            TRUST_CG_BOUNDED_EMPTY_TARGET_CONSUMED_CODE | TRUST_CG_SCALAR_TARGET_CONSUMED_CODE
        )
}

fn trust_cg_bounded_empty_target_semantic_consumption_is_bridge_owned(
    evidence: &BinaryTrustCgTargetSemanticConsumptionEvidence,
) -> bool {
    evidence.target_semantics_consumed
        && evidence.consumer == TRUST_CG_TARGET_SEMANTIC_CONSUMER
        && evidence.code == TRUST_CG_BOUNDED_EMPTY_TARGET_CONSUMED_CODE
}

fn is_bounded_empty_trivial_formula_evidence(entry: &BinaryTrustCgSymbolicFormulaEvidence) -> bool {
    matches!(entry.formula, Some(Formula::Bool(true)))
        && entry.result_tys.as_deref() == Some("bool")
        && entry.operand == "dialect_op"
        && entry.schema.as_deref() == Some(SYMBOLIC_FORMULA_SCHEMA)
        && entry.sort.as_deref() == Some("Bool")
        && entry.inferred_sort.as_deref() == Some("Bool")
        && entry.smtlib.as_deref() == Some("true")
        && entry.parse_error.is_none()
        && entry.schema_errors.is_empty()
}

fn is_bounded_empty_noop_provenance(entry: &BinaryTrustCgProvenanceEvidence) -> bool {
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

fn is_bounded_empty_checked_certificate(entry: &BinaryTrustCgCheckedCertificateEvidence) -> bool {
    entry.source.starts_with("canonical-trust_ir.trust_proof.checked_certificate")
        && checked_certificate_has_canonical_identity(&entry.certificate)
}

fn is_bounded_empty_exact_replay(entry: &BinaryTrustCgProofReplayEvidence) -> bool {
    entry.source.starts_with("canonical-trust_ir.trust_proof.proof_replay")
        && entry.replay == ReplayStatus::Replayed
        && entry.exact_replay_checked
        && entry.artifact_sha256.as_deref().is_some_and(|sha256| !sha256.trim().is_empty())
}

fn is_unsupported_ledger_eliminated_evidence(
    entry: &BinaryTrustCgUnsupportedLedgerEvidence,
) -> bool {
    entry.unsupported_ledger_eliminated
        && entry.unsupported_records == 0
        && entry.verification_unsupported == 0
}

fn trust_cg_scalar_bool_true_target_consumption(
    source: &VerifiableFunction,
    lir: &LirFunction,
    symbolic_formula_evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
    checked_certificate_evidence: &[BinaryTrustCgCheckedCertificateEvidence],
    proof_replay_evidence: &[BinaryTrustCgProofReplayEvidence],
    provenance_evidence: &[BinaryTrustCgProvenanceEvidence],
    unsupported_ledger_evidence: &[BinaryTrustCgUnsupportedLedgerEvidence],
) -> TrustCgScalarTargetConsumption {
    let mut blockers = Vec::new();

    let source_shape = match canonical_scalar_bool_true_source_shape(source) {
        Ok(shape) => Some(shape),
        Err(detail) => {
            blockers.push(validation_blocker(
                "non-empty-scalar-canonical-source-shape-validation-missing",
                &detail,
            ));
            None
        }
    };

    let target_result = match trust_cg_scalar_bool_true_target_result(lir) {
        Ok(result) => Some(result),
        Err(detail) => {
            blockers.push(validation_blocker("missing-scalar-formula-target-op-binding", &detail));
            None
        }
    };

    if let Some(shape) = &source_shape
        && !scalar_bool_true_formula_matches(shape, symbolic_formula_evidence)
    {
        blockers.push(validation_blocker(
            "missing-scalar-formula-target-op-binding",
            "trust-cg scalar proof consumer requires exactly one canonical Bool(true) formula metadata record matching the scalar source statement",
        ));
    }

    let matched_dispatch_ids =
        scalar_checked_replay_dispatch_ids(checked_certificate_evidence, proof_replay_evidence);
    if !checked_certificate_evidence
        .iter()
        .any(|entry| checked_certificate_has_canonical_identity(&entry.certificate))
    {
        blockers.push(validation_blocker(
            "non-empty-scalar-checked-certificate-identity-missing",
            "non-empty scalar trust_cg proof consumption requires checked certificate metadata with checker, format, and sha256 identity",
        ));
    }
    if !proof_replay_evidence.iter().any(has_replay_grade_artifact_identity) {
        blockers.push(validation_blocker(
            "non-empty-scalar-replay-artifact-identity-missing",
            "non-empty trust_cg target proof consumption requires replay metadata with ReplayStatus::Replayed, exact replay checked, and a replay-grade artifact SHA-256 identity bound to the emitted target output",
        ));
    }
    if matched_dispatch_ids.is_empty() {
        blockers.push(validation_blocker(
            "non-empty-scalar-proof-metadata-identity-mismatch",
            "non-empty scalar trust_cg proof consumption requires exactly one checked certificate and exactly one exact replay record for the same solver dispatch id",
        ));
    }
    if let Some(shape) = &source_shape
        && !scalar_noop_provenance_matches(shape, provenance_evidence, &matched_dispatch_ids)
    {
        blockers.push(validation_blocker(
            "non-empty-scalar-binary-provenance-missing",
            "non-empty scalar trust_cg proof consumption requires exact no-op binary provenance tied to the scalar source statement or matching solver dispatch",
        ));
    }
    if unsupported_ledger_evidence.is_empty() {
        blockers.push(validation_blocker(
            "non-empty-scalar-unsupported-ledger-evidence-missing",
            "non-empty scalar trust_cg proof consumption requires unsupported-ledger elimination evidence",
        ));
    } else if !unsupported_ledger_evidence.iter().all(is_unsupported_ledger_eliminated_evidence) {
        blockers.push(validation_blocker(
            "non-empty-scalar-unsupported-ledger-not-eliminated",
            "non-empty scalar trust_cg proof consumption requires empty unsupported ledgers and zero unsupported verification counters",
        ));
    }

    if !blockers.is_empty() {
        blockers.insert(
            0,
            validation_blocker(
                "non-empty-scalar-trust_cg-target-consumer-unavailable",
                "trust-cg target proof consumer observed emitted LIR output, but the bridge can only consume the narrow scalar Bool(true) -> Iconst(B1, 1) slice when source shape, target op, provenance, checked certificate identity, exact replay, and artifact identity all match",
            ),
        );
    }

    let accepted = blockers.is_empty();
    TrustCgScalarTargetConsumption {
        accepted,
        detail: if accepted {
            let shape = source_shape.expect("accepted scalar consumption has a source shape");
            let result = target_result.expect("accepted scalar consumption has a target result");
            format!(
                "trust-cg target proof consumer accepted scalar Bool(true) slice: {}::bb{}::stmt{} formula metadata is structurally bound to trust_cg Iconst(B1, 1) result v{} with checked certificate identity, exact replay, replay-grade artifact identity, no-op binary provenance, and empty unsupported-ledger evidence",
                shape.function, shape.block, shape.statement_index, result
            )
        } else {
            "non-empty scalar trust_cg target proof-consumer slice did not apply".to_string()
        },
        blockers,
    }
}

fn canonical_scalar_bool_true_source_shape(
    source: &VerifiableFunction,
) -> Result<ScalarBoolTrueSourceShape, String> {
    if source.body.arg_count != 0 {
        return Err(format!(
            "trust-cg scalar source-shape validation supports only zero-argument scalar proof obligations, got {} argument(s)",
            source.body.arg_count
        ));
    }
    if source.body.return_ty != Ty::Bool {
        return Err(format!(
            "trust-cg scalar source-shape validation supports only Bool return type, got {:?}",
            source.body.return_ty
        ));
    }
    match source.body.locals.iter().find(|local| local.index == 0) {
        Some(local) if local.ty == Ty::Bool => {}
        Some(local) => {
            return Err(format!(
                "trust-cg scalar source-shape validation requires local0 Bool return slot, got {:?}",
                local.ty
            ));
        }
        None => {
            return Err("trust-cg scalar source-shape validation requires local0 Bool return slot"
                .to_string());
        }
    }
    if !source.contracts.is_empty()
        || !source.preconditions.is_empty()
        || !source.postconditions.is_empty()
    {
        return Err(
            "trust-cg scalar source-shape validation does not consume contracts, preconditions, or postconditions"
                .to_string(),
        );
    }
    if source.body.blocks.len() != 1 {
        return Err(format!(
            "trust-cg scalar source-shape validation requires exactly one source block, got {}",
            source.body.blocks.len()
        ));
    }

    let block = &source.body.blocks[0];
    if block.id.0 != 0 {
        return Err(format!(
            "trust-cg scalar source-shape validation requires source block bb0, got bb{}",
            block.id.0
        ));
    }
    if block.stmts.len() != 1 {
        return Err(format!(
            "trust-cg scalar source-shape validation requires exactly one source statement, got {}",
            block.stmts.len()
        ));
    }
    if !matches!(block.terminator, Terminator::Return) {
        return Err("trust-cg scalar source-shape validation requires a direct Return terminator"
            .to_string());
    }

    match &block.stmts[0] {
        Statement::Assign { place, rvalue, .. }
            if place.local == 0
                && place.projections.is_empty()
                && matches!(rvalue, Rvalue::Use(Operand::Symbolic(Formula::Bool(true)))) =>
        {
            Ok(ScalarBoolTrueSourceShape {
                function: source.name.clone(),
                block: block.id.0,
                statement_index: 0,
            })
        }
        Statement::Assign { .. } => {
            Err("trust-cg scalar source-shape validation requires local0 = Symbolic(Bool(true))"
                .to_string())
        }
        other => Err(format!(
            "trust-cg scalar source-shape validation requires one Assign statement, got {other:?}"
        )),
    }
}

fn trust_cg_scalar_bool_true_target_result(lir: &LirFunction) -> Result<u32, String> {
    if !lir.signature.params.is_empty() || lir.signature.returns != vec![LirType::B1] {
        return Err(format!(
            "trust-cg scalar target matcher requires signature () -> B1, got params={:?} returns={:?}",
            lir.signature.params, lir.signature.returns
        ));
    }
    if lir.blocks.len() != 1 || lir.entry_block.0 != 0 {
        return Err(format!(
            "trust-cg scalar target matcher requires one entry block bb0, got entry=bb{} blocks={}",
            lir.entry_block.0,
            lir.blocks.len()
        ));
    }

    let block = lir
        .blocks
        .get(&lir.entry_block)
        .ok_or_else(|| "trust-cg scalar target matcher could not find entry block".to_string())?;
    if !block.params.is_empty() {
        return Err("trust-cg scalar target matcher requires no block parameters".to_string());
    }
    if block.instructions.len() != 2 {
        return Err(format!(
            "trust-cg scalar target matcher requires exactly Iconst plus Return, got {} instruction(s)",
            block.instructions.len()
        ));
    }

    let iconst = &block.instructions[0];
    let Opcode::Iconst { ty: LirType::B1, imm: 1 } = &iconst.opcode else {
        return Err(format!(
            "trust-cg scalar target matcher requires first op Iconst(B1, 1), got {:?}",
            iconst.opcode
        ));
    };
    if !iconst.args.is_empty() || iconst.results.len() != 1 {
        return Err(
            "trust-cg scalar target matcher requires Iconst with no args and exactly one result"
                .to_string(),
        );
    }

    let ret = &block.instructions[1];
    if !matches!(ret.opcode, Opcode::Return)
        || ret.args != iconst.results
        || !ret.results.is_empty()
    {
        return Err(
            "trust-cg scalar target matcher requires Return to return the Iconst result directly"
                .to_string(),
        );
    }

    Ok(iconst.results[0].0)
}

fn scalar_bool_true_formula_matches(
    shape: &ScalarBoolTrueSourceShape,
    evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
) -> bool {
    evidence.len() == 1
        && evidence.iter().all(|entry| {
            entry.function == shape.function
                && entry.block == shape.block
                && entry.statement_index == shape.statement_index
                && entry.operand == "use"
                && matches!(entry.formula, Some(Formula::Bool(true)))
                && entry.schema.as_deref() == Some(SYMBOLIC_FORMULA_SCHEMA)
                && entry.sort.as_deref() == Some("Bool")
                && entry.inferred_sort.as_deref() == Some("Bool")
                && entry.smtlib.as_deref() == Some("true")
                && entry.parse_error.is_none()
                && entry.schema_errors.is_empty()
        })
}

fn scalar_checked_replay_dispatch_ids(
    checked_certificate_evidence: &[BinaryTrustCgCheckedCertificateEvidence],
    proof_replay_evidence: &[BinaryTrustCgProofReplayEvidence],
) -> Vec<String> {
    if checked_certificate_evidence.len() != 1 || proof_replay_evidence.len() != 1 {
        return Vec::new();
    }
    checked_certificate_evidence
        .iter()
        .filter(|entry| checked_certificate_has_canonical_identity(&entry.certificate))
        .filter(|certificate| {
            proof_replay_evidence.iter().any(|replay| {
                replay.dispatch_id == certificate.dispatch_id
                    && has_replay_grade_artifact_identity(replay)
            })
        })
        .map(|entry| entry.dispatch_id.clone())
        .collect()
}

fn scalar_noop_provenance_matches(
    shape: &ScalarBoolTrueSourceShape,
    provenance_evidence: &[BinaryTrustCgProvenanceEvidence],
    dispatch_ids: &[String],
) -> bool {
    !provenance_evidence.is_empty()
        && provenance_evidence.iter().all(|entry| {
            entry.function == shape.function
                && entry
                    .origin
                    .instruction_size
                    .is_some_and(|size| usize::from(size) == entry.origin.instruction_bytes.len())
                && is_recognized_noop_instruction_bytes(&entry.origin.instruction_bytes)
        })
        && provenance_evidence.iter().any(|entry| {
            entry.function == shape.function
                && entry
                    .origin
                    .instruction_size
                    .is_some_and(|size| usize::from(size) == entry.origin.instruction_bytes.len())
                && is_recognized_noop_instruction_bytes(&entry.origin.instruction_bytes)
                && (entry.block == Some(shape.block)
                    && entry.statement_index == Some(shape.statement_index)
                    || dispatch_ids
                        .iter()
                        .any(|id| entry.source == format!("solver_dispatch:{id}")))
        })
}

fn collect_binary_scalar_refinement_metadata(
    source: &VerifiableFunction,
    lir: &LirFunction,
    symbolic_formula_evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
) -> Vec<BinaryTrustCgRefinementMetadataEvidence> {
    let Ok(shape) = canonical_scalar_bool_true_source_shape(source) else {
        return Vec::new();
    };
    let Ok(target_result) = trust_cg_scalar_bool_true_target_result(lir) else {
        return Vec::new();
    };
    if !scalar_bool_true_formula_matches(&shape, symbolic_formula_evidence) {
        return Vec::new();
    }

    vec![BinaryTrustCgRefinementMetadataEvidence {
        slice: "scalar-bool-true".to_string(),
        source: "lifted-trust_ir".to_string(),
        source_function: shape.function.clone(),
        source_block: Some(shape.block),
        source_statement_index: Some(shape.statement_index),
        source_formula: Some("true".to_string()),
        target: "trust-cg".to_string(),
        target_output: trust_cg_target_output_identifier(std::slice::from_ref(lir)),
        target_function: Some(lir.name.clone()),
        target_block: Some(lir.entry_block.0 as usize),
        target_result: Some(target_result),
        forward_relation: SCALAR_BOOL_TRUE_REFINEMENT_FORWARD.to_string(),
        reverse_relation: SCALAR_BOOL_TRUE_REFINEMENT_REVERSE.to_string(),
        bidirectional_consumption: trust_cg_refinement_metadata_pending_consumption_evidence(
            "scalar Bool(true) refinement metadata is structured but has not been consumed by bidirectional refinement validation",
        ),
        bidirectional_refinement_consumed: false,
    }]
}

fn collect_canonical_bounded_empty_refinement_metadata(
    canonical_trust_ir: &str,
    symbolic_formula_evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
    provenance_evidence: &[BinaryTrustCgProvenanceEvidence],
) -> Vec<BinaryTrustCgRefinementMetadataEvidence> {
    if !canonical_trust_ir_is_bounded_empty_metadata_slice(canonical_trust_ir) {
        return Vec::new();
    }
    if provenance_evidence.is_empty()
        || !provenance_evidence.iter().all(is_bounded_empty_noop_provenance)
    {
        return Vec::new();
    }
    let Some(formula) = symbolic_formula_evidence
        .iter()
        .find(|entry| is_bounded_empty_trivial_formula_evidence(entry))
    else {
        return Vec::new();
    };

    vec![BinaryTrustCgRefinementMetadataEvidence {
        slice: "bounded-empty-noop".to_string(),
        source: "canonical-trust_ir".to_string(),
        source_function: formula.function.clone(),
        source_block: Some(formula.block),
        source_statement_index: Some(formula.statement_index),
        source_formula: formula.smtlib.clone(),
        target: "trust-cg".to_string(),
        target_output: "trust_cg-lir:blocked:no-emitted-functions".to_string(),
        target_function: None,
        target_block: None,
        target_result: None,
        forward_relation: BOUNDED_EMPTY_NOOP_REFINEMENT_FORWARD.to_string(),
        reverse_relation: BOUNDED_EMPTY_NOOP_REFINEMENT_REVERSE.to_string(),
        bidirectional_consumption: trust_cg_refinement_metadata_pending_consumption_evidence(
            "bounded empty/no-op refinement metadata is structured but has not been consumed by bidirectional refinement validation",
        ),
        bidirectional_refinement_consumed: false,
    }]
}

fn consume_binary_scalar_refinement_metadata(
    source: &VerifiableFunction,
    lir: &LirFunction,
    symbolic_formula_evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
    refinement_metadata_evidence: &[BinaryTrustCgRefinementMetadataEvidence],
) -> Vec<BinaryTrustCgRefinementMetadataEvidence> {
    refinement_metadata_evidence
        .iter()
        .map(|entry| {
            let consumption = trust_cg_scalar_bool_true_refinement_metadata_consumption(
                source,
                lir,
                symbolic_formula_evidence,
                entry,
            );
            refinement_metadata_with_consumption(entry, consumption)
        })
        .collect()
}

fn consume_canonical_bounded_empty_refinement_metadata(
    target_output: &str,
    symbolic_formula_evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
    provenance_evidence: &[BinaryTrustCgProvenanceEvidence],
    refinement_metadata_evidence: &[BinaryTrustCgRefinementMetadataEvidence],
) -> Vec<BinaryTrustCgRefinementMetadataEvidence> {
    refinement_metadata_evidence
        .iter()
        .map(|entry| {
            let consumption = trust_cg_bounded_empty_refinement_metadata_consumption(
                target_output,
                symbolic_formula_evidence,
                provenance_evidence,
                entry,
            );
            refinement_metadata_with_consumption(entry, consumption)
        })
        .collect()
}

fn pending_refinement_metadata_evidence(
    refinement_metadata_evidence: &[BinaryTrustCgRefinementMetadataEvidence],
    detail: &str,
) -> Vec<BinaryTrustCgRefinementMetadataEvidence> {
    refinement_metadata_evidence
        .iter()
        .map(|entry| {
            refinement_metadata_with_consumption(
                entry,
                trust_cg_refinement_metadata_pending_consumption_evidence(detail),
            )
        })
        .collect()
}

fn refinement_metadata_with_consumption(
    entry: &BinaryTrustCgRefinementMetadataEvidence,
    bidirectional_consumption: BinaryTrustCgRefinementConsumptionEvidence,
) -> BinaryTrustCgRefinementMetadataEvidence {
    let bidirectional_refinement_consumed =
        bidirectional_consumption.bidirectional_refinement_consumed;
    BinaryTrustCgRefinementMetadataEvidence {
        bidirectional_consumption,
        bidirectional_refinement_consumed,
        ..entry.clone()
    }
}

fn trust_cg_scalar_bool_true_refinement_metadata_consumption(
    source: &VerifiableFunction,
    lir: &LirFunction,
    symbolic_formula_evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
    entry: &BinaryTrustCgRefinementMetadataEvidence,
) -> BinaryTrustCgRefinementConsumptionEvidence {
    let mut blockers = Vec::new();

    let source_shape = match canonical_scalar_bool_true_source_shape(source) {
        Ok(shape) => Some(shape),
        Err(detail) => {
            blockers.push(format!("source shape rejected: {detail}"));
            None
        }
    };
    let target_result = match trust_cg_scalar_bool_true_target_result(lir) {
        Ok(result) => Some(result),
        Err(detail) => {
            blockers.push(format!("target shape rejected: {detail}"));
            None
        }
    };

    expect_refinement_metadata_str_field(&mut blockers, "slice", &entry.slice, "scalar-bool-true");
    expect_refinement_metadata_str_field(&mut blockers, "source", &entry.source, "lifted-trust_ir");
    expect_refinement_metadata_str_field(&mut blockers, "target", &entry.target, "trust-cg");
    expect_refinement_metadata_str_field(
        &mut blockers,
        "target_output",
        &entry.target_output,
        &trust_cg_target_output_identifier(std::slice::from_ref(lir)),
    );
    expect_refinement_metadata_field(
        &mut blockers,
        "target_function",
        &entry.target_function,
        &Some(lir.name.clone()),
    );
    expect_refinement_metadata_field(
        &mut blockers,
        "target_block",
        &entry.target_block,
        &Some(lir.entry_block.0 as usize),
    );
    expect_refinement_metadata_str_field(
        &mut blockers,
        "forward_relation",
        &entry.forward_relation,
        SCALAR_BOOL_TRUE_REFINEMENT_FORWARD,
    );
    expect_refinement_metadata_str_field(
        &mut blockers,
        "reverse_relation",
        &entry.reverse_relation,
        SCALAR_BOOL_TRUE_REFINEMENT_REVERSE,
    );

    if let Some(shape) = &source_shape {
        expect_refinement_metadata_str_field(
            &mut blockers,
            "source_function",
            &entry.source_function,
            &shape.function,
        );
        expect_refinement_metadata_field(
            &mut blockers,
            "source_block",
            &entry.source_block,
            &Some(shape.block),
        );
        expect_refinement_metadata_field(
            &mut blockers,
            "source_statement_index",
            &entry.source_statement_index,
            &Some(shape.statement_index),
        );
        expect_refinement_metadata_field(
            &mut blockers,
            "source_formula",
            &entry.source_formula,
            &Some("true".to_string()),
        );
        if !scalar_bool_true_formula_matches(shape, symbolic_formula_evidence) {
            blockers.push(
                "symbolic formula evidence is not the canonical scalar Bool(true) source obligation"
                    .to_string(),
            );
        }
    }
    if let Some(result) = target_result {
        expect_refinement_metadata_field(
            &mut blockers,
            "target_result",
            &entry.target_result,
            &Some(result),
        );
    }

    if blockers.is_empty() {
        let shape = source_shape.as_ref().expect("accepted scalar refinement has a source shape");
        let result = target_result.expect("accepted scalar refinement has a target result");
        trust_cg_refinement_metadata_consumed_evidence(
            "scalar-bool-true-bidirectional-refinement-consumed",
            &format!(
                "bidirectional refinement consumer accepted scalar Bool(true) metadata for {}::bb{}::stmt{} and trust_cg result v{}",
                shape.function, shape.block, shape.statement_index, result
            ),
        )
    } else {
        trust_cg_refinement_metadata_rejected_consumption_evidence(&format!(
            "scalar Bool(true) bidirectional refinement metadata rejected: {}",
            blockers.join("; ")
        ))
    }
}

fn trust_cg_bounded_empty_refinement_metadata_consumption(
    target_output: &str,
    symbolic_formula_evidence: &[BinaryTrustCgSymbolicFormulaEvidence],
    provenance_evidence: &[BinaryTrustCgProvenanceEvidence],
    entry: &BinaryTrustCgRefinementMetadataEvidence,
) -> BinaryTrustCgRefinementConsumptionEvidence {
    let mut blockers = Vec::new();
    let formula_entries: Vec<_> = symbolic_formula_evidence
        .iter()
        .filter(|entry| is_bounded_empty_trivial_formula_evidence(entry))
        .collect();

    if symbolic_formula_evidence.len() != 1 || formula_entries.len() != 1 {
        blockers.push(
            "bounded empty/no-op refinement requires exactly one canonical Bool(true) formula record"
                .to_string(),
        );
    }
    if provenance_evidence.is_empty()
        || !provenance_evidence.iter().all(is_bounded_empty_noop_provenance)
    {
        blockers.push(
            "bounded empty/no-op refinement requires only recognized no-op binary provenance"
                .to_string(),
        );
    }

    expect_refinement_metadata_str_field(
        &mut blockers,
        "slice",
        &entry.slice,
        "bounded-empty-noop",
    );
    expect_refinement_metadata_str_field(
        &mut blockers,
        "source",
        &entry.source,
        "canonical-trust_ir",
    );
    expect_refinement_metadata_str_field(&mut blockers, "target", &entry.target, "trust-cg");
    expect_refinement_metadata_str_field(
        &mut blockers,
        "target_output",
        &entry.target_output,
        target_output,
    );
    expect_refinement_metadata_field(
        &mut blockers,
        "target_function",
        &entry.target_function,
        &None::<String>,
    );
    expect_refinement_metadata_field(
        &mut blockers,
        "target_block",
        &entry.target_block,
        &None::<usize>,
    );
    expect_refinement_metadata_field(
        &mut blockers,
        "target_result",
        &entry.target_result,
        &None::<u32>,
    );
    expect_refinement_metadata_str_field(
        &mut blockers,
        "forward_relation",
        &entry.forward_relation,
        BOUNDED_EMPTY_NOOP_REFINEMENT_FORWARD,
    );
    expect_refinement_metadata_str_field(
        &mut blockers,
        "reverse_relation",
        &entry.reverse_relation,
        BOUNDED_EMPTY_NOOP_REFINEMENT_REVERSE,
    );

    if let Some(formula) = formula_entries.first() {
        expect_refinement_metadata_str_field(
            &mut blockers,
            "source_function",
            &entry.source_function,
            &formula.function,
        );
        expect_refinement_metadata_field(
            &mut blockers,
            "source_block",
            &entry.source_block,
            &Some(formula.block),
        );
        expect_refinement_metadata_field(
            &mut blockers,
            "source_statement_index",
            &entry.source_statement_index,
            &Some(formula.statement_index),
        );
        expect_refinement_metadata_field(
            &mut blockers,
            "source_formula",
            &entry.source_formula,
            &formula.smtlib,
        );
    }

    if blockers.is_empty() {
        let formula =
            formula_entries.first().expect("accepted bounded refinement has a formula record");
        trust_cg_refinement_metadata_consumed_evidence(
            "bounded-empty-noop-bidirectional-refinement-consumed",
            &format!(
                "bidirectional refinement consumer accepted bounded empty/no-op metadata for {}::bb{}::stmt{} and empty trust_cg output",
                formula.function, formula.block, formula.statement_index
            ),
        )
    } else {
        trust_cg_refinement_metadata_rejected_consumption_evidence(&format!(
            "bounded empty/no-op bidirectional refinement metadata rejected: {}",
            blockers.join("; ")
        ))
    }
}

fn expect_refinement_metadata_field<T: std::fmt::Debug + PartialEq>(
    blockers: &mut Vec<String>,
    field: &str,
    actual: &T,
    expected: &T,
) {
    if actual != expected {
        blockers.push(format!("{field} mismatch: expected {expected:?}, got {actual:?}"));
    }
}

fn expect_refinement_metadata_str_field(
    blockers: &mut Vec<String>,
    field: &str,
    actual: &str,
    expected: &str,
) {
    if actual != expected {
        blockers.push(format!("{field} mismatch: expected {expected:?}, got {actual:?}"));
    }
}

struct TrustCgProofConsumerEvidenceInput<'a> {
    target_output: &'a str,
    symbolic_formula_evidence: &'a [BinaryTrustCgSymbolicFormulaEvidence],
    checked_certificate_evidence: &'a [BinaryTrustCgCheckedCertificateEvidence],
    proof_replay_evidence: &'a [BinaryTrustCgProofReplayEvidence],
    provenance_evidence: &'a [BinaryTrustCgProvenanceEvidence],
    unsupported_ledger_evidence: &'a [BinaryTrustCgUnsupportedLedgerEvidence],
    refinement_metadata_evidence: &'a [BinaryTrustCgRefinementMetadataEvidence],
    scalar_consumption: &'a TrustCgScalarTargetConsumption,
}

fn build_trust_cg_proof_consumer_evidence(
    input: TrustCgProofConsumerEvidenceInput<'_>,
) -> BinaryTrustCgProofConsumerEvidence {
    let bounded_consumption = trust_cg_bounded_empty_target_consumption(
        input.target_output,
        input.symbolic_formula_evidence,
        input.checked_certificate_evidence,
        input.proof_replay_evidence,
        input.provenance_evidence,
        input.unsupported_ledger_evidence,
    );
    let target_semantics_consumed =
        bounded_consumption.accepted || input.scalar_consumption.accepted;
    let accepted_detail = if bounded_consumption.accepted {
        bounded_consumption.detail.clone()
    } else {
        input.scalar_consumption.detail.clone()
    };
    let accepted_slice = if bounded_consumption.accepted {
        "bounded empty trust_cg target proof-consumer slice"
    } else {
        "scalar Bool(true) trust_cg target proof-consumer slice"
    };
    let mut records = vec![BinaryTrustCgProofConsumerRecord {
        kind: "target_semantics".to_string(),
        identifier: "trust_cg-lir".to_string(),
        accepted: target_semantics_consumed,
        detail: if target_semantics_consumed {
            accepted_detail
        } else {
            "trust-cg target semantics have not consumed conversion proof inputs".to_string()
        },
    }];

    records.extend(input.symbolic_formula_evidence.iter().map(|entry| {
        let entry_consumed = target_semantics_consumed
            || trust_cg_target_semantic_consumption_is_bridge_owned(
                &entry.target_semantic_consumption,
            );
        BinaryTrustCgProofConsumerRecord {
            kind: "symbolic_formula".to_string(),
            identifier: format!(
                "{}::bb{}::stmt{}::{}",
                entry.function, entry.block, entry.statement_index, entry.operand
            ),
            accepted: entry_consumed,
            detail: if entry_consumed {
                format!(
                    "formula schema={} sort={} smtlib={} was consumed by the {accepted_slice}; bridge-owned consumer {} accepted target-semantic consumption with code {}",
                    entry.schema.as_deref().unwrap_or("missing"),
                    entry.sort.as_deref().unwrap_or("missing"),
                    entry.smtlib.as_deref().unwrap_or("missing"),
                    entry.target_semantic_consumption.consumer,
                    entry.target_semantic_consumption.code
                )
            } else {
                format!(
                    "symbolic formula JSON/SMT-LIB/sort metadata is preserved, but trust-cg target semantics have not consumed it; bridge-owned consumer {} rejected target-semantic consumption: {}",
                    entry.target_semantic_consumption.consumer,
                    entry.target_semantic_consumption.detail
                )
            },
        }
    }));

    if input.provenance_evidence.is_empty() {
        records.push(BinaryTrustCgProofConsumerRecord {
            kind: "binary_provenance".to_string(),
            identifier: "missing".to_string(),
            accepted: false,
            detail:
                "no binary provenance metadata was carried into the trust_cg target proof consumer"
                    .to_string(),
        });
    } else {
        records.extend(input.provenance_evidence.iter().map(|entry| BinaryTrustCgProofConsumerRecord {
            kind: "binary_provenance".to_string(),
            identifier: binary_provenance_identifier(entry),
            accepted: target_semantics_consumed
                || trust_cg_target_semantic_consumption_is_bridge_owned(
                    &entry.target_semantic_consumption,
                ),
            detail: if target_semantics_consumed {
                format!(
                    "binary provenance source={} address=0x{:x} bytes={} was consumed by the {accepted_slice}",
                    entry.source,
                    entry.origin.instruction_address,
                    entry.origin.instruction_bytes.len()
                )
            } else {
                format!(
                    "binary provenance source={} address=0x{:x} bytes={} is preserved, but trust-cg target semantics have not consumed it; bridge-owned consumer {} rejected target-semantic consumption: {}",
                    entry.source,
                    entry.origin.instruction_address,
                    entry.origin.instruction_bytes.len(),
                    entry.target_semantic_consumption.consumer,
                    entry.target_semantic_consumption.detail
                )
            },
        }));
    }

    if input.checked_certificate_evidence.is_empty() {
        records.push(BinaryTrustCgProofConsumerRecord {
            kind: "checked_certificate".to_string(),
            identifier: "missing".to_string(),
            accepted: false,
            detail:
                "no checked certificate metadata was carried into the trust_cg target proof consumer"
                    .to_string(),
        });
    } else {
        records.extend(input.checked_certificate_evidence.iter().map(|certificate| {
            BinaryTrustCgProofConsumerRecord {
                kind: "checked_certificate".to_string(),
                identifier: checked_certificate_identifier(certificate),
                accepted: target_semantics_consumed
                    || trust_cg_target_semantic_consumption_is_bridge_owned(
                        &certificate.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "{} was consumed by the {accepted_slice}",
                        checked_certificate_label(&certificate.certificate)
                    )
                } else {
                    format!(
                        "{} is preserved, but trust-cg target semantics have not consumed it; bridge-owned consumer {} rejected target-semantic consumption: {}",
                        checked_certificate_label(&certificate.certificate),
                        certificate.target_semantic_consumption.consumer,
                        certificate.target_semantic_consumption.detail
                    )
                },
            }
        }));
    }

    if input.proof_replay_evidence.is_empty() {
        records.push(BinaryTrustCgProofConsumerRecord {
            kind: "proof_replay".to_string(),
            identifier: "missing".to_string(),
            accepted: false,
            detail: "no proof replay metadata was carried into the trust_cg target proof consumer"
                .to_string(),
        });
    } else {
        records.extend(input.proof_replay_evidence.iter().map(|replay| {
            BinaryTrustCgProofConsumerRecord {
                kind: "proof_replay".to_string(),
                identifier: proof_replay_identifier(replay),
                accepted: target_semantics_consumed
                    || trust_cg_target_semantic_consumption_is_bridge_owned(
                        &replay.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "proof replay status={:?} exact_replay_checked={} artifact_sha256={} was consumed by the {accepted_slice}",
                        replay.replay,
                        replay.exact_replay_checked,
                        replay.artifact_sha256.as_deref().unwrap_or("none")
                    )
                } else {
                    format!(
                        "proof replay status={:?} exact_replay_checked={} artifact_sha256={} is preserved, but trust-cg target semantics have not consumed it; bridge-owned consumer {} rejected target-semantic consumption: {}",
                        replay.replay,
                        replay.exact_replay_checked,
                        replay.artifact_sha256.as_deref().unwrap_or("none"),
                        replay.target_semantic_consumption.consumer,
                        replay.target_semantic_consumption.detail
                    )
                },
            }
        }));
    }

    if input.unsupported_ledger_evidence.is_empty() {
        records.push(BinaryTrustCgProofConsumerRecord {
            kind: "unsupported_ledger".to_string(),
            identifier: "missing".to_string(),
            accepted: false,
            detail: "no unsupported-ledger elimination evidence was carried into the trust_cg target proof consumer"
                .to_string(),
        });
    } else {
        records.extend(input.unsupported_ledger_evidence.iter().map(|ledger| {
            BinaryTrustCgProofConsumerRecord {
                kind: "unsupported_ledger".to_string(),
                identifier: unsupported_ledger_identifier(ledger),
                accepted: target_semantics_consumed
                    || trust_cg_target_semantic_consumption_is_bridge_owned(
                        &ledger.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "unsupported ledger eliminated={} records={} verification_unsupported={} was consumed by the {accepted_slice}",
                        ledger.unsupported_ledger_eliminated,
                        ledger.unsupported_records,
                        ledger.verification_unsupported
                    )
                } else {
                    format!(
                        "unsupported ledger eliminated={} records={} verification_unsupported={} is preserved, but trust-cg target semantics have not consumed it; bridge-owned consumer {} rejected target-semantic consumption: {}",
                        ledger.unsupported_ledger_eliminated,
                        ledger.unsupported_records,
                        ledger.verification_unsupported,
                        ledger.target_semantic_consumption.consumer,
                        ledger.target_semantic_consumption.detail
                    )
                },
            }
        }));
    }

    if input.refinement_metadata_evidence.is_empty() {
        records.push(BinaryTrustCgProofConsumerRecord {
            kind: "target_refinement".to_string(),
            identifier: "missing".to_string(),
            accepted: false,
            detail: "no bidirectional trust_cg refinement metadata was carried into the target proof consumer"
                .to_string(),
        });
    } else {
        records.extend(input.refinement_metadata_evidence.iter().map(|entry| {
            BinaryTrustCgProofConsumerRecord {
                kind: "target_refinement".to_string(),
                identifier: trust_cg_refinement_metadata_identifier(entry),
                accepted: entry.bidirectional_refinement_consumed,
                detail: if entry.bidirectional_refinement_consumed {
                    format!(
                        "bidirectional refinement metadata slice={} source={} target_output={} was consumed by {} with code {}",
                        entry.slice,
                        entry.source,
                        entry.target_output,
                        entry.bidirectional_consumption.consumer,
                        entry.bidirectional_consumption.code
                    )
                } else {
                    format!(
                        "bidirectional refinement metadata slice={} source={} target_output={} remains rejected by {}: {}",
                        entry.slice,
                        entry.source,
                        entry.target_output,
                        entry.bidirectional_consumption.consumer,
                        entry.bidirectional_consumption.detail
                    )
                },
            }
        }));
    }

    let mut blockers = trust_cg_proof_consumer_blockers(&input, &bounded_consumption);
    let target_inputs_consumed = target_semantics_consumed && blockers.is_empty();
    let binary_obligation_state = binary_proof_obligation_residual_state(
        target_inputs_consumed,
        input.refinement_metadata_evidence,
    );
    let proof_grade_blockers = residual_proof_grade_blockers_for(binary_obligation_state);
    append_unique_validation_blockers(&mut blockers, &proof_grade_blockers);

    let status = if target_inputs_consumed && proof_grade_blockers.is_empty() {
        BinaryTrustCgProofConsumerStatus::Accepted
    } else {
        BinaryTrustCgProofConsumerStatus::Rejected
    };
    let binding = build_trust_cg_target_proof_binding(
        &input,
        status,
        target_semantics_consumed,
        &blockers,
        accepted_slice,
    );

    BinaryTrustCgProofConsumerEvidence {
        target: "trust-cg".to_string(),
        status,
        target_semantics_consumed,
        records,
        binding,
        refinement_metadata_evidence: input.refinement_metadata_evidence.to_vec(),
        blockers,
        proof_grade_blockers,
    }
}

fn build_trust_cg_target_proof_binding(
    input: &TrustCgProofConsumerEvidenceInput<'_>,
    status: BinaryTrustCgProofConsumerStatus,
    target_semantics_consumed: bool,
    blockers: &[BinaryTrustCgValidationBlocker],
    accepted_slice: &str,
) -> BinaryTrustCgTargetProofBinding {
    let mut inputs = Vec::new();
    let target_output = input.target_output;
    let provenance_evidence = input.provenance_evidence;
    let checked_certificate_evidence = input.checked_certificate_evidence;
    let proof_replay_evidence = input.proof_replay_evidence;
    let unsupported_ledger_evidence = input.unsupported_ledger_evidence;
    let refinement_metadata_evidence = input.refinement_metadata_evidence;

    inputs.extend(input.symbolic_formula_evidence.iter().map(|entry| {
        let identifier = format!(
            "{}::bb{}::stmt{}::{}",
            entry.function, entry.block, entry.statement_index, entry.operand
        );
        let entry_consumed = target_semantics_consumed
            || trust_cg_target_semantic_consumption_is_bridge_owned(
                &entry.target_semantic_consumption,
            );
        BinaryTrustCgProofBindingInput {
            kind: "canonical_trust_ir_formula".to_string(),
            identifier,
            canonical_source: format!("{SYMBOLIC_FORMULA_DIALECT}.{SYMBOLIC_FORMULA_OP}"),
            target_output: target_output.to_string(),
            consumed_by_target_semantics: entry_consumed,
            detail: if entry_consumed {
                format!(
                    "formula schema={} sort={} smtlib={} is bound to {target_output} and consumed by the {accepted_slice}; bridge-owned consumer {} accepted with code {}",
                    entry.schema.as_deref().unwrap_or("missing"),
                    entry.sort.as_deref().unwrap_or("missing"),
                    entry.smtlib.as_deref().unwrap_or("missing"),
                    entry.target_semantic_consumption.consumer,
                    entry.target_semantic_consumption.code
                )
            } else {
                format!(
                    "formula schema={} sort={} smtlib={} is bound to {target_output}, but bridge-owned consumer {} has not consumed the edge: {}",
                    entry.schema.as_deref().unwrap_or("missing"),
                    entry.sort.as_deref().unwrap_or("missing"),
                    entry.smtlib.as_deref().unwrap_or("missing"),
                    entry.target_semantic_consumption.consumer,
                    entry.target_semantic_consumption.detail
                )
            },
        }
    }));

    if provenance_evidence.is_empty() {
        inputs.push(BinaryTrustCgProofBindingInput {
            kind: "binary_provenance".to_string(),
            identifier: "missing".to_string(),
            canonical_source: format!("{BINARY_PROVENANCE_DIALECT}.{BINARY_PROVENANCE_OP}"),
            target_output: target_output.to_string(),
            consumed_by_target_semantics: false,
            detail:
                "no canonical binary provenance input is available to bind to the trust_cg output"
                    .to_string(),
        });
    } else {
        inputs.extend(provenance_evidence.iter().map(|entry| BinaryTrustCgProofBindingInput {
            kind: "binary_provenance".to_string(),
            identifier: binary_provenance_identifier(entry),
            canonical_source: format!("{BINARY_PROVENANCE_DIALECT}.{BINARY_PROVENANCE_OP}"),
            target_output: target_output.to_string(),
            consumed_by_target_semantics: target_semantics_consumed
                || trust_cg_target_semantic_consumption_is_bridge_owned(
                    &entry.target_semantic_consumption,
                ),
            detail: if target_semantics_consumed {
                format!(
                    "provenance source={} address=0x{:x} bytes={} is bound to {target_output} and consumed by the {accepted_slice}",
                    entry.source,
                    entry.origin.instruction_address,
                    entry.origin.instruction_bytes.len()
                )
            } else {
                format!(
                    "provenance source={} address=0x{:x} bytes={} is bound to {target_output}, but trust-cg target semantics have not consumed it",
                    entry.source,
                    entry.origin.instruction_address,
                    entry.origin.instruction_bytes.len()
                )
            },
        }));
    }

    if checked_certificate_evidence.is_empty() {
        inputs.push(BinaryTrustCgProofBindingInput {
            kind: "checked_certificate".to_string(),
            identifier: "missing".to_string(),
            canonical_source: "checked-certificate".to_string(),
            target_output: target_output.to_string(),
            consumed_by_target_semantics: false,
            detail: "no checked certificate input is available to bind to the trust_cg output"
                .to_string(),
        });
    } else {
        inputs.extend(checked_certificate_evidence.iter().map(|certificate| {
            BinaryTrustCgProofBindingInput {
                kind: "checked_certificate".to_string(),
                identifier: checked_certificate_identifier(certificate),
                canonical_source: checked_certificate_canonical_source(certificate),
                target_output: target_output.to_string(),
                consumed_by_target_semantics: target_semantics_consumed
                    || trust_cg_target_semantic_consumption_is_bridge_owned(
                        &certificate.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "{} is bound to {target_output} and consumed by the {accepted_slice}",
                        checked_certificate_label(&certificate.certificate)
                    )
                } else {
                    format!(
                        "{} is bound to {target_output}, but trust-cg target semantics have not consumed the edge",
                        checked_certificate_label(&certificate.certificate)
                    )
                },
            }
        }));
    }

    if proof_replay_evidence.is_empty() {
        inputs.push(BinaryTrustCgProofBindingInput {
            kind: "proof_replay".to_string(),
            identifier: "missing".to_string(),
            canonical_source: "proof-replay".to_string(),
            target_output: target_output.to_string(),
            consumed_by_target_semantics: false,
            detail: "no proof replay input is available to bind to the trust_cg output".to_string(),
        });
    } else {
        inputs.extend(proof_replay_evidence.iter().map(|replay| {
            BinaryTrustCgProofBindingInput {
                kind: "proof_replay".to_string(),
                identifier: proof_replay_identifier(replay),
                canonical_source: proof_replay_canonical_source(replay),
                target_output: target_output.to_string(),
                consumed_by_target_semantics: target_semantics_consumed
                    || trust_cg_target_semantic_consumption_is_bridge_owned(
                        &replay.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "proof replay status={:?} exact_replay_checked={} artifact_sha256={} is bound to {target_output} and consumed by the {accepted_slice}",
                        replay.replay,
                        replay.exact_replay_checked,
                        replay.artifact_sha256.as_deref().unwrap_or("none")
                    )
                } else {
                    format!(
                        "proof replay status={:?} exact_replay_checked={} artifact_sha256={} is bound to {target_output}, but trust-cg target semantics have not consumed the edge",
                        replay.replay,
                        replay.exact_replay_checked,
                        replay.artifact_sha256.as_deref().unwrap_or("none")
                    )
                },
            }
        }));
    }

    if unsupported_ledger_evidence.is_empty() {
        inputs.push(BinaryTrustCgProofBindingInput {
            kind: "unsupported_ledger".to_string(),
            identifier: "missing".to_string(),
            canonical_source: format!("{PROOF_METADATA_DIALECT}.{UNSUPPORTED_LEDGER_OP}"),
            target_output: target_output.to_string(),
            consumed_by_target_semantics: false,
            detail:
                "no unsupported-ledger elimination input is available to bind to the trust_cg output"
                    .to_string(),
        });
    } else {
        inputs.extend(unsupported_ledger_evidence.iter().map(|ledger| {
            BinaryTrustCgProofBindingInput {
                kind: "unsupported_ledger".to_string(),
                identifier: unsupported_ledger_identifier(ledger),
                canonical_source: unsupported_ledger_canonical_source(ledger),
                target_output: target_output.to_string(),
                consumed_by_target_semantics: target_semantics_consumed
                    || trust_cg_target_semantic_consumption_is_bridge_owned(
                        &ledger.target_semantic_consumption,
                    ),
                detail: if target_semantics_consumed {
                    format!(
                        "unsupported ledger eliminated={} records={} verification_unsupported={} is bound to {target_output} and consumed by the {accepted_slice}",
                        ledger.unsupported_ledger_eliminated,
                        ledger.unsupported_records,
                        ledger.verification_unsupported
                    )
                } else {
                    format!(
                        "unsupported ledger eliminated={} records={} verification_unsupported={} is bound to {target_output}, but trust-cg target semantics have not consumed the edge",
                        ledger.unsupported_ledger_eliminated,
                        ledger.unsupported_records,
                        ledger.verification_unsupported
                    )
                },
            }
        }));
    }

    if refinement_metadata_evidence.is_empty() {
        inputs.push(BinaryTrustCgProofBindingInput {
            kind: "target_refinement".to_string(),
            identifier: "missing".to_string(),
            canonical_source: "bidirectional-refinement".to_string(),
            target_output: target_output.to_string(),
            consumed_by_target_semantics: false,
            detail: "no bidirectional refinement metadata input is available to bind lifted TrustIr to the trust_cg output"
                .to_string(),
        });
    } else {
        inputs.extend(refinement_metadata_evidence.iter().map(|entry| {
            BinaryTrustCgProofBindingInput {
                kind: "target_refinement".to_string(),
                identifier: trust_cg_refinement_metadata_identifier(entry),
                canonical_source: entry.source.clone(),
                target_output: target_output.to_string(),
                consumed_by_target_semantics: entry.bidirectional_refinement_consumed,
                detail: if entry.bidirectional_refinement_consumed {
                    format!(
                        "bidirectional refinement slice={} binds {}::bb{}::stmt{} to {target_output} and was consumed by {}",
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
                        entry.bidirectional_consumption.consumer
                    )
                } else {
                    format!(
                        "bidirectional refinement slice={} is bound to {target_output}, but {} has not consumed it: {}",
                        entry.slice,
                        entry.bidirectional_consumption.consumer,
                        entry.bidirectional_consumption.detail
                    )
                },
            }
        }));
    }

    BinaryTrustCgTargetProofBinding {
        target: "trust-cg".to_string(),
        target_output: target_output.to_string(),
        status,
        target_semantics_consumed,
        inputs,
        blockers: blockers.to_vec(),
    }
}

fn trust_cg_proof_consumer_blockers(
    input: &TrustCgProofConsumerEvidenceInput<'_>,
    bounded_consumption: &BoundedTrustCgTargetConsumption,
) -> Vec<BinaryTrustCgValidationBlocker> {
    let target_output = input.target_output;
    let symbolic_formula_evidence = input.symbolic_formula_evidence;
    let checked_certificate_evidence = input.checked_certificate_evidence;
    let proof_replay_evidence = input.proof_replay_evidence;
    let provenance_evidence = input.provenance_evidence;
    let unsupported_ledger_evidence = input.unsupported_ledger_evidence;
    let scalar_consumption = input.scalar_consumption;

    if bounded_consumption.accepted || scalar_consumption.accepted {
        return Vec::new();
    }

    let mut blockers = vec![validation_blocker(
        "target-semantics-not-consumed",
        "trust-cg target semantics have not consumed symbolic formula, checked-certificate, replay, or binary-provenance metadata",
    )];

    blockers.extend(
        trust_cg_bounded_empty_target_consumption(
            target_output,
            symbolic_formula_evidence,
            checked_certificate_evidence,
            proof_replay_evidence,
            provenance_evidence,
            unsupported_ledger_evidence,
        )
        .blockers,
    );

    if target_output != "trust_cg-lir:blocked:no-emitted-functions" {
        blockers.extend(scalar_consumption.blockers.clone());
    }

    if !symbolic_formula_evidence.is_empty()
        && !symbolic_formula_evidence.iter().all(|entry| {
            trust_cg_target_semantic_consumption_is_bridge_owned(&entry.target_semantic_consumption)
        })
    {
        blockers.push(validation_blocker(
            "symbolic-formula-not-consumed-by-target-semantics",
            &format!(
                "{} symbolic formula metadata record(s) are preserved but not consumed by trust-cg target semantics; bridge-owned consumer {TRUST_CG_TARGET_SEMANTIC_CONSUMER} has not consumed formula JSON/SMT-LIB/sort metadata: {}",
                symbolic_formula_evidence.len(),
                symbolic_formula_summary(symbolic_formula_evidence)
            ),
        ));
    }

    blockers.extend(binary_provenance_target_consumer_blockers(provenance_evidence));

    blockers.extend(trust_cg_checked_certificate_blockers(checked_certificate_evidence));
    blockers.extend(trust_cg_proof_replay_blockers(proof_replay_evidence));
    blockers.extend(trust_cg_unsupported_ledger_blockers(unsupported_ledger_evidence));

    blockers
}

fn has_replay_grade_artifact_identity(entry: &BinaryTrustCgProofReplayEvidence) -> bool {
    entry.replay == ReplayStatus::Replayed
        && entry.exact_replay_checked
        && entry.artifact_sha256.as_deref().is_some_and(|sha256| !sha256.trim().is_empty())
}

fn binary_provenance_target_consumer_blockers(
    provenance_evidence: &[BinaryTrustCgProvenanceEvidence],
) -> Vec<BinaryTrustCgValidationBlocker> {
    if provenance_evidence.is_empty() {
        vec![validation_blocker(
            "missing-binary-provenance",
            "trust-cg target proof consumer has no binary provenance metadata tying output back to machine instructions",
        )]
    } else if provenance_evidence.iter().all(|entry| {
        trust_cg_target_semantic_consumption_is_bridge_owned(&entry.target_semantic_consumption)
    }) {
        Vec::new()
    } else {
        vec![validation_blocker(
            "binary-provenance-not-consumed-by-target-semantics",
            &format!(
                "{} binary provenance record(s) are preserved but not consumed by trust-cg target semantics; authoritative consumed state is bridge-owned by {TRUST_CG_TARGET_SEMANTIC_CONSUMER}, and any canonical target_semantics_consumed attr is treated as an untrusted input claim",
                provenance_evidence.len()
            ),
        )]
    }
}

fn replace_binary_provenance_blockers(
    blockers: &mut Vec<BinaryTrustCgValidationBlocker>,
    provenance_evidence: &[BinaryTrustCgProvenanceEvidence],
) {
    blockers.retain(|blocker| {
        !matches!(
            blocker.code.as_str(),
            "missing-binary-provenance" | "binary-provenance-not-consumed-by-target-semantics"
        )
    });
    blockers.extend(binary_provenance_target_consumer_blockers(provenance_evidence));
}

fn replace_proof_metadata_blockers(
    blockers: &mut Vec<BinaryTrustCgValidationBlocker>,
    checked_certificate_evidence: &[BinaryTrustCgCheckedCertificateEvidence],
    proof_replay_evidence: &[BinaryTrustCgProofReplayEvidence],
) {
    blockers.retain(|blocker| {
        !matches!(
            blocker.code.as_str(),
            "missing-checked-proof-certificate"
                | "checked-certificate-not-consumed-by-target-semantics"
                | "checked-proof-certificate-incomplete"
                | "missing-proof-replay-metadata"
                | "proof-replay-not-consumed-by-target-semantics"
                | "proof-replay-incomplete"
        )
    });
    blockers.extend(trust_cg_checked_certificate_blockers(checked_certificate_evidence));
    blockers.extend(trust_cg_proof_replay_blockers(proof_replay_evidence));
}

fn replace_unsupported_ledger_blockers(
    blockers: &mut Vec<BinaryTrustCgValidationBlocker>,
    unsupported_ledger_evidence: &[BinaryTrustCgUnsupportedLedgerEvidence],
) {
    blockers.retain(|blocker| {
        !matches!(
            blocker.code.as_str(),
            "missing-unsupported-ledger-evidence"
                | "unsupported-ledger-not-eliminated"
                | "unsupported-ledger-not-consumed-by-target-semantics"
        )
    });
    blockers.extend(trust_cg_unsupported_ledger_blockers(unsupported_ledger_evidence));
}

fn trust_cg_checked_certificate_blockers(
    checked_certificate_evidence: &[BinaryTrustCgCheckedCertificateEvidence],
) -> Vec<BinaryTrustCgValidationBlocker> {
    if checked_certificate_evidence.is_empty() {
        return vec![validation_blocker(
            "missing-checked-proof-certificate",
            "trust-cg conversion has no checked proof certificate for the emitted artifact",
        )];
    }

    let mut blockers = Vec::new();
    if !checked_certificate_evidence.iter().all(|entry| {
        trust_cg_target_semantic_consumption_is_bridge_owned(&entry.target_semantic_consumption)
    }) {
        blockers.push(validation_blocker(
            "checked-certificate-not-consumed-by-target-semantics",
            &format!(
                "{} checked certificate metadata record(s) are preserved but not consumed by trust-cg target semantics; authoritative consumed state is bridge-owned by {TRUST_CG_TARGET_SEMANTIC_CONSUMER}",
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

fn trust_cg_proof_replay_blockers(
    proof_replay_evidence: &[BinaryTrustCgProofReplayEvidence],
) -> Vec<BinaryTrustCgValidationBlocker> {
    if proof_replay_evidence.is_empty() {
        return vec![validation_blocker(
            "missing-proof-replay-metadata",
            "trust-cg conversion has no replay metadata tying proof results to the emitted artifact",
        )];
    }

    let mut blockers = Vec::new();
    if !proof_replay_evidence.iter().all(|entry| {
        trust_cg_target_semantic_consumption_is_bridge_owned(&entry.target_semantic_consumption)
    }) {
        blockers.push(validation_blocker(
            "proof-replay-not-consumed-by-target-semantics",
            &format!(
                "{} proof replay metadata record(s) are preserved but not consumed by trust-cg target semantics; authoritative consumed state is bridge-owned by {TRUST_CG_TARGET_SEMANTIC_CONSUMER}",
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

fn trust_cg_unsupported_ledger_blockers(
    unsupported_ledger_evidence: &[BinaryTrustCgUnsupportedLedgerEvidence],
) -> Vec<BinaryTrustCgValidationBlocker> {
    if unsupported_ledger_evidence.is_empty() {
        return vec![validation_blocker(
            "missing-unsupported-ledger-evidence",
            "trust-cg target proof consumer has no unsupported-ledger elimination evidence",
        )];
    }

    let mut blockers = Vec::new();
    if !unsupported_ledger_evidence.iter().all(|entry| {
        trust_cg_target_semantic_consumption_is_bridge_owned(&entry.target_semantic_consumption)
    }) {
        blockers.push(validation_blocker(
            "unsupported-ledger-not-consumed-by-target-semantics",
            &format!(
                "{} unsupported-ledger evidence record(s) are preserved but not consumed by trust-cg target semantics; authoritative consumed state is bridge-owned by {TRUST_CG_TARGET_SEMANTIC_CONSUMER}",
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

fn collect_function_provenance_evidence(
    function: &VerifiableFunction,
) -> Vec<BinaryTrustCgProvenanceEvidence> {
    let mut evidence = Vec::new();
    if let Some(origin) = origin_from_span(&function.span) {
        evidence.push(BinaryTrustCgProvenanceEvidence {
            function: function.name.clone(),
            source: "lifted.function_span".to_string(),
            block: None,
            statement_index: None,
            origin,
            target_semantic_consumption: trust_cg_target_semantic_consumption_evidence(None),
            target_semantics_consumed: false,
        });
    }

    for block in &function.body.blocks {
        for (statement_index, statement) in block.stmts.iter().enumerate() {
            let Statement::Assign { span, .. } = statement else {
                continue;
            };
            if let Some(origin) = origin_from_span(span) {
                evidence.push(BinaryTrustCgProvenanceEvidence {
                    function: function.name.clone(),
                    source: format!("lifted.bb{}.stmt{}", block.id.0, statement_index),
                    block: Some(block.id.0),
                    statement_index: Some(statement_index),
                    origin,
                    target_semantic_consumption: trust_cg_target_semantic_consumption_evidence(
                        None,
                    ),
                    target_semantics_consumed: false,
                });
            }
        }
    }
    evidence
}

fn collect_decompiled_provenance_evidence(
    function: &DecompiledFunction,
) -> Vec<BinaryTrustCgProvenanceEvidence> {
    let mut evidence = Vec::new();
    if let Some(origin) = &function.origin {
        evidence.push(BinaryTrustCgProvenanceEvidence {
            function: function.name.clone(),
            source: "decompiled.function_origin".to_string(),
            block: None,
            statement_index: None,
            origin: origin.clone(),
            target_semantic_consumption: trust_cg_target_semantic_consumption_evidence(None),
            target_semantics_consumed: false,
        });
    }
    for (index, origin) in function.instruction_provenance.iter().enumerate() {
        evidence.push(BinaryTrustCgProvenanceEvidence {
            function: function.name.clone(),
            source: format!("decompiled.instruction_provenance[{index}]"),
            block: None,
            statement_index: None,
            origin: origin.clone(),
            target_semantic_consumption: trust_cg_target_semantic_consumption_evidence(None),
            target_semantics_consumed: false,
        });
    }
    for dispatch in &function.verification.solver_dispatch {
        if let Some(origin) = &dispatch.origin {
            evidence.push(BinaryTrustCgProvenanceEvidence {
                function: dispatch.function.clone().unwrap_or_else(|| function.name.clone()),
                source: format!("solver_dispatch:{}", dispatch.id),
                block: None,
                statement_index: None,
                origin: origin.clone(),
                target_semantic_consumption: trust_cg_target_semantic_consumption_evidence(None),
                target_semantics_consumed: false,
            });
        }
    }
    evidence
}

fn merge_provenance_evidence(
    target: &mut Vec<BinaryTrustCgProvenanceEvidence>,
    source: Vec<BinaryTrustCgProvenanceEvidence>,
) {
    for evidence in source {
        if !target.iter().any(|existing| {
            existing.function == evidence.function
                && existing.source == evidence.source
                && existing.block == evidence.block
                && existing.statement_index == evidence.statement_index
                && existing.origin == evidence.origin
        }) {
            target.push(evidence);
        }
    }
}

fn trust_cg_target_semantic_consumption_evidence(
    input_claimed_target_semantics_consumed: Option<bool>,
) -> BinaryTrustCgTargetSemanticConsumptionEvidence {
    let claim_detail = match input_claimed_target_semantics_consumed {
        Some(true) => {
            "canonical input claimed target_semantics_consumed=true; claim is preserved only as untrusted metadata"
        }
        Some(false) => {
            "canonical input claimed target_semantics_consumed=false; claim is preserved only as untrusted metadata"
        }
        None => "no canonical target_semantics_consumed claim was present",
    };

    BinaryTrustCgTargetSemanticConsumptionEvidence {
        consumer: TRUST_CG_TARGET_SEMANTIC_CONSUMER.to_string(),
        target_semantics_consumed: false,
        input_claimed_target_semantics_consumed,
        code: "no-trust_cg-target-semantic-consumer".to_string(),
        detail: format!(
            "{claim_detail}; no bridge-owned trust_cg target semantic consumer has consumed binary provenance, symbolic formula, checked-certificate, replay, or unsupported-ledger evidence"
        ),
    }
}

fn trust_cg_bounded_empty_target_semantic_consumption_evidence(
    detail: &str,
) -> BinaryTrustCgTargetSemanticConsumptionEvidence {
    BinaryTrustCgTargetSemanticConsumptionEvidence {
        consumer: TRUST_CG_TARGET_SEMANTIC_CONSUMER.to_string(),
        target_semantics_consumed: true,
        input_claimed_target_semantics_consumed: None,
        code: TRUST_CG_BOUNDED_EMPTY_TARGET_CONSUMED_CODE.to_string(),
        detail: detail.to_string(),
    }
}

fn trust_cg_scalar_target_semantic_consumption_evidence(
    detail: &str,
) -> BinaryTrustCgTargetSemanticConsumptionEvidence {
    BinaryTrustCgTargetSemanticConsumptionEvidence {
        consumer: TRUST_CG_TARGET_SEMANTIC_CONSUMER.to_string(),
        target_semantics_consumed: true,
        input_claimed_target_semantics_consumed: None,
        code: TRUST_CG_SCALAR_TARGET_CONSUMED_CODE.to_string(),
        detail: detail.to_string(),
    }
}

fn trust_cg_refinement_metadata_consumed_evidence(
    code: &str,
    detail: &str,
) -> BinaryTrustCgRefinementConsumptionEvidence {
    BinaryTrustCgRefinementConsumptionEvidence {
        consumer: TRUST_CG_REFINEMENT_METADATA_CONSUMER.to_string(),
        bidirectional_refinement_consumed: true,
        code: code.to_string(),
        detail: detail.to_string(),
    }
}

fn trust_cg_refinement_metadata_pending_consumption_evidence(
    detail: &str,
) -> BinaryTrustCgRefinementConsumptionEvidence {
    BinaryTrustCgRefinementConsumptionEvidence {
        consumer: TRUST_CG_REFINEMENT_METADATA_CONSUMER.to_string(),
        bidirectional_refinement_consumed: false,
        code: "bidirectional-refinement-not-consumed".to_string(),
        detail: detail.to_string(),
    }
}

fn trust_cg_refinement_metadata_rejected_consumption_evidence(
    detail: &str,
) -> BinaryTrustCgRefinementConsumptionEvidence {
    BinaryTrustCgRefinementConsumptionEvidence {
        consumer: TRUST_CG_REFINEMENT_METADATA_CONSUMER.to_string(),
        bidirectional_refinement_consumed: false,
        code: "bidirectional-refinement-metadata-rejected".to_string(),
        detail: detail.to_string(),
    }
}

fn origin_from_span(span: &trust_types::SourceSpan) -> Option<BinaryOrigin> {
    span.binary_address_value().map(|instruction_address| BinaryOrigin {
        instruction_address,
        source: Some(span.clone()),
        ..Default::default()
    })
}

fn binary_provenance_identifier(entry: &BinaryTrustCgProvenanceEvidence) -> String {
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

fn checked_certificate_identifier(entry: &BinaryTrustCgCheckedCertificateEvidence) -> String {
    if entry.block.is_none() && entry.statement_index.is_none() {
        return entry.dispatch_id.clone();
    }
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
    match (&entry.function, entry.block, entry.statement_index) {
        (Some(function), Some(block), Some(statement_index)) => {
            format!("{function}::bb{block}::stmt{statement_index}::{suffix}")
        }
        (Some(function), _, _) => format!("{function}::{}::{suffix}", entry.source),
        (None, _, _) => format!("{}::{suffix}", entry.source),
    }
}

fn checked_certificate_canonical_source(entry: &BinaryTrustCgCheckedCertificateEvidence) -> String {
    if entry.block.is_some() || entry.source.starts_with("canonical-trust_ir.") {
        format!("{PROOF_METADATA_DIALECT}.{CHECKED_CERTIFICATE_OP}")
    } else {
        "checked-certificate".to_string()
    }
}

fn proof_replay_identifier(entry: &BinaryTrustCgProofReplayEvidence) -> String {
    if entry.block.is_none() && entry.statement_index.is_none() {
        return entry.dispatch_id.clone();
    }
    let suffix = format!(
        "{:?}:{}:{}",
        entry.replay,
        if entry.exact_replay_checked { "exact" } else { "not-exact" },
        entry.artifact_sha256.as_deref().unwrap_or("missing-artifact-sha256")
    );
    match (&entry.function, entry.block, entry.statement_index) {
        (Some(function), Some(block), Some(statement_index)) => {
            format!("{function}::bb{block}::stmt{statement_index}::{suffix}")
        }
        (Some(function), _, _) => format!("{function}::{}::{suffix}", entry.source),
        (None, _, _) => format!("{}::{suffix}", entry.source),
    }
}

fn proof_replay_canonical_source(entry: &BinaryTrustCgProofReplayEvidence) -> String {
    if entry.block.is_some() || entry.source.starts_with("canonical-trust_ir.") {
        format!("{PROOF_METADATA_DIALECT}.{PROOF_REPLAY_OP}")
    } else {
        "proof-replay".to_string()
    }
}

fn unsupported_ledger_identifier(entry: &BinaryTrustCgUnsupportedLedgerEvidence) -> String {
    let suffix = format!(
        "records={}:verification_unsupported={}:eliminated={}",
        entry.unsupported_records,
        entry.verification_unsupported,
        entry.unsupported_ledger_eliminated
    );
    match (&entry.function, entry.block, entry.statement_index) {
        (Some(function), Some(block), Some(statement_index)) => {
            format!("{function}::bb{block}::stmt{statement_index}::{suffix}")
        }
        (Some(function), _, _) => format!("{function}::{}::{suffix}", entry.source),
        (None, _, _) => format!("{}::{suffix}", entry.source),
    }
}

fn unsupported_ledger_canonical_source(entry: &BinaryTrustCgUnsupportedLedgerEvidence) -> String {
    if entry.block.is_some() || entry.source.starts_with("canonical-trust_ir.") {
        format!("{PROOF_METADATA_DIALECT}.{UNSUPPORTED_LEDGER_OP}")
    } else {
        "unsupported-ledger".to_string()
    }
}

fn trust_cg_refinement_metadata_identifier(
    entry: &BinaryTrustCgRefinementMetadataEvidence,
) -> String {
    let source_block = entry
        .source_block
        .map(|block| format!("bb{block}"))
        .unwrap_or_else(|| "bbnone".to_string());
    let source_statement = entry
        .source_statement_index
        .map(|statement| format!("stmt{statement}"))
        .unwrap_or_else(|| "stmtnone".to_string());
    let target_result = entry
        .target_result
        .map(|result| format!("v{result}"))
        .unwrap_or_else(|| "target-result-none".to_string());
    format!(
        "{}::{}::{}::{}::{}::{}",
        entry.slice,
        entry.source,
        entry.source_function,
        source_block,
        source_statement,
        target_result
    )
}

fn trust_cg_target_output_identifier(lir: &[LirFunction]) -> String {
    if lir.is_empty() {
        return "trust_cg-lir:blocked:no-emitted-functions".to_string();
    }

    let mut functions = lir
        .iter()
        .map(|function| {
            format!(
                "{}#entry=bb{}#blocks={}",
                function.name,
                function.entry_block.0,
                function.blocks.len()
            )
        })
        .collect::<Vec<_>>();
    functions.sort();
    format!("trust_cg-lir:{}", functions.join("|"))
}

fn binary_provenance_evidence_detail(entry: &BinaryTrustCgProvenanceEvidence) -> String {
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
    if let Some(binary_path) = &entry.origin.binary_path {
        parts.push(format!("binary_provenance.binary_path={binary_path}"));
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

fn hex_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect::<Vec<_>>().join("")
}

fn collect_symbolic_formula_evidence(
    function: &VerifiableFunction,
) -> Vec<BinaryTrustCgSymbolicFormulaEvidence> {
    let mut evidence = Vec::new();
    for block in &function.body.blocks {
        for (statement_index, statement) in block.stmts.iter().enumerate() {
            match statement {
                Statement::Assign { rvalue, .. } => {
                    collect_rvalue_symbolics(
                        &function.name,
                        block.id.0,
                        statement_index,
                        rvalue,
                        &mut evidence,
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
                            &mut evidence,
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
    evidence
}

fn collect_rvalue_symbolics(
    function: &str,
    block: usize,
    statement_index: usize,
    rvalue: &Rvalue,
    evidence: &mut Vec<BinaryTrustCgSymbolicFormulaEvidence>,
) {
    match rvalue {
        Rvalue::Use(operand) => {
            collect_operand_symbolic(function, block, statement_index, "use", operand, evidence);
        }
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            collect_operand_symbolic(function, block, statement_index, "lhs", lhs, evidence);
            collect_operand_symbolic(function, block, statement_index, "rhs", rhs, evidence);
        }
        Rvalue::UnaryOp(_, operand) | Rvalue::Cast(operand, _) | Rvalue::Repeat(operand, _) => {
            collect_operand_symbolic(
                function,
                block,
                statement_index,
                "operand",
                operand,
                evidence,
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
                    evidence,
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
    evidence: &mut Vec<BinaryTrustCgSymbolicFormulaEvidence>,
) {
    if let Operand::Symbolic(formula) = value {
        evidence.push(formula_evidence_from_formula(
            function,
            block,
            statement_index,
            operand,
            formula,
        ));
    }
}

fn collect_canonical_symbolic_formula_evidence(
    canonical_trust_ir: &str,
) -> Vec<BinaryTrustCgSymbolicFormulaEvidence> {
    let mut evidence = Vec::new();
    let mut function = "unknown".to_string();
    let mut block = 0;
    let mut statement_index = 0;
    let mut in_block = false;
    let symbolic_op = symbolic_formula_dialect_op_text();

    for line in canonical_trust_ir.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if let Some(name) = canonical_function_name(trimmed) {
            function = name;
            in_block = false;
            continue;
        }
        if let Some(id) = canonical_block_id(trimmed) {
            block = id;
            statement_index = 0;
            in_block = true;
            continue;
        }
        if trimmed == "}" {
            in_block = false;
            continue;
        }
        if !in_block {
            continue;
        }

        let current_statement_index = statement_index;
        statement_index += 1;
        if !trimmed.contains(&symbolic_op) {
            continue;
        }
        evidence.push(canonical_symbolic_formula_evidence(
            &function,
            block,
            current_statement_index,
            trimmed,
        ));
    }
    evidence
}

fn canonical_symbolic_formula_evidence(
    function: &str,
    block: usize,
    statement_index: usize,
    line: &str,
) -> BinaryTrustCgSymbolicFormulaEvidence {
    let formula_json = canonical_attr_string(line, SYMBOLIC_FORMULA_ATTR_JSON);
    let schema = canonical_attr_string(line, SYMBOLIC_FORMULA_ATTR_SCHEMA);
    let smtlib = canonical_attr_string(line, SYMBOLIC_FORMULA_ATTR_SMTLIB);
    let sort = canonical_attr_string(line, SYMBOLIC_FORMULA_ATTR_SORT);
    let (formula, parse_error) = match formula_json.as_deref() {
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

    BinaryTrustCgSymbolicFormulaEvidence {
        function: function.to_string(),
        block,
        statement_index,
        operand: "dialect_op".to_string(),
        result_tys: Some(canonical_result_tys_label(line)),
        formula,
        formula_json,
        smtlib,
        sort,
        inferred_sort,
        bit_width,
        schema,
        debug: canonical_attr_string(line, SYMBOLIC_FORMULA_ATTR_DEBUG),
        parse_error,
        schema_errors,
        target_semantic_consumption: trust_cg_target_semantic_consumption_evidence(None),
        target_semantics_consumed: false,
    }
}

fn collect_canonical_binary_provenance_evidence(
    canonical_trust_ir: &str,
) -> Vec<BinaryTrustCgProvenanceEvidence> {
    let mut evidence = Vec::new();
    let mut function = "unknown".to_string();
    let mut block = 0;
    let mut statement_index = 0;
    let mut in_block = false;
    let provenance_op = format!("dialect_op {BINARY_PROVENANCE_DIALECT}.{BINARY_PROVENANCE_OP}");

    for line in canonical_trust_ir.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if let Some(name) = canonical_function_name(trimmed) {
            function = name;
            in_block = false;
            continue;
        }
        if let Some(id) = canonical_block_id(trimmed) {
            block = id;
            statement_index = 0;
            in_block = true;
            continue;
        }
        if trimmed == "}" {
            in_block = false;
            continue;
        }
        if !in_block {
            continue;
        }

        let current_statement_index = statement_index;
        statement_index += 1;
        if !trimmed.contains(&provenance_op) {
            continue;
        }
        if let Some(entry) =
            canonical_binary_provenance_evidence(&function, block, current_statement_index, trimmed)
        {
            evidence.push(entry);
        }
    }
    evidence
}

fn canonical_binary_provenance_evidence(
    function: &str,
    block: usize,
    statement_index: usize,
    line: &str,
) -> Option<BinaryTrustCgProvenanceEvidence> {
    let schema = canonical_attr_string(line, BINARY_PROVENANCE_ATTR_SCHEMA)?;
    if schema != BINARY_PROVENANCE_SCHEMA {
        return None;
    }
    let instruction_address = canonical_attr_u64(line, BINARY_PROVENANCE_ATTR_INSTRUCTION_ADDRESS)?;
    let instruction_bytes =
        canonical_attr_hex_bytes(line, BINARY_PROVENANCE_ATTR_INSTRUCTION_BYTES)?;
    if instruction_bytes.is_empty() {
        return None;
    }

    let instruction_size = canonical_attr_u64(line, BINARY_PROVENANCE_ATTR_INSTRUCTION_SIZE)
        .and_then(|value| u8::try_from(value).ok())
        .or_else(|| u8::try_from(instruction_bytes.len()).ok());
    let source = canonical_binary_provenance_source(canonical_attr_string(
        line,
        BINARY_PROVENANCE_ATTR_SOURCE,
    ));
    let target_semantic_consumption = trust_cg_target_semantic_consumption_evidence(
        canonical_attr_bool(line, BINARY_PROVENANCE_ATTR_TARGET_SEMANTICS_CONSUMED),
    );
    let target_semantics_consumed = target_semantic_consumption.target_semantics_consumed;

    Some(BinaryTrustCgProvenanceEvidence {
        function: function.to_string(),
        source,
        block: Some(block),
        statement_index: Some(statement_index),
        origin: BinaryOrigin {
            binary_path: canonical_attr_string(line, BINARY_PROVENANCE_ATTR_BINARY_PATH),
            function_entry: canonical_attr_u64(line, BINARY_PROVENANCE_ATTR_FUNCTION_ENTRY),
            instruction_address,
            instruction_size,
            encoding: canonical_attr_u64(line, BINARY_PROVENANCE_ATTR_ENCODING)
                .and_then(|value| u32::try_from(value).ok()),
            instruction_bytes,
            source: Some(trust_types::SourceSpan::binary_address(instruction_address)),
        },
        target_semantic_consumption,
        target_semantics_consumed,
    })
}

fn collect_canonical_checked_certificate_evidence(
    canonical_trust_ir: &str,
) -> Vec<BinaryTrustCgCheckedCertificateEvidence> {
    let mut evidence = Vec::new();
    let mut function = "unknown".to_string();
    let mut block = 0;
    let mut statement_index = 0;
    let mut in_block = false;
    let proof_op = format!("dialect_op {PROOF_METADATA_DIALECT}.{CHECKED_CERTIFICATE_OP}");

    for line in canonical_trust_ir.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if let Some(name) = canonical_function_name(trimmed) {
            function = name;
            in_block = false;
            continue;
        }
        if let Some(id) = canonical_block_id(trimmed) {
            block = id;
            statement_index = 0;
            in_block = true;
            continue;
        }
        if trimmed == "}" {
            in_block = false;
            continue;
        }
        if !in_block {
            continue;
        }

        let current_statement_index = statement_index;
        statement_index += 1;
        if !trimmed.contains(&proof_op) {
            continue;
        }
        if let Some(entry) = canonical_checked_certificate_evidence(
            &function,
            block,
            current_statement_index,
            trimmed,
        ) {
            evidence.push(entry);
        }
    }
    evidence
}

fn collect_canonical_proof_replay_evidence(
    canonical_trust_ir: &str,
) -> Vec<BinaryTrustCgProofReplayEvidence> {
    let mut evidence = Vec::new();
    let mut function = "unknown".to_string();
    let mut block = 0;
    let mut statement_index = 0;
    let mut in_block = false;
    let proof_op = format!("dialect_op {PROOF_METADATA_DIALECT}.{PROOF_REPLAY_OP}");

    for line in canonical_trust_ir.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if let Some(name) = canonical_function_name(trimmed) {
            function = name;
            in_block = false;
            continue;
        }
        if let Some(id) = canonical_block_id(trimmed) {
            block = id;
            statement_index = 0;
            in_block = true;
            continue;
        }
        if trimmed == "}" {
            in_block = false;
            continue;
        }
        if !in_block {
            continue;
        }

        let current_statement_index = statement_index;
        statement_index += 1;
        if !trimmed.contains(&proof_op) {
            continue;
        }
        if let Some(entry) =
            canonical_proof_replay_evidence(&function, block, current_statement_index, trimmed)
        {
            evidence.push(entry);
        }
    }
    evidence
}

fn collect_canonical_unsupported_ledger_evidence(
    canonical_trust_ir: &str,
) -> Vec<BinaryTrustCgUnsupportedLedgerEvidence> {
    let mut evidence = Vec::new();
    let mut function = "unknown".to_string();
    let mut block = 0;
    let mut statement_index = 0;
    let mut in_block = false;
    let proof_op = format!("dialect_op {PROOF_METADATA_DIALECT}.{UNSUPPORTED_LEDGER_OP}");

    for line in canonical_trust_ir.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if let Some(name) = canonical_function_name(trimmed) {
            function = name;
            in_block = false;
            continue;
        }
        if let Some(id) = canonical_block_id(trimmed) {
            block = id;
            statement_index = 0;
            in_block = true;
            continue;
        }
        if trimmed == "}" {
            in_block = false;
            continue;
        }
        if !in_block {
            continue;
        }

        let current_statement_index = statement_index;
        statement_index += 1;
        if !trimmed.contains(&proof_op) {
            continue;
        }
        if let Some(entry) = canonical_unsupported_ledger_evidence(
            &function,
            block,
            current_statement_index,
            trimmed,
        ) {
            evidence.push(entry);
        }
    }
    evidence
}

fn canonical_checked_certificate_evidence(
    function: &str,
    block: usize,
    statement_index: usize,
    line: &str,
) -> Option<BinaryTrustCgCheckedCertificateEvidence> {
    let schema = canonical_attr_string(line, PROOF_METADATA_ATTR_SCHEMA)?;
    if schema != CHECKED_CERTIFICATE_SCHEMA {
        return None;
    }
    let certificate = proof_certificate_status_from_canonical_attrs(line)?;
    let target_semantic_consumption = trust_cg_target_semantic_consumption_evidence(
        canonical_attr_bool(line, PROOF_METADATA_ATTR_TARGET_SEMANTICS_CONSUMED),
    );
    let target_semantics_consumed = target_semantic_consumption.target_semantics_consumed;
    let source = proof_metadata_source(
        CHECKED_CERTIFICATE_OP,
        canonical_attr_string(line, PROOF_METADATA_ATTR_SOURCE),
    );
    let dispatch_id = format!("{function}::bb{block}::stmt{statement_index}");
    let (checker, format, sha256) = checked_certificate_identity(&certificate);

    Some(BinaryTrustCgCheckedCertificateEvidence {
        dispatch_id,
        function: Some(function.to_string()),
        source,
        block: Some(block),
        statement_index: Some(statement_index),
        origin: None,
        certificate,
        checker,
        format,
        sha256,
        replay: ReplayStatus::NotAttempted,
        audit_readback_metadata: Vec::new(),
        target_semantic_consumption,
        target_semantics_consumed,
    })
}

fn canonical_proof_replay_evidence(
    function: &str,
    block: usize,
    statement_index: usize,
    line: &str,
) -> Option<BinaryTrustCgProofReplayEvidence> {
    let schema = canonical_attr_string(line, PROOF_METADATA_ATTR_SCHEMA)?;
    if schema != PROOF_REPLAY_SCHEMA {
        return None;
    }
    let replay = replay_status_from_canonical_attrs(line)?;
    let target_semantic_consumption = trust_cg_target_semantic_consumption_evidence(
        canonical_attr_bool(line, PROOF_METADATA_ATTR_TARGET_SEMANTICS_CONSUMED),
    );
    let target_semantics_consumed = target_semantic_consumption.target_semantics_consumed;

    Some(BinaryTrustCgProofReplayEvidence {
        dispatch_id: format!("{function}::bb{block}::stmt{statement_index}"),
        function: Some(function.to_string()),
        source: proof_metadata_source(
            PROOF_REPLAY_OP,
            canonical_attr_string(line, PROOF_METADATA_ATTR_SOURCE),
        ),
        block: Some(block),
        statement_index: Some(statement_index),
        replay,
        artifact_sha256: non_empty_canonical_attr_string(line, PROOF_METADATA_ATTR_ARTIFACT_SHA256),
        exact_replay_checked: canonical_attr_bool(line, PROOF_METADATA_ATTR_EXACT_REPLAY_CHECKED)
            .unwrap_or(false),
        target_semantic_consumption,
        target_semantics_consumed,
    })
}

fn canonical_unsupported_ledger_evidence(
    function: &str,
    block: usize,
    statement_index: usize,
    line: &str,
) -> Option<BinaryTrustCgUnsupportedLedgerEvidence> {
    let schema = canonical_attr_string(line, PROOF_METADATA_ATTR_SCHEMA)?;
    if schema != UNSUPPORTED_LEDGER_SCHEMA {
        return None;
    }
    let unsupported_records = canonical_attr_u64(line, PROOF_METADATA_ATTR_UNSUPPORTED_RECORDS)
        .and_then(|value| usize::try_from(value).ok())
        .unwrap_or(usize::MAX);
    let verification_unsupported =
        canonical_attr_u64(line, PROOF_METADATA_ATTR_VERIFICATION_UNSUPPORTED)
            .and_then(|value| usize::try_from(value).ok())
            .unwrap_or(0);
    let target_semantic_consumption = trust_cg_target_semantic_consumption_evidence(
        canonical_attr_bool(line, PROOF_METADATA_ATTR_TARGET_SEMANTICS_CONSUMED),
    );
    let target_semantics_consumed = target_semantic_consumption.target_semantics_consumed;

    Some(BinaryTrustCgUnsupportedLedgerEvidence {
        source: proof_metadata_source(
            UNSUPPORTED_LEDGER_OP,
            canonical_attr_string(line, PROOF_METADATA_ATTR_SOURCE),
        ),
        function: Some(function.to_string()),
        block: Some(block),
        statement_index: Some(statement_index),
        unsupported_records,
        verification_unsupported,
        unsupported_ledger_eliminated: unsupported_records == 0 && verification_unsupported == 0,
        target_semantic_consumption,
        target_semantics_consumed,
    })
}

fn formula_evidence_from_formula(
    function: &str,
    block: usize,
    statement_index: usize,
    operand: &str,
    formula: &Formula,
) -> BinaryTrustCgSymbolicFormulaEvidence {
    let formula_schema = symbolic_formula_schema(formula);
    let mut schema_errors = Vec::new();
    let formula_json = match serde_json::to_string(formula) {
        Ok(json) => Some(json),
        Err(err) => {
            schema_errors.push(format!("failed to serialize formula_json: {err}"));
            None
        }
    };

    BinaryTrustCgSymbolicFormulaEvidence {
        function: function.to_string(),
        block,
        statement_index,
        operand: operand.to_string(),
        result_tys: None,
        formula: Some(formula.clone()),
        formula_json,
        smtlib: Some(formula_schema.smtlib),
        sort: Some(formula_schema.sort.clone()),
        inferred_sort: Some(formula_schema.sort),
        bit_width: formula_schema.bit_width,
        schema: Some(SYMBOLIC_FORMULA_SCHEMA.to_string()),
        debug: Some(format!("{formula:?}")),
        parse_error: None,
        schema_errors,
        target_semantic_consumption: trust_cg_target_semantic_consumption_evidence(None),
        target_semantics_consumed: false,
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

    match (sort, formula_schema) {
        (Some(sort), Some(formula_schema)) if sort == formula_schema.sort => {}
        (Some(sort), Some(formula_schema)) => errors.push(format!(
            "formula.sort `{sort}` does not match inferred sort `{}`",
            formula_schema.sort
        )),
        (None, _) => errors.push(format!("missing `{SYMBOLIC_FORMULA_ATTR_SORT}` attr")),
        (Some(_), None) => {}
    }

    match (smtlib, formula_schema) {
        (Some(smtlib), Some(formula_schema)) if smtlib == formula_schema.smtlib => {}
        (Some(smtlib), Some(formula_schema)) => errors.push(format!(
            "formula.smtlib2 `{smtlib}` does not match parsed formula `{}`",
            formula_schema.smtlib
        )),
        (None, _) => errors.push(format!("missing `{SYMBOLIC_FORMULA_ATTR_SMTLIB}` attr")),
        (Some(_), None) => {}
    }

    errors
}

fn canonical_function_name(line: &str) -> Option<String> {
    let start = line.find("fn @")? + "fn @".len();
    let rest = &line[start..];
    let end = rest.find('(')?;
    Some(rest[..end].to_string())
}

fn canonical_block_id(line: &str) -> Option<usize> {
    let rest = line.strip_prefix("bb")?;
    let digits = rest.chars().take_while(|ch| ch.is_ascii_digit()).collect::<String>();
    if digits.is_empty() {
        return None;
    }
    digits.parse().ok()
}

fn canonical_attr_string(line: &str, name: &str) -> Option<String> {
    canonical_attr_entries(line).into_iter().find_map(|entry| {
        let (attr_name, value) = entry.split_once('=')?;
        if attr_name == name { canonical_str_attr_value(value) } else { None }
    })
}

fn non_empty_canonical_attr_string(line: &str, name: &str) -> Option<String> {
    canonical_attr_string(line, name).and_then(|value| {
        let trimmed = value.trim();
        if trimmed.is_empty() { None } else { Some(trimmed.to_string()) }
    })
}

fn canonical_attr_u64(line: &str, name: &str) -> Option<u64> {
    canonical_attr_string(line, name).and_then(|value| parse_canonical_u64(&value))
}

fn canonical_attr_bool(line: &str, name: &str) -> Option<bool> {
    canonical_attr_string(line, name).and_then(|value| match value.trim() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    })
}

fn canonical_attr_hex_bytes(line: &str, name: &str) -> Option<Vec<u8>> {
    canonical_attr_string(line, name).and_then(|value| parse_canonical_hex_bytes(&value))
}

fn canonical_attr_entries(line: &str) -> Vec<&str> {
    let mut entries = Vec::new();
    let mut entry_start = None;
    let mut in_quote = false;
    let mut escaped = false;

    for (idx, ch) in line.char_indices() {
        let Some(start) = entry_start else {
            if ch == '[' {
                entry_start = Some(idx + ch.len_utf8());
            }
            continue;
        };

        if in_quote {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_quote = false;
            }
            continue;
        }

        if ch == '"' {
            in_quote = true;
        } else if ch == ']' {
            entries.push(&line[start..idx]);
            entry_start = None;
        }
    }

    entries
}

fn canonical_str_attr_value(value: &str) -> Option<String> {
    let payload = value.trim().strip_prefix("str:")?;
    serde_json::from_str::<String>(payload).ok()
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

fn canonical_binary_provenance_source(source: Option<String>) -> String {
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

fn proof_certificate_status_from_canonical_attrs(line: &str) -> Option<ProofCertificateStatus> {
    if let Some(json) = canonical_attr_string(line, PROOF_METADATA_ATTR_STATUS_JSON) {
        return serde_json::from_str::<ProofCertificateStatus>(&json).ok();
    }

    let checked =
        canonical_attr_bool(line, PROOF_METADATA_ATTR_CERTIFICATE_CHECKED).unwrap_or(false);
    let checker = non_empty_canonical_attr_string(line, PROOF_METADATA_ATTR_CHECKER);
    let format = non_empty_canonical_attr_string(line, PROOF_METADATA_ATTR_FORMAT);
    let sha256 = non_empty_canonical_attr_string(line, PROOF_METADATA_ATTR_SHA256);

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

fn replay_status_from_canonical_attrs(line: &str) -> Option<ReplayStatus> {
    if let Some(json) = canonical_attr_string(line, PROOF_METADATA_ATTR_STATUS_JSON) {
        return serde_json::from_str::<ReplayStatus>(&json).ok();
    }
    canonical_attr_string(line, PROOF_METADATA_ATTR_REPLAY_STATUS).and_then(|status| {
        match status.as_str() {
            "not_attempted" | "not-attempted" | "NotAttempted" => Some(ReplayStatus::NotAttempted),
            "replayed" | "Replayed" => Some(ReplayStatus::Replayed),
            "spurious" | "Spurious" => Some(ReplayStatus::Spurious),
            "failed" | "Failed" => Some(ReplayStatus::Failed),
            _ => None,
        }
    })
}

fn checked_certificate_identity(
    status: &ProofCertificateStatus,
) -> (String, String, Option<String>) {
    match status {
        ProofCertificateStatus::Checked { checker, format, sha256 } => {
            (checker.clone(), format.clone(), sha256.clone())
        }
        ProofCertificateStatus::Present { format, sha256, .. } => {
            ("unchecked".to_string(), format.clone(), sha256.clone())
        }
        ProofCertificateStatus::Rejected { checker, .. } => (
            checker.clone().unwrap_or_else(|| "rejected".to_string()),
            "rejected".to_string(),
            None,
        ),
        ProofCertificateStatus::Unavailable { .. } => {
            ("unavailable".to_string(), "unavailable".to_string(), None)
        }
        ProofCertificateStatus::NotRequested => {
            ("not-requested".to_string(), "not-requested".to_string(), None)
        }
        _ => ("unknown".to_string(), "unknown".to_string(), None),
    }
}

fn canonical_result_tys_label(line: &str) -> String {
    let symbolic_op = symbolic_formula_dialect_op_text();
    let Some((_, after_op)) = line.split_once(&symbolic_op) else {
        return "()".to_string();
    };
    let Some((_, result_and_attrs)) = after_op.split_once(" -> ") else {
        return "()".to_string();
    };
    let attr_start = result_and_attrs.find(" [").unwrap_or(result_and_attrs.len());
    result_and_attrs[..attr_start].trim().to_string()
}

fn symbolic_formula_dialect_op_text() -> String {
    format!("dialect_op {SYMBOLIC_FORMULA_DIALECT}.{SYMBOLIC_FORMULA_OP}")
}

fn symbolic_formula_evidence_detail(entry: &BinaryTrustCgSymbolicFormulaEvidence) -> String {
    let mut parts = vec![
        format!("function={}", entry.function),
        format!("block={}", entry.block),
        format!("statement_index={}", entry.statement_index),
        format!("operand={}", entry.operand),
        format!("formula.target_semantics_consumed={}", entry.target_semantics_consumed),
        format!("formula.consumption.consumer={}", entry.target_semantic_consumption.consumer),
        format!("formula.consumption.code={}", entry.target_semantic_consumption.code),
        format!(
            "formula.consumption.target_semantics_consumed={}",
            entry.target_semantic_consumption.target_semantics_consumed
        ),
    ];
    if let Some(result_tys) = &entry.result_tys {
        parts.push(format!("result_tys={result_tys}"));
    }
    if let Some(schema) = &entry.schema {
        parts.push(format!("formula.schema={schema}"));
    }
    if let Some(sort) = &entry.sort {
        parts.push(format!("formula.sort={sort}"));
    }
    if let Some(inferred_sort) = &entry.inferred_sort {
        parts.push(format!("formula.inferred_sort={inferred_sort}"));
    }
    if let Some(bit_width) = entry.bit_width {
        parts.push(format!("formula.bit_width={bit_width}"));
    }
    if let Some(smtlib) = &entry.smtlib {
        parts.push(format!("formula.smtlib2={smtlib}"));
    }
    if let Some(json) = &entry.formula_json {
        parts.push(format!("formula_json={json}"));
    }
    if let Some(debug) = &entry.debug {
        parts.push(format!("formula.debug={debug}"));
    }
    if let Some(parse_error) = &entry.parse_error {
        parts.push(format!("formula_json_error={parse_error}"));
    }
    for error in &entry.schema_errors {
        parts.push(format!("formula.schema_error={error}"));
    }
    parts.join("; ")
}

fn refinement_metadata_evidence_detail(entry: &BinaryTrustCgRefinementMetadataEvidence) -> String {
    let mut parts = vec![
        format!("refinement_metadata.slice={}", entry.slice),
        format!("refinement_metadata.source={}", entry.source),
        format!("refinement_metadata.source_function={}", entry.source_function),
        format!("refinement_metadata.target={}", entry.target),
        format!("refinement_metadata.target_output={}", entry.target_output),
        format!(
            "refinement_metadata.bidirectional_refinement_consumed={}",
            entry.bidirectional_refinement_consumed
        ),
        format!(
            "refinement_metadata.consumption.consumer={}",
            entry.bidirectional_consumption.consumer
        ),
        format!("refinement_metadata.consumption.code={}", entry.bidirectional_consumption.code),
        format!(
            "refinement_metadata.consumption.bidirectional_refinement_consumed={}",
            entry.bidirectional_consumption.bidirectional_refinement_consumed
        ),
    ];
    if let Some(block) = entry.source_block {
        parts.push(format!("refinement_metadata.source_block={block}"));
    }
    if let Some(statement_index) = entry.source_statement_index {
        parts.push(format!("refinement_metadata.source_statement_index={statement_index}"));
    }
    if let Some(source_formula) = &entry.source_formula {
        parts.push(format!("refinement_metadata.source_formula={source_formula}"));
    }
    if let Some(target_function) = &entry.target_function {
        parts.push(format!("refinement_metadata.target_function={target_function}"));
    }
    if let Some(target_block) = entry.target_block {
        parts.push(format!("refinement_metadata.target_block={target_block}"));
    }
    if let Some(target_result) = entry.target_result {
        parts.push(format!("refinement_metadata.target_result={target_result}"));
    }
    parts.push(format!("refinement_metadata.forward={}", entry.forward_relation));
    parts.push(format!("refinement_metadata.reverse={}", entry.reverse_relation));
    parts.push(format!(
        "refinement_metadata.consumption.detail={}",
        entry.bidirectional_consumption.detail
    ));
    parts.join("; ")
}

fn replace_refinement_metadata_diagnostics(
    diagnostics: &mut Vec<String>,
    refinement_metadata_evidence: &[BinaryTrustCgRefinementMetadataEvidence],
) {
    diagnostics.retain(|diagnostic| !diagnostic.starts_with("refinement_metadata."));
    diagnostics
        .extend(refinement_metadata_evidence.iter().map(refinement_metadata_evidence_detail));
}

fn checked_certificate_evidence_detail(entry: &BinaryTrustCgCheckedCertificateEvidence) -> String {
    let mut parts = vec![
        format!("checked_certificate.dispatch_id={}", entry.dispatch_id),
        format!("checked_certificate.source={}", entry.source),
        format!("checked_certificate.status={}", checked_certificate_label(&entry.certificate)),
        format!("checked_certificate.checker={}", entry.checker),
        format!("checked_certificate.format={}", entry.format),
        format!("checked_certificate.replay={:?}", entry.replay),
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
    if let Some(function) = &entry.function {
        parts.push(format!("checked_certificate.function={function}"));
    }
    if let Some(block) = entry.block {
        parts.push(format!("checked_certificate.block={block}"));
    }
    if let Some(statement_index) = entry.statement_index {
        parts.push(format!("checked_certificate.statement_index={statement_index}"));
    }
    if let Some(origin) = &entry.origin {
        parts.push(format!(
            "checked_certificate.origin.instruction_address=0x{:x}",
            origin.instruction_address
        ));
    }
    if let Some(sha256) = &entry.sha256 {
        parts.push(format!("checked_certificate.sha256={sha256}"));
    }
    for metadata in &entry.audit_readback_metadata {
        parts.push(format!("checked_certificate.audit_readback={metadata}"));
    }
    parts.join("; ")
}

fn proof_replay_evidence_detail(entry: &BinaryTrustCgProofReplayEvidence) -> String {
    let mut parts = vec![
        format!("proof_replay.dispatch_id={}", entry.dispatch_id),
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
    if let Some(function) = &entry.function {
        parts.push(format!("proof_replay.function={function}"));
    }
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

fn unsupported_ledger_evidence_detail(entry: &BinaryTrustCgUnsupportedLedgerEvidence) -> String {
    let mut parts = vec![
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
    if let Some(function) = &entry.function {
        parts.push(format!("unsupported_ledger.function={function}"));
    }
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
            "rejected certificate checker={} reason={}",
            checker.as_deref().unwrap_or("unknown"),
            reason
        ),
        ProofCertificateStatus::NotRequested => "certificate not requested".to_string(),
        _ => "unknown certificate status".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use trust_cg_lower::instructions::{Block, Opcode};
    use trust_types::{
        BasicBlock as TrustBlock, BinOp, BlockId, DecompileTarget, DecompiledOutput, LocalDecl,
        Operand, Place, Rvalue, Sort, SourceSpan, Statement, TargetValidationBlocker, Terminator,
        Ty, VerifiableBody,
    };

    use super::*;

    fn add_trust_ir(name: &str) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("binary::{name}"),
            span: SourceSpan::binary_address(0x401000),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".to_string()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".to_string()) },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::binary_address(0x401004),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn lower_binary_trust_ir_to_lir_lowers_and_validates_lir() {
        let trust_ir = add_trust_ir("add");

        let conversion =
            lower_binary_trust_ir_to_lir(&trust_ir).expect("binary TrustIr should lower");

        assert_eq!(conversion.lir.name, "add");
        assert_eq!(conversion.lir.entry_block, Block(0));
        assert!(
            conversion.lir.blocks[&Block(0)]
                .instructions
                .iter()
                .any(|instruction| matches!(instruction.opcode, Opcode::Iadd))
        );
        validate_lir(&conversion.lir).expect("conversion must return validated LIR");
        assert_eq!(conversion.structural_validation, ReconstructionValidationStatus::Validated);
        assert_eq!(
            conversion.trust_cg_validation,
            BinaryTrustCgValidationStatus::InspectableRejected
        );
        assert_eq!(conversion.trust_level, TrustLevel::Rejected);
        for code in [
            "missing-target-semantic-validation",
            "missing-refinement-metadata",
            "missing-checked-proof-certificate",
            "missing-unsupported-ledger-evidence",
            "missing-binary-proof-obligation",
        ] {
            assert!(
                conversion.validation_blockers.iter().any(|blocker| blocker.code == code),
                "missing proof-grade blocker `{code}`"
            );
        }
    }

    #[test]
    fn lower_binary_trust_ir_to_lir_clones_reconstructed_trust_ir_candidate() {
        let trust_ir = add_trust_ir("candidate_add");

        let conversion =
            lower_binary_trust_ir_to_lir(&trust_ir).expect("binary TrustIr should lower");

        assert_eq!(conversion.reconstructed_trust_ir.name, trust_ir.name);
        assert_eq!(conversion.reconstructed_trust_ir.def_path, trust_ir.def_path);
        assert_eq!(conversion.reconstructed_trust_ir.content_hash(), trust_ir.content_hash());
    }

    #[test]
    fn lower_binary_decompiled_function_to_lir_requires_lifted_trust_ir() {
        let function = DecompiledFunction { name: "missing".to_string(), ..Default::default() };

        let err = lower_binary_decompiled_function_to_lir(&function)
            .expect_err("missing lifted TrustIr must be rejected");

        assert!(
            matches!(err, BinaryTrustCgConversionError::MissingLiftedTrustIr { function } if function == "missing")
        );
    }

    #[test]
    fn lower_binary_conversion_diagnostics_are_not_proof_grade() {
        let function = DecompiledFunction {
            name: "add".to_string(),
            lifted: Some(add_trust_ir("add")),
            ..Default::default()
        };

        let conversion = lower_binary_decompiled_function_to_lir(&function)
            .expect("lifted TrustIr should lower");

        for expected in [
            "target=trust_cg-lir",
            "source=binary-derived-trust_ir",
            "not-proof-grade",
            "trust_cg-validation=inspectable-rejected",
        ] {
            assert!(conversion.diagnostics.iter().any(|diagnostic| diagnostic == expected));
        }
        assert!(conversion.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("binary_provenance.source=lifted.function_span")
                && diagnostic.contains("binary_provenance.instruction_address=0x401000")
        }));
        assert!(conversion.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("binary_provenance.source=lifted.bb0.stmt0")
                && diagnostic.contains("binary_provenance.instruction_address=0x401004")
                && diagnostic.contains("binary_provenance.target_semantics_consumed=false")
        }));
    }

    #[test]
    fn binary_trust_cg_semantic_blockers_remain_json_visible_and_rejected() {
        let trust_ir = add_trust_ir("reported_add");

        let conversion =
            lower_binary_trust_ir_to_lir(&trust_ir).expect("binary TrustIr should lower");
        assert_eq!(
            conversion.trust_cg_validation,
            BinaryTrustCgValidationStatus::InspectableRejected
        );
        assert_eq!(conversion.trust_level, TrustLevel::Rejected);
        assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);

        let output = DecompiledOutput {
            target: DecompileTarget::TrustCg,
            text: Some("; structurally valid trust_cg LIR omitted".to_string()),
            validation: conversion.structural_validation,
            trust_level: conversion.trust_level,
            target_validation_blockers: conversion
                .validation_blockers
                .iter()
                .map(|blocker| TargetValidationBlocker {
                    target: DecompileTarget::TrustCg,
                    code: blocker.code.clone(),
                    stage: "trust-cg-bridge::target-validation".to_string(),
                    feature: blocker.code.clone(),
                    reason: blocker.detail.clone(),
                    diagnostics: conversion.diagnostics.clone(),
                    ..Default::default()
                })
                .collect(),
            diagnostics: conversion.diagnostics.clone(),
            ..Default::default()
        };

        let json = serde_json::to_value(&output).expect("report output should serialize");

        assert_eq!(json["target"], "TrustCg");
        assert_eq!(json["validation"], "Validated");
        assert_eq!(json["trust_level"], "Rejected");
        assert_ne!(json["trust_level"], "ProofGrade");
        let diagnostics = json["diagnostics"].as_array().expect("diagnostics should be visible");
        assert!(diagnostics.iter().any(|diagnostic| {
            diagnostic.as_str().unwrap() == "source=binary-derived-trust_ir"
        }));
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic.as_str().unwrap() == "not-proof-grade")
        );

        let blockers = json["target_validation_blockers"]
            .as_array()
            .expect("target validation blockers should be JSON-visible");
        assert_eq!(blockers.len(), conversion.validation_blockers.len());
        for required in &conversion.validation_blockers {
            assert!(
                blockers.iter().any(|blocker| {
                    blocker["code"] == required.code && blocker["feature"] == required.code
                }),
                "missing semantic validation blocker `{}` in {json}",
                required.code
            );
        }
    }

    #[test]
    fn lower_binary_conversion_rejects_non_ground_symbolic_formula() {
        let formula = Formula::Var("x0".to_string(), Sort::BitVec(32));
        let mut trust_ir = add_trust_ir("symbolic_add");
        trust_ir.body.blocks[0].stmts[0] = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Symbolic(formula)),
            span: SourceSpan::binary_address(0x401004),
        };

        let error = lower_binary_trust_ir_to_lir(&trust_ir)
            .expect_err("non-ground symbolic TrustIr must not produce executable LIR");
        assert!(matches!(
            error,
            BinaryTrustCgConversionError::Lowering(BridgeError::UnsupportedOp(message))
                if message.contains("symbolic operand requires target-semantic lowering")
        ));
    }
}
