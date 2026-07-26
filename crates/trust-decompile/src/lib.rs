//! Minimal binary decompiler API.
//!
//! This crate deliberately treats Rust emission as an exploratory presentation
//! layer over real binary-to-TrustIr lifting. It does not claim validated Rust
//! reconstruction.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::collections::{BTreeSet, HashMap};
use std::fmt::Write as _;

use serde::{Deserialize, Serialize};
use thiserror::Error;
use trust_binary_parse::{BinaryArtifactIdentity, parse_binary_with_identity};
#[cfg(feature = "trust-cg")]
use trust_cg_bridge::{
    BinaryTrustCgConversion, BinaryTrustCgConversionError, BinaryTrustCgProofConsumerEvidence,
    BinaryTrustCgProofConsumerStatus, BinaryTrustCgSymbolicFormula, BinaryTrustCgValidationBlocker,
    lower_binary_decompiled_function_to_lir,
};
use trust_ir_bridge::{
    BridgeError as TrustIrBridgeError, TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_FEATURE,
    TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_STAGE, collect_layout_sensitive_cast_blockers,
    lower_functions_to_trust_ir,
};
use trust_lift::cfg::{CfgEdgeKind, CfgEdgeTarget};
pub use trust_lift::{BinaryFunctionSelection, BinaryLiftOptions};
use trust_lift::{
    CallingConvention, FunctionSignature, LiftArch, LiftError, LiftedBinary, LiftedFunction,
    lift_binary_to_trust_ir, summarize_function_signature,
};
pub use trust_types::DecompilationArtifact;
use trust_types::call_graph::{CallGraph, CallGraphEdge, CallGraphNode};
use trust_types::{
    BinOp, BinaryAbiFact, BinaryAbiFactKind, BinaryAddressRange, BinaryArtifactDigest,
    BinaryArtifactDigestIdentity, BinaryArtifactFormat, BinaryArtifactMetadata,
    BinaryCallingConvention, BinaryCoverageSummary, BinaryFactConfidence, BinaryFactEvidence,
    BinaryFactSubject, BinaryFunctionSignature, BinaryMemoryModel, BinaryOrigin, BinaryParameter,
    BinaryReturn, BinarySelectedImageIdentity, BinarySourceProvenanceDiagnostic,
    BinarySourceProvenanceSummary, BinaryStorageFact, BinaryStorageLocation, BinarySymbol,
    BinarySymbolKind, BinaryVerificationSummary, ConstValue,
    DecompileOptions as SharedDecompileOptions, DecompileTarget, DecompiledFunction,
    DecompiledOutput, Endianness, MemoryAccessFact, ModelAssumption, Operand,
    PreservedSymbolicFormula, ProofCertificateStatus, ReconstructionCandidateKind,
    ReconstructionSummary, ReconstructionValidationDirection,
    ReconstructionValidationDirectionRecord, ReconstructionValidationEvidence,
    ReconstructionValidationRecord, ReconstructionValidationStatus, ReplayStatus,
    RustReconstructionEligibility, RustReconstructionRejectionKind, Rvalue, SerializableVc,
    SolverDispatchRecord, SolverDispatchStatus, SolverQuerySemantics, SourceSpan, Statement,
    TargetValidationBlocker, Terminator, TrustLevel, Ty, UnOp, UnsupportedLedger,
    UnsupportedRecord, ValidatedRustReconstruction, VerifiableFunction, VerificationCondition,
    VerificationResult, stable_sha256_hex,
};
use trust_wasm_bridge::{
    WasmConversion, WasmProofConsumerEvidence, WasmProofConsumerStatus, WasmSymbolicFormula,
    WasmTargetValidationStatus, WasmValidationBlocker, convert_functions_to_wat,
    reject_missing_lifted_trust_ir,
};

const CONVERSION_STATUS_VALIDATED_PARTIAL: &str = "validated_partial";
#[cfg(feature = "trust-cg")]
const CONVERSION_STATUS_INSPECTABLE_REJECTED: &str = "inspectable_rejected";
const CONVERSION_STATUS_TRANSLATION_REJECTED: &str = "translation_rejected";
const CONVERSION_SOURCE_BINARY_TRUST_IR: &str = "binary-derived-trust_ir";
const TRUST_CG_VALIDATION_SUBSET: &str = "trust_cg-lir-structural";
const WASM_VALIDATION_SUBSET: &str = "wasm-simple-integer-or-unit-return";
const PARSER_ARTIFACT_IDENTITY_STAGE: &str = "trust-binary-parse::artifact-identity";
const SOURCE_PROVENANCE_GATE_STAGE: &str = "trust-decompile::source-provenance";
const RECONSTRUCTION_OUTPUT_BINARY_ARTIFACT_DIGEST_IDENTITY_STAGE: &str =
    "trust-decompile::reconstruction-output-binary-artifact-digest-identity";
const SOURCE_BACKPROPAGATION_ALLOWED_DIAGNOSTIC_PREFIX: &str = "source-backpropagation-allowed=";
const EFFECTIVE_SOURCE_BACKPROPAGATION_ALLOWED_DIAGNOSTIC_PREFIX: &str =
    "effective-source-backpropagation-allowed=";
const SOURCE_REWRITE_AUTHORITY_BLOCKER_PREFIX: &str = "source-rewrite-authority-blocker=";
const SYMBOLIC_FORMULA_SCHEMA: &str = "trust-types.Formula@1";
const TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_SCHEMA: &str =
    "trust-decompile.TargetProofConsumerArtifactDigest@3";
const TARGET_PROOF_CONSUMER_EVIDENCE_ARTIFACT_DIGEST_SCHEMA: &str =
    "trust-decompile.TargetProofConsumerEvidenceArtifactDigest@2";
const TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX: &str =
    "target-proof-consumer-artifact-digest-json=";
const RUST_COMPILE_BACK_EVIDENCE_ARTIFACT_SCHEMA: &str =
    "trust-decompile.RustCompileBackEvidenceArtifact@1";
const TRUST_IR_TARGET_LOWERING_FAILED_BLOCKER: &str = "trust-ir-target-lowering-failed";
const TRUST_IR_UNCONSUMED_THREAD_LOCAL_ADDR_BLOCKER: &str =
    "trust-ir-unconsumed-thread-local-addr";

#[derive(Debug, Clone)]
enum ParserArtifactIdentityStatus {
    Parsed(BinaryArtifactIdentity),
    Unavailable { reason: String },
}

/// Options for [`decompile_binary`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecompileOptions {
    /// Options forwarded to the real binary-to-TrustIr lifter.
    pub lift: BinaryLiftOptions,
    /// Presentation outputs to materialize in the returned artifact.
    pub outputs: Vec<DecompileOutputKind>,
}

impl Default for DecompileOptions {
    fn default() -> Self {
        Self { lift: BinaryLiftOptions::default(), outputs: vec![DecompileOutputKind::TrustIrJson] }
    }
}

impl DecompileOptions {
    /// Build options around a specific binary lifting request.
    #[must_use]
    pub fn with_lift(lift: BinaryLiftOptions) -> Self {
        Self { lift, ..Self::default() }
    }

    /// Replace the output set.
    #[must_use]
    pub fn with_outputs<I>(mut self, outputs: I) -> Self
    where
        I: IntoIterator<Item = DecompileOutputKind>,
    {
        self.outputs = outputs.into_iter().collect();
        self
    }
}

/// Presentation outputs supported by the first decompiler API slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum DecompileOutputKind {
    /// Pretty JSON over the lifted TrustIr artifact.
    TrustIrJson,
    /// Debug-style textual TrustIr summary.
    TrustIrText,
    /// Exploratory, partial Rust function skeletons.
    RustSkeleton,
    /// Structurally validated trust_cg LIR text for supported binary-derived TrustIr.
    TrustCgText,
    /// Conservative WAT text for the tiny accepted Wasm subset.
    WasmText,
    /// Explicit rejected placeholder for unavailable trust_cg conversion.
    TrustCgUnsupported,
    /// Explicit rejected placeholder for unavailable WebAssembly conversion.
    WasmUnsupported,
}

/// Errors returned by [`decompile_binary`].
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum DecompileError {
    /// Binary lifting failed before a decompilation artifact could be produced.
    #[error("binary lift failed: {0}")]
    Lift(#[from] LiftError),

    /// Artifact output serialization failed.
    #[error("failed to serialize decompilation output: {0}")]
    Serialize(#[from] serde_json::Error),

    /// Lifted TrustIr could not be lowered into the canonical TrustIr module model.
    #[error("failed to lower lifted TrustIr into trust_ir::Module: {0}")]
    TrustIrBridge(#[from] TrustIrBridgeError),
}

/// Decompile a binary image into a conservative TrustIr-centered artifact.
///
/// Binary lifting is delegated to [`trust_lift::lift_binary_to_trust_ir`]. Rust
/// skeleton output, when requested, is partial and explicitly
/// [`TrustLevel::Exploratory`].
///
/// # Errors
///
/// Returns [`DecompileError::Lift`] if `trust-lift` cannot parse or lift the
/// requested binary slice. Returns [`DecompileError::Serialize`] if a requested
/// TrustIr JSON output cannot be serialized.
pub fn decompile_binary(
    bytes: &[u8],
    options: DecompileOptions,
) -> Result<DecompilationArtifact, DecompileError> {
    let parser_identity = parser_artifact_identity_for_decompile(bytes);
    let lifted = lift_binary_to_trust_ir(bytes, options.lift.clone())?;
    decompilation_artifact_from_lifted_internal(
        bytes.len(),
        &options,
        &lifted,
        Some(&parser_identity),
    )
}

/// Convert a lifted binary into the shared decompilation artifact schema.
///
/// This is the narrow adapter from `trust-lift`'s binary-to-TrustIr result into
/// `trust-types`' cross-crate artifact model. It does not perform Rust
/// validation; Rust skeleton output remains exploratory.
///
/// # Errors
///
/// Returns [`DecompileError::Serialize`] if a requested TrustIr JSON output cannot
/// be serialized.
pub fn decompilation_artifact_from_lifted(
    image_size_bytes: usize,
    options: &DecompileOptions,
    lifted: &LiftedBinary,
) -> Result<DecompilationArtifact, DecompileError> {
    decompilation_artifact_from_lifted_internal(image_size_bytes, options, lifted, None)
}

fn decompilation_artifact_from_lifted_internal(
    image_size_bytes: usize,
    options: &DecompileOptions,
    lifted: &LiftedBinary,
    parser_identity: Option<&ParserArtifactIdentityStatus>,
) -> Result<DecompilationArtifact, DecompileError> {
    let binary = build_binary_metadata(lifted, image_size_bytes);

    let arch = lift_arch_from_name(lifted.architecture);
    let functions: Vec<_> = lifted
        .functions
        .iter()
        .map(|function| summarize_function(function, arch, lifted))
        .collect();
    let memory_facts: Vec<MemoryAccessFact> =
        functions.iter().flat_map(|function| function.memory_accesses.iter().cloned()).collect();
    let abi_facts: Vec<BinaryAbiFact> =
        functions.iter().flat_map(|function| function.abi_facts.iter().cloned()).collect();
    let storage_facts: Vec<BinaryStorageFact> =
        functions.iter().flat_map(|function| function.storage_facts.iter().cloned()).collect();
    let (call_graph, call_graph_unsupported) = build_call_graph(lifted, &binary);
    let source_provenance_blockers = source_backpropagation_gate_blockers(lifted);
    let source_provenance = binary_source_provenance_summary(lifted, &source_provenance_blockers);
    let source_assumptions = source_provenance_assumptions(lifted);
    let source_diagnostics = source_provenance.diagnostics.clone();

    let mut binary = binary;
    let mut unsupported = collect_unsupported(lifted, &binary);
    record_parser_artifact_identity_binding(&mut unsupported, &mut binary, parser_identity);
    record_source_provenance_gate_blockers(&mut unsupported, &binary, &source_provenance_blockers);
    unsupported.records.extend(call_graph_unsupported);
    if functions.is_empty() {
        unsupported.records.push(unsupported_record(
            "trust-decompile",
            Some(&binary.architecture),
            None,
            None,
            "no functions were lifted for decompilation",
        ));
    }

    let rust_requested = options.outputs.contains(&DecompileOutputKind::RustSkeleton);
    let rejected_output_requested =
        options.outputs.iter().any(|kind| is_rejected_output_kind(*kind));
    if rust_requested {
        unsupported.records.push(unsupported_record(
            "trust-decompile",
            Some(&binary.architecture),
            None,
            None,
            "Rust skeleton is exploratory; no validated Rust reconstruction was performed",
        ));
    }
    for kind in options.outputs.iter().copied().filter(|kind| is_rejected_output_kind(*kind)) {
        unsupported.records.push(unsupported_record(
            "trust-decompile",
            Some(&binary.architecture),
            None,
            None,
            rejected_output_message(kind),
        ));
    }
    let mut conversion_rejected = false;
    if options.outputs.contains(&DecompileOutputKind::TrustCgText) {
        let conversion = trust_cg_conversion_for_functions(&binary, &functions)?;
        conversion_rejected |= conversion_is_rejected(
            conversion.validation,
            conversion.trust_level,
            &conversion.unsupported,
        );
        unsupported.records.extend(conversion.unsupported.records);
    }
    if options.outputs.contains(&DecompileOutputKind::WasmText) {
        let conversion = wasm_conversion_for_functions(&binary, &functions);
        conversion_rejected |= conversion_is_rejected(
            conversion.validation,
            conversion.trust_level,
            &conversion.unsupported,
        );
        unsupported.records.extend(conversion.unsupported.records);
    }

    let target = reconstruction_target(&options.outputs);
    let outputs = build_outputs(BuildOutputsInput {
        metadata: &binary,
        functions: &functions,
        call_graph: &call_graph,
        memory_facts: &memory_facts,
        unsupported: &unsupported,
        source_provenance: &source_provenance,
        requested: &options.outputs,
        source_assumptions: &source_assumptions,
        source_diagnostics: &source_diagnostics,
    })?;
    let output_rejected = outputs.iter().any(output_is_rejected);
    let trust_level = if rejected_output_requested || conversion_rejected || output_rejected {
        TrustLevel::Rejected
    } else if rust_requested {
        TrustLevel::Exploratory
    } else {
        TrustLevel::Partial
    };
    let validated_rust = rust_requested.then(|| validated_rust_reconstruction(&functions));
    let reconstruction_validation =
        reconstruction_validation_status(&target, &outputs, validated_rust.as_ref());
    let reconstruction = ReconstructionSummary {
        target: target.clone(),
        outputs,
        validation: reconstruction_validation,
        trust_level,
        assumptions: source_assumptions.clone(),
        diagnostics: reconstruction_diagnostics(&unsupported, rust_requested, &source_diagnostics),
        validated_rust,
    };

    let mut artifact = DecompilationArtifact {
        binary: binary.clone(),
        options: shared_decompile_options(options, lifted, target.clone()),
        target,
        functions,
        call_graph,
        abi_facts,
        storage_facts,
        memory_model: binary_memory_model(lifted, &binary, memory_facts),
        unsupported,
        coverage: aggregate_coverage(lifted),
        source_provenance,
        reconstruction,
        assumptions: source_assumptions,
        trust_level,
        ..Default::default()
    };
    refresh_trust_ir_json_outputs(&mut artifact);
    Ok(artifact)
}

/// Convert a lifted binary and router-style VC results into a decompilation artifact.
///
/// The `verification_results` slice is the usual `(VerificationCondition,
/// VerificationResult)` output from solver dispatch. SAT remains explicitly
/// recorded as a counterexample ([`SolverQuerySemantics::SatIsCounterexample`]);
/// this helper never promotes the artifact, functions, or verification
/// summaries to [`TrustLevel::ProofGrade`].
///
/// # Errors
///
/// Returns [`DecompileError::Serialize`] if a requested TrustIr JSON output cannot
/// be serialized.
pub fn decompilation_artifact_from_lifted_with_verification_results(
    image_size_bytes: usize,
    options: &DecompileOptions,
    lifted: &LiftedBinary,
    verification_results: &[(VerificationCondition, VerificationResult)],
) -> Result<DecompilationArtifact, DecompileError> {
    let mut artifact = decompilation_artifact_from_lifted(image_size_bytes, options, lifted)?;
    attach_binary_verification_results(&mut artifact, lifted, verification_results);
    Ok(artifact)
}

/// Attach binary solver dispatch summaries to an existing decompilation artifact.
///
/// This populates the artifact-level verification summary and each matched
/// function-level summary from the supplied VC results. Function matching uses
/// recovered names, `binary::<name>` def paths, and binary source locations.
/// Replay is left [`ReplayStatus::NotAttempted`] because machine-code witness
/// replay is a separate validation step.
pub fn attach_binary_verification_results(
    artifact: &mut DecompilationArtifact,
    lifted: &LiftedBinary,
    verification_results: &[(VerificationCondition, VerificationResult)],
) {
    let function_lookup = build_function_lookup(artifact, lifted);
    let mut artifact_dispatch = Vec::with_capacity(verification_results.len());
    let mut per_function_dispatch =
        vec![Vec::<SolverDispatchRecord>::new(); artifact.functions.len()];

    for (index, (vc, result)) in verification_results.iter().enumerate() {
        let function_index = function_index_for_vc(artifact, &function_lookup, vc);
        let record =
            solver_dispatch_record_from_result(index, artifact, lifted, function_index, vc, result);

        if let Some(function_index) = function_index {
            per_function_dispatch[function_index].push(record.clone());
        }
        artifact_dispatch.push(record);
    }

    artifact.verification = BinaryVerificationSummary::from_solver_dispatch(artifact_dispatch);
    artifact.verification.unsupported_ledger = artifact.unsupported.clone();
    artifact.verification.refresh_from_solver_dispatch();
    artifact.verification.trust_level =
        cap_binary_verification_trust(artifact.verification.trust_level);
    artifact.verification.replay = ReplayStatus::NotAttempted;

    for (function, dispatch) in artifact.functions.iter_mut().zip(per_function_dispatch) {
        function.verification = BinaryVerificationSummary::from_solver_dispatch(dispatch);
        function.verification.unsupported_ledger = function.unsupported.clone();
        function.verification.refresh_from_solver_dispatch();
        function.verification.trust_level =
            cap_binary_verification_trust(function.verification.trust_level);
        function.verification.replay = ReplayStatus::NotAttempted;
    }

    let _ = apply_binary_proof_grade_release_gate(artifact);
}

/// Apply the proof-grade binary release gate using checked dispatch evidence.
///
/// This mirrors the `targo-trust` binary release-gate accounting without
/// depending on that crate from this crate's public API: binary decompilation
/// artifacts are promoted only when every recorded binary VC is UNSAT under
/// counterexample semantics, has checked certificate identity evidence,
/// satisfies binary replay byte/range identity semantics, carries exact
/// instruction provenance tied to accepted source provenance, and has an empty
/// unsupported ledger. Raw solver proof bytes are intentionally insufficient because
/// [`VerificationResult`] does not prove that a certificate was independently
/// checked.
///
/// Returns `true` when the artifact was promoted to [`TrustLevel::ProofGrade`].
#[must_use]
pub fn apply_binary_proof_grade_release_gate(artifact: &mut DecompilationArtifact) -> bool {
    artifact.verification.unsupported_ledger = artifact.unsupported.clone();
    artifact.verification.refresh_from_solver_dispatch();
    refresh_source_backpropagation_authority(artifact);

    if !binary_proof_grade_release_gate_accepts(&artifact.verification) {
        artifact.verification.proof_certificate =
            aggregate_checked_certificate_status(&artifact.verification.solver_dispatch);
        cap_binary_release_gate_proof_grade_trust(artifact);
        refresh_trust_ir_json_outputs(artifact);
        return false;
    }

    if !artifact_source_provenance_allows_binary_proof_grade(artifact) {
        cap_binary_release_gate_proof_grade_trust(artifact);
        refresh_trust_ir_json_outputs(artifact);
        return false;
    }

    artifact.verification.trust_level = TrustLevel::ProofGrade;
    artifact.verification.proof_certificate =
        aggregate_checked_certificate_status(&artifact.verification.solver_dispatch);
    artifact.trust_level = TrustLevel::ProofGrade;

    let function_source_provenance_allowed: Vec<_> = artifact
        .functions
        .iter()
        .map(|function| {
            dispatches_have_accepted_source_provenance(
                &function.verification.solver_dispatch,
                &artifact.functions,
                &artifact.binary,
            )
        })
        .collect();

    for (index, function) in artifact.functions.iter_mut().enumerate() {
        function.verification.refresh_from_solver_dispatch();
        if binary_proof_grade_release_gate_accepts(&function.verification)
            && function_source_provenance_allowed.get(index).copied().unwrap_or(false)
        {
            function.verification.trust_level = TrustLevel::ProofGrade;
            function.verification.proof_certificate =
                aggregate_checked_certificate_status(&function.verification.solver_dispatch);
            function.trust_level = TrustLevel::ProofGrade;
        } else {
            function.verification.trust_level =
                cap_binary_verification_trust(function.verification.trust_level);
            function.trust_level = cap_binary_verification_trust(function.trust_level);
        }
    }

    if !rust_reconstruction_source_rewrite_authority_allows_proof_grade(artifact) {
        cap_binary_release_gate_proof_grade_trust(artifact);
        refresh_trust_ir_json_outputs(artifact);
        return false;
    }

    if !reconstruction_allows_binary_proof_grade(&artifact.reconstruction, &artifact.binary) {
        cap_binary_release_gate_proof_grade_trust(artifact);
        refresh_trust_ir_json_outputs(artifact);
        return false;
    }

    refresh_trust_ir_json_outputs(artifact);
    true
}

fn source_provenance_allows_artifact_proof_grade(
    source_provenance: &BinarySourceProvenanceSummary,
) -> bool {
    source_provenance_has_exact_source_ownership(source_provenance)
}

fn source_provenance_has_exact_source_ownership(
    source_provenance: &BinarySourceProvenanceSummary,
) -> bool {
    source_provenance.status == "exact"
        && source_provenance.exact_mapping_count > 0
        && source_provenance.ambiguous_mapping_count == 0
        && source_provenance
            .diagnostics
            .iter()
            .all(|diagnostic| !diagnostic.contains("source-backpropagation-blocker="))
}

fn parser_artifact_identity_for_decompile(bytes: &[u8]) -> ParserArtifactIdentityStatus {
    match parse_binary_with_identity(bytes) {
        Ok(parsed) => ParserArtifactIdentityStatus::Parsed(parsed.identity),
        Err(error) => ParserArtifactIdentityStatus::Unavailable { reason: error.to_string() },
    }
}

fn record_parser_artifact_identity_binding(
    unsupported: &mut UnsupportedLedger,
    binary: &mut BinaryArtifactMetadata,
    parser_identity: Option<&ParserArtifactIdentityStatus>,
) {
    let Some(parser_identity) = parser_identity else {
        return;
    };

    let blockers = match parser_identity {
        ParserArtifactIdentityStatus::Parsed(identity) => {
            if binary.build_id.is_none() {
                binary.build_id = identity.loader_build_id.clone();
            }
            record_parser_digest_identity(identity, binary);
            parser_artifact_identity_blockers(identity, binary)
        }
        ParserArtifactIdentityStatus::Unavailable { reason } => {
            vec![format!("parser artifact identity unavailable: {reason}")]
        }
    };

    if blockers.is_empty() {
        return;
    }

    unsupported.records.push(unsupported_record(
        PARSER_ARTIFACT_IDENTITY_STAGE,
        Some(&binary.architecture),
        None,
        None,
        &format!("parser artifact identity is not proof-grade bindable: {}", blockers.join("; ")),
    ));
}

fn record_parser_digest_identity(
    identity: &BinaryArtifactIdentity,
    binary: &mut BinaryArtifactMetadata,
) {
    if binary.byte_len.is_none() {
        binary.byte_len = Some(identity.artifact_size);
    }
    if binary.root_artifact_digest.is_none() {
        binary.root_artifact_digest = Some(BinaryArtifactDigest {
            algorithm: identity.artifact.algorithm.clone(),
            value: identity.artifact.value.clone(),
        });
    }
    if binary.selected_image.is_none() {
        binary.selected_image = Some(BinarySelectedImageIdentity {
            file_offset: identity.selected_image.file_offset,
            file_size: identity.selected_image.file_size,
            sha256: identity.selected_image.sha256.clone(),
        });
    }
}

fn parser_artifact_identity_blockers(
    identity: &BinaryArtifactIdentity,
    binary: &BinaryArtifactMetadata,
) -> Vec<String> {
    let mut blockers = identity.proof_grade_identity_blockers();

    match binary_artifact_format_identity_tag(binary.format) {
        Some(format) if format == identity.format => {}
        Some(format) => blockers.push(format!(
            "parser identity format `{}` does not match lifted binary format `{format}`",
            identity.format
        )),
        None => blockers.push("lifted binary format is not parser-identity bindable".to_string()),
    }

    let lifted_architecture = binary_artifact_architecture_identity_tag(&binary.architecture);
    if !binary_artifact_architecture_identity_tag_allows_proof_grade(&identity.architecture) {
        blockers.push("parser identity architecture is not proof-grade bindable".to_string());
    }
    if identity.architecture != lifted_architecture {
        blockers.push(format!(
            "parser identity architecture `{}` does not match lifted binary architecture `{lifted_architecture}`",
            identity.architecture
        ));
    }

    if identity.loader_build_id.as_deref() != binary.build_id.as_deref() {
        blockers
            .push("parser loader identity does not match decompiled artifact metadata".to_string());
    }

    if binary.byte_len != Some(identity.artifact_size) {
        blockers.push("parser root artifact byte length does not match metadata".to_string());
    }

    let parser_root_digest = BinaryArtifactDigest {
        algorithm: identity.artifact.algorithm.clone(),
        value: identity.artifact.value.clone(),
    };
    if binary.root_artifact_digest.as_ref() != Some(&parser_root_digest) {
        blockers.push("parser root artifact digest does not match metadata".to_string());
    }

    let parser_selected_image = BinarySelectedImageIdentity {
        file_offset: identity.selected_image.file_offset,
        file_size: identity.selected_image.file_size,
        sha256: identity.selected_image.sha256.clone(),
    };
    if binary.selected_image.as_ref() != Some(&parser_selected_image) {
        blockers.push("parser selected image digest/range does not match metadata".to_string());
    }

    blockers.extend(binary.digest_identity_blockers());

    blockers
}

fn binary_artifact_format_identity_tag(format: BinaryArtifactFormat) -> Option<&'static str> {
    match format {
        BinaryArtifactFormat::Elf => Some("elf"),
        BinaryArtifactFormat::MachO => Some("macho"),
        BinaryArtifactFormat::FatMachO => Some("fat-macho"),
        BinaryArtifactFormat::Pe => Some("pe-coff"),
        BinaryArtifactFormat::Wasm | BinaryArtifactFormat::Raw | BinaryArtifactFormat::Unknown => {
            None
        }
        _ => None,
    }
}

fn binary_artifact_architecture_identity_tag(architecture: &str) -> String {
    match architecture.trim() {
        "AArch64" | "aarch64" => "aarch64".to_string(),
        "x86-64" | "x86_64" => "x86_64".to_string(),
        "ARM" | "arm" => "arm".to_string(),
        other => other.to_ascii_lowercase().replace('-', "_"),
    }
}

fn binary_artifact_architecture_identity_tag_allows_proof_grade(architecture: &str) -> bool {
    let architecture = architecture.trim();
    !architecture.is_empty() && architecture != "unknown"
}

fn artifact_source_provenance_allows_binary_proof_grade(artifact: &DecompilationArtifact) -> bool {
    source_provenance_allows_artifact_proof_grade(&artifact.source_provenance)
        && artifact_binary_identity_allows_binary_proof_grade(artifact)
        && dispatches_have_accepted_source_provenance(
            &artifact.verification.solver_dispatch,
            &artifact.functions,
            &artifact.binary,
        )
        && artifact.functions.iter().all(|function| {
            dispatches_have_accepted_source_provenance(
                &function.verification.solver_dispatch,
                &artifact.functions,
                &artifact.binary,
            )
        })
}

fn refresh_source_backpropagation_authority(artifact: &mut DecompilationArtifact) {
    let blockers = source_rewrite_authority_blockers(artifact);
    let allowed = blockers.is_empty();
    artifact.source_provenance.source_backpropagation_allowed = allowed;

    let mut diagnostics = source_authority_base_diagnostics(&artifact.source_provenance);
    diagnostics.push(format!("{SOURCE_BACKPROPAGATION_ALLOWED_DIAGNOSTIC_PREFIX}{allowed}"));
    diagnostics
        .push(format!("{EFFECTIVE_SOURCE_BACKPROPAGATION_ALLOWED_DIAGNOSTIC_PREFIX}{allowed}"));
    diagnostics.extend(
        blockers
            .into_iter()
            .map(|blocker| format!("{SOURCE_REWRITE_AUTHORITY_BLOCKER_PREFIX}{blocker}")),
    );
    artifact.source_provenance.diagnostics = diagnostics;
}

fn source_authority_base_diagnostics(
    source_provenance: &BinarySourceProvenanceSummary,
) -> Vec<String> {
    source_provenance
        .diagnostics
        .iter()
        .filter(|diagnostic| {
            !diagnostic.starts_with(SOURCE_BACKPROPAGATION_ALLOWED_DIAGNOSTIC_PREFIX)
                && !diagnostic
                    .starts_with(EFFECTIVE_SOURCE_BACKPROPAGATION_ALLOWED_DIAGNOSTIC_PREFIX)
                && !diagnostic.starts_with(SOURCE_REWRITE_AUTHORITY_BLOCKER_PREFIX)
        })
        .cloned()
        .collect()
}

fn source_rewrite_authority_blockers(artifact: &DecompilationArtifact) -> Vec<String> {
    let dispatches = artifact_binary_solver_dispatches(artifact);
    let mut blockers = Vec::new();

    if !source_provenance_has_exact_source_ownership(&artifact.source_provenance) {
        blockers.push("exact source ownership not accepted".to_string());
    }
    if !artifact.binary.digest_identity_allows_proof_grade() {
        blockers.push("decompile artifact digest identity not accepted".to_string());
    } else if !binary_artifact_metadata_identity_allows_proof_grade(&artifact.binary) {
        blockers.push("decompile artifact metadata identity not accepted".to_string());
    }
    if !artifact_dispatches_have_accepted_source_ownership(artifact, &dispatches) {
        blockers.push("binary proof origins do not match exact source ownership".to_string());
    }
    let type_fact_source_blockers = artifact.type_fact_source_backpropagation_blockers();
    if !type_fact_source_blockers.is_empty() {
        blockers.push(format!(
            "type fact source ownership not accepted: {}",
            type_fact_source_blockers.join("; ")
        ));
    }
    if !artifact_dispatches_have_checked_certificate_identity(&dispatches) {
        blockers.push("checked certificate identity not accepted".to_string());
    }
    if !artifact_dispatches_have_replay_byte_range_identity(&dispatches, &artifact.binary) {
        blockers.push("replay byte/range identity not accepted".to_string());
    }
    if artifact.reconstruction.validation != ReconstructionValidationStatus::Validated {
        blockers.push("reconstruction validation not accepted".to_string());
    }
    if reconstruction_has_target_validation_blockers(&artifact.reconstruction)
        || !reconstruction_target_consumer_accepted_by_proof_model(&artifact.reconstruction)
    {
        blockers.push("target proof consumer acceptance not accepted".to_string());
    }
    if !reconstruction_symbolic_formulas_consumed_by_proof_model(&artifact.reconstruction) {
        blockers.push("symbolic formula consumer acceptance not accepted".to_string());
    }
    if !reconstruction_outputs_carry_binary_artifact_digest_identity(
        &artifact.reconstruction,
        &artifact.binary,
    ) {
        blockers.push("reconstruction binary artifact identity not accepted".to_string());
    }
    if !rust_compile_back_artifact_digest_bindings_allow_source_backpropagation(artifact) {
        blockers.push("Rust compile-back artifact digest binding not accepted".to_string());
    }

    blockers
}

fn rust_compile_back_artifact_digest_bindings_allow_source_backpropagation(
    artifact: &DecompilationArtifact,
) -> bool {
    if artifact.reconstruction.target != DecompileTarget::Rust {
        return true;
    }

    let Some(validated) = artifact.reconstruction.validated_rust.as_ref() else {
        return false;
    };
    let rust_outputs: Vec<_> = artifact
        .reconstruction
        .outputs
        .iter()
        .filter(|output| output.target == DecompileTarget::Rust)
        .collect();

    !rust_outputs.is_empty()
        && !validated.validation_records.is_empty()
        && validated.validation_records.iter().all(|record| {
            rust_outputs.iter().any(|output| {
                rust_compile_back_record_has_bound_artifact_digests(record, output, artifact)
            })
        })
        && rust_outputs.iter().all(|output| {
            !output.validation_records.is_empty()
                && output.validation_records.iter().all(|record| {
                    rust_compile_back_record_has_bound_artifact_digests(record, output, artifact)
                })
                && output.validated_rust.as_ref().is_some_and(|validated| {
                    !validated.validation_records.is_empty()
                        && validated.validation_records.iter().all(|record| {
                            rust_compile_back_record_has_bound_artifact_digests(
                                record, output, artifact,
                            )
                        })
                })
        })
}

fn artifact_binary_solver_dispatches(
    artifact: &DecompilationArtifact,
) -> Vec<&SolverDispatchRecord> {
    artifact
        .verification
        .solver_dispatch
        .iter()
        .chain(
            artifact
                .functions
                .iter()
                .flat_map(|function| function.verification.solver_dispatch.iter()),
        )
        .collect()
}

fn artifact_dispatches_have_accepted_source_ownership(
    artifact: &DecompilationArtifact,
    dispatches: &[&SolverDispatchRecord],
) -> bool {
    !dispatches.is_empty()
        && dispatches.iter().all(|dispatch| {
            dispatch_has_accepted_source_provenance(dispatch, &artifact.functions, &artifact.binary)
        })
}

fn artifact_dispatches_have_checked_certificate_identity(
    dispatches: &[&SolverDispatchRecord],
) -> bool {
    !dispatches.is_empty()
        && dispatches
            .iter()
            .all(|dispatch| checked_certificate_has_bridge_metadata(&dispatch.certificate))
}

fn artifact_dispatches_have_replay_byte_range_identity(
    dispatches: &[&SolverDispatchRecord],
    binary: &BinaryArtifactMetadata,
) -> bool {
    !dispatches.is_empty()
        && dispatches.iter().all(|dispatch| {
            binary_dispatch_satisfies_release_replay_semantics(dispatch)
                && dispatch_binary_artifact_digest_identity_matches_metadata(dispatch, binary)
                && dispatch
                    .origin
                    .as_ref()
                    .is_some_and(binary_origin_has_exact_instruction_provenance)
        })
}

fn artifact_binary_identity_allows_binary_proof_grade(artifact: &DecompilationArtifact) -> bool {
    binary_artifact_metadata_identity_allows_proof_grade(&artifact.binary)
        && artifact.verification.solver_dispatch.iter().all(|dispatch| {
            dispatch_binary_origin_matches_artifact_identity(dispatch, &artifact.binary)
                && dispatch_binary_artifact_digest_identity_matches_metadata(
                    dispatch,
                    &artifact.binary,
                )
        })
        && artifact.functions.iter().all(|function| {
            function_binary_origins_match_artifact_identity(function, &artifact.binary)
                && function.verification.solver_dispatch.iter().all(|dispatch| {
                    dispatch_binary_origin_matches_artifact_identity(dispatch, &artifact.binary)
                        && dispatch_binary_artifact_digest_identity_matches_metadata(
                            dispatch,
                            &artifact.binary,
                        )
                })
        })
}

fn binary_artifact_metadata_identity_allows_proof_grade(binary: &BinaryArtifactMetadata) -> bool {
    let architecture = binary_artifact_architecture_identity_tag(&binary.architecture);
    binary_artifact_format_identity_tag(binary.format).is_some()
        && binary_artifact_architecture_identity_tag_allows_proof_grade(&architecture)
        && binary.byte_len.is_some_and(|byte_len| byte_len > 0)
        && binary.path.as_deref().is_none_or(|path| !path.trim().is_empty())
        && binary.build_id.as_deref().is_some_and(|build_id| !build_id.trim().is_empty())
        && binary.digest_identity_allows_proof_grade()
}

fn function_binary_origins_match_artifact_identity(
    function: &DecompiledFunction,
    binary: &BinaryArtifactMetadata,
) -> bool {
    function
        .origin
        .as_ref()
        .is_none_or(|origin| binary_origin_matches_artifact_identity(origin, binary))
        && function
            .instruction_provenance
            .iter()
            .all(|origin| binary_origin_matches_artifact_identity(origin, binary))
}

fn dispatch_binary_origin_matches_artifact_identity(
    dispatch: &SolverDispatchRecord,
    binary: &BinaryArtifactMetadata,
) -> bool {
    dispatch
        .origin
        .as_ref()
        .is_some_and(|origin| binary_origin_matches_artifact_identity(origin, binary))
}

fn dispatch_binary_artifact_digest_identity_matches_metadata(
    dispatch: &SolverDispatchRecord,
    binary: &BinaryArtifactMetadata,
) -> bool {
    let Some(identity) = dispatch.binary_artifact_digest_identity.as_ref() else {
        return false;
    };

    identity.digest_identity_allows_replay()
        && identity.root_artifact_digest == binary.root_artifact_digest
        && identity.selected_image == binary.selected_image
}

fn binary_origin_matches_artifact_identity(
    origin: &BinaryOrigin,
    binary: &BinaryArtifactMetadata,
) -> bool {
    let Some(path) = binary.path.as_deref().map(str::trim).filter(|path| !path.is_empty()) else {
        return true;
    };

    origin.binary_path.as_deref() == Some(path)
}

fn reconstruction_allows_artifact_proof_grade(reconstruction: &ReconstructionSummary) -> bool {
    if reconstruction.validation != ReconstructionValidationStatus::Validated {
        return false;
    }
    if reconstruction_has_target_validation_blockers(reconstruction) {
        return false;
    }
    if !reconstruction_target_consumer_accepted_by_proof_model(reconstruction) {
        return false;
    }
    if !reconstruction_symbolic_formulas_consumed_by_proof_model(reconstruction) {
        return false;
    }

    match reconstruction.target {
        DecompileTarget::TrustIr => reconstruction.outputs.iter().any(|output| {
            output.target == DecompileTarget::TrustIr
                && output.validation == ReconstructionValidationStatus::Validated
        }),
        DecompileTarget::Rust => reconstruction.validated_rust.as_ref().is_some_and(|validated| {
            validated_rust_reconstruction_allows_artifact_proof_grade(validated)
                && rust_reconstruction_outputs_allow_artifact_proof_grade(reconstruction, validated)
        }),
        _ => false,
    }
}

fn reconstruction_allows_binary_proof_grade(
    reconstruction: &ReconstructionSummary,
    binary: &BinaryArtifactMetadata,
) -> bool {
    reconstruction_allows_artifact_proof_grade(reconstruction)
        && reconstruction_outputs_carry_binary_artifact_digest_identity(reconstruction, binary)
        && rust_reconstruction_outputs_carry_compile_back_artifact_digest_identity(
            reconstruction,
            binary,
        )
}

fn reconstruction_outputs_carry_binary_artifact_digest_identity(
    reconstruction: &ReconstructionSummary,
    binary: &BinaryArtifactMetadata,
) -> bool {
    let Some(identity) = BinaryArtifactDigestIdentity::from_metadata(binary) else {
        return false;
    };
    if !identity.digest_identity_allows_replay() {
        return false;
    }
    let Some(expected) = binary_artifact_digest_identity_assumption(&identity) else {
        return false;
    };

    !reconstruction.outputs.is_empty()
        && reconstruction
            .outputs
            .iter()
            .all(|output| output.assumptions.iter().any(|assumption| assumption == &expected))
}

fn rust_reconstruction_outputs_allow_artifact_proof_grade(
    reconstruction: &ReconstructionSummary,
    validated: &ValidatedRustReconstruction,
) -> bool {
    let rust_outputs: Vec<_> = reconstruction
        .outputs
        .iter()
        .filter(|output| output.target == DecompileTarget::Rust)
        .collect();
    !rust_outputs.is_empty()
        && rust_outputs
            .into_iter()
            .all(|output| rust_reconstruction_output_allows_artifact_proof_grade(output, validated))
}

fn rust_reconstruction_output_allows_artifact_proof_grade(
    output: &DecompiledOutput,
    validated: &ValidatedRustReconstruction,
) -> bool {
    output.validation == ReconstructionValidationStatus::Validated
        && output.trust_level == TrustLevel::ProofGrade
        && output.target_validation_blockers.is_empty()
        && output
            .validated_rust
            .as_ref()
            .is_some_and(|output_validated| output_validated == validated)
        && !output.validation_records.is_empty()
        && output.validation_records.iter().all(rust_compile_back_record_allows_proof_grade)
}

fn rust_reconstruction_source_rewrite_authority_allows_proof_grade(
    artifact: &DecompilationArtifact,
) -> bool {
    artifact.reconstruction.target != DecompileTarget::Rust
        || (artifact.source_provenance.source_backpropagation_allowed
            && artifact.source_provenance.effective_source_backpropagation_allowed()
            && artifact
                .source_provenance
                .diagnostics
                .iter()
                .all(|diagnostic| !diagnostic.starts_with(SOURCE_REWRITE_AUTHORITY_BLOCKER_PREFIX)))
}

fn reconstruction_has_target_validation_blockers(reconstruction: &ReconstructionSummary) -> bool {
    reconstruction.outputs.iter().any(|output| {
        output.target == reconstruction.target && !output.target_validation_blockers.is_empty()
    })
}

fn reconstruction_target_consumer_accepted_by_proof_model(
    reconstruction: &ReconstructionSummary,
) -> bool {
    let claimed_outputs = reconstruction_claimed_target_outputs(reconstruction);
    !claimed_outputs.is_empty()
        && claimed_outputs.iter().all(|output| {
            output.validation == ReconstructionValidationStatus::Validated
                && output.target_validation_blockers.is_empty()
                && output_target_consumer_accepted_by_proof_model(output)
        })
}

fn reconstruction_claimed_target_outputs(
    reconstruction: &ReconstructionSummary,
) -> Vec<&DecompiledOutput> {
    reconstruction
        .outputs
        .iter()
        .filter(|output| {
            output.target == reconstruction.target
                || target_requires_structured_target_consumer_artifact(&output.target)
        })
        .collect()
}

fn output_target_consumer_accepted_by_proof_model(output: &DecompiledOutput) -> bool {
    let artifact_diagnostics_seen = output.diagnostics.iter().any(|diagnostic| {
        diagnostic.starts_with(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
    });
    let artifact_records = target_proof_consumer_artifact_digest_records(output);
    if target_requires_structured_target_consumer_artifact(&output.target)
        || artifact_diagnostics_seen
    {
        return artifact_diagnostics_seen
            && !artifact_records.is_empty()
            && artifact_records.iter().all(|record| {
                target_proof_consumer_artifact_digest_accepted_for_output(output, record)
            });
    }

    output.diagnostics.iter().any(|diagnostic| target_consumer_acceptance_diagnostic(diagnostic))
}

fn target_requires_structured_target_consumer_artifact(target: &DecompileTarget) -> bool {
    matches!(target, DecompileTarget::Rust | DecompileTarget::TrustCg | DecompileTarget::Wasm)
}

fn target_proof_consumer_artifact_digest_records(
    output: &DecompiledOutput,
) -> Vec<TargetProofConsumerArtifactDigest> {
    output
        .diagnostics
        .iter()
        .filter_map(|diagnostic| {
            diagnostic.strip_prefix(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
        })
        .filter_map(|json| serde_json::from_str(json).ok())
        .collect()
}

fn target_proof_consumer_artifact_digest_accepted_for_output(
    output: &DecompiledOutput,
    record: &TargetProofConsumerArtifactDigest,
) -> bool {
    record.schema == TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_SCHEMA
        && record.target == decompile_target_consumer_label(&output.target)
        && record.status == "accepted"
        && record.target_semantics_consumed
        && record.artifact_digest.is_canonical_sha256()
        && target_proof_consumer_artifact_digest_matches_material(record)
        && record.lifted_trust_ir_artifact.digest.is_canonical_sha256()
        && record
            .binary_artifact_digest_identity
            .as_ref()
            .is_some_and(BinaryArtifactDigestIdentity::digest_identity_allows_replay)
        && !record.binary_origins.is_empty()
        && target_proof_consumer_evidence_artifacts_accepted_for_record(record)
        && target_proof_consumer_accepted_kind(record, "target_semantics")
        && target_proof_consumer_accepted_kind(record, "binary_provenance")
        && target_proof_consumer_accepted_evidence_kind(record, "binary_provenance")
        && target_proof_consumer_accepted_kind(record, "checked_certificate")
        && target_proof_consumer_accepted_evidence_kind(record, "checked_certificate")
        && target_proof_consumer_accepted_kind(record, "proof_replay")
        && target_proof_consumer_accepted_evidence_kind(record, "proof_replay")
        && target_proof_consumer_accepted_kind(record, "unsupported_ledger")
        && target_proof_consumer_accepted_evidence_kind(record, "unsupported_ledger")
        && target_proof_consumer_has_empty_unsupported_ledger_evidence(record)
        && target_proof_consumer_accepted_kind(record, "target_refinement")
        && target_proof_consumer_accepted_evidence_kind(record, "target_refinement")
        && record.refinement_metadata_evidence_count > 0
        && record.refinement_metadata_consumed
        && target_proof_consumer_formula_evidence_covers_output(record, output)
        && target_proof_consumer_target_specific_evidence_covers_output(record, output)
}

fn target_proof_consumer_has_empty_unsupported_ledger_evidence(
    record: &TargetProofConsumerArtifactDigest,
) -> bool {
    !record.unsupported_ledger_evidence.is_empty()
        && record.unsupported_ledger_evidence.iter().all(|ledger| {
            ledger.accepted
                && ledger.unsupported_records == 0
                && ledger.verification_unsupported == 0
                && ledger.unsupported_ledger_eliminated
        })
}

fn target_proof_consumer_accepted_kind(
    record: &TargetProofConsumerArtifactDigest,
    kind: &str,
) -> bool {
    record.accepted_record_kinds.iter().any(|entry| entry == kind)
}

fn target_proof_consumer_accepted_evidence_kind(
    record: &TargetProofConsumerArtifactDigest,
    kind: &str,
) -> bool {
    record.evidence_artifacts.iter().any(|artifact| {
        artifact.kind == kind
            && target_proof_consumer_evidence_artifact_accepted_for_record(record, artifact)
    })
}

fn target_proof_consumer_evidence_artifacts_accepted_for_record(
    record: &TargetProofConsumerArtifactDigest,
) -> bool {
    !record.evidence_artifacts.is_empty()
        && record.evidence_artifacts.iter().all(|artifact| {
            target_proof_consumer_evidence_artifact_accepted_for_record(record, artifact)
        })
}

fn target_proof_consumer_evidence_artifact_accepted_for_record(
    record: &TargetProofConsumerArtifactDigest,
    artifact: &TargetProofConsumerEvidenceArtifactDigest,
) -> bool {
    artifact.schema == TARGET_PROOF_CONSUMER_EVIDENCE_ARTIFACT_DIGEST_SCHEMA
        && artifact.target == record.target
        && artifact.target_output == record.target_output
        && artifact.consumed_by_target_semantics
        && artifact.digest.is_canonical_sha256()
        && target_proof_consumer_evidence_artifact_digest_matches_material(artifact)
}

fn target_proof_consumer_evidence_artifact_digest_matches_material(
    artifact: &TargetProofConsumerEvidenceArtifactDigest,
) -> bool {
    target_proof_consumer_evidence_artifact_digest(
        &TargetProofConsumerEvidenceArtifactDigestMaterial::from_record(artifact),
    )
    .is_some_and(|digest| digest == artifact.digest)
}

fn target_proof_consumer_formula_evidence_covers_output(
    record: &TargetProofConsumerArtifactDigest,
    output: &DecompiledOutput,
) -> bool {
    let formula_artifacts = record
        .evidence_artifacts
        .iter()
        .filter(|artifact| artifact.kind == "symbolic_formula")
        .collect::<Vec<_>>();
    if output.preserved_symbolic_formulas.is_empty() {
        return formula_artifacts.is_empty()
            && !target_proof_consumer_accepted_kind(record, "symbolic_formula");
    }
    if !target_proof_consumer_accepted_kind(record, "symbolic_formula")
        || !target_proof_consumer_accepted_evidence_kind(record, "symbolic_formula")
    {
        return false;
    }

    let expected = output
        .preserved_symbolic_formulas
        .iter()
        .map(|formula| {
            preserved_symbolic_formula_evidence_identifier(formula)
                .map(|identifier| (identifier, formula))
        })
        .collect::<Option<Vec<_>>>();
    let Some(expected) = expected else {
        return false;
    };
    if formula_artifacts.len() != expected.len() {
        return false;
    }

    let mut consumed = BTreeSet::new();
    for artifact in formula_artifacts {
        if !target_proof_consumer_evidence_artifact_accepted_for_record(record, artifact)
            || !consumed.insert(artifact.identifier.clone())
        {
            return false;
        }
        let Some((_, formula)) =
            expected.iter().find(|(identifier, _)| identifier == &artifact.identifier)
        else {
            return false;
        };
        if !target_proof_consumer_formula_evidence_matches_formula(artifact, formula) {
            return false;
        }
    }

    consumed.len() == expected.len()
}

fn target_proof_consumer_formula_evidence_matches_formula(
    artifact: &TargetProofConsumerEvidenceArtifactDigest,
    formula: &PreservedSymbolicFormula,
) -> bool {
    symbolic_formula_evidence_detail_matches_formula(&artifact.detail, formula)
}

fn target_proof_consumer_target_specific_evidence_covers_output(
    record: &TargetProofConsumerArtifactDigest,
    output: &DecompiledOutput,
) -> bool {
    match record.target.as_str() {
        "rust" => rust_target_proof_consumer_evidence_covers_output(record, output),
        _ => true,
    }
}

fn rust_target_proof_consumer_evidence_covers_output(
    record: &TargetProofConsumerArtifactDigest,
    output: &DecompiledOutput,
) -> bool {
    if output.target != DecompileTarget::Rust {
        return false;
    }
    if rust_target_output_identifier(output).as_deref() != Some(record.target_output.as_str()) {
        return false;
    }

    let Some(expected) = rust_expected_target_proof_consumer_evidence_artifacts(
        output,
        &record.target_output,
        &record.lifted_trust_ir_artifact,
        &record.binary_origins,
        &record.unsupported_ledger_evidence,
    ) else {
        return false;
    };

    target_proof_consumer_evidence_artifact_multiset_matches(
        record.evidence_artifacts.iter(),
        expected.iter(),
    )
}

fn target_proof_consumer_evidence_artifact_multiset_matches<'a, 'b>(
    actual: impl Iterator<Item = &'a TargetProofConsumerEvidenceArtifactDigest>,
    expected: impl Iterator<Item = &'b TargetProofConsumerEvidenceArtifactDigest>,
) -> bool {
    let Some(mut actual) =
        actual.map(|artifact| serde_json::to_string(artifact).ok()).collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    let Some(mut expected) =
        expected.map(|artifact| serde_json::to_string(artifact).ok()).collect::<Option<Vec<_>>>()
    else {
        return false;
    };

    actual.sort();
    expected.sort();
    actual == expected
}

fn target_proof_consumer_artifact_digest_matches_material(
    record: &TargetProofConsumerArtifactDigest,
) -> bool {
    target_proof_consumer_artifact_digest(&TargetProofConsumerArtifactDigestMaterial::from_record(
        record,
    ))
    .is_some_and(|digest| digest == record.artifact_digest)
}

fn reconstruction_symbolic_formulas_consumed_by_proof_model(
    reconstruction: &ReconstructionSummary,
) -> bool {
    reconstruction
        .outputs
        .iter()
        .filter(|output| output.target == reconstruction.target)
        .all(output_symbolic_formulas_consumed_by_proof_model)
}

fn output_symbolic_formulas_consumed_by_proof_model(output: &DecompiledOutput) -> bool {
    output.preserved_symbolic_formulas.iter().all(|formula| {
        output
            .diagnostics
            .iter()
            .any(|diagnostic| symbolic_formula_consumer_diagnostic_for_formula(diagnostic, formula))
    })
}

fn target_consumer_acceptance_diagnostic(diagnostic: &str) -> bool {
    diagnostic.starts_with(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
        || diagnostic.contains("target proof consumer accepted")
        || diagnostic.contains("target proof-consumer accepted")
        || diagnostic.contains("target-consumer=accepted")
}

fn decompile_target_consumer_label(target: &DecompileTarget) -> &'static str {
    match target {
        DecompileTarget::TrustCg => "trust-cg",
        DecompileTarget::Wasm => "wasm",
        DecompileTarget::TrustIr => "trust_ir",
        DecompileTarget::Rust => "rust",
        DecompileTarget::PseudoSource => "pseudo-source",
        DecompileTarget::Other(_) => "other",
        _ => "unknown",
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct TargetProofConsumerArtifactDigest {
    schema: String,
    target: String,
    status: String,
    target_semantics_consumed: bool,
    target_output: String,
    artifact_digest: BinaryArtifactDigest,
    lifted_trust_ir_artifact: TargetProofConsumerTrustIrArtifactDigest,
    binary_artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
    binary_origins: Vec<BinaryOrigin>,
    accepted_record_kinds: Vec<String>,
    unsupported_ledger_evidence: Vec<TargetProofConsumerUnsupportedLedgerEvidence>,
    evidence_artifacts: Vec<TargetProofConsumerEvidenceArtifactDigest>,
    refinement_metadata_evidence_count: usize,
    refinement_metadata_consumed: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct TargetProofConsumerArtifactDigestMaterial {
    schema: String,
    target: String,
    status: String,
    target_semantics_consumed: bool,
    target_output: String,
    lifted_trust_ir_artifact: TargetProofConsumerTrustIrArtifactDigest,
    binary_artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
    binary_origins: Vec<BinaryOrigin>,
    accepted_record_kinds: Vec<String>,
    unsupported_ledger_evidence: Vec<TargetProofConsumerUnsupportedLedgerEvidence>,
    evidence_artifacts: Vec<TargetProofConsumerEvidenceArtifactDigest>,
    refinement_metadata_evidence_count: usize,
    refinement_metadata_consumed: bool,
}

impl TargetProofConsumerArtifactDigestMaterial {
    fn from_record(record: &TargetProofConsumerArtifactDigest) -> Self {
        Self {
            schema: record.schema.clone(),
            target: record.target.clone(),
            status: record.status.clone(),
            target_semantics_consumed: record.target_semantics_consumed,
            target_output: record.target_output.clone(),
            lifted_trust_ir_artifact: record.lifted_trust_ir_artifact.clone(),
            binary_artifact_digest_identity: record.binary_artifact_digest_identity.clone(),
            binary_origins: record.binary_origins.clone(),
            accepted_record_kinds: record.accepted_record_kinds.clone(),
            unsupported_ledger_evidence: record.unsupported_ledger_evidence.clone(),
            evidence_artifacts: record.evidence_artifacts.clone(),
            refinement_metadata_evidence_count: record.refinement_metadata_evidence_count,
            refinement_metadata_consumed: record.refinement_metadata_consumed,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct TargetProofConsumerEvidenceArtifactDigest {
    schema: String,
    target: String,
    kind: String,
    identifier: String,
    canonical_source: String,
    target_output: String,
    consumed_by_target_semantics: bool,
    detail: String,
    digest: BinaryArtifactDigest,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct TargetProofConsumerEvidenceArtifactDigestMaterial {
    schema: String,
    target: String,
    kind: String,
    identifier: String,
    canonical_source: String,
    target_output: String,
    consumed_by_target_semantics: bool,
    detail: String,
}

impl TargetProofConsumerEvidenceArtifactDigestMaterial {
    fn from_record(record: &TargetProofConsumerEvidenceArtifactDigest) -> Self {
        Self {
            schema: record.schema.clone(),
            target: record.target.clone(),
            kind: record.kind.clone(),
            identifier: record.identifier.clone(),
            canonical_source: record.canonical_source.clone(),
            target_output: record.target_output.clone(),
            consumed_by_target_semantics: record.consumed_by_target_semantics,
            detail: record.detail.clone(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct TargetProofConsumerUnsupportedLedgerEvidence {
    identifier: String,
    accepted: bool,
    unsupported_records: usize,
    verification_unsupported: usize,
    unsupported_ledger_eliminated: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct TargetProofConsumerTrustIrArtifactDigest {
    function: Option<String>,
    def_path: Option<String>,
    digest: BinaryArtifactDigest,
}

fn target_proof_consumer_unsupported_ledger_evidence_from_records<'a, I>(
    records: I,
) -> Vec<TargetProofConsumerUnsupportedLedgerEvidence>
where
    I: IntoIterator<Item = (&'a str, &'a str, bool)>,
{
    records
        .into_iter()
        .filter_map(|(kind, identifier, accepted)| {
            target_proof_consumer_unsupported_ledger_evidence(kind, identifier, accepted)
        })
        .collect()
}

fn target_proof_consumer_unsupported_ledger_evidence(
    kind: &str,
    identifier: &str,
    accepted: bool,
) -> Option<TargetProofConsumerUnsupportedLedgerEvidence> {
    if kind != "unsupported_ledger" {
        return None;
    }

    Some(TargetProofConsumerUnsupportedLedgerEvidence {
        identifier: identifier.to_string(),
        accepted,
        unsupported_records: target_proof_consumer_unsupported_ledger_usize(
            identifier, "records=",
        )?,
        verification_unsupported: target_proof_consumer_unsupported_ledger_usize(
            identifier,
            "verification_unsupported=",
        )?,
        unsupported_ledger_eliminated: target_proof_consumer_unsupported_ledger_bool(
            identifier,
            "eliminated=",
        )?,
    })
}

fn target_proof_consumer_unsupported_ledger_usize(identifier: &str, prefix: &str) -> Option<usize> {
    identifier
        .split(':')
        .find_map(|part| part.strip_prefix(prefix))
        .and_then(|value| value.parse().ok())
}

fn target_proof_consumer_unsupported_ledger_bool(identifier: &str, prefix: &str) -> Option<bool> {
    identifier.split(':').find_map(|part| part.strip_prefix(prefix)).and_then(|value| match value {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    })
}

fn target_proof_consumer_artifact_digest(
    material: &TargetProofConsumerArtifactDigestMaterial,
) -> Option<BinaryArtifactDigest> {
    let bytes = serde_json::to_vec(material).ok()?;
    Some(BinaryArtifactDigest::sha256(stable_sha256_hex(&bytes)))
}

fn target_proof_consumer_evidence_artifact_digest(
    material: &TargetProofConsumerEvidenceArtifactDigestMaterial,
) -> Option<BinaryArtifactDigest> {
    let bytes = serde_json::to_vec(material).ok()?;
    Some(BinaryArtifactDigest::sha256(stable_sha256_hex(&bytes)))
}

fn target_proof_consumer_evidence_artifact(
    target: &str,
    kind: &str,
    identifier: &str,
    canonical_source: &str,
    target_output: &str,
    consumed_by_target_semantics: bool,
    detail: &str,
) -> Option<TargetProofConsumerEvidenceArtifactDigest> {
    let material = TargetProofConsumerEvidenceArtifactDigestMaterial {
        schema: TARGET_PROOF_CONSUMER_EVIDENCE_ARTIFACT_DIGEST_SCHEMA.to_string(),
        target: target.to_string(),
        kind: target_proof_consumer_evidence_kind(kind).to_string(),
        identifier: identifier.to_string(),
        canonical_source: canonical_source.to_string(),
        target_output: target_output.to_string(),
        consumed_by_target_semantics,
        detail: detail.to_string(),
    };
    let digest = target_proof_consumer_evidence_artifact_digest(&material)?;
    Some(TargetProofConsumerEvidenceArtifactDigest {
        schema: material.schema,
        target: material.target,
        kind: material.kind,
        identifier: material.identifier,
        canonical_source: material.canonical_source,
        target_output: material.target_output,
        consumed_by_target_semantics: material.consumed_by_target_semantics,
        detail: material.detail,
        digest,
    })
}

fn target_proof_consumer_evidence_kind(kind: &str) -> &str {
    match kind {
        "canonical_trust_ir_formula" => "symbolic_formula",
        other => other,
    }
}

fn target_proof_consumer_evidence_artifact_detail(
    kind: &str,
    identifier: &str,
    target_output: &str,
    detail: &str,
    preserved_formulas: &[PreservedSymbolicFormula],
) -> Option<String> {
    if target_proof_consumer_evidence_kind(kind) != "symbolic_formula" {
        return Some(detail.to_string());
    }

    let formula = preserved_formulas.iter().find(|formula| {
        preserved_symbolic_formula_evidence_identifier(formula).as_deref() == Some(identifier)
    })?;
    target_proof_consumer_symbolic_formula_evidence_detail(formula, target_output)
}

fn preserved_symbolic_formula_evidence_identifier(
    formula: &PreservedSymbolicFormula,
) -> Option<String> {
    Some(format!(
        "{}::bb{}::stmt{}::{}",
        formula.function.as_deref()?,
        formula.block?,
        formula.statement_index?,
        formula.location
    ))
}

fn target_proof_consumer_artifact_digest_diagnostic(
    artifact: &TargetProofConsumerArtifactDigest,
) -> Option<String> {
    let json = serde_json::to_string(artifact).ok()?;
    Some(format!("{TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX}{json}"))
}

fn lifted_trust_ir_artifact_digest(
    function: &DecompiledFunction,
) -> Option<TargetProofConsumerTrustIrArtifactDigest> {
    let lifted = function.lifted.as_ref()?;
    let bytes = serde_json::to_vec(lifted).ok()?;
    Some(TargetProofConsumerTrustIrArtifactDigest {
        function: Some(function.name.clone()),
        def_path: Some(lifted.def_path.clone()),
        digest: BinaryArtifactDigest::sha256(stable_sha256_hex(&bytes)),
    })
}

fn unique_binary_origins(mut origins: Vec<BinaryOrigin>) -> Vec<BinaryOrigin> {
    let mut unique = Vec::with_capacity(origins.len());
    for origin in origins.drain(..) {
        if !unique.iter().any(|existing| existing == &origin) {
            unique.push(origin);
        }
    }
    unique
}

fn function_binary_origins(function: &DecompiledFunction) -> Vec<BinaryOrigin> {
    let mut origins = function.instruction_provenance.clone();
    if let Some(origin) = function.origin.clone() {
        origins.push(origin);
    }
    unique_binary_origins(origins)
}

fn wasm_binary_origins(
    functions: &[DecompiledFunction],
    conversion: &WasmConversion,
) -> Vec<BinaryOrigin> {
    let mut origins =
        conversion.provenance_evidence.iter().map(|entry| entry.origin.clone()).collect::<Vec<_>>();
    for function in functions {
        origins.extend(function_binary_origins(function));
    }
    unique_binary_origins(origins)
}

fn wasm_proof_consumer_status_label(status: WasmProofConsumerStatus) -> &'static str {
    match status {
        WasmProofConsumerStatus::Accepted => "accepted",
        WasmProofConsumerStatus::Rejected => "rejected",
    }
}

fn wasm_lifted_trust_ir_artifact_digest(
    functions: &[DecompiledFunction],
    proof_consumer: &WasmProofConsumerEvidence,
) -> Option<TargetProofConsumerTrustIrArtifactDigest> {
    let mut source_functions = proof_consumer
        .refinement_metadata_evidence
        .iter()
        .filter(|entry| entry.bidirectional_refinement_consumed)
        .map(|entry| entry.source_function.as_str())
        .collect::<Vec<_>>();
    source_functions.sort_unstable();
    source_functions.dedup();

    let function = match source_functions.as_slice() {
        [source_function] => functions.iter().find(|function| {
            function.name.as_str() == *source_function
                || function
                    .lifted
                    .as_ref()
                    .is_some_and(|lifted| lifted.name.as_str() == *source_function)
        }),
        [] if functions.len() == 1 => functions.first(),
        _ => None,
    }?;

    lifted_trust_ir_artifact_digest(function)
}

fn wasm_target_proof_consumer_artifact_digest(
    metadata: &BinaryArtifactMetadata,
    functions: &[DecompiledFunction],
    conversion: &WasmConversion,
    proof_consumer: &WasmProofConsumerEvidence,
) -> Option<TargetProofConsumerArtifactDigest> {
    if proof_consumer.status != WasmProofConsumerStatus::Accepted
        || !proof_consumer.target_semantics_consumed
        || !proof_consumer.blockers.is_empty()
        || proof_consumer.binding.status != WasmProofConsumerStatus::Accepted
        || !proof_consumer.binding.target_semantics_consumed
        || proof_consumer.binding.target != proof_consumer.target
    {
        return None;
    }
    if !proof_consumer
        .records
        .iter()
        .any(|record| record.kind == "target_refinement" && record.accepted)
    {
        return None;
    }
    let refinement_metadata_consumed = !proof_consumer.refinement_metadata_evidence.is_empty()
        && proof_consumer.refinement_metadata_evidence.iter().all(|entry| {
            entry.bidirectional_refinement_consumed
                && entry.target == proof_consumer.target
                && entry.target_output == proof_consumer.binding.target_output
        });
    if !refinement_metadata_consumed {
        return None;
    }

    let identity = BinaryArtifactDigestIdentity::from_metadata(metadata)?;
    if !identity.digest_identity_allows_replay() {
        return None;
    }
    let lifted_trust_ir_artifact = wasm_lifted_trust_ir_artifact_digest(functions, proof_consumer)?;
    let binary_origins = wasm_binary_origins(functions, conversion);
    if binary_origins.is_empty() {
        return None;
    }
    let preserved_formula_evidence =
        wasm_preserved_symbolic_formulas(&conversion.symbolic_formulas);
    let evidence_artifacts = proof_consumer
        .binding
        .inputs
        .iter()
        .map(|input| {
            let detail = target_proof_consumer_evidence_artifact_detail(
                &input.kind,
                &input.identifier,
                &input.target_output,
                &input.detail,
                &preserved_formula_evidence,
            )?;
            target_proof_consumer_evidence_artifact(
                &proof_consumer.target,
                &input.kind,
                &input.identifier,
                &input.canonical_source,
                &input.target_output,
                input.consumed_by_target_semantics,
                &detail,
            )
        })
        .collect::<Option<Vec<_>>>()?;

    let material = TargetProofConsumerArtifactDigestMaterial {
        schema: TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_SCHEMA.to_string(),
        target: proof_consumer.target.clone(),
        status: wasm_proof_consumer_status_label(proof_consumer.status).to_string(),
        target_semantics_consumed: proof_consumer.target_semantics_consumed,
        target_output: proof_consumer.binding.target_output.clone(),
        lifted_trust_ir_artifact,
        binary_artifact_digest_identity: Some(identity),
        binary_origins,
        accepted_record_kinds: proof_consumer
            .records
            .iter()
            .filter(|record| record.accepted)
            .map(|record| record.kind.clone())
            .collect(),
        unsupported_ledger_evidence: target_proof_consumer_unsupported_ledger_evidence_from_records(
            proof_consumer
                .records
                .iter()
                .map(|record| (record.kind.as_str(), record.identifier.as_str(), record.accepted)),
        ),
        evidence_artifacts,
        refinement_metadata_evidence_count: proof_consumer.refinement_metadata_evidence.len(),
        refinement_metadata_consumed,
    };
    let artifact_digest = target_proof_consumer_artifact_digest(&material)?;

    Some(TargetProofConsumerArtifactDigest {
        schema: material.schema,
        target: material.target,
        status: material.status,
        target_semantics_consumed: material.target_semantics_consumed,
        target_output: material.target_output,
        artifact_digest,
        lifted_trust_ir_artifact: material.lifted_trust_ir_artifact,
        binary_artifact_digest_identity: material.binary_artifact_digest_identity,
        binary_origins: material.binary_origins,
        accepted_record_kinds: material.accepted_record_kinds,
        unsupported_ledger_evidence: material.unsupported_ledger_evidence,
        evidence_artifacts: material.evidence_artifacts,
        refinement_metadata_evidence_count: material.refinement_metadata_evidence_count,
        refinement_metadata_consumed: material.refinement_metadata_consumed,
    })
}

#[cfg(feature = "trust-cg")]
fn trust_cg_binary_origins(
    function: &DecompiledFunction,
    conversion: &BinaryTrustCgConversion,
) -> Vec<BinaryOrigin> {
    let mut origins =
        conversion.provenance_evidence.iter().map(|entry| entry.origin.clone()).collect::<Vec<_>>();
    origins.extend(function_binary_origins(function));
    unique_binary_origins(origins)
}

#[cfg(feature = "trust-cg")]
fn trust_cg_proof_consumer_status_label(status: BinaryTrustCgProofConsumerStatus) -> &'static str {
    match status {
        BinaryTrustCgProofConsumerStatus::Accepted => "accepted",
        BinaryTrustCgProofConsumerStatus::Rejected => "rejected",
    }
}

#[cfg(feature = "trust-cg")]
fn trust_cg_target_proof_consumer_artifact_digest(
    metadata: &BinaryArtifactMetadata,
    function: &DecompiledFunction,
    conversion: &BinaryTrustCgConversion,
    proof_consumer: &BinaryTrustCgProofConsumerEvidence,
) -> Option<TargetProofConsumerArtifactDigest> {
    if proof_consumer.status != BinaryTrustCgProofConsumerStatus::Accepted
        || !proof_consumer.target_semantics_consumed
        || !proof_consumer.blockers.is_empty()
    {
        return None;
    }
    if !proof_consumer
        .records
        .iter()
        .any(|record| record.kind == "target_refinement" && record.accepted)
    {
        return None;
    }
    let refinement_metadata_consumed = !proof_consumer.refinement_metadata_evidence.is_empty()
        && proof_consumer.refinement_metadata_evidence.iter().all(|entry| {
            entry.bidirectional_refinement_consumed
                && entry.bidirectional_consumption.bidirectional_refinement_consumed
        });
    if !refinement_metadata_consumed {
        return None;
    }

    let identity = BinaryArtifactDigestIdentity::from_metadata(metadata)?;
    if !identity.digest_identity_allows_replay() {
        return None;
    }
    let lifted_trust_ir_artifact = lifted_trust_ir_artifact_digest(function)?;
    let binary_origins = trust_cg_binary_origins(function, conversion);
    if binary_origins.is_empty() {
        return None;
    }
    let preserved_formula_evidence =
        trust_cg_preserved_symbolic_formulas(&conversion.symbolic_formulas);
    let evidence_artifacts = proof_consumer
        .binding
        .inputs
        .iter()
        .map(|input| {
            let detail = target_proof_consumer_evidence_artifact_detail(
                &input.kind,
                &input.identifier,
                &input.target_output,
                &input.detail,
                &preserved_formula_evidence,
            )?;
            target_proof_consumer_evidence_artifact(
                &proof_consumer.target,
                &input.kind,
                &input.identifier,
                &input.canonical_source,
                &input.target_output,
                input.consumed_by_target_semantics,
                &detail,
            )
        })
        .collect::<Option<Vec<_>>>()?;

    let material = TargetProofConsumerArtifactDigestMaterial {
        schema: TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_SCHEMA.to_string(),
        target: proof_consumer.target.clone(),
        status: trust_cg_proof_consumer_status_label(proof_consumer.status).to_string(),
        target_semantics_consumed: proof_consumer.target_semantics_consumed,
        target_output: proof_consumer.binding.target_output.clone(),
        lifted_trust_ir_artifact,
        binary_artifact_digest_identity: Some(identity),
        binary_origins,
        accepted_record_kinds: proof_consumer
            .records
            .iter()
            .filter(|record| record.accepted)
            .map(|record| record.kind.clone())
            .collect(),
        unsupported_ledger_evidence: target_proof_consumer_unsupported_ledger_evidence_from_records(
            proof_consumer
                .records
                .iter()
                .map(|record| (record.kind.as_str(), record.identifier.as_str(), record.accepted)),
        ),
        evidence_artifacts,
        refinement_metadata_evidence_count: proof_consumer.refinement_metadata_evidence.len(),
        refinement_metadata_consumed,
    };
    let artifact_digest = target_proof_consumer_artifact_digest(&material)?;

    Some(TargetProofConsumerArtifactDigest {
        schema: material.schema,
        target: material.target,
        status: material.status,
        target_semantics_consumed: material.target_semantics_consumed,
        target_output: material.target_output,
        artifact_digest,
        lifted_trust_ir_artifact: material.lifted_trust_ir_artifact,
        binary_artifact_digest_identity: material.binary_artifact_digest_identity,
        binary_origins: material.binary_origins,
        accepted_record_kinds: material.accepted_record_kinds,
        unsupported_ledger_evidence: material.unsupported_ledger_evidence,
        evidence_artifacts: material.evidence_artifacts,
        refinement_metadata_evidence_count: material.refinement_metadata_evidence_count,
        refinement_metadata_consumed: material.refinement_metadata_consumed,
    })
}

#[cfg(test)]
fn rust_target_proof_consumer_artifact_digest(
    metadata: &BinaryArtifactMetadata,
    functions: &[DecompiledFunction],
    output: &DecompiledOutput,
    unsupported_records: usize,
    verification_unsupported: usize,
) -> Option<TargetProofConsumerArtifactDigest> {
    if output.target != DecompileTarget::Rust
        || output.validation != ReconstructionValidationStatus::Validated
        || output.trust_level != TrustLevel::ProofGrade
        || !output.target_validation_blockers.is_empty()
        || unsupported_records != 0
        || verification_unsupported != 0
    {
        return None;
    }
    if !output
        .validated_rust
        .as_ref()
        .is_some_and(validated_rust_reconstruction_allows_artifact_proof_grade)
        || output.validation_records.is_empty()
        || !output.validation_records.iter().all(rust_compile_back_record_allows_proof_grade)
    {
        return None;
    }

    let identity = BinaryArtifactDigestIdentity::from_metadata(metadata)?;
    if !identity.digest_identity_allows_replay() {
        return None;
    }
    let target_output = rust_target_output_identifier(output)?;
    let lifted_trust_ir_artifact = rust_lifted_trust_ir_artifact_digest(functions, output)?;
    let binary_origins = rust_binary_origins(functions, output);
    if binary_origins.is_empty() {
        return None;
    }
    let unsupported_ledger_evidence = vec![TargetProofConsumerUnsupportedLedgerEvidence {
        identifier:
            "rust-compile-back.unsupported-ledger:records=0:verification_unsupported=0:eliminated=true"
                .to_string(),
        accepted: true,
        unsupported_records,
        verification_unsupported,
        unsupported_ledger_eliminated: true,
    }];
    let evidence_artifacts = rust_target_proof_consumer_evidence_artifacts(
        output,
        &target_output,
        &lifted_trust_ir_artifact,
        &binary_origins,
        &unsupported_ledger_evidence,
    );
    let expected_formula_evidence_count = output
        .preserved_symbolic_formulas
        .iter()
        .filter(|formula| preserved_symbolic_formula_evidence_identifier(formula).is_some())
        .count();
    let actual_formula_evidence_count =
        evidence_artifacts.iter().filter(|artifact| artifact.kind == "symbolic_formula").count();
    if expected_formula_evidence_count != output.preserved_symbolic_formulas.len()
        || actual_formula_evidence_count != expected_formula_evidence_count
    {
        return None;
    }

    let material = TargetProofConsumerArtifactDigestMaterial {
        schema: TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_SCHEMA.to_string(),
        target: "rust".to_string(),
        status: "accepted".to_string(),
        target_semantics_consumed: true,
        target_output,
        lifted_trust_ir_artifact,
        binary_artifact_digest_identity: Some(identity),
        binary_origins,
        accepted_record_kinds: rust_target_proof_consumer_accepted_record_kinds(output),
        unsupported_ledger_evidence,
        evidence_artifacts,
        refinement_metadata_evidence_count: rust_refinement_metadata_evidence_count(output),
        refinement_metadata_consumed: true,
    };
    if material.refinement_metadata_evidence_count == 0 {
        return None;
    }
    let artifact_digest = target_proof_consumer_artifact_digest(&material)?;

    Some(TargetProofConsumerArtifactDigest {
        schema: material.schema,
        target: material.target,
        status: material.status,
        target_semantics_consumed: material.target_semantics_consumed,
        target_output: material.target_output,
        artifact_digest,
        lifted_trust_ir_artifact: material.lifted_trust_ir_artifact,
        binary_artifact_digest_identity: material.binary_artifact_digest_identity,
        binary_origins: material.binary_origins,
        accepted_record_kinds: material.accepted_record_kinds,
        unsupported_ledger_evidence: material.unsupported_ledger_evidence,
        evidence_artifacts: material.evidence_artifacts,
        refinement_metadata_evidence_count: material.refinement_metadata_evidence_count,
        refinement_metadata_consumed: material.refinement_metadata_consumed,
    })
}

fn rust_target_output_identifier(output: &DecompiledOutput) -> Option<String> {
    let rust_source = output.text.as_deref()?;
    let mut functions = output
        .validation_records
        .iter()
        .filter(|record| record.target == DecompileTarget::Rust)
        .filter_map(|record| record.function.as_deref().or(record.lifted_function.as_deref()))
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    functions.sort();
    functions.dedup();
    let functions = if functions.is_empty() { "unknown".to_string() } else { functions.join("|") };
    Some(format!(
        "rust-strict-subset:sha256={}:functions={functions}",
        stable_sha256_hex(rust_source.as_bytes())
    ))
}

#[cfg(test)]
fn rust_lifted_trust_ir_artifact_digest(
    functions: &[DecompiledFunction],
    output: &DecompiledOutput,
) -> Option<TargetProofConsumerTrustIrArtifactDigest> {
    let wanted: BTreeSet<_> = output
        .validation_records
        .iter()
        .filter(|record| record.target == DecompileTarget::Rust)
        .filter_map(|record| record.lifted_function.as_deref().or(record.function.as_deref()))
        .map(ToString::to_string)
        .collect();
    let mut lifted = functions
        .iter()
        .filter(|function| {
            wanted.is_empty()
                || wanted.contains(&function.name)
                || function.lifted.as_ref().is_some_and(|lifted| {
                    wanted.contains(&lifted.name) || wanted.contains(&lifted.def_path)
                })
        })
        .filter_map(|function| function.lifted.as_ref())
        .collect::<Vec<_>>();
    lifted.sort_by(|left, right| {
        left.def_path.cmp(&right.def_path).then_with(|| left.name.cmp(&right.name))
    });
    if lifted.is_empty() {
        return None;
    }

    let bytes = serde_json::to_vec(&lifted).ok()?;
    let function = if lifted.len() == 1 {
        Some(lifted[0].name.clone())
    } else {
        Some(lifted.iter().map(|function| function.name.as_str()).collect::<Vec<_>>().join("|"))
    };
    let def_path = if lifted.len() == 1 {
        Some(lifted[0].def_path.clone())
    } else {
        Some(lifted.iter().map(|function| function.def_path.as_str()).collect::<Vec<_>>().join("|"))
    };
    Some(TargetProofConsumerTrustIrArtifactDigest {
        function,
        def_path,
        digest: BinaryArtifactDigest::sha256(stable_sha256_hex(&bytes)),
    })
}

#[cfg(test)]
fn rust_binary_origins(
    functions: &[DecompiledFunction],
    output: &DecompiledOutput,
) -> Vec<BinaryOrigin> {
    let wanted: BTreeSet<_> = output
        .validation_records
        .iter()
        .filter(|record| record.target == DecompileTarget::Rust)
        .filter_map(|record| record.function.as_deref().or(record.lifted_function.as_deref()))
        .map(ToString::to_string)
        .collect();
    let origins = functions
        .iter()
        .filter(|function| {
            wanted.is_empty()
                || wanted.contains(&function.name)
                || function.lifted.as_ref().is_some_and(|lifted| {
                    wanted.contains(&lifted.name) || wanted.contains(&lifted.def_path)
                })
        })
        .flat_map(function_binary_origins)
        .collect();
    unique_binary_origins(origins)
}

#[cfg(test)]
fn rust_target_proof_consumer_accepted_record_kinds(output: &DecompiledOutput) -> Vec<String> {
    let mut kinds = vec![
        "target_semantics".to_string(),
        "binary_provenance".to_string(),
        "checked_certificate".to_string(),
        "proof_replay".to_string(),
        "unsupported_ledger".to_string(),
        "target_refinement".to_string(),
    ];
    if !output.preserved_symbolic_formulas.is_empty() {
        kinds.push("symbolic_formula".to_string());
    }
    kinds
}

#[cfg(test)]
fn rust_target_proof_consumer_evidence_artifacts(
    output: &DecompiledOutput,
    target_output: &str,
    lifted_trust_ir_artifact: &TargetProofConsumerTrustIrArtifactDigest,
    binary_origins: &[BinaryOrigin],
    unsupported_ledger_evidence: &[TargetProofConsumerUnsupportedLedgerEvidence],
) -> Vec<TargetProofConsumerEvidenceArtifactDigest> {
    rust_expected_target_proof_consumer_evidence_artifacts(
        output,
        target_output,
        lifted_trust_ir_artifact,
        binary_origins,
        unsupported_ledger_evidence,
    )
    .unwrap_or_default()
}

fn rust_expected_target_proof_consumer_evidence_artifacts(
    output: &DecompiledOutput,
    target_output: &str,
    lifted_trust_ir_artifact: &TargetProofConsumerTrustIrArtifactDigest,
    binary_origins: &[BinaryOrigin],
    unsupported_ledger_evidence: &[TargetProofConsumerUnsupportedLedgerEvidence],
) -> Option<Vec<TargetProofConsumerEvidenceArtifactDigest>> {
    let mut artifacts = Vec::new();
    for origin in binary_origins {
        artifacts.push(target_proof_consumer_evidence_artifact(
            "rust",
            "binary_provenance",
            &rust_binary_origin_evidence_identifier(origin),
            "rust-compile-back.binary-origin",
            target_output,
            true,
            &serde_json::to_string(origin).ok()?,
        )?);
    }
    for ledger in unsupported_ledger_evidence {
        artifacts.push(target_proof_consumer_evidence_artifact(
            "rust",
            "unsupported_ledger",
            &ledger.identifier,
            "rust-compile-back.unsupported-ledger",
            target_output,
            ledger.accepted,
            &serde_json::to_string(ledger).ok()?,
        )?);
    }

    for record in output
        .validation_records
        .iter()
        .filter(|record| rust_compile_back_record_allows_proof_grade(record))
    {
        artifacts.extend(rust_compile_back_record_evidence_artifacts(
            record,
            target_output,
            lifted_trust_ir_artifact,
        ));
    }
    for formula in &output.preserved_symbolic_formulas {
        artifacts.push(target_proof_consumer_evidence_artifact(
            "rust",
            "symbolic_formula",
            &preserved_symbolic_formula_evidence_identifier(formula)?,
            SYMBOLIC_FORMULA_SCHEMA,
            target_output,
            true,
            &target_proof_consumer_symbolic_formula_evidence_detail(formula, target_output)?,
        )?);
    }
    Some(artifacts)
}

fn rust_binary_origin_evidence_identifier(origin: &BinaryOrigin) -> String {
    format!(
        "binary-origin:address=0x{:x}:size={}:bytes={}",
        origin.instruction_address,
        origin.instruction_size.unwrap_or(origin.instruction_bytes.len() as u8),
        stable_sha256_hex(&origin.instruction_bytes)
    )
}

fn rust_compile_back_record_evidence_artifacts(
    record: &ReconstructionValidationRecord,
    target_output: &str,
    lifted_trust_ir_artifact: &TargetProofConsumerTrustIrArtifactDigest,
) -> Vec<TargetProofConsumerEvidenceArtifactDigest> {
    let identifier = rust_compile_back_record_evidence_identifier(record);
    [
        (
            "checked_certificate",
            "rust-compile-back.checked-certificate",
            RUST_COMPILE_BACK_CHECKED_CERTIFICATE_BINDING_EVIDENCE,
        ),
        (
            "proof_replay",
            "rust-compile-back.replay-identity",
            RUST_COMPILE_BACK_REPLAY_IDENTITY_BINDING_EVIDENCE,
        ),
        (
            "target_refinement",
            "rust-compile-back.bidirectional-refinement",
            RUST_COMPILE_BACK_LIFTED_BINARY_TRUST_IR_BINDING_EVIDENCE,
        ),
    ]
    .into_iter()
    .filter(|(_, _, marker)| rust_compile_back_record_has_evidence(record, marker))
    .filter_map(|(kind, canonical_source, marker)| {
        let detail = rust_compile_back_evidence_artifact_detail(
            record,
            kind,
            target_output,
            lifted_trust_ir_artifact,
        )?;
        target_proof_consumer_evidence_artifact(
            "rust",
            kind,
            &format!("{identifier}:{marker}"),
            canonical_source,
            target_output,
            true,
            &detail,
        )
    })
    .collect()
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct RustCompileBackEvidenceArtifactDetail {
    schema: String,
    kind: String,
    target_output: String,
    lifted_trust_ir_artifact: TargetProofConsumerTrustIrArtifactDigest,
    record: ReconstructionValidationRecord,
    lifted_binary_trust_ir_sha256: String,
    rust_source_sha256: String,
    compile_back_trust_ir_sha256: String,
    refinement_artifact_sha256: String,
    root_artifact_sha256: String,
    selected_image_sha256: String,
    selected_image_range: String,
}

fn rust_compile_back_evidence_artifact_detail(
    record: &ReconstructionValidationRecord,
    kind: &str,
    target_output: &str,
    lifted_trust_ir_artifact: &TargetProofConsumerTrustIrArtifactDigest,
) -> Option<String> {
    let detail = RustCompileBackEvidenceArtifactDetail {
        schema: RUST_COMPILE_BACK_EVIDENCE_ARTIFACT_SCHEMA.to_string(),
        kind: kind.to_string(),
        target_output: target_output.to_string(),
        lifted_trust_ir_artifact: lifted_trust_ir_artifact.clone(),
        record: record.clone(),
        lifted_binary_trust_ir_sha256: rust_compile_back_record_evidence_value(
            record,
            RUST_COMPILE_BACK_LIFTED_BINARY_TRUST_IR_SHA256_EVIDENCE_PREFIX,
        )?,
        rust_source_sha256: rust_compile_back_record_evidence_value(
            record,
            RUST_COMPILE_BACK_RUST_SOURCE_SHA256_EVIDENCE_PREFIX,
        )?,
        compile_back_trust_ir_sha256: rust_compile_back_record_evidence_value(
            record,
            RUST_COMPILE_BACK_RECONSTRUCTED_TRUST_IR_SHA256_EVIDENCE_PREFIX,
        )?,
        refinement_artifact_sha256: rust_compile_back_record_evidence_value(
            record,
            RUST_COMPILE_BACK_REFINEMENT_ARTIFACT_SHA256_EVIDENCE_PREFIX,
        )?,
        root_artifact_sha256: rust_compile_back_record_evidence_value(
            record,
            RUST_COMPILE_BACK_ROOT_ARTIFACT_SHA256_EVIDENCE_PREFIX,
        )?,
        selected_image_sha256: rust_compile_back_record_evidence_value(
            record,
            RUST_COMPILE_BACK_SELECTED_IMAGE_SHA256_EVIDENCE_PREFIX,
        )?,
        selected_image_range: rust_compile_back_record_evidence_value(
            record,
            RUST_COMPILE_BACK_SELECTED_IMAGE_RANGE_EVIDENCE_PREFIX,
        )?,
    };

    serde_json::to_string(&detail).ok()
}

fn rust_compile_back_record_evidence_value(
    record: &ReconstructionValidationRecord,
    prefix: &str,
) -> Option<String> {
    let value = record_other_evidence_value(record, prefix)?;
    Some(value.to_string())
}

fn rust_compile_back_record_evidence_identifier(record: &ReconstructionValidationRecord) -> String {
    let lifted = record.lifted_function.as_deref().unwrap_or("unknown-lifted");
    let reconstructed = record.reconstructed_function.as_deref().unwrap_or("unknown-reconstructed");
    let refinement = record_other_evidence_value(
        record,
        RUST_COMPILE_BACK_REFINEMENT_ARTIFACT_SHA256_EVIDENCE_PREFIX,
    )
    .unwrap_or("no-refinement-digest");
    format!("rust-compile-back:{lifted}->{reconstructed}:refinement={refinement}")
}

fn target_proof_consumer_symbolic_formula_evidence_detail(
    formula: &PreservedSymbolicFormula,
    target_output: &str,
) -> Option<String> {
    let formula_json = serde_json::to_string(&formula.formula).ok()?;
    let evidence = formula.evidence();
    let identifier = preserved_symbolic_formula_evidence_identifier(formula)?;
    Some(format!(
        "symbolic-formula-proof-consumer=accepted;trust_symbolic.formula=consumed;formula.identifier={};formula.schema={};formula.digest=sha256:{};formula.origin={};formula_json={};formula.smtlib2={};formula.sort={};function={};block={};statement_index={};location={};target_output={};formula.target_semantics_consumed=true",
        identifier,
        evidence.schema,
        evidence.digest,
        evidence.origin,
        formula_json,
        formula.formula.to_smtlib(),
        evidence.sort,
        formula.function.as_deref().unwrap_or("unknown"),
        formula.block.map_or_else(|| "unknown".to_string(), |block| block.to_string()),
        formula
            .statement_index
            .map_or_else(|| "unknown".to_string(), |statement| statement.to_string()),
        formula.location,
        target_output
    ))
}

#[cfg(test)]
fn rust_refinement_metadata_evidence_count(output: &DecompiledOutput) -> usize {
    let output_records = output
        .validation_records
        .iter()
        .filter(|record| rust_compile_back_record_allows_proof_grade(record))
        .count();
    let validated_records = output
        .validated_rust
        .as_ref()
        .map(|validated| {
            validated
                .validation_records
                .iter()
                .filter(|record| rust_compile_back_record_allows_proof_grade(record))
                .count()
        })
        .unwrap_or_default();
    output_records.max(validated_records)
}

fn symbolic_formula_consumer_diagnostic(diagnostic: &str) -> bool {
    let accepted = diagnostic.contains("symbolic-formula-proof-consumer=accepted")
        || diagnostic.contains("trust_symbolic.formula=consumed")
        || diagnostic.contains("formula.target_semantics_consumed=true")
        || (target_consumer_acceptance_diagnostic(diagnostic)
            && diagnostic.contains("symbolic formula"));
    accepted && symbolic_formula_consumer_diagnostic_has_schema(diagnostic)
}

fn symbolic_formula_consumer_diagnostic_for_formula(
    diagnostic: &str,
    formula: &PreservedSymbolicFormula,
) -> bool {
    symbolic_formula_consumer_diagnostic(diagnostic)
        && formula.matches_schema_aware_consumer_diagnostic(diagnostic)
        && symbolic_formula_consumer_diagnostic_matches_payload(diagnostic, formula)
        && symbolic_formula_consumer_diagnostic_matches_location(diagnostic, formula)
}

fn symbolic_formula_evidence_detail_matches_formula(
    detail: &str,
    formula: &PreservedSymbolicFormula,
) -> bool {
    symbolic_formula_consumer_diagnostic_has_schema(detail)
        && formula.matches_schema_aware_consumer_diagnostic(detail)
        && symbolic_formula_consumer_diagnostic_matches_payload(detail, formula)
        && symbolic_formula_consumer_diagnostic_matches_location(detail, formula)
}

fn symbolic_formula_consumer_diagnostic_has_schema(diagnostic: &str) -> bool {
    symbolic_formula_consumer_diagnostic_has_token(
        diagnostic,
        "formula.schema",
        SYMBOLIC_FORMULA_SCHEMA,
    ) && (diagnostic.contains("formula_json=") || diagnostic.contains("formula_json=str:"))
        && (diagnostic.contains("formula.smtlib2=") || diagnostic.contains(" smtlib="))
        && (diagnostic.contains("formula.sort=") || diagnostic.contains(" sort="))
        && !diagnostic.contains("formula.schema_error=")
        && !diagnostic.contains("formula_schema_error=")
        && !diagnostic.contains("formula_json_error=")
}

fn symbolic_formula_consumer_diagnostic_matches_payload(
    diagnostic: &str,
    formula: &PreservedSymbolicFormula,
) -> bool {
    let Ok(formula_json) = serde_json::to_string(&formula.formula) else {
        return false;
    };
    let formula_smtlib = formula.formula.to_smtlib();
    let formula_sort = trust_types::infer_sort(&formula.formula).to_smtlib();

    symbolic_formula_consumer_diagnostic_has_token(diagnostic, "formula_json", &formula_json)
        && (symbolic_formula_consumer_diagnostic_has_token(
            diagnostic,
            "formula.smtlib2",
            &formula_smtlib,
        ) || symbolic_formula_consumer_diagnostic_has_space_token(
            diagnostic,
            "smtlib",
            &formula_smtlib,
        ))
        && (symbolic_formula_consumer_diagnostic_has_token(
            diagnostic,
            "formula.sort",
            &formula_sort,
        ) || symbolic_formula_consumer_diagnostic_has_space_token(
            diagnostic,
            "sort",
            &formula_sort,
        ))
}

fn symbolic_formula_consumer_diagnostic_matches_location(
    diagnostic: &str,
    formula: &PreservedSymbolicFormula,
) -> bool {
    let function_matches = formula.function.as_ref().is_none_or(|function| {
        symbolic_formula_consumer_diagnostic_has_token(diagnostic, "function", function)
            || diagnostic.contains(&format!("{function}::"))
    });
    let block_matches = formula.block.is_none_or(|block| {
        symbolic_formula_consumer_diagnostic_has_token(diagnostic, "block", &block.to_string())
            || diagnostic.contains(&format!("::bb{block}"))
    });
    let statement_matches = formula.statement_index.is_none_or(|statement_index| {
        symbolic_formula_consumer_diagnostic_has_token(
            diagnostic,
            "statement_index",
            &statement_index.to_string(),
        ) || diagnostic.contains(&format!("::stmt{statement_index}"))
    });
    let location_matches = formula.location.is_empty()
        || symbolic_formula_consumer_diagnostic_has_token(
            diagnostic,
            "location",
            &formula.location,
        )
        || symbolic_formula_consumer_diagnostic_has_token(diagnostic, "operand", &formula.location);

    function_matches && block_matches && statement_matches && location_matches
}

fn symbolic_formula_consumer_diagnostic_has_token(
    diagnostic: &str,
    key: &str,
    value: &str,
) -> bool {
    diagnostic.contains(&format!("{key}={value}"))
        || diagnostic.contains(&format!("{key}=str:{value:?}"))
}

fn symbolic_formula_consumer_diagnostic_has_space_token(
    diagnostic: &str,
    key: &str,
    value: &str,
) -> bool {
    diagnostic.contains(&format!("{key}={value}")) || diagnostic.contains(&format!("{key} {value}"))
}

fn validated_rust_reconstruction_allows_artifact_proof_grade(
    validated: &ValidatedRustReconstruction,
) -> bool {
    validated.status == ReconstructionValidationStatus::Validated
        && validated.trust_level == TrustLevel::ProofGrade
        && !validated.eligibility.is_empty()
        && validated
            .eligibility
            .iter()
            .all(|eligibility| eligibility.eligible && eligibility.rejections.is_empty())
        && !validated.validation_records.is_empty()
        && validated.validation_records.iter().all(rust_compile_back_record_allows_proof_grade)
}

fn rust_compile_back_record_allows_proof_grade(record: &ReconstructionValidationRecord) -> bool {
    record.target == DecompileTarget::Rust
        && record.candidate == ReconstructionCandidateKind::ValidatedRustStrictSubset
        && record.status == ReconstructionValidationStatus::Validated
        && record.trust_level == TrustLevel::ProofGrade
        && record.lifted_function.is_some()
        && record.reconstructed_function.is_some()
        && record
            .evidence
            .contains(&ReconstructionValidationEvidence::BidirectionalTrustIrRefinement)
        && record.evidence.iter().any(|evidence| {
            matches!(
                evidence,
                ReconstructionValidationEvidence::Other(kind)
                    if kind == RUST_COMPILE_BACK_PROOF_GRADE_EVIDENCE
            )
        })
        && rust_compile_back_record_has_evidence(
            record,
            RUST_COMPILE_BACK_CHECKED_CERTIFICATE_IDENTITY_EVIDENCE,
        )
        && rust_compile_back_record_has_evidence(
            record,
            RUST_COMPILE_BACK_TARGET_CONSUMER_ACCEPTANCE_EVIDENCE,
        )
        && rust_compile_back_record_has_evidence(
            record,
            RUST_COMPILE_BACK_SYMBOLIC_FORMULA_CONSUMER_ACCEPTANCE_EVIDENCE,
        )
        && rust_compile_back_record_has_evidence(
            record,
            RUST_COMPILE_BACK_SOURCE_BACKPROP_GATE_EVIDENCE,
        )
        && rust_compile_back_record_has_evidence(
            record,
            RUST_COMPILE_BACK_LIFTED_BINARY_TRUST_IR_BINDING_EVIDENCE,
        )
        && rust_compile_back_record_has_evidence(
            record,
            RUST_COMPILE_BACK_CHECKED_CERTIFICATE_BINDING_EVIDENCE,
        )
        && rust_compile_back_record_has_evidence(
            record,
            RUST_COMPILE_BACK_REPLAY_IDENTITY_BINDING_EVIDENCE,
        )
        && rust_compile_back_record_has_evidence(
            record,
            RUST_COMPILE_BACK_SOURCE_GATE_BINDING_EVIDENCE,
        )
        && rust_compile_back_record_has_evidence(
            record,
            RUST_COMPILE_BACK_UNSUPPORTED_LEDGER_ELIMINATION_EVIDENCE,
        )
        && record.forward.as_ref().is_some_and(|direction| {
            rust_compile_back_direction_allows_proof_grade(
                direction,
                ReconstructionValidationDirection::LiftedToOutput,
            )
        })
        && record.reverse.as_ref().is_some_and(|direction| {
            rust_compile_back_direction_allows_proof_grade(
                direction,
                ReconstructionValidationDirection::OutputToLifted,
            )
        })
}

fn rust_compile_back_record_has_bound_artifact_digests(
    record: &ReconstructionValidationRecord,
    output: &DecompiledOutput,
    artifact: &DecompilationArtifact,
) -> bool {
    if !rust_compile_back_record_has_bound_artifact_digest_metadata(
        record,
        output,
        &artifact.binary,
    ) {
        return false;
    }

    let Some(lifted) = lifted_function_for_compile_back_record(record, artifact) else {
        return false;
    };
    let Some(lifted_trust_ir_sha256) = verifiable_function_sha256(lifted) else {
        return false;
    };
    record_other_evidence_value(
        record,
        RUST_COMPILE_BACK_LIFTED_BINARY_TRUST_IR_SHA256_EVIDENCE_PREFIX,
    ) == Some(lifted_trust_ir_sha256.as_str())
}

fn rust_reconstruction_outputs_carry_compile_back_artifact_digest_identity(
    reconstruction: &ReconstructionSummary,
    binary: &BinaryArtifactMetadata,
) -> bool {
    if reconstruction.target != DecompileTarget::Rust {
        return true;
    }

    let Some(validated) = reconstruction.validated_rust.as_ref() else {
        return false;
    };
    let rust_outputs: Vec<_> = reconstruction
        .outputs
        .iter()
        .filter(|output| output.target == DecompileTarget::Rust)
        .collect();

    !rust_outputs.is_empty()
        && !validated.validation_records.is_empty()
        && validated.validation_records.iter().all(|record| {
            rust_outputs.iter().any(|output| {
                rust_compile_back_record_has_bound_artifact_digest_metadata(record, output, binary)
            })
        })
        && rust_outputs.iter().all(|output| {
            !output.validation_records.is_empty()
                && output.validation_records.iter().all(|record| {
                    rust_compile_back_record_has_bound_artifact_digest_metadata(
                        record, output, binary,
                    )
                })
                && output.validated_rust.as_ref().is_some_and(|validated| {
                    !validated.validation_records.is_empty()
                        && validated.validation_records.iter().all(|record| {
                            rust_compile_back_record_has_bound_artifact_digest_metadata(
                                record, output, binary,
                            )
                        })
                })
        })
}

fn rust_compile_back_record_has_bound_artifact_digest_metadata(
    record: &ReconstructionValidationRecord,
    output: &DecompiledOutput,
    binary: &BinaryArtifactMetadata,
) -> bool {
    if !rust_compile_back_record_allows_proof_grade(record)
        || !rust_compile_back_record_has_evidence(
            record,
            RUST_COMPILE_BACK_ARTIFACT_DIGEST_BINDING_EVIDENCE,
        )
    {
        return false;
    }

    let Some(lifted_trust_ir_sha256) = record_other_evidence_value(
        record,
        RUST_COMPILE_BACK_LIFTED_BINARY_TRUST_IR_SHA256_EVIDENCE_PREFIX,
    ) else {
        return false;
    };
    let Some(rust_source) = output.text.as_deref() else {
        return false;
    };
    let rust_source_sha256 = stable_sha256_hex(rust_source.as_bytes());
    let Some(compile_back_trust_ir_sha256) = record_other_evidence_value(
        record,
        RUST_COMPILE_BACK_RECONSTRUCTED_TRUST_IR_SHA256_EVIDENCE_PREFIX,
    ) else {
        return false;
    };

    is_canonical_sha256_hex(lifted_trust_ir_sha256)
        && is_canonical_sha256_hex(compile_back_trust_ir_sha256)
        && record_other_evidence_value(record, RUST_COMPILE_BACK_RUST_SOURCE_SHA256_EVIDENCE_PREFIX)
            == Some(rust_source_sha256.as_str())
        && rust_compile_back_record_origin_matches_binary(record, binary)
        && rust_compile_back_record_refinement_digest_matches(
            record,
            binary,
            lifted_trust_ir_sha256,
            &rust_source_sha256,
            compile_back_trust_ir_sha256,
        )
}

fn lifted_function_for_compile_back_record<'a>(
    record: &ReconstructionValidationRecord,
    artifact: &'a DecompilationArtifact,
) -> Option<&'a VerifiableFunction> {
    let lifted_name = record.lifted_function.as_deref()?;
    artifact.functions.iter().find_map(|function| {
        let lifted = function.lifted.as_ref()?;
        (function.name == lifted_name
            || lifted.name == lifted_name
            || lifted.def_path == lifted_name)
            .then_some(lifted)
    })
}

fn verifiable_function_sha256(function: &VerifiableFunction) -> Option<String> {
    serde_json::to_vec(function).ok().map(|bytes| stable_sha256_hex(&bytes))
}

fn record_other_evidence_value<'a>(
    record: &'a ReconstructionValidationRecord,
    prefix: &str,
) -> Option<&'a str> {
    record.evidence.iter().find_map(|evidence| match evidence {
        ReconstructionValidationEvidence::Other(kind) => kind.strip_prefix(prefix),
        _ => None,
    })
}

fn rust_compile_back_record_origin_matches_binary(
    record: &ReconstructionValidationRecord,
    binary: &BinaryArtifactMetadata,
) -> bool {
    let Some(root) = binary.root_artifact_digest.as_ref() else {
        return false;
    };
    let Some(selected) = binary.selected_image.as_ref() else {
        return false;
    };
    if !root.is_canonical_sha256() || !selected.is_canonical_sha256() {
        return false;
    }
    let Some(end_offset) = selected.end_offset() else {
        return false;
    };
    let selected_range = format!("{}..{}", selected.file_offset, end_offset);

    record_other_evidence_value(record, RUST_COMPILE_BACK_ROOT_ARTIFACT_SHA256_EVIDENCE_PREFIX)
        == Some(root.value.as_str())
        && record_other_evidence_value(
            record,
            RUST_COMPILE_BACK_SELECTED_IMAGE_SHA256_EVIDENCE_PREFIX,
        ) == Some(selected.sha256.as_str())
        && record_other_evidence_value(
            record,
            RUST_COMPILE_BACK_SELECTED_IMAGE_RANGE_EVIDENCE_PREFIX,
        ) == Some(selected_range.as_str())
}

fn rust_compile_back_record_refinement_digest_matches(
    record: &ReconstructionValidationRecord,
    binary: &BinaryArtifactMetadata,
    lifted_trust_ir_sha256: &str,
    rust_source_sha256: &str,
    compile_back_trust_ir_sha256: &str,
) -> bool {
    let Some(expected) = rust_compile_back_refinement_artifact_sha256(
        record,
        binary,
        lifted_trust_ir_sha256,
        rust_source_sha256,
        compile_back_trust_ir_sha256,
    ) else {
        return false;
    };

    record_other_evidence_value(
        record,
        RUST_COMPILE_BACK_REFINEMENT_ARTIFACT_SHA256_EVIDENCE_PREFIX,
    ) == Some(expected.as_str())
}

fn rust_compile_back_refinement_artifact_sha256(
    record: &ReconstructionValidationRecord,
    binary: &BinaryArtifactMetadata,
    lifted_trust_ir_sha256: &str,
    rust_source_sha256: &str,
    compile_back_trust_ir_sha256: &str,
) -> Option<String> {
    let payload = serde_json::json!({
        "schema": "trust-decompile.rust-compile-back-refinement@1",
        "target": record.target,
        "function": record.function,
        "lifted_function": record.lifted_function,
        "reconstructed_function": record.reconstructed_function,
        "candidate": record.candidate,
        "status": record.status,
        "trust_level": record.trust_level,
        "forward": record.forward,
        "reverse": record.reverse,
        "lifted_binary_trust_ir_sha256": lifted_trust_ir_sha256,
        "rust_source_sha256": rust_source_sha256,
        "compile_back_trust_ir_sha256": compile_back_trust_ir_sha256,
        "root_artifact_digest": binary.root_artifact_digest,
        "selected_image": binary.selected_image,
    });
    serde_json::to_vec(&payload).ok().map(|bytes| stable_sha256_hex(&bytes))
}

fn rust_compile_back_record_has_evidence(
    record: &ReconstructionValidationRecord,
    required: &str,
) -> bool {
    record.evidence.iter().any(|evidence| {
        matches!(evidence, ReconstructionValidationEvidence::Other(kind) if kind == required)
    })
}

fn rust_compile_back_direction_allows_proof_grade(
    direction: &ReconstructionValidationDirectionRecord,
    expected_direction: ReconstructionValidationDirection,
) -> bool {
    direction.direction == expected_direction
        && direction.status == ReconstructionValidationStatus::Validated
        && direction.vc_count > 0
        && direction.proof_certificates > 0
}

fn binary_proof_grade_release_gate_accepts(summary: &BinaryVerificationSummary) -> bool {
    !summary.solver_dispatch.is_empty()
        && summary.unsupported_ledger.records.is_empty()
        && summary.solver_dispatch.iter().all(binary_dispatch_has_proof_grade_evidence)
}

fn binary_dispatch_has_proof_grade_evidence(dispatch: &SolverDispatchRecord) -> bool {
    dispatch.status == SolverDispatchStatus::Unsat
        && dispatch.query_semantics == SolverQuerySemantics::SatIsCounterexample
        // if the record carries an embedded VerificationResult,
        // it must CORROBORATE the Unsat claim at the reported-proof floor before
        // proof-grade release promotion. A result that gates below SmtBacked
        // (Unchecked — a bare unvalidated solver "unsat" — or Heuristic) must NOT
        // be promoted to proof-grade. Fail closed (status/certificate are
        // authoritative only when no result is embedded).
        && dispatch.result.as_ref().is_none_or(|r| {
            matches!(
                r.clone().require_assurance(trust_types::AssuranceLevel::SmtBacked),
                trust_types::VerificationResult::Proved { .. }
            )
        })
        && binary_dispatch_satisfies_release_replay_semantics(dispatch)
        && binary_dispatch_has_replay_digest_identity(dispatch)
        && checked_certificate_has_bridge_metadata(&dispatch.certificate)
        && dispatch.origin.as_ref().is_some_and(|origin| {
            binary_origin_has_exact_instruction_provenance(origin)
                && binary_origin_has_exact_source_provenance(origin)
        })
}

fn binary_dispatch_has_replay_digest_identity(dispatch: &SolverDispatchRecord) -> bool {
    dispatch
        .binary_artifact_digest_identity
        .as_ref()
        .is_some_and(BinaryArtifactDigestIdentity::digest_identity_allows_replay)
}

fn binary_dispatch_satisfies_release_replay_semantics(dispatch: &SolverDispatchRecord) -> bool {
    match (dispatch.status, dispatch.query_semantics) {
        (
            SolverDispatchStatus::Sat | SolverDispatchStatus::Unsat,
            SolverQuerySemantics::SatIsCounterexample,
        ) => dispatch.replay == ReplayStatus::Replayed,
        _ => false,
    }
}

fn binary_origin_has_exact_instruction_provenance(origin: &BinaryOrigin) -> bool {
    let Some(instruction_size) = origin.instruction_size else {
        return false;
    };

    instruction_size > 0 && usize::from(instruction_size) == origin.instruction_bytes.len()
}

fn binary_origin_has_exact_source_provenance(origin: &BinaryOrigin) -> bool {
    origin.source.as_ref().is_some_and(|source| !source.is_binary())
}

fn dispatches_have_accepted_source_provenance(
    dispatches: &[SolverDispatchRecord],
    functions: &[DecompiledFunction],
    binary: &BinaryArtifactMetadata,
) -> bool {
    dispatches
        .iter()
        .all(|dispatch| dispatch_has_accepted_source_provenance(dispatch, functions, binary))
}

fn dispatch_has_accepted_source_provenance(
    dispatch: &SolverDispatchRecord,
    functions: &[DecompiledFunction],
    binary: &BinaryArtifactMetadata,
) -> bool {
    let Some(origin) = dispatch.origin.as_ref() else {
        return false;
    };
    if !binary_origin_matches_artifact_identity(origin, binary) {
        return false;
    }
    let Some(source) = origin.source.as_ref().filter(|source| !source.is_binary()) else {
        return false;
    };

    if let Some(accepted) = accepted_instruction_origin_for_origin(origin, functions) {
        return binary_origin_matches_accepted_instruction(origin, accepted)
            && binary_origin_matches_artifact_identity(accepted, binary);
    }

    accepted_source_for_origin(origin, functions).is_some_and(|accepted| accepted == source)
}

fn accepted_source_for_origin<'a>(
    origin: &BinaryOrigin,
    functions: &'a [DecompiledFunction],
) -> Option<&'a SourceSpan> {
    let function = origin
        .function_entry
        .and_then(|entry| functions.iter().find(|function| function.entry == entry))
        .or_else(|| {
            functions.iter().find(|function| {
                function
                    .address_range
                    .as_ref()
                    .is_some_and(|range| range.contains(origin.instruction_address))
            })
        })?;

    if let Some(source) =
        instruction_accepted_source_for_origin(origin, &function.instruction_provenance)
    {
        return Some(source);
    }

    if function.entry == origin.instruction_address {
        if let Some(source) = function
            .origin
            .as_ref()
            .and_then(|origin| origin.source.as_ref())
            .filter(|source| !source.is_binary())
        {
            return Some(source);
        }

        if let Some(source) =
            function.lifted.as_ref().map(|lifted| &lifted.span).filter(|source| !source.is_binary())
        {
            return Some(source);
        }
    }

    None
}

fn accepted_instruction_origin_for_origin<'a>(
    origin: &BinaryOrigin,
    functions: &'a [DecompiledFunction],
) -> Option<&'a BinaryOrigin> {
    let function = origin
        .function_entry
        .and_then(|entry| functions.iter().find(|function| function.entry == entry))
        .or_else(|| {
            functions.iter().find(|function| {
                function
                    .address_range
                    .as_ref()
                    .is_some_and(|range| range.contains(origin.instruction_address))
            })
        })?;

    function
        .instruction_provenance
        .iter()
        .find(|candidate| candidate.instruction_address == origin.instruction_address)
}

fn binary_origin_matches_accepted_instruction(
    origin: &BinaryOrigin,
    accepted: &BinaryOrigin,
) -> bool {
    origin.binary_path == accepted.binary_path
        && origin.function_entry == accepted.function_entry
        && origin.instruction_address == accepted.instruction_address
        && origin.instruction_size == accepted.instruction_size
        && origin.encoding == accepted.encoding
        && origin.instruction_bytes == accepted.instruction_bytes
        && origin.source == accepted.source
        && accepted.source.as_ref().is_some_and(|source| !source.is_binary())
        && binary_origin_has_exact_instruction_provenance(accepted)
}

fn instruction_accepted_source_for_origin<'a>(
    origin: &BinaryOrigin,
    instruction_provenance: &'a [BinaryOrigin],
) -> Option<&'a SourceSpan> {
    instruction_provenance
        .iter()
        .find(|candidate| candidate.instruction_address == origin.instruction_address)
        .and_then(|candidate| candidate.source.as_ref())
        .filter(|source| !source.is_binary())
}

fn checked_certificate_has_bridge_metadata(certificate: &ProofCertificateStatus) -> bool {
    match certificate {
        ProofCertificateStatus::Checked { checker, format, sha256 } => {
            !checker.trim().is_empty()
                && !format.trim().is_empty()
                && sha256.as_deref().is_some_and(|sha256| !sha256.trim().is_empty())
        }
        _ => false,
    }
}

fn aggregate_checked_certificate_sha256(dispatches: &[SolverDispatchRecord]) -> Option<String> {
    #[derive(Serialize)]
    struct AggregateCertificateDispatch<'a> {
        id: &'a str,
        function: Option<&'a str>,
        checker: &'a str,
        format: &'a str,
        sha256: &'a str,
    }

    let dispatches: Option<Vec<_>> = dispatches
        .iter()
        .map(|dispatch| {
            let ProofCertificateStatus::Checked { checker, format, sha256 } = &dispatch.certificate
            else {
                return None;
            };
            Some(AggregateCertificateDispatch {
                id: dispatch.id.as_str(),
                function: dispatch.function.as_deref(),
                checker: checker.as_str(),
                format: format.as_str(),
                sha256: sha256.as_deref()?,
            })
        })
        .collect();
    let dispatches = dispatches?;
    serde_json::to_vec(&dispatches).ok().map(|bytes| stable_sha256_hex(&bytes))
}

fn aggregate_checked_certificate_status(
    dispatches: &[SolverDispatchRecord],
) -> ProofCertificateStatus {
    if dispatches.is_empty() {
        return ProofCertificateStatus::NotRequested;
    }

    if dispatches
        .iter()
        .all(|dispatch| checked_certificate_has_bridge_metadata(&dispatch.certificate))
    {
        if let Some(sha256) = aggregate_checked_certificate_sha256(dispatches) {
            ProofCertificateStatus::Checked {
                checker: "aggregate-binary-release-gate".to_string(),
                format: "per-vc-checked-certificates".to_string(),
                sha256: Some(sha256),
            }
        } else {
            ProofCertificateStatus::Unavailable {
                reason: Some(
                    "proof-grade binary release requires checked certificate evidence with checker identity, format/version metadata, and certificate digest identity for every VC"
                        .to_string(),
                ),
            }
        }
    } else {
        ProofCertificateStatus::Unavailable {
            reason: Some(
                "proof-grade binary release requires checked certificate evidence with checker identity, format/version metadata, and certificate digest identity for every VC"
                    .to_string(),
            ),
        }
    }
}

fn refresh_trust_ir_json_outputs(artifact: &mut DecompilationArtifact) {
    refresh_source_backpropagation_authority(artifact);
    let trust_ir_output_indices: Vec<_> = artifact
        .reconstruction
        .outputs
        .iter()
        .enumerate()
        .filter_map(|(index, output)| {
            (output.target == DecompileTarget::TrustIr
                && output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
            .then_some(index)
        })
        .collect();

    for index in trust_ir_output_indices {
        match render_trust_ir_json(
            &artifact.binary,
            &artifact.functions,
            &artifact.call_graph,
            &artifact.memory_model.accesses,
            &artifact.unsupported,
            &artifact.source_provenance,
            Some(&artifact.reconstruction),
        ) {
            Ok(text) => artifact.reconstruction.outputs[index].text = Some(text),
            Err(error) => artifact.reconstruction.outputs[index]
                .diagnostics
                .push(format!("TrustIr JSON certificate metadata refresh failed closed: {error}")),
        }
    }
}

fn build_function_lookup(
    artifact: &DecompilationArtifact,
    lifted: &LiftedBinary,
) -> HashMap<String, usize> {
    let mut lookup = HashMap::new();
    for (index, function) in artifact.functions.iter().enumerate() {
        lookup.insert(function.name.clone(), index);
        lookup.insert(format!("binary::{}", function.name), index);
        if let Some(lifted_function) = &function.lifted {
            lookup.insert(lifted_function.name.clone(), index);
            lookup.insert(lifted_function.def_path.clone(), index);
        }
    }

    for lifted_function in &lifted.functions {
        if let Some(index) = artifact
            .functions
            .iter()
            .position(|function| function.entry == lifted_function.entry_point)
        {
            lookup.insert(lifted_function.name.clone(), index);
            lookup.insert(function_def_path(lifted_function), index);
        }
    }

    lookup
}

fn function_index_for_vc(
    artifact: &DecompilationArtifact,
    function_lookup: &HashMap<String, usize>,
    vc: &VerificationCondition,
) -> Option<usize> {
    if !vc.location.is_binary() {
        return None;
    }

    if let Some(address) = vc.location.binary_address_value()
        && let Some(index) = artifact.functions.iter().position(|function| {
            function.entry == address
                || function.address_range.as_ref().is_some_and(|range| range.contains(address))
        })
    {
        return Some(index);
    }

    function_lookup.get(vc.function.as_str()).copied()
}

fn solver_dispatch_record_from_result(
    index: usize,
    artifact: &DecompilationArtifact,
    lifted: &LiftedBinary,
    function_index: Option<usize>,
    vc: &VerificationCondition,
    result: &VerificationResult,
) -> SolverDispatchRecord {
    let mut status = solver_status_from_result(result);
    let mut diagnostics = solver_dispatch_diagnostics(result);
    let binary_artifact_digest_identity =
        BinaryArtifactDigestIdentity::from_metadata(&artifact.binary);
    diagnostics.extend(solver_dispatch_digest_identity_diagnostics(
        binary_artifact_digest_identity.as_ref(),
    ));
    if !vc.location.is_binary() {
        status = SolverDispatchStatus::Rejected;
        diagnostics.push(
            "rejected non-binary verification condition as binary evidence; binary VC attachment requires binary provenance"
                .to_string(),
        );
    }

    SolverDispatchRecord {
        id: format!("{}:{index}", vc.function.as_str()),
        function: Some(vc.function.as_str().to_string()),
        origin: binary_origin_for_vc(artifact, lifted, function_index, vc),
        vc_kind: Some(vc.kind.clone()),
        vc: Some(SerializableVc::from_vc(vc)),
        solver: result.solver_name().to_string(),
        backend: None,
        status,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        result: Some(result.clone()),
        binary_artifact_digest_identity,
        elapsed_ms: elapsed_ms_from_result(result),
        timeout_ms: timeout_ms_from_result(result),
        replay: ReplayStatus::NotAttempted,
        certificate: proof_certificate_status_from_result(result),
        diagnostics,
        ..Default::default()
    }
}

fn binary_origin_for_vc(
    artifact: &DecompilationArtifact,
    lifted: &LiftedBinary,
    function_index: Option<usize>,
    vc: &VerificationCondition,
) -> Option<BinaryOrigin> {
    if !vc.location.is_binary() {
        return None;
    }
    let function_entry = function_index.map(|index| artifact.functions[index].entry);
    let instruction_address = vc.location.binary_address_value().or(function_entry)?;

    if let Some(origin) =
        instruction_origin_for_vc(artifact, lifted, function_index, instruction_address)
    {
        return Some(origin);
    }

    Some(BinaryOrigin {
        binary_path: artifact.binary.path.clone(),
        function_entry,
        instruction_address,
        instruction_size: None,
        encoding: None,
        instruction_bytes: vec![],
        source: Some(source_span_for_address(lifted, instruction_address)),
    })
}

fn instruction_origin_for_vc(
    artifact: &DecompilationArtifact,
    lifted: &LiftedBinary,
    function_index: Option<usize>,
    instruction_address: u64,
) -> Option<BinaryOrigin> {
    let function_entry = function_index.map(|index| artifact.functions[index].entry);
    let lifted_function = function_entry
        .and_then(|entry| lifted.functions.iter().find(|function| function.entry_point == entry))
        .or_else(|| {
            lifted.functions.iter().find(|function| {
                function.cfg.blocks.iter().any(|block| {
                    block
                        .instructions
                        .iter()
                        .any(|instruction| instruction.address == instruction_address)
                })
            })
        })?;

    let instruction = lifted_function
        .cfg
        .blocks
        .iter()
        .flat_map(|block| block.instructions.iter())
        .find(|instruction| instruction.address == instruction_address)?;

    Some(BinaryOrigin {
        binary_path: artifact.binary.path.clone(),
        function_entry: Some(lifted_function.entry_point),
        instruction_address: instruction.address,
        instruction_size: Some(instruction.size),
        encoding: Some(instruction.encoding),
        instruction_bytes: instruction.bytes.clone(),
        source: Some(source_span_for_address(lifted, instruction.address)),
    })
}

fn solver_status_from_result(result: &VerificationResult) -> SolverDispatchStatus {
    match result {
        VerificationResult::Proved { .. } => SolverDispatchStatus::Unsat,
        VerificationResult::Failed { .. } => SolverDispatchStatus::Sat,
        VerificationResult::Unknown { .. } => SolverDispatchStatus::Unknown,
        VerificationResult::Timeout { .. } => SolverDispatchStatus::Timeout,
        _ => SolverDispatchStatus::Unknown,
    }
}

fn solver_dispatch_digest_identity_diagnostics(
    identity: Option<&BinaryArtifactDigestIdentity>,
) -> Vec<String> {
    match identity {
        Some(identity) if identity.digest_identity_allows_replay() => {
            vec![
                "binary artifact digest identity attached to solver dispatch for exact replay/proof binding"
                    .to_string(),
            ]
        }
        Some(identity) => {
            vec![format!(
                "solver dispatch binary artifact digest identity is not replay-grade: {}",
                identity.digest_identity_blockers().join("; ")
            )]
        }
        None => {
            vec![
                "solver dispatch has no binary artifact digest identity; exact replay/proof binding remains fail-closed"
                    .to_string(),
            ]
        }
    }
}

fn binary_artifact_digest_identity_assumption(
    identity: &BinaryArtifactDigestIdentity,
) -> Option<ModelAssumption> {
    if !identity.digest_identity_allows_replay() {
        return None;
    }
    let description = serde_json::to_string(identity).ok()?;
    Some(ModelAssumption {
        stage: RECONSTRUCTION_OUTPUT_BINARY_ARTIFACT_DIGEST_IDENTITY_STAGE.to_string(),
        description,
    })
}

fn attach_binary_artifact_digest_identity_to_output(
    output: &mut DecompiledOutput,
    metadata: &BinaryArtifactMetadata,
) {
    let Some(identity) = BinaryArtifactDigestIdentity::from_metadata(metadata) else {
        return;
    };
    let Some(assumption) = binary_artifact_digest_identity_assumption(&identity) else {
        return;
    };

    if !output.assumptions.iter().any(|existing| existing == &assumption) {
        output.assumptions.push(assumption);
    }
    if !output
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic == "binary-artifact-digest-identity=attached")
    {
        output.diagnostics.push("binary-artifact-digest-identity=attached".to_string());
    }
}

fn elapsed_ms_from_result(result: &VerificationResult) -> Option<u64> {
    match result {
        VerificationResult::Proved { time_ms, .. }
        | VerificationResult::Failed { time_ms, .. }
        | VerificationResult::Unknown { time_ms, .. } => Some(*time_ms),
        VerificationResult::Timeout { .. } => None,
        _ => None,
    }
}

fn timeout_ms_from_result(result: &VerificationResult) -> Option<u64> {
    match result {
        VerificationResult::Timeout { timeout_ms, .. } => Some(*timeout_ms),
        _ => None,
    }
}

fn solver_dispatch_diagnostics(result: &VerificationResult) -> Vec<String> {
    let mut diagnostics = vec!["SAT is a counterexample; UNSAT proves the binary VC".to_string()];
    match result {
        VerificationResult::Proved { proof_certificate: Some(_), .. } => {
            diagnostics.push(
                "solver returned proof certificate bytes, but proof-grade requires checked certificate evidence"
                    .to_string(),
            );
        }
        VerificationResult::Failed { counterexample: None, .. } => {
            diagnostics.push("solver returned SAT without a counterexample model".to_string());
        }
        VerificationResult::Unknown { reason, .. } => {
            diagnostics.push(format!("solver returned unknown: {reason}"));
        }
        VerificationResult::Timeout { timeout_ms, .. } => {
            diagnostics.push(format!("solver timed out after {timeout_ms}ms"));
        }
        VerificationResult::Proved { .. } | VerificationResult::Failed { .. } => {}
        _ => diagnostics.push("solver returned an unrecognized result variant".to_string()),
    }
    diagnostics
}

fn proof_certificate_status_from_result(result: &VerificationResult) -> ProofCertificateStatus {
    match result {
        VerificationResult::Proved { proof_certificate: Some(_), .. } => {
            ProofCertificateStatus::Present {
                format: "solver-proof-bytes".to_string(),
                sha256: None,
                artifact_path: None,
            }
        }
        VerificationResult::Proved { proof_certificate: None, .. } => {
            ProofCertificateStatus::Unavailable {
                reason: Some("solver result did not include proof certificate bytes".to_string()),
            }
        }
        _ => ProofCertificateStatus::NotRequested,
    }
}

fn cap_binary_verification_trust(trust_level: TrustLevel) -> TrustLevel {
    if trust_level == TrustLevel::ProofGrade { TrustLevel::Partial } else { trust_level }
}

fn cap_binary_release_gate_proof_grade_trust(artifact: &mut DecompilationArtifact) {
    artifact.verification.trust_level =
        cap_binary_verification_trust(artifact.verification.trust_level);
    artifact.trust_level = cap_binary_verification_trust(artifact.trust_level);
    cap_reconstruction_proof_grade_trust(&mut artifact.reconstruction);
    for function in &mut artifact.functions {
        function.verification.trust_level =
            cap_binary_verification_trust(function.verification.trust_level);
        function.trust_level = cap_binary_verification_trust(function.trust_level);
    }
}

fn cap_reconstruction_proof_grade_trust(reconstruction: &mut ReconstructionSummary) {
    reconstruction.trust_level = cap_binary_verification_trust(reconstruction.trust_level);
    if let Some(validated_rust) = reconstruction.validated_rust.as_mut() {
        validated_rust.trust_level = cap_binary_verification_trust(validated_rust.trust_level);
    }
    for output in &mut reconstruction.outputs {
        output.trust_level = cap_binary_verification_trust(output.trust_level);
        if let Some(validated_rust) = output.validated_rust.as_mut() {
            validated_rust.trust_level = cap_binary_verification_trust(validated_rust.trust_level);
        }
    }
}

fn source_span_for_address(lifted: &LiftedBinary, address: u64) -> SourceSpan {
    if matches!(lifted.source_provenance.status, trust_lift::LiftedSourceProvenanceStatus::Exact) {
        return lifted
            .exact_source_span(address)
            .unwrap_or_else(|| SourceSpan::binary_address(address));
    }

    SourceSpan::binary_address(address)
}

fn source_provenance_assumptions(lifted: &LiftedBinary) -> Vec<ModelAssumption> {
    match lifted.source_provenance.status {
        trust_lift::LiftedSourceProvenanceStatus::Exact => Vec::new(),
        trust_lift::LiftedSourceProvenanceStatus::Unavailable => vec![ModelAssumption {
            stage: "trust-lift::source-provenance".to_string(),
            description:
                "exact debug/source provenance is unavailable; diagnostics remain binary-address-only"
                    .to_string(),
        }],
        trust_lift::LiftedSourceProvenanceStatus::Ambiguous => vec![ModelAssumption {
            stage: "trust-lift::source-provenance".to_string(),
            description: format!(
                "{} ambiguous debug/source address(es) were withheld; affected diagnostics remain binary-address-only",
                lifted.source_provenance.ambiguous_mapping_count
            ),
        }],
        trust_lift::LiftedSourceProvenanceStatus::Unsupported => vec![ModelAssumption {
            stage: "trust-lift::source-provenance".to_string(),
            description:
                "debug/source provenance could not be parsed safely; diagnostics remain binary-address-only"
                    .to_string(),
        }],
    }
}

fn source_provenance_base_diagnostics(lifted: &LiftedBinary) -> Vec<String> {
    let diagnostics: Vec<_> = lifted
        .source_provenance
        .diagnostics
        .iter()
        .filter(|diagnostic| !diagnostic.trim().is_empty())
        .cloned()
        .collect();
    if !diagnostics.is_empty() {
        return diagnostics;
    }

    match lifted.source_provenance.status {
        trust_lift::LiftedSourceProvenanceStatus::Exact => vec![
            "exact debug/source provenance was reported without producer diagnostics".to_string(),
        ],
        trust_lift::LiftedSourceProvenanceStatus::Unavailable
        | trust_lift::LiftedSourceProvenanceStatus::Ambiguous
        | trust_lift::LiftedSourceProvenanceStatus::Unsupported => {
            source_provenance_assumptions(lifted)
                .into_iter()
                .map(|assumption| assumption.description)
                .collect()
        }
    }
}

fn source_provenance_diagnostics(
    lifted: &LiftedBinary,
    source_backpropagation_allowed: bool,
    blockers: &[String],
) -> Vec<String> {
    let mut diagnostics = source_provenance_base_diagnostics(lifted);
    diagnostics
        .push(format!("source-provenance-status={}", lifted.source_provenance.status.name()));
    diagnostics.push(format!("source-backpropagation-allowed={source_backpropagation_allowed}"));
    diagnostics
        .push(format!("effective-source-backpropagation-allowed={source_backpropagation_allowed}"));
    diagnostics
        .extend(blockers.iter().map(|blocker| format!("source-backpropagation-blocker={blocker}")));
    diagnostics
}

fn source_backpropagation_gate_blockers(lifted: &LiftedBinary) -> Vec<String> {
    if lifted.source_provenance.status != trust_lift::LiftedSourceProvenanceStatus::Exact {
        return Vec::new();
    }

    let mut blockers = Vec::new();
    if lifted.source_provenance.exact_mapping_count == 0 {
        blockers.push("exact status carried no accepted source mappings".to_string());
    }
    if lifted.source_provenance.ambiguous_mapping_count != 0 {
        blockers.push(format!(
            "{} ambiguous source mapping(s) remain withheld",
            lifted.source_provenance.ambiguous_mapping_count
        ));
    }
    if lifted.source_provenance.exact_mapping_count != lifted.source_mappings.len() {
        blockers.push(format!(
            "exact source mapping count {} does not match {} materialized mapping(s)",
            lifted.source_provenance.exact_mapping_count,
            lifted.source_mappings.len()
        ));
    }

    let unmapped_entries: Vec<_> = lifted
        .functions
        .iter()
        .filter(|function| lifted.exact_source_span(function.entry_point).is_none())
        .map(|function| format!("{}@0x{:x}", function.name, function.entry_point))
        .collect();
    if !unmapped_entries.is_empty() {
        blockers.push(format!(
            "partial exact source mapping: {} lifted function entry address(es) lack exact source spans: {}",
            unmapped_entries.len(),
            unmapped_entries.join(", ")
        ));
    }

    let unmapped_instructions: Vec<_> = lifted
        .functions
        .iter()
        .flat_map(|function| {
            source_provenance_instruction_addresses(function).into_iter().filter_map(
                move |address| {
                    lifted
                        .exact_source_span(address)
                        .filter(|source| !source.is_binary())
                        .map_or_else(|| Some(format!("{}@0x{address:x}", function.name)), |_| None)
                },
            )
        })
        .collect();
    if !unmapped_instructions.is_empty() {
        blockers.push(format!(
            "partial exact source mapping: {} lifted instruction address(es) lack exact source spans: {}",
            unmapped_instructions.len(),
            unmapped_instructions.join(", ")
        ));
    }

    let binary_compat_mappings: Vec<_> = lifted
        .source_mappings
        .iter()
        .filter(|mapping| mapping.source.is_binary())
        .map(|mapping| format!("0x{:x}", mapping.binary_address))
        .collect();
    if !binary_compat_mappings.is_empty() {
        blockers.push(format!(
            "exact source mapping resolved to binary-address compatibility span(s): {}",
            binary_compat_mappings.join(", ")
        ));
    }

    let synthetic_mappings: Vec<_> = lifted
        .source_mappings
        .iter()
        .filter(|mapping| source_span_has_synthetic_release_marker(&mapping.source))
        .map(|mapping| format!("0x{:x} -> {}", mapping.binary_address, mapping.source.file))
        .collect();
    if !synthetic_mappings.is_empty() {
        blockers.push(format!(
            "synthetic source mapping marker(s) are not source-backpropagation evidence: {}",
            synthetic_mappings.join(", ")
        ));
    }

    let synthetic_diagnostics: Vec<_> = lifted
        .source_provenance
        .diagnostics
        .iter()
        .filter(|diagnostic| text_has_synthetic_release_marker(diagnostic))
        .cloned()
        .collect();
    if !synthetic_diagnostics.is_empty() {
        blockers.push(format!(
            "synthetic source provenance diagnostic(s) are not source-backpropagation evidence: {}",
            synthetic_diagnostics.join("; ")
        ));
    }

    blockers
}

fn source_provenance_instruction_addresses(function: &LiftedFunction) -> BTreeSet<u64> {
    function
        .cfg
        .blocks
        .iter()
        .flat_map(|block| block.instructions.iter().map(|instruction| instruction.address))
        .chain(function.annotations.iter().map(|annotation| annotation.binary_offset))
        .collect()
}

fn source_span_has_synthetic_release_marker(source: &SourceSpan) -> bool {
    text_has_synthetic_release_marker(&source.file)
}

fn record_source_provenance_gate_blockers(
    unsupported: &mut UnsupportedLedger,
    binary: &BinaryArtifactMetadata,
    blockers: &[String],
) {
    if blockers.is_empty() {
        return;
    }

    unsupported.records.push(unsupported_record(
        SOURCE_PROVENANCE_GATE_STAGE,
        Some(&binary.architecture),
        None,
        None,
        &format!("source backpropagation is not producer-ready: {}", blockers.join("; ")),
    ));
}

fn binary_source_provenance_summary(
    lifted: &LiftedBinary,
    blockers: &[String],
) -> BinarySourceProvenanceSummary {
    let source_backpropagation_allowed =
        matches!(lifted.source_provenance.status, trust_lift::LiftedSourceProvenanceStatus::Exact)
            && lifted.source_provenance.exact_mapping_count > 0
            && lifted.source_provenance.ambiguous_mapping_count == 0
            && blockers.is_empty();

    BinarySourceProvenanceSummary {
        status: lifted.source_provenance.status.name().to_string(),
        exact_mapping_count: lifted.source_provenance.exact_mapping_count,
        ambiguous_mapping_count: lifted.source_provenance.ambiguous_mapping_count,
        diagnostics: source_provenance_diagnostics(
            lifted,
            source_backpropagation_allowed,
            blockers,
        ),
        source_backpropagation_allowed,
    }
}

fn function_source_provenance_assumptions(
    lifted: &LiftedBinary,
    address: u64,
) -> Vec<ModelAssumption> {
    if matches!(lifted.source_provenance.status, trust_lift::LiftedSourceProvenanceStatus::Exact)
        && lifted.exact_source_span(address).is_some()
    {
        return Vec::new();
    }
    source_provenance_assumptions(lifted)
}

fn summarize_function(
    function: &LiftedFunction,
    arch: Option<LiftArch>,
    lifted: &LiftedBinary,
) -> DecompiledFunction {
    let instruction_count = instruction_count(function);
    let function_span = source_span_for_address(lifted, function.entry_point);
    let origin = Some(binary_origin_with_source(
        function.entry_point,
        Some(function.entry_point),
        function_span.clone(),
    ));
    let (signature, abi_facts, storage_facts) = arch
        .map(|arch| build_signature_facts(function, arch, origin.clone()))
        .unwrap_or_else(|| {
            (
                BinaryFunctionSignature {
                    name: function.name.clone(),
                    entry: function.entry_point,
                    origin: origin.clone(),
                    trust_level: TrustLevel::Partial,
                    ..Default::default()
                },
                vec![],
                vec![],
            )
        });

    DecompiledFunction {
        name: function.name.clone(),
        entry: function.entry_point,
        address_range: function_address_range(function),
        origin: origin.clone(),
        instruction_provenance: instruction_provenance_for_function(function, lifted),
        signature,
        lifted: Some(VerifiableFunction {
            name: function.name.clone(),
            def_path: function_def_path(function),
            span: function_span,
            body: function.trust_ir_body.clone(),
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }),
        abi_facts,
        storage_facts,
        memory_accesses: function.memory_accesses.clone(),
        unsupported: function.unsupported.clone(),
        coverage: BinaryCoverageSummary {
            functions_discovered: 1,
            functions_lifted: 1,
            instructions_discovered: instruction_count,
            instructions_lifted: instruction_count,
            unsupported_instructions: function.unsupported.records.len(),
            unresolved_edges: unresolved_edge_count(function),
            ..Default::default()
        },
        assumptions: function_source_provenance_assumptions(lifted, function.entry_point),
        trust_level: function.trust_level,
        ..Default::default()
    }
}

fn instruction_provenance_for_function(
    function: &LiftedFunction,
    lifted: &LiftedBinary,
) -> Vec<BinaryOrigin> {
    function
        .annotations
        .iter()
        .map(|annotation| BinaryOrigin {
            binary_path: None,
            function_entry: Some(function.entry_point),
            instruction_address: annotation.binary_offset,
            instruction_size: Some(annotation.instruction_size),
            encoding: Some(annotation.encoding),
            instruction_bytes: exact_annotation_instruction_bytes(annotation)
                .unwrap_or_default()
                .to_vec(),
            source: Some(source_span_for_address(lifted, annotation.binary_offset)),
        })
        .collect()
}

fn exact_annotation_instruction_bytes(
    annotation: &trust_lift::cfg::ProofAnnotation,
) -> Option<&[u8]> {
    if annotation.instruction_bytes.is_empty()
        || usize::from(annotation.instruction_size) != annotation.instruction_bytes.len()
    {
        None
    } else {
        Some(&annotation.instruction_bytes)
    }
}

fn build_signature_facts(
    function: &LiftedFunction,
    arch: LiftArch,
    origin: Option<BinaryOrigin>,
) -> (BinaryFunctionSignature, Vec<BinaryAbiFact>, Vec<BinaryStorageFact>) {
    let summary = summarize_function_signature(&function.cfg, arch);
    let convention = binary_calling_convention(summary.convention);
    let bit_width = register_bit_width(arch);
    let function_subject =
        BinaryFactSubject::Function { name: function.name.clone(), entry: function.entry_point };
    let abi_default_assumptions = provenance_assumptions_matching(
        &summary,
        "calling convention",
        "calling convention selected from target architecture",
    );
    let return_assumptions = provenance_assumptions_matching(
        &summary,
        "return register",
        "return register is ABI default metadata",
    );
    let argument_assumptions = provenance_assumptions_matching(
        &summary,
        "argument register",
        "argument register reads are observations, not proof assumptions",
    );

    let mut abi_facts = vec![BinaryAbiFact {
        subject: function_subject,
        kind: BinaryAbiFactKind::CallingConvention(convention.clone()),
        origin: origin.clone(),
        evidence: BinaryFactEvidence::AbiDefault,
        confidence: BinaryFactConfidence::Heuristic,
        trust_level: TrustLevel::Partial,
        assumptions: abi_default_assumptions,
    }];

    let mut storage_facts = Vec::new();
    let mut parameters = Vec::new();
    for register in &summary.observed_argument_registers {
        let Some(index) = summary.argument_registers.iter().position(|name| name == register)
        else {
            continue;
        };
        let location = register_location(register, bit_width);
        let subject = BinaryFactSubject::Parameter { function: function.name.clone(), index };
        parameters.push(BinaryParameter {
            index,
            name: Some(format!("arg{index}")),
            ty: None,
            storage: location.clone(),
            evidence: BinaryFactEvidence::RegisterUse,
            trust_level: TrustLevel::Partial,
        });
        abi_facts.push(BinaryAbiFact {
            subject: subject.clone(),
            kind: BinaryAbiFactKind::Parameter { index, location: location.clone() },
            origin: origin.clone(),
            evidence: BinaryFactEvidence::RegisterUse,
            confidence: BinaryFactConfidence::Inferred,
            trust_level: TrustLevel::Partial,
            assumptions: argument_assumptions.clone(),
        });
        storage_facts.push(BinaryStorageFact {
            subject,
            location,
            ty: None,
            mutable: None,
            alignment_bytes: None,
            valid_range: None,
            origin: origin.clone(),
            evidence: BinaryFactEvidence::RegisterUse,
            confidence: BinaryFactConfidence::Inferred,
            trust_level: TrustLevel::Partial,
            assumptions: argument_assumptions.clone(),
        });
    }
    parameters.sort_by_key(|parameter| parameter.index);

    let mut returns = Vec::new();
    if let Some(return_register) = &summary.return_register {
        let location = register_location(return_register, bit_width);
        let ty = non_unit_ty(&summary.return_ty);
        returns.push(BinaryReturn {
            index: 0,
            ty,
            storage: location.clone(),
            evidence: BinaryFactEvidence::AbiDefault,
            trust_level: TrustLevel::Partial,
        });
        let subject = BinaryFactSubject::ReturnValue { function: function.name.clone(), index: 0 };
        abi_facts.push(BinaryAbiFact {
            subject: subject.clone(),
            kind: BinaryAbiFactKind::Return { index: 0, location: location.clone() },
            origin: origin.clone(),
            evidence: BinaryFactEvidence::AbiDefault,
            confidence: BinaryFactConfidence::Heuristic,
            trust_level: TrustLevel::Partial,
            assumptions: return_assumptions.clone(),
        });
        storage_facts.push(BinaryStorageFact {
            subject,
            location,
            ty: non_unit_ty(&summary.return_ty),
            mutable: None,
            alignment_bytes: None,
            valid_range: None,
            origin: origin.clone(),
            evidence: BinaryFactEvidence::AbiDefault,
            confidence: BinaryFactConfidence::Heuristic,
            trust_level: TrustLevel::Partial,
            assumptions: return_assumptions,
        });
    }

    let signature = BinaryFunctionSignature {
        name: function.name.clone(),
        entry: function.entry_point,
        calling_convention: convention,
        parameters,
        returns,
        origin,
        trust_level: TrustLevel::Partial,
        assumptions: provenance_assumptions(&summary, "signature summary"),
        ..Default::default()
    };

    (signature, abi_facts, storage_facts)
}

fn lift_arch_from_name(architecture: &str) -> Option<LiftArch> {
    match architecture {
        "AArch64" | "aarch64" | "arm64" => Some(LiftArch::Aarch64),
        "x86-64" | "x86_64" | "amd64" => Some(LiftArch::X86_64),
        _ => None,
    }
}

fn binary_calling_convention(convention: CallingConvention) -> BinaryCallingConvention {
    match convention {
        CallingConvention::Aapcs64 => BinaryCallingConvention::Aapcs64,
        CallingConvention::SysV64 => BinaryCallingConvention::SystemV,
        CallingConvention::Win64 => BinaryCallingConvention::Win64,
        CallingConvention::Unknown => BinaryCallingConvention::Unknown,
    }
}

fn register_bit_width(arch: LiftArch) -> Option<u32> {
    match arch {
        LiftArch::Aarch64 | LiftArch::X86_64 => Some(64),
    }
}

fn register_location(register: &str, bit_width: Option<u32>) -> BinaryStorageLocation {
    BinaryStorageLocation::Register { name: register.to_string(), bit_width }
}

fn non_unit_ty(ty: &Ty) -> Option<Ty> {
    (!matches!(ty, Ty::Unit)).then(|| ty.clone())
}

fn provenance_assumptions(summary: &FunctionSignature, fallback: &str) -> Vec<ModelAssumption> {
    provenance_assumptions_from_descriptions(summary.provenance.iter().cloned(), fallback)
}

fn provenance_assumptions_matching(
    summary: &FunctionSignature,
    needle: &str,
    fallback: &str,
) -> Vec<ModelAssumption> {
    provenance_assumptions_from_descriptions(
        summary.provenance.iter().filter(|description| description.contains(needle)).cloned(),
        fallback,
    )
}

fn provenance_assumptions_from_descriptions<I>(
    descriptions: I,
    fallback: &str,
) -> Vec<ModelAssumption>
where
    I: IntoIterator<Item = String>,
{
    let assumptions: Vec<_> = descriptions
        .into_iter()
        .map(|description| ModelAssumption {
            stage: "trust-lift::summarize_function_signature".to_string(),
            description,
        })
        .collect();

    if assumptions.is_empty() {
        vec![ModelAssumption {
            stage: "trust-decompile::abi-signature-adapter".to_string(),
            description: fallback.to_string(),
        }]
    } else {
        assumptions
    }
}

fn build_call_graph(
    lifted: &LiftedBinary,
    metadata: &BinaryArtifactMetadata,
) -> (CallGraph, Vec<UnsupportedRecord>) {
    let mut graph = CallGraph::new();
    let mut unsupported = Vec::new();
    let mut entry_to_def_path = HashMap::new();

    for function in &lifted.functions {
        let def_path = function_def_path(function);
        entry_to_def_path.insert(function.entry_point, def_path.clone());
        graph.add_node(CallGraphNode {
            def_path,
            name: function.name.clone(),
            is_public: false,
            is_entry_point: Some(function.entry_point) == metadata.entry_point,
            span: source_span_for_address(lifted, function.entry_point),
        });
    }

    for function in &lifted.functions {
        let caller = function_def_path(function);
        for block in &function.cfg.blocks {
            for edge in function.cfg.edges_for_block(block) {
                if edge.kind != CfgEdgeKind::Call {
                    continue;
                }

                let callee = match edge.target {
                    CfgEdgeTarget::Internal(addr) | CfgEdgeTarget::External(addr) => {
                        entry_to_def_path
                            .get(&addr)
                            .cloned()
                            .unwrap_or_else(|| format!("binary::0x{addr:x}"))
                    }
                    CfgEdgeTarget::Unresolved => {
                        unsupported.push(unsupported_record(
                            "trust-decompile",
                            Some(&metadata.architecture),
                            Some(function.entry_point),
                            Some(block.start_addr),
                            "unresolved indirect call target omitted from call graph",
                        ));
                        continue;
                    }
                    CfgEdgeTarget::None => continue,
                };

                graph.add_edge(CallGraphEdge {
                    caller: caller.clone(),
                    callee,
                    call_site: source_span_for_address(lifted, block.start_addr),
                });
            }
        }
    }

    (graph, unsupported)
}

fn collect_unsupported(
    lifted: &LiftedBinary,
    metadata: &BinaryArtifactMetadata,
) -> UnsupportedLedger {
    let mut ledger = UnsupportedLedger::default();

    for function in &lifted.functions {
        ledger.records.extend(function.unsupported.records.clone());
    }

    for failure in &lifted.failures {
        let name = failure.name.as_deref().unwrap_or("<unnamed>");
        ledger.records.push(unsupported_record(
            "trust-lift",
            Some(&metadata.architecture),
            Some(failure.entry_point),
            Some(failure.entry_point),
            &format!("failed to lift function {name}: {}", failure.error),
        ));
    }

    ledger
}

fn build_binary_metadata(lifted: &LiftedBinary, image_size_bytes: usize) -> BinaryArtifactMetadata {
    BinaryArtifactMetadata {
        format: binary_format(lifted.format),
        architecture: lifted.architecture.to_string(),
        entry_point: lifted.entry_point,
        byte_len: Some(image_size_bytes as u64),
        build_id: lifted.build_id.clone(),
        segments: lifted.segments.clone(),
        symbols: lifted
            .functions
            .iter()
            .map(|function| BinarySymbol {
                name: function.name.clone(),
                address: function.entry_point,
                size: function_address_range(function).map(|range| range.len()),
                kind: BinarySymbolKind::Function,
            })
            .collect(),
        ..Default::default()
    }
}

fn binary_format(format: &str) -> BinaryArtifactFormat {
    match format {
        "ELF" => BinaryArtifactFormat::Elf,
        "Mach-O" => BinaryArtifactFormat::MachO,
        "Fat Mach-O" => BinaryArtifactFormat::FatMachO,
        "PE/COFF" => BinaryArtifactFormat::Pe,
        "Wasm" | "WebAssembly" => BinaryArtifactFormat::Wasm,
        "Raw" | "raw" => BinaryArtifactFormat::Raw,
        _ => BinaryArtifactFormat::Unknown,
    }
}

fn lifted_format_name(format: BinaryArtifactFormat) -> &'static str {
    match format {
        BinaryArtifactFormat::Elf => "ELF",
        BinaryArtifactFormat::MachO => "Mach-O",
        BinaryArtifactFormat::FatMachO => "Fat Mach-O",
        BinaryArtifactFormat::Pe => "PE/COFF",
        BinaryArtifactFormat::Wasm => "Wasm",
        BinaryArtifactFormat::Raw => "Raw",
        BinaryArtifactFormat::Unknown => "unknown",
        _ => "unknown",
    }
}

fn shared_decompile_options(
    options: &DecompileOptions,
    lifted: &LiftedBinary,
    target: DecompileTarget,
) -> SharedDecompileOptions {
    let rust_requested = target == DecompileTarget::Rust;
    let mut shared = SharedDecompileOptions {
        target,
        strict: options.lift.strict,
        validate_reconstruction: false,
        recover_types: false,
        allow_partial: rust_requested || !options.lift.strict,
        emit_unsafe_rust: rust_requested,
        ..Default::default()
    };

    match &options.lift.functions {
        BinaryFunctionSelection::Entry => {
            if let Some(entry) = lifted.entry_point {
                shared.entry_points.push(entry);
            }
        }
        BinaryFunctionSelection::All => {}
        BinaryFunctionSelection::Addresses(addresses) => {
            shared.entry_points = addresses.clone();
        }
        BinaryFunctionSelection::Names(names) => {
            shared.function_names = names.clone();
        }
    }

    shared
}

fn reconstruction_target(requested: &[DecompileOutputKind]) -> DecompileTarget {
    if requested.contains(&DecompileOutputKind::TrustCgText) {
        DecompileTarget::TrustCg
    } else if requested.contains(&DecompileOutputKind::WasmText) {
        DecompileTarget::Wasm
    } else if requested.contains(&DecompileOutputKind::TrustCgUnsupported) {
        DecompileTarget::TrustCg
    } else if requested.contains(&DecompileOutputKind::WasmUnsupported) {
        DecompileTarget::Wasm
    } else if requested.contains(&DecompileOutputKind::RustSkeleton) {
        DecompileTarget::Rust
    } else {
        DecompileTarget::TrustIr
    }
}

fn is_rejected_output_kind(kind: DecompileOutputKind) -> bool {
    matches!(kind, DecompileOutputKind::TrustCgUnsupported | DecompileOutputKind::WasmUnsupported)
}

fn rejected_output_message(kind: DecompileOutputKind) -> &'static str {
    match kind {
        DecompileOutputKind::TrustCgUnsupported => {
            "trust-cg conversion backend is unavailable for binary-derived TrustIr; no trust_cg artifact was emitted"
        }
        DecompileOutputKind::WasmUnsupported => {
            "Wasm conversion backend is unavailable for binary-derived TrustIr; no Wasm artifact was emitted"
        }
        DecompileOutputKind::WasmText => {
            "Wasm conversion was rejected for binary-derived TrustIr; no Wasm artifact was emitted"
        }
        DecompileOutputKind::TrustCgText => {
            "trust-cg conversion was rejected for binary-derived TrustIr; no trust_cg artifact was emitted"
        }
        _ => "requested conversion backend is unavailable; no artifact was emitted",
    }
}

fn reconstruction_diagnostics(
    unsupported: &UnsupportedLedger,
    rust_requested: bool,
    source_diagnostics: &[String],
) -> Vec<String> {
    let mut diagnostics = Vec::new();
    if rust_requested {
        diagnostics.push("Rust skeleton output is exploratory and was not validated".to_string());
    }
    if !unsupported.records.is_empty() {
        diagnostics.push(format!("unsupported records: {}", unsupported.records.len()));
    }
    diagnostics.extend(source_diagnostics.iter().cloned());
    diagnostics
}

fn output_diagnostics_with_source(base: &[&str], source_diagnostics: &[String]) -> Vec<String> {
    let mut diagnostics: Vec<_> = base.iter().map(|diagnostic| (*diagnostic).to_string()).collect();
    diagnostics.extend(source_diagnostics.iter().cloned());
    diagnostics
}

fn target_validation_blockers_from_records(
    target: DecompileTarget,
    unsupported: &UnsupportedLedger,
    records: &[ReconstructionValidationRecord],
) -> Vec<TargetValidationBlocker> {
    let mut blockers: Vec<_> = unsupported
        .records
        .iter()
        .map(|record| TargetValidationBlocker {
            target: target.clone(),
            function: None,
            code: record.feature.clone(),
            stage: record.stage.clone(),
            feature: record.feature.clone(),
            reason: record.feature.clone(),
            origin: record.origin.clone(),
            diagnostics: vec![
                format!("stage={}", record.stage),
                format!("feature={}", record.feature),
            ],
        })
        .collect();

    blockers.extend(records.iter().filter_map(|record| {
        if !matches!(
            record.status,
            ReconstructionValidationStatus::Failed | ReconstructionValidationStatus::Refuted
        ) && record.trust_level != TrustLevel::Rejected
        {
            return None;
        }

        let reason = record
            .diagnostics
            .iter()
            .find(|diagnostic| !diagnostic.contains('='))
            .cloned()
            .unwrap_or_else(|| format!("{:?} output validation rejected", target));
        Some(TargetValidationBlocker {
            target: target.clone(),
            function: record.function.clone(),
            code: record
                .diagnostics
                .iter()
                .find_map(|diagnostic| diagnostic.strip_prefix("blocker-code="))
                .filter(|code| !code.is_empty())
                .unwrap_or("target-semantic-validation-missing")
                .to_string(),
            stage: "trust-decompile::target-validation".to_string(),
            feature: format!("{:?} validation blocker", target),
            reason,
            origin: None,
            diagnostics: record.diagnostics.clone(),
        })
    }));

    blockers
}

fn wasm_target_validation_blockers(
    blockers: &[WasmValidationBlocker],
) -> Vec<TargetValidationBlocker> {
    blockers
        .iter()
        .map(|blocker| TargetValidationBlocker {
            target: DecompileTarget::Wasm,
            function: None,
            code: blocker.code.clone(),
            stage: "trust-wasm-bridge::target-validation".to_string(),
            feature: blocker.code.clone(),
            reason: blocker.detail.clone(),
            origin: None,
            diagnostics: vec![format!("blocker-code={}", blocker.code), blocker.detail.clone()],
        })
        .collect()
}

fn symbolic_formula_target_validation_blockers(
    target: DecompileTarget,
    formulas: &[PreservedSymbolicFormula],
) -> Vec<TargetValidationBlocker> {
    formulas
        .iter()
        .map(|formula| {
            let mut diagnostics = vec![
                "blocker-code=symbolic-formula-proof-semantics".to_string(),
                "target-semantics-consumer=missing".to_string(),
                "required-evidence=formula-specific-checked-certificate".to_string(),
                "required-evidence=formula-specific-replay".to_string(),
                "checked-certificate=missing".to_string(),
                "replay=missing".to_string(),
                "proof-grade=false".to_string(),
                format!("location={}", formula.location),
                format!("formula.schema={SYMBOLIC_FORMULA_SCHEMA}"),
                format!("formula={:?}", formula.formula),
                format!("formula.smtlib2={}", formula.formula.to_smtlib()),
                format!("formula.sort={}", trust_types::infer_sort(&formula.formula).to_smtlib()),
                format!("formula.debug={:?}", formula.formula),
            ];
            match serde_json::to_string(&formula.formula) {
                Ok(formula_json) => diagnostics.push(format!("formula_json={formula_json}")),
                Err(error) => diagnostics.push(format!("formula_json_error={error}")),
            }
            if let Some(block) = formula.block {
                diagnostics.push(format!("block={block}"));
            }
            if let Some(statement_index) = formula.statement_index {
                diagnostics.push(format!("statement_index={statement_index}"));
            }

            TargetValidationBlocker {
                target: target.clone(),
                function: formula.function.clone(),
                code: "symbolic-formula-proof-semantics".to_string(),
                stage: symbolic_formula_target_validation_stage(&target).to_string(),
                feature: "symbolic-formula-proof-semantics".to_string(),
                reason:
                    "symbolic formula is preserved for inspection, but target proof semantics lack formula-specific checked certificate and replay metadata"
                        .to_string(),
                origin: None,
                diagnostics,
            }
        })
        .collect()
}

fn symbolic_formula_target_validation_stage(target: &DecompileTarget) -> &'static str {
    match target {
        DecompileTarget::TrustIr => "trust-ir-bridge::target-validation",
        DecompileTarget::TrustCg => "trust-cg-bridge::target-validation",
        DecompileTarget::Wasm => "trust-wasm-bridge::target-validation",
        _ => "trust-decompile::target-validation",
    }
}

fn symbolic_formula_target_validation_blockers_unless_consumed(
    target: DecompileTarget,
    formulas: &[PreservedSymbolicFormula],
    target_proof_consumer_accepted: bool,
) -> Vec<TargetValidationBlocker> {
    if target_proof_consumer_accepted {
        Vec::new()
    } else {
        symbolic_formula_target_validation_blockers(target, formulas)
    }
}

fn trust_ir_target_validation_blockers(
    functions: &[DecompiledFunction],
) -> Vec<TargetValidationBlocker> {
    let lifted: Vec<_> = functions.iter().filter_map(|function| function.lifted.as_ref()).collect();
    if lifted.is_empty() {
        return Vec::new();
    }
    let lifted_function_count = lifted.len();

    let module = match lower_functions_to_trust_ir("trust_ir-target-validation", lifted) {
        Ok(module) => module,
        Err(error) => {
            let reason = format!(
                "canonical TrustIr target validation could not run because lowering failed: {error}"
            );
            return vec![TargetValidationBlocker {
                target: DecompileTarget::TrustIr,
                function: None,
                code: TRUST_IR_TARGET_LOWERING_FAILED_BLOCKER.to_string(),
                stage: "trust-ir-bridge::target-validation".to_string(),
                feature: TRUST_IR_TARGET_LOWERING_FAILED_BLOCKER.to_string(),
                reason: reason.clone(),
                origin: None,
                diagnostics: vec![
                    format!("blocker-code={TRUST_IR_TARGET_LOWERING_FAILED_BLOCKER}"),
                    format!("lowering-error={error}"),
                    format!("lifted-function-count={lifted_function_count}"),
                    "target-validation=not-run".to_string(),
                    "target-semantics-consumer=missing".to_string(),
                    "fail-closed=true".to_string(),
                    "proof-grade=false".to_string(),
                ],
            }];
        }
    };

    let mut blockers = collect_layout_sensitive_cast_blockers(&module)
        .into_iter()
        .map(|blocker| TargetValidationBlocker {
            target: DecompileTarget::TrustIr,
            function: Some(blocker.function.clone()),
            code: TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_FEATURE.to_string(),
            stage: TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_STAGE.to_string(),
            feature: TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_FEATURE.to_string(),
            reason: blocker.reason_summary(),
            origin: None,
            diagnostics: blocker.diagnostics(),
        })
        .collect::<Vec<_>>();
    blockers.extend(trust_ir_thread_local_addr_target_validation_blockers(&module));
    blockers
}

fn trust_ir_thread_local_addr_target_validation_blockers(
    module: &trust_ir::Module,
) -> Vec<TargetValidationBlocker> {
    let mut blockers = Vec::new();

    // The sealed payload distinguishes a demonic TLS address from core
    // `Inst::Undef` poison, but carrying that payload is not evidence that a
    // target proof model consumed its semantics. Keep canonical payloads and
    // schema-shaped malformed near misses closed until such evidence exists.
    for function in &module.functions {
        for block in &function.blocks {
            for (statement_index, node) in block.body.iter().enumerate() {
                let trust_ir::Inst::DialectOp(op) = &node.inst else {
                    continue;
                };
                if op.dialect != trust_ir::dialect::trust_rust::DIALECT
                    || op.op != trust_ir::dialect::trust_rust::THREAD_LOCAL_ADDR_OP
                {
                    continue;
                }

                let decoded = trust_ir::dialect::trust_rust::decode_thread_local_addr(op);
                let node_shape_error = (node.results.len() != 1).then(|| {
                    format!(
                        "enclosing instruction has {} results instead of exactly one",
                        node.results.len()
                    )
                });
                let canonical = decoded.is_ok() && node_shape_error.is_none();
                let payload_detail = match (&decoded, &node_shape_error) {
                    (Ok(spec), None) => format!(
                        "canonical version-1 payload for TLS symbol {:?}",
                        spec.symbol
                    ),
                    (Ok(_), Some(error)) => error.clone(),
                    (Err(error), None) => format!("noncanonical payload: {error}"),
                    (Err(error), Some(shape_error)) => {
                        format!("noncanonical payload: {error}; {shape_error}")
                    }
                };
                let reason = if canonical {
                    format!(
                        "canonical trust_rust.thread_local_addr remains unconsumed by a checked target proof-semantics consumer ({payload_detail})"
                    )
                } else {
                    format!(
                        "trust_rust.thread_local_addr-shaped operation is noncanonical and remains fail-closed ({payload_detail})"
                    )
                };
                let mut diagnostics = vec![
                    format!("blocker-code={TRUST_IR_UNCONSUMED_THREAD_LOCAL_ADDR_BLOCKER}"),
                    "dialect-op=trust_rust.thread_local_addr".to_string(),
                    format!(
                        "dialect-payload={}",
                        if canonical { "canonical-v1" } else { "noncanonical" }
                    ),
                    format!("function={}", function.name),
                    format!("block={}", block.id.as_usize()),
                    format!("statement_index={statement_index}"),
                    format!("node-result-count={}", node.results.len()),
                    "target-semantics-consumer=missing".to_string(),
                    "required-evidence=checked-thread-local-address-semantics-consumer".to_string(),
                    "fail-closed=true".to_string(),
                    "proof-grade=false".to_string(),
                ];
                if let Ok(spec) = decoded {
                    diagnostics.push(format!("tls-symbol={:?}", spec.symbol));
                } else {
                    diagnostics.push(format!("payload-error={payload_detail}"));
                }

                blockers.push(TargetValidationBlocker {
                    target: DecompileTarget::TrustIr,
                    function: Some(function.name.clone()),
                    code: TRUST_IR_UNCONSUMED_THREAD_LOCAL_ADDR_BLOCKER.to_string(),
                    stage: "trust-ir-bridge::target-validation".to_string(),
                    feature: TRUST_IR_UNCONSUMED_THREAD_LOCAL_ADDR_BLOCKER.to_string(),
                    reason,
                    origin: None,
                    diagnostics,
                });
            }
        }
    }

    blockers
}

fn trust_cg_target_proof_consumer_accepted(conversion: &TrustCgTextConversion) -> bool {
    conversion.target_proof_consumer_accepted
}

#[cfg(feature = "trust-cg")]
fn trust_cg_target_validation_blockers(
    function: &DecompiledFunction,
    blockers: &[BinaryTrustCgValidationBlocker],
) -> Vec<TargetValidationBlocker> {
    blockers
        .iter()
        .map(|blocker| {
            trust_cg_target_validation_blocker(Some(function), &blocker.code, &blocker.detail)
        })
        .collect()
}

#[cfg(feature = "trust-cg")]
fn trust_cg_target_validation_blocker(
    function: Option<&DecompiledFunction>,
    code: &str,
    detail: &str,
) -> TargetValidationBlocker {
    trust_cg_target_validation_blocker_with_status(
        function,
        code,
        detail,
        CONVERSION_STATUS_INSPECTABLE_REJECTED,
    )
}

fn trust_cg_target_validation_blocker_with_status(
    function: Option<&DecompiledFunction>,
    code: &str,
    detail: &str,
    conversion_status: &str,
) -> TargetValidationBlocker {
    TargetValidationBlocker {
        target: DecompileTarget::TrustCg,
        function: function.map(|function| function.name.clone()),
        code: code.to_string(),
        stage: "trust-cg-bridge::target-validation".to_string(),
        feature: code.to_string(),
        reason: detail.to_string(),
        origin: function.and_then(function_origin),
        diagnostics: vec![
            format!("blocker-code={code}"),
            format!("conversion-status={conversion_status}"),
            "trust-level=rejected".to_string(),
            "proof-grade=false".to_string(),
            "fail-closed=true".to_string(),
            detail.to_string(),
        ],
    }
}

fn rejected_trust_cg_target_validation_blockers(
    function: Option<&DecompiledFunction>,
    code: &str,
    detail: &str,
) -> Vec<TargetValidationBlocker> {
    let mut blockers = vec![trust_cg_target_validation_blocker_with_status(
        function,
        code,
        detail,
        CONVERSION_STATUS_TRANSLATION_REJECTED,
    )];
    blockers.extend(
        [
            (
                "missing-target-semantic-validation",
                "trust-cg conversion was rejected before trust_cg target semantics validation could accept the artifact",
            ),
            (
                "missing-refinement-metadata",
                "trust-cg conversion has no bidirectional refinement metadata tying it to lifted TrustIr",
            ),
            (
                "missing-checked-proof-certificate",
                "trust-cg conversion has no checked proof certificate for the emitted artifact",
            ),
            (
                "missing-binary-proof-obligation",
                "trust-cg conversion has not discharged machine-code proof obligations",
            ),
        ]
        .into_iter()
        .map(|(code, detail)| {
            trust_cg_target_validation_blocker_with_status(
                function,
                code,
                detail,
                CONVERSION_STATUS_TRANSLATION_REJECTED,
            )
        }),
    );
    blockers
}

#[cfg(feature = "trust-cg")]
fn trust_cg_error_blocker_code(error: &BinaryTrustCgConversionError) -> &'static str {
    match error {
        BinaryTrustCgConversionError::MissingLiftedTrustIr { .. } => "missing-lifted-trust_ir",
        BinaryTrustCgConversionError::Lowering(_) => "trust_cg-lowering-failed",
        BinaryTrustCgConversionError::Validation(_) => "trust_cg-lir-structural-validation-failed",
        _ => "trust_cg-conversion-failed",
    }
}

fn function_origin(function: &DecompiledFunction) -> Option<BinaryOrigin> {
    (function.entry != 0).then(|| BinaryOrigin {
        binary_path: None,
        function_entry: Some(function.entry),
        instruction_address: function.entry,
        instruction_size: None,
        encoding: None,
        instruction_bytes: vec![],
        source: Some(SourceSpan::binary_address(function.entry)),
    })
}

fn preserved_symbolic_formulas_for_target(
    target: DecompileTarget,
    functions: &[DecompiledFunction],
) -> Vec<PreservedSymbolicFormula> {
    let mut formulas = Vec::new();
    for function in functions {
        if let Some(lifted) = &function.lifted {
            for block in &lifted.body.blocks {
                for (statement_index, statement) in block.stmts.iter().enumerate() {
                    collect_symbolic_formulas_from_statement(
                        &target,
                        &function.name,
                        block.id.0,
                        statement_index,
                        statement,
                        &mut formulas,
                    );
                }
                collect_symbolic_formulas_from_terminator(
                    &target,
                    &function.name,
                    block.id.0,
                    &block.terminator,
                    &mut formulas,
                );
            }
        }
    }
    formulas
}

fn collect_symbolic_formulas_from_statement(
    target: &DecompileTarget,
    function: &str,
    block: usize,
    statement_index: usize,
    statement: &Statement,
    formulas: &mut Vec<PreservedSymbolicFormula>,
) {
    match statement {
        Statement::Assign { rvalue, .. } => collect_symbolic_formulas_from_rvalue(
            target,
            function,
            block,
            Some(statement_index),
            "statement.assign",
            rvalue,
            formulas,
        ),
        Statement::Intrinsic { args, .. } | Statement::Unsupported { operands: args, .. } => {
            for operand in args {
                collect_symbolic_formula_from_operand(
                    target,
                    function,
                    block,
                    Some(statement_index),
                    "statement.operands",
                    operand,
                    formulas,
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

#[cfg(feature = "trust-cg")]
fn trust_cg_preserved_symbolic_formulas(
    formulas: &[BinaryTrustCgSymbolicFormula],
) -> Vec<PreservedSymbolicFormula> {
    formulas
        .iter()
        .map(|formula| PreservedSymbolicFormula {
            target: DecompileTarget::TrustCg,
            function: Some(formula.function.clone()),
            block: Some(formula.block),
            statement_index: Some(formula.statement_index),
            location: formula.operand.clone(),
            formula: formula.formula.clone(),
        })
        .collect()
}

fn wasm_preserved_symbolic_formulas(
    formulas: &[WasmSymbolicFormula],
) -> Vec<PreservedSymbolicFormula> {
    formulas
        .iter()
        .map(|formula| PreservedSymbolicFormula {
            target: DecompileTarget::Wasm,
            function: Some(formula.function.clone()),
            block: Some(formula.block),
            statement_index: Some(formula.statement_index),
            location: formula.operand.clone(),
            formula: formula.formula.clone(),
        })
        .collect()
}

fn merge_preserved_symbolic_formulas(
    mut preferred: Vec<PreservedSymbolicFormula>,
    fallback: Vec<PreservedSymbolicFormula>,
) -> Vec<PreservedSymbolicFormula> {
    for formula in fallback {
        let already_preserved = preferred.iter().any(|existing| {
            existing.target == formula.target
                && existing.function == formula.function
                && existing.block == formula.block
                && existing.statement_index == formula.statement_index
                && existing.formula == formula.formula
        });
        if !already_preserved {
            preferred.push(formula);
        }
    }
    preferred
}

fn collect_symbolic_formulas_from_rvalue(
    target: &DecompileTarget,
    function: &str,
    block: usize,
    statement_index: Option<usize>,
    location: &str,
    rvalue: &Rvalue,
    formulas: &mut Vec<PreservedSymbolicFormula>,
) {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Cast(operand, _)
        | Rvalue::Repeat(operand, _) => collect_symbolic_formula_from_operand(
            target,
            function,
            block,
            statement_index,
            location,
            operand,
            formulas,
        ),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            collect_symbolic_formula_from_operand(
                target,
                function,
                block,
                statement_index,
                location,
                lhs,
                formulas,
            );
            collect_symbolic_formula_from_operand(
                target,
                function,
                block,
                statement_index,
                location,
                rhs,
                formulas,
            );
        }
        Rvalue::Aggregate(_, operands) | Rvalue::Unsupported { operands, .. } => {
            for operand in operands {
                collect_symbolic_formula_from_operand(
                    target,
                    function,
                    block,
                    statement_index,
                    location,
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

fn collect_symbolic_formulas_from_terminator(
    target: &DecompileTarget,
    function: &str,
    block: usize,
    terminator: &Terminator,
    formulas: &mut Vec<PreservedSymbolicFormula>,
) {
    match terminator {
        Terminator::SwitchInt { discr, .. } => collect_symbolic_formula_from_operand(
            target,
            function,
            block,
            None,
            "terminator.switch_int",
            discr,
            formulas,
        ),
        Terminator::Call { args, .. } => {
            for operand in args {
                collect_symbolic_formula_from_operand(
                    target,
                    function,
                    block,
                    None,
                    "terminator.call",
                    operand,
                    formulas,
                );
            }
        }
        Terminator::Assert { cond, .. } => collect_symbolic_formula_from_operand(
            target,
            function,
            block,
            None,
            "terminator.assert",
            cond,
            formulas,
        ),
        Terminator::Goto(_)
        | Terminator::Return
        | Terminator::Drop { .. }
        | Terminator::Opaque { .. }
        | Terminator::Unreachable => {}
        _ => {}
    }
}

fn collect_symbolic_formula_from_operand(
    target: &DecompileTarget,
    function: &str,
    block: usize,
    statement_index: Option<usize>,
    location: &str,
    operand: &Operand,
    formulas: &mut Vec<PreservedSymbolicFormula>,
) {
    if let Operand::Symbolic(formula) = operand {
        formulas.push(PreservedSymbolicFormula {
            target: target.clone(),
            function: Some(function.to_string()),
            block: Some(block),
            statement_index,
            location: location.to_string(),
            formula: formula.clone(),
        });
    }
}

fn conversion_is_rejected(
    validation: ReconstructionValidationStatus,
    trust_level: TrustLevel,
    unsupported: &UnsupportedLedger,
) -> bool {
    trust_level == TrustLevel::Rejected
        || matches!(
            validation,
            ReconstructionValidationStatus::Failed | ReconstructionValidationStatus::Refuted
        )
        || !unsupported.records.is_empty()
}

fn output_is_rejected(output: &DecompiledOutput) -> bool {
    output.trust_level == TrustLevel::Rejected
        || matches!(
            output.validation,
            ReconstructionValidationStatus::Failed | ReconstructionValidationStatus::Refuted
        )
}

fn decompile_error_is_symbolic_formula_undef_blocker(error: &DecompileError) -> bool {
    matches!(
        error,
        DecompileError::TrustIrBridge(TrustIrBridgeError::UnsupportedOp(message))
            if message.contains("symbolic formula") && message.contains("Undef")
    )
}

fn rust_skeleton_validation_records(
    functions: &[DecompiledFunction],
) -> Vec<ReconstructionValidationRecord> {
    if functions.is_empty() {
        return vec![ReconstructionValidationRecord {
            target: DecompileTarget::Rust,
            candidate: ReconstructionCandidateKind::TextOnly,
            status: ReconstructionValidationStatus::NotAttempted,
            trust_level: TrustLevel::Exploratory,
            evidence: vec![
                ReconstructionValidationEvidence::TextOnlyCandidateRejected,
                ReconstructionValidationEvidence::MissingComparableTrustIr,
            ],
            diagnostics: vec![
                "Rust skeleton is text-only; no lifted binary TrustIr function was available"
                    .to_string(),
                "Rust skeleton was rejected as semantic validation evidence".to_string(),
                "validation was not attempted".to_string(),
            ],
            ..Default::default()
        }];
    }

    functions
        .iter()
        .map(|function| ReconstructionValidationRecord {
            target: DecompileTarget::Rust,
            function: Some(function.name.clone()),
            lifted_function: function.lifted.as_ref().map(|lifted| lifted.name.clone()),
            reconstructed_function: None,
            candidate: ReconstructionCandidateKind::TextOnly,
            status: ReconstructionValidationStatus::NotAttempted,
            trust_level: TrustLevel::Exploratory,
            forward: None,
            reverse: None,
            evidence: vec![
                ReconstructionValidationEvidence::TextOnlyCandidateRejected,
                ReconstructionValidationEvidence::MissingComparableTrustIr,
            ],
            diagnostics: vec![
                "Rust skeleton is text-only; no structured reconstructed TrustIr candidate was supplied"
                    .to_string(),
                "Rust skeleton was rejected as semantic validation evidence".to_string(),
                "validation was not attempted".to_string(),
            ],
        })
        .collect()
}

fn validated_rust_reconstruction(functions: &[DecompiledFunction]) -> ValidatedRustReconstruction {
    let candidates: Vec<_> = if functions.is_empty() {
        vec![StrictRustSubsetCandidate::missing()]
    } else {
        functions.iter().map(strict_rust_subset_candidate).collect()
    };
    let eligibility: Vec<_> =
        candidates.iter().map(|candidate| candidate.eligibility.clone()).collect();
    let validation_records: Vec<_> =
        candidates.iter().map(validated_rust_validation_record).collect();
    let status = validation_status_from_records(&validation_records);
    let trust_level = if validation_records
        .iter()
        .any(|record| matches!(record.trust_level, TrustLevel::Rejected))
    {
        TrustLevel::Rejected
    } else {
        TrustLevel::Exploratory
    };

    ValidatedRustReconstruction {
        status,
        trust_level,
        diagnostics: vec![
            "validated Rust reconstruction path is structured, but production compile-back TrustIr evidence was not supplied"
                .to_string(),
            format!(
                "strict subset candidates emitted: {}",
                candidates.iter().filter(|candidate| candidate.source_text.is_some()).count()
            ),
            "RustSkeleton output remains exploratory text and is not this validation path"
                .to_string(),
        ],
        eligibility,
        validation_records,
    }
}

#[derive(Debug, Clone)]
struct StrictRustSubsetCandidate {
    eligibility: RustReconstructionEligibility,
    source_text: Option<String>,
    validation_input: Option<VerifiableFunction>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
enum RustCompileBackEvidence {
    Missing,
    ValidatedPartial { proof_certificates: usize },
    ProofGrade { proof_certificates: usize },
}

const RUST_COMPILE_BACK_PROOF_GRADE_EVIDENCE: &str = "compile-back-proof-grade";
const RUST_COMPILE_BACK_CHECKED_CERTIFICATE_IDENTITY_EVIDENCE: &str =
    "compile-back-checked-certificate-identity";
const RUST_COMPILE_BACK_TARGET_CONSUMER_ACCEPTANCE_EVIDENCE: &str =
    "compile-back-target-consumer-accepted";
const RUST_COMPILE_BACK_SYMBOLIC_FORMULA_CONSUMER_ACCEPTANCE_EVIDENCE: &str =
    "compile-back-symbolic-formula-consumer-accepted";
const RUST_COMPILE_BACK_SOURCE_BACKPROP_GATE_EVIDENCE: &str =
    "compile-back-source-backpropagation-gate-accepted";
const RUST_COMPILE_BACK_LIFTED_BINARY_TRUST_IR_BINDING_EVIDENCE: &str =
    "compile-back-lifted-binary-trust_ir-bound";
const RUST_COMPILE_BACK_CHECKED_CERTIFICATE_BINDING_EVIDENCE: &str =
    "compile-back-checked-certificate-bound";
const RUST_COMPILE_BACK_REPLAY_IDENTITY_BINDING_EVIDENCE: &str =
    "compile-back-replay-identity-bound";
const RUST_COMPILE_BACK_SOURCE_GATE_BINDING_EVIDENCE: &str = "compile-back-source-gate-bound";
const RUST_COMPILE_BACK_UNSUPPORTED_LEDGER_ELIMINATION_EVIDENCE: &str =
    "compile-back-unsupported-ledger-eliminated";
const RUST_COMPILE_BACK_ARTIFACT_DIGEST_BINDING_EVIDENCE: &str =
    "compile-back-artifact-digests-bound";
const RUST_COMPILE_BACK_LIFTED_BINARY_TRUST_IR_SHA256_EVIDENCE_PREFIX: &str =
    "compile-back-lifted-binary-trust_ir-sha256=";
const RUST_COMPILE_BACK_RUST_SOURCE_SHA256_EVIDENCE_PREFIX: &str =
    "compile-back-rust-source-sha256=";
const RUST_COMPILE_BACK_RECONSTRUCTED_TRUST_IR_SHA256_EVIDENCE_PREFIX: &str =
    "compile-back-reconstructed-trust_ir-sha256=";
const RUST_COMPILE_BACK_REFINEMENT_ARTIFACT_SHA256_EVIDENCE_PREFIX: &str =
    "compile-back-refinement-artifact-sha256=";
const RUST_COMPILE_BACK_ROOT_ARTIFACT_SHA256_EVIDENCE_PREFIX: &str =
    "compile-back-root-artifact-sha256=";
const RUST_COMPILE_BACK_SELECTED_IMAGE_SHA256_EVIDENCE_PREFIX: &str =
    "compile-back-selected-image-sha256=";
const RUST_COMPILE_BACK_SELECTED_IMAGE_RANGE_EVIDENCE_PREFIX: &str =
    "compile-back-selected-image-range=";

#[derive(Debug, Clone, PartialEq, Eq)]
struct RustCompileBackValidationDecision {
    status: ReconstructionValidationStatus,
    trust_level: TrustLevel,
    forward: Option<ReconstructionValidationDirectionRecord>,
    reverse: Option<ReconstructionValidationDirectionRecord>,
    evidence: Vec<ReconstructionValidationEvidence>,
    diagnostics: Vec<String>,
}

impl StrictRustSubsetCandidate {
    fn missing() -> Self {
        Self {
            eligibility: RustReconstructionEligibility {
                function: None,
                eligible: false,
                rejections: vec![RustReconstructionRejectionKind::MissingLiftedTrustIr],
                evidence: vec![ReconstructionValidationEvidence::MissingComparableTrustIr],
                diagnostics: vec![
                    "validated Rust reconstruction rejected: no lifted binary TrustIr function was available"
                        .to_string(),
                ],
                ..Default::default()
            },
            source_text: None,
            validation_input: None,
        }
    }
}

fn strict_rust_subset_candidate(function: &DecompiledFunction) -> StrictRustSubsetCandidate {
    let Some(lifted) = function.lifted.as_ref() else {
        return StrictRustSubsetCandidate {
            eligibility: RustReconstructionEligibility {
                function: Some(function.name.clone()),
                eligible: false,
                rejections: vec![RustReconstructionRejectionKind::MissingLiftedTrustIr],
                evidence: vec![ReconstructionValidationEvidence::MissingComparableTrustIr],
                diagnostics: vec![
                    "validated Rust reconstruction rejected: missing lifted binary TrustIr"
                        .to_string(),
                ],
                ..Default::default()
            },
            source_text: None,
            validation_input: None,
        };
    };

    let mut rejections = Vec::new();
    let mut evidence = Vec::new();
    let mut diagnostics = Vec::new();

    if !is_straight_line(lifted) {
        rejections.push(RustReconstructionRejectionKind::NonStraightLine);
        evidence.push(ReconstructionValidationEvidence::RejectedNonStraightLine);
        diagnostics.push(
            "validated Rust reconstruction rejected: function is not straight-line".to_string(),
        );
    }
    if has_lifted_memory(function, lifted) {
        rejections.push(RustReconstructionRejectionKind::MemoryAccess);
        evidence.push(ReconstructionValidationEvidence::RejectedMemoryAccess);
        diagnostics.push(
            "validated Rust reconstruction rejected: lifted memory access is outside the strict subset"
                .to_string(),
        );
    }
    if has_call(lifted) {
        rejections.push(RustReconstructionRejectionKind::Call);
        evidence.push(ReconstructionValidationEvidence::RejectedCall);
        diagnostics.push(
            "validated Rust reconstruction rejected: calls are outside the strict subset"
                .to_string(),
        );
    }
    if !function.unsupported.is_empty() {
        rejections.push(RustReconstructionRejectionKind::Unsupported);
        evidence.push(ReconstructionValidationEvidence::RejectedUnsupported);
        diagnostics.push(format!(
            "validated Rust reconstruction rejected: {} unsupported lifted feature(s) remain",
            function.unsupported.records.len()
        ));
    }

    let mut emitted = None;
    let eligible = rejections.is_empty();
    if eligible {
        match emit_strict_rust_subset(function, lifted) {
            Ok(source) => {
                evidence.push(ReconstructionValidationEvidence::StrictRustSubsetEligible);
                evidence.push(ReconstructionValidationEvidence::NoCheckedProofCertificate);
                evidence.push(ReconstructionValidationEvidence::NoBinaryProofObligation);
                diagnostics.push(
                    "strict Rust reconstruction subset candidate emitted; compile-back validation not attempted"
                        .to_string(),
                );
                diagnostics.push(format!("strict Rust reconstruction candidate source:\n{source}"));
                emitted = Some(source);
            }
            Err(reason) => {
                rejections.push(RustReconstructionRejectionKind::Other(
                    "strict-subset-emission".to_string(),
                ));
                evidence.push(ReconstructionValidationEvidence::RejectedUnsupported);
                diagnostics.push(format!(
                    "validated Rust reconstruction rejected: strict subset emitter could not produce source: {reason}"
                ));
            }
        }
    }

    let eligible = rejections.is_empty();
    StrictRustSubsetCandidate {
        eligibility: RustReconstructionEligibility {
            function: Some(function.name.clone()),
            eligible,
            rejections,
            evidence,
            diagnostics,
            ..Default::default()
        },
        source_text: emitted,
        validation_input: eligible.then(|| lifted.clone()),
    }
}

fn emit_strict_rust_subset(
    function: &DecompiledFunction,
    lifted: &VerifiableFunction,
) -> Result<String, String> {
    let block = lifted.body.blocks.first().ok_or_else(|| "missing basic block".to_string())?;
    if lifted.body.blocks.len() != 1 || !matches!(block.terminator, Terminator::Return) {
        return Err("only one return-terminated block is supported".to_string());
    }

    let mut out = String::new();
    let ident = rust_identifier(&function.name, 0);
    let args = (0..lifted.body.arg_count)
        .map(|arg| {
            let local = arg + 1;
            let ty = rust_ty(local_ty(lifted, local)?)?;
            Ok(format!("{}: {ty}", local_name(lifted, local, LocalRole::Arg)))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let return_ty = rust_ty(&lifted.body.return_ty)?;

    let _ = write!(out, "pub fn {ident}({})", args.join(", "));
    if lifted.body.return_ty != Ty::Unit {
        let _ = write!(out, " -> {return_ty}");
    }
    let _ = writeln!(out, " {{");

    for local in temp_locals(lifted) {
        let ty = rust_ty(local_ty(lifted, local)?)?;
        let _ = writeln!(out, "    let mut {}: {ty};", local_name(lifted, local, LocalRole::Temp));
    }

    let mut return_expr = None;
    for stmt in &block.stmts {
        match stmt {
            Statement::Assign { place, rvalue, .. } if place.projections.is_empty() => {
                let expr = rust_rvalue(lifted, rvalue)?;
                if place.local == 0 {
                    return_expr = Some(expr);
                } else {
                    let name = local_name(lifted, place.local, LocalRole::Temp);
                    let _ = writeln!(out, "    {name} = {expr};");
                }
            }
            Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::Coverage
            | Statement::ConstEvalCounter
            | Statement::Nop => {}
            _ => return Err(format!("unsupported statement in strict subset: {stmt:?}")),
        }
    }

    match (&lifted.body.return_ty, return_expr) {
        (Ty::Unit, _) => {}
        (_, Some(expr)) => {
            let _ = writeln!(out, "    {expr}");
        }
        _ => return Err("non-unit function did not assign the return local".to_string()),
    }

    let _ = writeln!(out, "}}");
    Ok(out)
}

#[derive(Clone, Copy)]
enum LocalRole {
    Arg,
    Temp,
}

fn temp_locals(function: &VerifiableFunction) -> impl Iterator<Item = usize> + '_ {
    function
        .body
        .locals
        .iter()
        .map(|local| local.index)
        .filter(|index| *index != 0 && *index > function.body.arg_count)
}

fn local_ty(function: &VerifiableFunction, local: usize) -> Result<&Ty, String> {
    function
        .body
        .locals
        .iter()
        .find(|decl| decl.index == local)
        .map(|decl| &decl.ty)
        .ok_or_else(|| format!("missing local declaration for _{local}"))
}

fn local_name(function: &VerifiableFunction, local: usize, role: LocalRole) -> String {
    let fallback = match role {
        LocalRole::Arg => format!("arg{local}"),
        LocalRole::Temp => format!("_local{local}"),
    };
    let raw = function
        .body
        .locals
        .iter()
        .find(|decl| decl.index == local)
        .and_then(|decl| decl.name.as_deref())
        .unwrap_or(&fallback);
    rust_identifier(raw, local)
}

fn rust_ty(ty: &Ty) -> Result<&'static str, String> {
    match ty {
        Ty::Bool => Ok("bool"),
        Ty::Int { width: 8, signed: false } => Ok("u8"),
        Ty::Int { width: 8, signed: true } => Ok("i8"),
        Ty::Int { width: 16, signed: false } => Ok("u16"),
        Ty::Int { width: 16, signed: true } => Ok("i16"),
        Ty::Int { width: 32, signed: false } => Ok("u32"),
        Ty::Int { width: 32, signed: true } => Ok("i32"),
        Ty::Int { width: 64, signed: false } => Ok("u64"),
        Ty::Int { width: 64, signed: true } => Ok("i64"),
        Ty::Int { width: 128, signed: false } => Ok("u128"),
        Ty::Int { width: 128, signed: true } => Ok("i128"),
        Ty::Float { width: 32 } => Ok("f32"),
        Ty::Float { width: 64 } => Ok("f64"),
        Ty::Bv(8) => Ok("u8"),
        Ty::Bv(16) => Ok("u16"),
        Ty::Bv(32) => Ok("u32"),
        Ty::Bv(64) => Ok("u64"),
        Ty::Bv(128) => Ok("u128"),
        Ty::Unit => Ok("()"),
        other => Err(format!("unsupported non-primitive type: {other:?}")),
    }
}

fn rust_rvalue(function: &VerifiableFunction, rvalue: &Rvalue) -> Result<String, String> {
    match rvalue {
        Rvalue::Use(operand) => rust_operand(function, operand),
        Rvalue::BinaryOp(op, lhs, rhs) => Ok(format!(
            "{} {} {}",
            rust_operand(function, lhs)?,
            rust_binop(*op)?,
            rust_operand(function, rhs)?
        )),
        Rvalue::UnaryOp(op, operand) => {
            Ok(format!("{}{}", rust_unop(*op)?, rust_operand(function, operand)?))
        }
        Rvalue::Cast(operand, ty) => {
            Ok(format!("{} as {}", rust_operand(function, operand)?, rust_ty(ty)?))
        }
        other => Err(format!("unsupported rvalue in strict subset: {other:?}")),
    }
}

fn rust_operand(function: &VerifiableFunction, operand: &Operand) -> Result<String, String> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => {
            if place.local == 0 {
                return Err(
                    "return local cannot be used as an operand in strict subset".to_string()
                );
            }
            let role = if place.local <= function.body.arg_count {
                LocalRole::Arg
            } else {
                LocalRole::Temp
            };
            Ok(local_name(function, place.local, role))
        }
        Operand::Constant(value) => rust_const(value),
        other => Err(format!("unsupported operand in strict subset: {other:?}")),
    }
}

fn rust_const(value: &ConstValue) -> Result<String, String> {
    match value {
        ConstValue::Bool(value) => Ok(value.to_string()),
        ConstValue::Int(value) => Ok(value.to_string()),
        ConstValue::Uint(value, _) => Ok(value.to_string()),
        ConstValue::Float(value) if value.is_finite() => Ok(value.to_string()),
        ConstValue::Unit => Ok("()".to_string()),
        ConstValue::CallableItem { .. } => {
            Err("callable-item identity is outside the strict decompile subset".to_string())
        }
        other => Err(format!("unsupported constant in strict subset: {other:?}")),
    }
}

fn rust_binop(op: BinOp) -> Result<&'static str, String> {
    match op {
        BinOp::Add => Ok("+"),
        BinOp::Sub => Ok("-"),
        BinOp::Mul => Ok("*"),
        BinOp::Div => Ok("/"),
        BinOp::Rem => Ok("%"),
        BinOp::Eq => Ok("=="),
        BinOp::Ne => Ok("!="),
        BinOp::Lt => Ok("<"),
        BinOp::Le => Ok("<="),
        BinOp::Gt => Ok(">"),
        BinOp::Ge => Ok(">="),
        BinOp::BitAnd => Ok("&"),
        BinOp::BitOr => Ok("|"),
        BinOp::BitXor => Ok("^"),
        BinOp::Shl => Ok("<<"),
        BinOp::Shr => Ok(">>"),
        other => Err(format!("unsupported binary operator in strict subset: {other:?}")),
    }
}

fn rust_unop(op: UnOp) -> Result<&'static str, String> {
    match op {
        UnOp::Not => Ok("!"),
        UnOp::Neg => Ok("-"),
        other => Err(format!("unsupported unary operator in strict subset: {other:?}")),
    }
}

fn strict_rust_compile_back_validation(
    candidate: &StrictRustSubsetCandidate,
    evidence: RustCompileBackEvidence,
) -> RustCompileBackValidationDecision {
    if !candidate.eligibility.eligible {
        return RustCompileBackValidationDecision {
            status: ReconstructionValidationStatus::Failed,
            trust_level: TrustLevel::Rejected,
            forward: None,
            reverse: None,
            evidence: vec![],
            diagnostics: vec![],
        };
    }

    match evidence {
        RustCompileBackEvidence::Missing => RustCompileBackValidationDecision {
            status: ReconstructionValidationStatus::NotAttempted,
            trust_level: TrustLevel::Exploratory,
            forward: None,
            reverse: None,
            evidence: vec![
                ReconstructionValidationEvidence::MissingComparableTrustIr,
                ReconstructionValidationEvidence::Other(
                    "compile-back-validation-missing".to_string(),
                ),
            ],
            diagnostics: vec![
                "compile-back validation evidence is missing; strict subset eligibility is not semantic validation"
                    .to_string(),
                "validated Rust reconstruction remains exploratory until reconstructed MIR is compared with lifted binary TrustIr"
                    .to_string(),
            ],
        },
        RustCompileBackEvidence::ValidatedPartial { proof_certificates } => {
            rust_compile_back_validated_decision(proof_certificates, TrustLevel::Partial)
        }
        RustCompileBackEvidence::ProofGrade { proof_certificates } if proof_certificates > 0 => {
            rust_compile_back_validated_decision(proof_certificates, TrustLevel::ProofGrade)
        }
        RustCompileBackEvidence::ProofGrade { .. } => RustCompileBackValidationDecision {
            status: ReconstructionValidationStatus::Unknown,
            trust_level: TrustLevel::Exploratory,
            forward: None,
            reverse: None,
            evidence: vec![ReconstructionValidationEvidence::NoCheckedProofCertificate],
            diagnostics: vec![
                "compile-back proof-grade evidence was requested without checked proof certificates"
                    .to_string(),
            ],
        },
    }
}

fn rust_compile_back_validated_decision(
    proof_certificates: usize,
    trust_level: TrustLevel,
) -> RustCompileBackValidationDecision {
    let proof_grade = trust_level == TrustLevel::ProofGrade;
    let mut evidence = vec![
        ReconstructionValidationEvidence::BidirectionalTrustIrRefinement,
        ReconstructionValidationEvidence::Other(if proof_grade {
            RUST_COMPILE_BACK_PROOF_GRADE_EVIDENCE.to_string()
        } else {
            "compile-back-validated-partial".to_string()
        }),
    ];
    let mut diagnostics = vec![if proof_grade {
        "compile-back validation accepted with proof-grade evidence".to_string()
    } else {
        "compile-back validation accepted reconstructed MIR evidence".to_string()
    }];
    if proof_grade {
        evidence.extend(
            [
                RUST_COMPILE_BACK_CHECKED_CERTIFICATE_IDENTITY_EVIDENCE,
                RUST_COMPILE_BACK_TARGET_CONSUMER_ACCEPTANCE_EVIDENCE,
                RUST_COMPILE_BACK_SYMBOLIC_FORMULA_CONSUMER_ACCEPTANCE_EVIDENCE,
                RUST_COMPILE_BACK_SOURCE_BACKPROP_GATE_EVIDENCE,
                RUST_COMPILE_BACK_LIFTED_BINARY_TRUST_IR_BINDING_EVIDENCE,
                RUST_COMPILE_BACK_CHECKED_CERTIFICATE_BINDING_EVIDENCE,
                RUST_COMPILE_BACK_REPLAY_IDENTITY_BINDING_EVIDENCE,
                RUST_COMPILE_BACK_SOURCE_GATE_BINDING_EVIDENCE,
                RUST_COMPILE_BACK_UNSUPPORTED_LEDGER_ELIMINATION_EVIDENCE,
            ]
            .into_iter()
            .map(|kind| ReconstructionValidationEvidence::Other(kind.to_string())),
        );
        diagnostics.push(
            "compile-back caller supplied checked certificate identity, target consumer acceptance, symbolic formula consumer acceptance, source-backpropagation gate evidence, and explicit lifted-binary TrustIr binding evidence"
                .to_string(),
        );
    }

    RustCompileBackValidationDecision {
        status: ReconstructionValidationStatus::Validated,
        trust_level,
        forward: Some(rust_compile_back_direction_record(
            ReconstructionValidationDirection::LiftedToOutput,
            proof_certificates,
            proof_grade,
        )),
        reverse: Some(rust_compile_back_direction_record(
            ReconstructionValidationDirection::OutputToLifted,
            proof_certificates,
            proof_grade,
        )),
        evidence,
        diagnostics,
    }
}

fn rust_compile_back_direction_record(
    direction: ReconstructionValidationDirection,
    proof_certificates: usize,
    proof_grade: bool,
) -> ReconstructionValidationDirectionRecord {
    ReconstructionValidationDirectionRecord {
        direction,
        status: ReconstructionValidationStatus::Validated,
        vc_count: proof_certificates,
        counterexamples: 0,
        proof_certificates,
        diagnostics: vec![if proof_grade {
            "compile-back direction validated with checked proof certificate evidence".to_string()
        } else {
            "compile-back direction validated by reconstructed MIR comparison".to_string()
        }],
    }
}

fn validated_rust_validation_record(
    candidate: &StrictRustSubsetCandidate,
) -> ReconstructionValidationRecord {
    rust_compile_back_validation_record(candidate, RustCompileBackEvidence::Missing)
}

fn rust_compile_back_validation_record(
    candidate: &StrictRustSubsetCandidate,
    evidence: RustCompileBackEvidence,
) -> ReconstructionValidationRecord {
    let decision = strict_rust_compile_back_validation(candidate, evidence);
    let mut evidence = candidate.eligibility.evidence.clone();
    evidence.extend(decision.evidence);
    let mut diagnostics = candidate.eligibility.diagnostics.clone();
    diagnostics.extend(decision.diagnostics);
    let reconstructed_function = if decision.forward.is_some() && decision.reverse.is_some() {
        candidate
            .validation_input
            .as_ref()
            .map(|input| format!("{}::compile_back_trust_ir", input.name))
    } else {
        None
    };

    ReconstructionValidationRecord {
        target: DecompileTarget::Rust,
        function: candidate.eligibility.function.clone(),
        lifted_function: candidate
            .validation_input
            .as_ref()
            .map(|input| input.name.clone())
            .or_else(|| candidate.eligibility.function.clone()),
        reconstructed_function,
        candidate: ReconstructionCandidateKind::ValidatedRustStrictSubset,
        status: decision.status,
        trust_level: decision.trust_level,
        forward: decision.forward,
        reverse: decision.reverse,
        evidence,
        diagnostics,
    }
}

#[cfg(test)]
fn attach_rust_compile_back_artifact_digest_bindings(artifact: &mut DecompilationArtifact) {
    if artifact.reconstruction.target != DecompileTarget::Rust {
        return;
    }

    let Some(rust_source_sha256) = artifact
        .reconstruction
        .outputs
        .iter()
        .find(|output| output.target == DecompileTarget::Rust)
        .and_then(|output| output.text.as_deref())
        .map(|source| stable_sha256_hex(source.as_bytes()))
    else {
        return;
    };

    let function_digests = compile_back_lifted_function_digests(&artifact.functions);
    let binary = artifact.binary.clone();

    if let Some(validated) = artifact.reconstruction.validated_rust.as_mut() {
        for record in &mut validated.validation_records {
            attach_rust_compile_back_artifact_digest_binding_to_record(
                record,
                &rust_source_sha256,
                &function_digests,
                &binary,
            );
        }
    }

    for output in &mut artifact.reconstruction.outputs {
        if output.target != DecompileTarget::Rust {
            continue;
        }
        for record in &mut output.validation_records {
            attach_rust_compile_back_artifact_digest_binding_to_record(
                record,
                &rust_source_sha256,
                &function_digests,
                &binary,
            );
        }
        if let Some(validated) = output.validated_rust.as_mut() {
            for record in &mut validated.validation_records {
                attach_rust_compile_back_artifact_digest_binding_to_record(
                    record,
                    &rust_source_sha256,
                    &function_digests,
                    &binary,
                );
            }
        }
    }
}

#[cfg(test)]
fn compile_back_lifted_function_digests(
    functions: &[DecompiledFunction],
) -> HashMap<String, String> {
    let mut digests = HashMap::new();
    for function in functions {
        let Some(lifted) = function.lifted.as_ref() else {
            continue;
        };
        let Some(digest) = verifiable_function_sha256(lifted) else {
            continue;
        };
        digests.insert(function.name.clone(), digest.clone());
        digests.insert(lifted.name.clone(), digest.clone());
        digests.insert(lifted.def_path.clone(), digest);
    }
    digests
}

#[cfg(test)]
fn attach_rust_compile_back_artifact_digest_binding_to_record(
    record: &mut ReconstructionValidationRecord,
    rust_source_sha256: &str,
    function_digests: &HashMap<String, String>,
    binary: &BinaryArtifactMetadata,
) {
    if !rust_compile_back_record_allows_proof_grade(record) {
        return;
    }
    let Some(lifted_function) = record.lifted_function.as_deref() else {
        return;
    };
    let Some(lifted_trust_ir_sha256) = function_digests.get(lifted_function) else {
        return;
    };
    let compile_back_trust_ir_sha256 = lifted_trust_ir_sha256.as_str();
    let Some(root) = binary.root_artifact_digest.as_ref() else {
        return;
    };
    let Some(selected) = binary.selected_image.as_ref() else {
        return;
    };
    let Some(end_offset) = selected.end_offset() else {
        return;
    };
    let Some(refinement_sha256) = rust_compile_back_refinement_artifact_sha256(
        record,
        binary,
        lifted_trust_ir_sha256,
        rust_source_sha256,
        compile_back_trust_ir_sha256,
    ) else {
        return;
    };

    push_unique_compile_back_evidence(
        record,
        ReconstructionValidationEvidence::Other(
            RUST_COMPILE_BACK_ARTIFACT_DIGEST_BINDING_EVIDENCE.to_string(),
        ),
    );
    push_unique_compile_back_evidence(
        record,
        ReconstructionValidationEvidence::Other(format!(
            "{RUST_COMPILE_BACK_LIFTED_BINARY_TRUST_IR_SHA256_EVIDENCE_PREFIX}{lifted_trust_ir_sha256}"
        )),
    );
    push_unique_compile_back_evidence(
        record,
        ReconstructionValidationEvidence::Other(format!(
            "{RUST_COMPILE_BACK_RUST_SOURCE_SHA256_EVIDENCE_PREFIX}{rust_source_sha256}"
        )),
    );
    push_unique_compile_back_evidence(
        record,
        ReconstructionValidationEvidence::Other(format!(
            "{RUST_COMPILE_BACK_RECONSTRUCTED_TRUST_IR_SHA256_EVIDENCE_PREFIX}{compile_back_trust_ir_sha256}"
        )),
    );
    push_unique_compile_back_evidence(
        record,
        ReconstructionValidationEvidence::Other(format!(
            "{RUST_COMPILE_BACK_REFINEMENT_ARTIFACT_SHA256_EVIDENCE_PREFIX}{refinement_sha256}"
        )),
    );
    push_unique_compile_back_evidence(
        record,
        ReconstructionValidationEvidence::Other(format!(
            "{RUST_COMPILE_BACK_ROOT_ARTIFACT_SHA256_EVIDENCE_PREFIX}{}",
            root.value
        )),
    );
    push_unique_compile_back_evidence(
        record,
        ReconstructionValidationEvidence::Other(format!(
            "{RUST_COMPILE_BACK_SELECTED_IMAGE_SHA256_EVIDENCE_PREFIX}{}",
            selected.sha256
        )),
    );
    push_unique_compile_back_evidence(
        record,
        ReconstructionValidationEvidence::Other(format!(
            "{RUST_COMPILE_BACK_SELECTED_IMAGE_RANGE_EVIDENCE_PREFIX}{}..{}",
            selected.file_offset, end_offset
        )),
    );
    record.diagnostics.push(
        "compile-back artifact digest binding accepted: Rust source, compile-back TrustIr, refinement artifact, lifted binary TrustIr, and binary image digests agree"
            .to_string(),
    );
}

#[cfg(test)]
fn push_unique_compile_back_evidence(
    record: &mut ReconstructionValidationRecord,
    evidence: ReconstructionValidationEvidence,
) {
    if !record.evidence.iter().any(|existing| existing == &evidence) {
        record.evidence.push(evidence);
    }
}

fn is_straight_line(function: &VerifiableFunction) -> bool {
    function.body.blocks.len() == 1
        && function
            .body
            .blocks
            .first()
            .is_some_and(|block| matches!(block.terminator, Terminator::Return))
}

fn has_call(function: &VerifiableFunction) -> bool {
    function.body.blocks.iter().any(|block| matches!(block.terminator, Terminator::Call { .. }))
}

fn has_lifted_memory(function: &DecompiledFunction, lifted: &VerifiableFunction) -> bool {
    !function.memory_accesses.is_empty()
        || lifted
            .body
            .blocks
            .iter()
            .flat_map(|block| block.stmts.iter())
            .any(statement_mentions_memory)
}

fn statement_mentions_memory(statement: &Statement) -> bool {
    match statement {
        Statement::Assign { place, rvalue, .. } => {
            place
                .projections
                .iter()
                .any(|projection| matches!(projection, trust_types::Projection::Deref))
                || rvalue_mentions_memory(rvalue)
        }
        Statement::Retag { .. } | Statement::PlaceMention(_) => true,
        _ => false,
    }
}

fn rvalue_mentions_memory(rvalue: &trust_types::Rvalue) -> bool {
    match rvalue {
        trust_types::Rvalue::Ref { .. }
        | trust_types::Rvalue::AddressOf(..)
        | trust_types::Rvalue::CopyForDeref(_) => true,
        trust_types::Rvalue::Use(operand)
        | trust_types::Rvalue::UnaryOp(_, operand)
        | trust_types::Rvalue::Cast(operand, _)
        | trust_types::Rvalue::Repeat(operand, _) => operand_mentions_memory(operand),
        trust_types::Rvalue::BinaryOp(_, lhs, rhs)
        | trust_types::Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_mentions_memory(lhs) || operand_mentions_memory(rhs)
        }
        trust_types::Rvalue::Aggregate(_, operands) => operands.iter().any(operand_mentions_memory),
        trust_types::Rvalue::Discriminant(place) | trust_types::Rvalue::Len(place) => place
            .projections
            .iter()
            .any(|projection| matches!(projection, trust_types::Projection::Deref)),
        _ => false,
    }
}

fn operand_mentions_memory(operand: &trust_types::Operand) -> bool {
    match operand {
        trust_types::Operand::Copy(place) | trust_types::Operand::Move(place) => place
            .projections
            .iter()
            .any(|projection| matches!(projection, trust_types::Projection::Deref)),
        _ => false,
    }
}

fn trust_ir_self_validation_records(
    functions: &[DecompiledFunction],
) -> Vec<ReconstructionValidationRecord> {
    functions
        .iter()
        .filter_map(|function| {
            let lifted = function.lifted.as_ref()?;
            Some(ReconstructionValidationRecord {
                target: DecompileTarget::TrustIr,
                function: Some(function.name.clone()),
                lifted_function: Some(lifted.name.clone()),
                reconstructed_function: Some(lifted.name.clone()),
                candidate: ReconstructionCandidateKind::StructuredTrustIr,
                status: ReconstructionValidationStatus::Validated,
                trust_level: TrustLevel::Partial,
                forward: Some(trust_ir_self_validation_direction_record(
                    ReconstructionValidationDirection::LiftedToOutput,
                )),
                reverse: Some(trust_ir_self_validation_direction_record(
                    ReconstructionValidationDirection::OutputToLifted,
                )),
                evidence: vec![
                    ReconstructionValidationEvidence::TrustIrIdentitySelfCheck,
                    ReconstructionValidationEvidence::BidirectionalTrustIrRefinement,
                    ReconstructionValidationEvidence::NoCheckedProofCertificate,
                    ReconstructionValidationEvidence::NoBinaryProofObligation,
                ],
                diagnostics: vec![
                    "structured TrustIr output is the lifted binary TrustIr candidate".to_string(),
                    "validated means partial TrustIr consistency, not validated Rust reconstruction"
                        .to_string(),
                    "self-validation is reconstruction consistency only; not proof-grade"
                        .to_string(),
                ],
            })
        })
        .collect()
}

fn trust_ir_self_validation_direction_record(
    direction: ReconstructionValidationDirection,
) -> ReconstructionValidationDirectionRecord {
    ReconstructionValidationDirectionRecord {
        direction,
        status: ReconstructionValidationStatus::Validated,
        vc_count: 0,
        counterexamples: 0,
        proof_certificates: 0,
        diagnostics: vec![
            "identity TrustIr comparison; no proof certificate or binary proof obligation discharged"
                .to_string(),
        ],
    }
}

fn validation_status_from_records(
    records: &[ReconstructionValidationRecord],
) -> ReconstructionValidationStatus {
    validation_status_from_statuses(records.iter().map(|record| record.status))
}

fn reconstruction_validation_status(
    target: &DecompileTarget,
    outputs: &[DecompiledOutput],
    validated_rust: Option<&ValidatedRustReconstruction>,
) -> ReconstructionValidationStatus {
    if *target == DecompileTarget::Rust {
        return validated_rust
            .map(|validated| validated.status)
            .unwrap_or(ReconstructionValidationStatus::NotAttempted);
    }

    validation_status_from_statuses(
        outputs.iter().filter(|output| output.target == *target).map(|output| output.validation),
    )
}

fn validation_status_from_statuses<I>(statuses: I) -> ReconstructionValidationStatus
where
    I: IntoIterator<Item = ReconstructionValidationStatus>,
{
    let statuses: Vec<_> = statuses.into_iter().collect();
    if statuses.is_empty() {
        return ReconstructionValidationStatus::NotAttempted;
    }

    if statuses.iter().any(|status| matches!(status, ReconstructionValidationStatus::Refuted)) {
        return ReconstructionValidationStatus::Refuted;
    }

    if statuses.iter().any(|status| matches!(status, ReconstructionValidationStatus::Failed)) {
        return ReconstructionValidationStatus::Failed;
    }

    if statuses.iter().all(|status| matches!(status, ReconstructionValidationStatus::Validated)) {
        return ReconstructionValidationStatus::Validated;
    }

    if statuses.iter().all(|status| matches!(status, ReconstructionValidationStatus::NotAttempted))
    {
        return ReconstructionValidationStatus::NotAttempted;
    }

    ReconstructionValidationStatus::Unknown
}

fn binary_memory_model(
    lifted: &LiftedBinary,
    binary: &BinaryArtifactMetadata,
    accesses: Vec<MemoryAccessFact>,
) -> BinaryMemoryModel {
    let mut model = lifted.memory_model.clone();
    if model.pointer_width_bits.is_none() {
        model.pointer_width_bits = pointer_width_bits(&binary.architecture);
    }
    if model.endianness == Endianness::Unknown {
        model.endianness = endianness(&binary.architecture);
    }
    model.accesses = accesses;
    if model.trust_level == TrustLevel::ProofGrade {
        model.trust_level = TrustLevel::Partial;
    }
    model
}

fn pointer_width_bits(architecture: &str) -> Option<u32> {
    match architecture {
        "x86-64" | "AArch64" => Some(64),
        "x86" | "ARM" => Some(32),
        _ => None,
    }
}

fn endianness(architecture: &str) -> Endianness {
    match architecture {
        "x86-64" | "x86" | "AArch64" | "ARM" => Endianness::Little,
        _ => Endianness::Unknown,
    }
}

fn aggregate_coverage(lifted: &LiftedBinary) -> BinaryCoverageSummary {
    let instructions = lifted.functions.iter().map(instruction_count).sum();
    let unsupported_instructions =
        lifted.functions.iter().map(|function| function.unsupported.records.len()).sum::<usize>()
            + lifted.failures.len();

    BinaryCoverageSummary {
        functions_discovered: lifted.functions.len() + lifted.failures.len(),
        functions_lifted: lifted.functions.len(),
        instructions_discovered: instructions,
        instructions_lifted: instructions,
        unsupported_instructions,
        unresolved_edges: lifted.functions.iter().map(unresolved_edge_count).sum(),
        ..Default::default()
    }
}

fn instruction_count(function: &LiftedFunction) -> usize {
    function.cfg.blocks.iter().map(|block| block.instructions.len()).sum()
}

fn unresolved_edge_count(function: &LiftedFunction) -> usize {
    function
        .cfg
        .blocks
        .iter()
        .flat_map(|block| function.cfg.edges_for_block(block))
        .filter(|edge| edge.target == CfgEdgeTarget::Unresolved)
        .count()
}

fn function_address_range(function: &LiftedFunction) -> Option<BinaryAddressRange> {
    let mut start = None::<u64>;
    let mut end = None::<u64>;

    for block in &function.cfg.blocks {
        start = Some(start.map_or(block.start_addr, |current| current.min(block.start_addr)));
        let block_end = block
            .instructions
            .iter()
            .map(|instruction| instruction.address.saturating_add(u64::from(instruction.size)))
            .max()
            .unwrap_or(block.start_addr);
        end = Some(end.map_or(block_end, |current| current.max(block_end)));
    }

    start.map(|start| BinaryAddressRange {
        start,
        end: end.unwrap_or(start).max(start.saturating_add(1)),
    })
}

fn binary_origin_with_source(
    instruction_address: u64,
    function_entry: Option<u64>,
    source: SourceSpan,
) -> BinaryOrigin {
    BinaryOrigin {
        binary_path: None,
        function_entry,
        instruction_address,
        instruction_size: None,
        encoding: None,
        instruction_bytes: vec![],
        source: Some(source),
    }
}

struct BuildOutputsInput<'a> {
    metadata: &'a BinaryArtifactMetadata,
    functions: &'a [DecompiledFunction],
    call_graph: &'a CallGraph,
    memory_facts: &'a [MemoryAccessFact],
    unsupported: &'a UnsupportedLedger,
    source_provenance: &'a BinarySourceProvenanceSummary,
    requested: &'a [DecompileOutputKind],
    source_assumptions: &'a [ModelAssumption],
    source_diagnostics: &'a [String],
}

fn build_outputs(input: BuildOutputsInput<'_>) -> Result<Vec<DecompiledOutput>, DecompileError> {
    let BuildOutputsInput {
        metadata,
        functions,
        call_graph,
        memory_facts,
        unsupported,
        source_provenance,
        requested,
        source_assumptions,
        source_diagnostics,
    } = input;
    let mut outputs = Vec::with_capacity(requested.len());
    for kind in requested {
        let mut output = match kind {
            DecompileOutputKind::TrustIrJson => {
                let validation_records = trust_ir_self_validation_records(functions);
                let preserved_symbolic_formulas =
                    preserved_symbolic_formulas_for_target(DecompileTarget::TrustIr, functions);
                let mut target_validation_blockers =
                    trust_ir_target_validation_blockers(functions);
                target_validation_blockers.extend(symbolic_formula_target_validation_blockers(
                    DecompileTarget::TrustIr,
                    &preserved_symbolic_formulas,
                ));
                match render_trust_ir_json(
                    metadata,
                    functions,
                    call_graph,
                    memory_facts,
                    unsupported,
                    source_provenance,
                    None,
                ) {
                    Ok(text) => DecompiledOutput {
                        target: DecompileTarget::TrustIr,
                        text: Some(text),
                        validation: validation_status_from_records(&validation_records),
                        trust_level: TrustLevel::Partial,
                        validation_records,
                        target_validation_blockers,
                        preserved_symbolic_formulas,
                        assumptions: source_assumptions.to_vec(),
                        diagnostics: output_diagnostics_with_source(
                            &[
                                "format=trust_ir-json",
                                "validation-records=structured-trust_ir-self",
                                "self-validation is partial; not proof-grade",
                            ],
                            source_diagnostics,
                        ),
                        ..Default::default()
                    },
                    Err(error) if decompile_error_is_symbolic_formula_undef_blocker(&error) => {
                        let reason = error.to_string();
                        let mut target_validation_blockers = target_validation_blockers;
                        target_validation_blockers.push(TargetValidationBlocker {
                            target: DecompileTarget::TrustIr,
                            function: None,
                            code: "symbolic-formula-undef-blocked".to_string(),
                            stage: "trust-ir-bridge::target-validation".to_string(),
                            feature: "symbolic-formula-undef-blocked".to_string(),
                            reason,
                            origin: None,
                            diagnostics: vec![
                                "blocker-code=symbolic-formula-undef-blocked".to_string(),
                                "fail-closed=true".to_string(),
                                "proof-grade=false".to_string(),
                            ],
                        });
                        DecompiledOutput {
                            target: DecompileTarget::TrustIr,
                            text: None,
                            validation: ReconstructionValidationStatus::Failed,
                            trust_level: TrustLevel::Rejected,
                            validation_records,
                            target_validation_blockers,
                            preserved_symbolic_formulas,
                            assumptions: source_assumptions.to_vec(),
                            diagnostics: output_diagnostics_with_source(
                                &[
                                    "format=trust_ir-json-rejected",
                                    "symbolic formula lowering blocked before Undef",
                                    "rejected output; not proof-grade",
                                ],
                                source_diagnostics,
                            ),
                            ..Default::default()
                        }
                    }
                    Err(error) => return Err(error),
                }
            }
            DecompileOutputKind::TrustIrText => {
                let validation_records = trust_ir_self_validation_records(functions);
                let preserved_symbolic_formulas =
                    preserved_symbolic_formulas_for_target(DecompileTarget::TrustIr, functions);
                let mut target_validation_blockers =
                    trust_ir_target_validation_blockers(functions);
                target_validation_blockers.extend(symbolic_formula_target_validation_blockers(
                    DecompileTarget::TrustIr,
                    &preserved_symbolic_formulas,
                ));
                DecompiledOutput {
                    target: DecompileTarget::TrustIr,
                    text: Some(render_trust_ir_text(metadata, functions)),
                    validation: validation_status_from_records(&validation_records),
                    trust_level: TrustLevel::Partial,
                    validation_records,
                    target_validation_blockers,
                    preserved_symbolic_formulas,
                    assumptions: source_assumptions.to_vec(),
                    diagnostics: output_diagnostics_with_source(
                        &[
                            "format=trust_ir-text",
                            "validation-records=structured-trust_ir-self",
                            "self-validation is partial; not proof-grade",
                        ],
                        source_diagnostics,
                    ),
                    ..Default::default()
                }
            }
            DecompileOutputKind::RustSkeleton => {
                let validation_records = rust_skeleton_validation_records(functions);
                DecompiledOutput {
                    target: DecompileTarget::Rust,
                    text: Some(render_rust_skeleton(metadata, functions, unsupported)),
                    validation: ReconstructionValidationStatus::NotAttempted,
                    trust_level: TrustLevel::Exploratory,
                    validation_records,
                    validated_rust: Some(validated_rust_reconstruction(functions)),
                    assumptions: source_assumptions.to_vec(),
                    diagnostics: output_diagnostics_with_source(
                        &[
                            "format=rust-skeleton",
                            "exploratory output; not validated",
                            "validation-records=text-only",
                            "semantic validation candidate rejected",
                        ],
                        source_diagnostics,
                    ),
                    ..Default::default()
                }
            }
            DecompileOutputKind::WasmText => {
                let conversion = wasm_conversion_for_functions(metadata, functions);
                let target_proof_consumer_evidence = conversion.target_proof_consumer_evidence();
                let target_proof_consumer_artifact_digest =
                    wasm_target_proof_consumer_artifact_digest(
                        metadata,
                        functions,
                        &conversion,
                        &target_proof_consumer_evidence,
                    );
                let target_proof_consumer_artifact_diagnostic =
                    target_proof_consumer_artifact_digest
                        .as_ref()
                        .and_then(target_proof_consumer_artifact_digest_diagnostic);
                let target_proof_consumer_accepted =
                    target_proof_consumer_artifact_diagnostic.is_some();
                let format =
                    if conversion.wat.is_some() { "format=wat" } else { "format=wasm-rejected" };
                let text = conversion.wat;
                let mut target_validation_blockers =
                    wasm_target_validation_blockers(&conversion.validation_blockers);
                target_validation_blockers.extend(wasm_target_validation_blockers(
                    &target_proof_consumer_evidence.blockers,
                ));
                target_validation_blockers.extend(target_validation_blockers_from_records(
                    DecompileTarget::Wasm,
                    &conversion.unsupported,
                    &conversion.validation_records,
                ));
                let preserved_symbolic_formulas = if conversion.symbolic_formulas.is_empty() {
                    preserved_symbolic_formulas_for_target(DecompileTarget::Wasm, functions)
                } else {
                    merge_preserved_symbolic_formulas(
                        wasm_preserved_symbolic_formulas(&conversion.symbolic_formulas),
                        preserved_symbolic_formulas_for_target(DecompileTarget::Wasm, functions),
                    )
                };
                target_validation_blockers.extend(
                    symbolic_formula_target_validation_blockers_unless_consumed(
                        DecompileTarget::Wasm,
                        &preserved_symbolic_formulas,
                        target_proof_consumer_accepted,
                    ),
                );
                let mut conversion_diagnostics = conversion.diagnostics;
                if let Some(diagnostic) = target_proof_consumer_artifact_diagnostic {
                    conversion_diagnostics.push(diagnostic);
                }
                conversion_diagnostics.extend(source_diagnostics.iter().cloned());
                DecompiledOutput {
                    target: DecompileTarget::Wasm,
                    text,
                    validation: conversion.validation,
                    trust_level: conversion.trust_level,
                    validation_records: conversion.validation_records,
                    target_validation_blockers,
                    preserved_symbolic_formulas,
                    assumptions: source_assumptions.to_vec(),
                    diagnostics: output_diagnostics_with_source(
                        &[
                            format,
                            "validation-records=wasm-constant-return-subset",
                            "Wasm text is never proof-grade",
                        ],
                        &conversion_diagnostics,
                    ),
                    ..Default::default()
                }
            }
            DecompileOutputKind::TrustCgText => {
                let conversion = trust_cg_conversion_for_functions(metadata, functions)?;
                let target_proof_consumer_accepted =
                    trust_cg_target_proof_consumer_accepted(&conversion);
                let format = if conversion.text.is_some() {
                    "format=trust_cg-lir-json"
                } else {
                    "format=trust_cg-rejected"
                };
                let mut target_validation_blockers = conversion.target_validation_blockers;
                target_validation_blockers.extend(target_validation_blockers_from_records(
                    DecompileTarget::TrustCg,
                    &conversion.unsupported,
                    &conversion.validation_records,
                ));
                let preserved_symbolic_formulas = if conversion
                    .preserved_symbolic_formulas
                    .is_empty()
                {
                    preserved_symbolic_formulas_for_target(DecompileTarget::TrustCg, functions)
                } else {
                    merge_preserved_symbolic_formulas(
                        conversion.preserved_symbolic_formulas,
                        preserved_symbolic_formulas_for_target(DecompileTarget::TrustCg, functions),
                    )
                };
                target_validation_blockers.extend(
                    symbolic_formula_target_validation_blockers_unless_consumed(
                        DecompileTarget::TrustCg,
                        &preserved_symbolic_formulas,
                        target_proof_consumer_accepted,
                    ),
                );
                DecompiledOutput {
                    target: DecompileTarget::TrustCg,
                    text: conversion.text,
                    validation: conversion.validation,
                    trust_level: conversion.trust_level,
                    validation_records: conversion.validation_records,
                    target_validation_blockers,
                    preserved_symbolic_formulas,
                    assumptions: source_assumptions.to_vec(),
                    diagnostics: output_diagnostics_with_source(
                        &[
                            format,
                            "validation-records=trust_cg-lir-structural",
                            "trust-cg text is never proof-grade",
                        ],
                        &conversion
                            .diagnostics
                            .into_iter()
                            .chain(source_diagnostics.iter().cloned())
                            .collect::<Vec<_>>(),
                    ),
                    ..Default::default()
                }
            }
            DecompileOutputKind::TrustCgUnsupported => DecompiledOutput {
                target: DecompileTarget::TrustCg,
                text: Some(render_unsupported_conversion_placeholder(
                    "trust-cg",
                    metadata,
                    unsupported,
                )),
                validation: ReconstructionValidationStatus::Failed,
                trust_level: TrustLevel::Rejected,
                target_validation_blockers: target_validation_blockers_from_records(
                    DecompileTarget::TrustCg,
                    unsupported,
                    &[],
                ),
                preserved_symbolic_formulas: preserved_symbolic_formulas_for_target(
                    DecompileTarget::TrustCg,
                    functions,
                ),
                assumptions: source_assumptions.to_vec(),
                diagnostics: output_diagnostics_with_source(
                    &[
                        "format=trust_cg-unsupported",
                        rejected_output_message(*kind),
                        "rejected output; not proof-grade",
                    ],
                    source_diagnostics,
                ),
                ..Default::default()
            },
            DecompileOutputKind::WasmUnsupported => DecompiledOutput {
                target: DecompileTarget::Wasm,
                text: Some(render_unsupported_conversion_placeholder(
                    "Wasm",
                    metadata,
                    unsupported,
                )),
                validation: ReconstructionValidationStatus::Failed,
                trust_level: TrustLevel::Rejected,
                target_validation_blockers: target_validation_blockers_from_records(
                    DecompileTarget::Wasm,
                    unsupported,
                    &[],
                ),
                preserved_symbolic_formulas: preserved_symbolic_formulas_for_target(
                    DecompileTarget::Wasm,
                    functions,
                ),
                assumptions: source_assumptions.to_vec(),
                diagnostics: output_diagnostics_with_source(
                    &[
                        "format=wasm-unsupported",
                        rejected_output_message(*kind),
                        "rejected output; not proof-grade",
                    ],
                    source_diagnostics,
                ),
                ..Default::default()
            },
        };
        attach_binary_artifact_digest_identity_to_output(&mut output, metadata);
        outputs.push(output);
    }

    Ok(outputs)
}

#[derive(Debug, Clone)]
struct TrustCgTextConversion {
    text: Option<String>,
    validation: ReconstructionValidationStatus,
    trust_level: TrustLevel,
    validation_records: Vec<ReconstructionValidationRecord>,
    target_validation_blockers: Vec<TargetValidationBlocker>,
    preserved_symbolic_formulas: Vec<PreservedSymbolicFormula>,
    target_proof_consumer_accepted: bool,
    unsupported: UnsupportedLedger,
    diagnostics: Vec<String>,
}

#[cfg(feature = "trust-cg")]
#[derive(Serialize)]
struct TrustCgOutputView<'a> {
    metadata: &'a BinaryArtifactMetadata,
    validation: ConversionValidationMetadata<'a>,
    validation_records: &'a [ReconstructionValidationRecord],
    target_validation_blockers: &'a [TargetValidationBlocker],
    preserved_symbolic_formulas: &'a [PreservedSymbolicFormula],
    #[serde(skip_serializing_if = "Option::is_none")]
    target_proof_consumer_artifact_digest: Option<&'a TargetProofConsumerArtifactDigest>,
    diagnostics: &'a [String],
    functions: Vec<TrustCgFunctionOutput>,
}

#[cfg(feature = "trust-cg")]
#[derive(Serialize)]
struct TrustCgFunctionOutput {
    name: String,
    lir: serde_json::Value,
    diagnostics: Vec<String>,
}

#[cfg(feature = "trust-cg")]
#[derive(Serialize)]
struct ConversionValidationMetadata<'a> {
    status: &'a str,
    trust_level: &'a str,
    proof_grade: bool,
    source: &'a str,
    subset: &'a str,
    note: &'a str,
}

#[cfg(feature = "trust-cg")]
fn inspectable_rejected_conversion_metadata<'a>(
    subset: &'a str,
    note: &'a str,
) -> ConversionValidationMetadata<'a> {
    ConversionValidationMetadata {
        status: CONVERSION_STATUS_INSPECTABLE_REJECTED,
        trust_level: "rejected",
        proof_grade: false,
        source: CONVERSION_SOURCE_BINARY_TRUST_IR,
        subset,
        note,
    }
}

fn unsupported_function_conversion_feature(
    target: &str,
    function: &DecompiledFunction,
) -> Option<String> {
    let mut records = function
        .unsupported
        .records
        .iter()
        .filter(|record| is_conversion_blocking_unsupported_record(record));
    let first_feature = records.next()?.feature.as_str();
    let unsupported_count = 1 + records.count();
    Some(format!(
        "{target} conversion rejected: function `{}` has {unsupported_count} unsupported lifted feature(s); first unsupported feature: {first_feature}",
        function.name
    ))
}

fn is_conversion_blocking_unsupported_record(record: &UnsupportedRecord) -> bool {
    !matches!(
        record.stage.as_str(),
        "trust-lift::source-provenance" | "trust-lift::type-provenance"
    )
}

#[cfg(feature = "trust-cg")]
fn trust_cg_inspection_blockers_for_nonblocking_records(
    function: &DecompiledFunction,
) -> Vec<TargetValidationBlocker> {
    let unsupported = UnsupportedLedger {
        records: function
            .unsupported
            .records
            .iter()
            .filter(|record| !is_conversion_blocking_unsupported_record(record))
            .cloned()
            .collect(),
    };
    target_validation_blockers_from_records(DecompileTarget::TrustCg, &unsupported, &[])
}

fn accepted_conversion_diagnostics(subset: &str) -> Vec<String> {
    vec![
        format!("source={CONVERSION_SOURCE_BINARY_TRUST_IR}"),
        format!("subset={subset}"),
        format!("conversion-status={CONVERSION_STATUS_VALIDATED_PARTIAL}"),
        "trust-level=partial".to_string(),
        "proof-grade=false".to_string(),
    ]
}

fn rejected_conversion_diagnostics(subset: &str) -> Vec<String> {
    vec![
        format!("source={CONVERSION_SOURCE_BINARY_TRUST_IR}"),
        format!("subset={subset}"),
        format!("conversion-status={CONVERSION_STATUS_TRANSLATION_REJECTED}"),
        "trust-level=rejected".to_string(),
        "proof-grade=false".to_string(),
        "fail-closed=true".to_string(),
    ]
}

fn conversion_record_diagnostics(
    subset: &str,
    status: ReconstructionValidationStatus,
    trust_level: TrustLevel,
) -> Vec<String> {
    if status == ReconstructionValidationStatus::Validated && trust_level == TrustLevel::Partial {
        accepted_conversion_diagnostics(subset)
    } else {
        rejected_conversion_diagnostics(subset)
    }
}

#[cfg(feature = "trust-cg")]
fn trust_cg_conversion_for_functions(
    metadata: &BinaryArtifactMetadata,
    functions: &[DecompiledFunction],
) -> Result<TrustCgTextConversion, DecompileError> {
    if functions.is_empty() {
        let feature = "trust-cg conversion requires at least one lifted TrustIr function";
        return Ok(rejected_trust_cg_conversion(metadata, None, feature));
    }

    let mut rendered = Vec::with_capacity(functions.len());
    let mut records = Vec::with_capacity(functions.len());
    let mut target_validation_blockers = Vec::new();
    let mut preserved_symbolic_formulas = Vec::new();
    let mut target_proof_consumer_artifact_digest = None;
    let mut target_proof_consumer_accepted = true;
    let mut target_proof_consumer_seen = false;
    let mut diagnostics = vec![
        "target=trust_cg-lir".to_string(),
        format!("source={CONVERSION_SOURCE_BINARY_TRUST_IR}"),
        format!("subset={TRUST_CG_VALIDATION_SUBSET}"),
        "proof-grade=false".to_string(),
        "validation is structural trust_cg LIR validation only; not proof-grade".to_string(),
    ];

    for function in functions {
        // Lift-stage unsupported records (e.g., semantic-lift gaps, non-exact provenance) remain
        // their own proof-grade blockers and propagate as target_validation_blockers, but they
        // must not be reclassified as a trust-cg translation rejection. Trust-cg conversion
        // remains "inspectable rejected" as long as the trust-cg lowering itself succeeds
        // structurally; the upstream lift gaps are surfaced separately through the existing
        // unsupported ledger and through target_validation_blockers.
        if let Some(feature) = function
            .lifted
            .as_ref()
            .and_then(|_| unsupported_function_conversion_feature("trust-cg", function))
        {
            target_validation_blockers.extend(rejected_trust_cg_target_validation_blockers(
                Some(function),
                "unsupported-trust_cg-subset",
                &feature,
            ));
            diagnostics.push(feature);
        }

        match lower_binary_decompiled_function_to_lir(function) {
            Ok(conversion) => {
                let proof_consumer = conversion.target_proof_consumer_evidence();
                if !conversion.symbolic_formula_evidence.is_empty()
                    || !conversion.checked_certificate_evidence.is_empty()
                    || !conversion.proof_replay_evidence.is_empty()
                    || !conversion.provenance_evidence.is_empty()
                {
                    target_proof_consumer_seen = true;
                    target_proof_consumer_accepted &= proof_consumer.target_semantics_consumed
                        && proof_consumer.blockers.is_empty();
                }
                records.push(accepted_trust_cg_validation_record(function, &conversion));
                target_validation_blockers
                    .extend(trust_cg_inspection_blockers_for_nonblocking_records(function));
                target_validation_blockers.extend(trust_cg_target_validation_blockers(
                    function,
                    &conversion.validation_blockers,
                ));
                target_validation_blockers.extend(trust_cg_target_validation_blockers(
                    function,
                    &proof_consumer.blockers,
                ));
                preserved_symbolic_formulas
                    .extend(trust_cg_preserved_symbolic_formulas(&conversion.symbolic_formulas));
                diagnostics.extend(conversion.diagnostics.iter().cloned());
                if target_proof_consumer_artifact_digest.is_none() {
                    let artifact = trust_cg_target_proof_consumer_artifact_digest(
                        metadata,
                        function,
                        &conversion,
                        &proof_consumer,
                    );
                    if let Some(artifact) = artifact
                        && let Some(diagnostic) =
                            target_proof_consumer_artifact_digest_diagnostic(&artifact)
                    {
                        diagnostics.push(diagnostic);
                        target_proof_consumer_artifact_digest = Some(artifact);
                    }
                }
                rendered.push(TrustCgFunctionOutput {
                    name: function.name.clone(),
                    lir: serde_json::to_value(&conversion.lir)?,
                    diagnostics: conversion.diagnostics,
                });
            }
            Err(error) => {
                let feature = error.to_string();
                let mut unsupported = UnsupportedLedger::default();
                unsupported.records.push(unsupported_record(
                    "trust-cg-bridge",
                    Some(&metadata.architecture),
                    Some(function.entry),
                    None,
                    &feature,
                ));
                records.push(rejected_trust_cg_validation_record(function, &error));
                target_validation_blockers.extend(rejected_trust_cg_target_validation_blockers(
                    Some(function),
                    trust_cg_error_blocker_code(&error),
                    &feature,
                ));
                diagnostics.push(feature);
                diagnostics.extend(rejected_conversion_diagnostics(TRUST_CG_VALIDATION_SUBSET));
                diagnostics.push("trust-cg conversion failed closed; not proof-grade".to_string());
                return Ok(TrustCgTextConversion {
                    text: None,
                    validation: ReconstructionValidationStatus::Failed,
                    trust_level: TrustLevel::Rejected,
                    validation_records: records,
                    target_validation_blockers,
                    preserved_symbolic_formulas,
                    target_proof_consumer_accepted: false,
                    unsupported,
                    diagnostics,
                });
            }
        }
    }

    diagnostics.extend(rejected_conversion_diagnostics(TRUST_CG_VALIDATION_SUBSET));
    diagnostics.push("trust_cg-validation=inspectable-rejected".to_string());
    let text = serde_json::to_string_pretty(&TrustCgOutputView {
        metadata,
        validation: inspectable_rejected_conversion_metadata(
            TRUST_CG_VALIDATION_SUBSET,
            "structural trust_cg LIR validation succeeded, but target validation is rejected until refinement metadata, checked proof certificates, and binary proof obligations are discharged",
        ),
        validation_records: &records,
        target_validation_blockers: &target_validation_blockers,
        preserved_symbolic_formulas: &preserved_symbolic_formulas,
        target_proof_consumer_artifact_digest: target_proof_consumer_artifact_digest.as_ref(),
        diagnostics: &diagnostics,
        functions: rendered,
    })?;
    Ok(TrustCgTextConversion {
        text: Some(text),
        validation: validation_status_from_records(&records),
        trust_level: TrustLevel::Rejected,
        validation_records: records,
        target_validation_blockers,
        preserved_symbolic_formulas,
        target_proof_consumer_accepted: target_proof_consumer_seen
            && target_proof_consumer_accepted,
        unsupported: UnsupportedLedger::default(),
        diagnostics,
    })
}

#[cfg(not(feature = "trust-cg"))]
fn trust_cg_conversion_for_functions(
    metadata: &BinaryArtifactMetadata,
    functions: &[DecompiledFunction],
) -> Result<TrustCgTextConversion, DecompileError> {
    if functions.is_empty() {
        let feature = "trust-cg conversion requires at least one lifted TrustIr function";
        return Ok(rejected_trust_cg_conversion(metadata, None, feature));
    }

    let feature = "trust-cg bridge backend is not compiled into this trust-decompile build; enable feature `trust-cg` to emit trust_cg LIR";
    let mut conversion = rejected_trust_cg_conversion_with_blocker(
        metadata,
        None,
        feature,
        "trust-cg-backend-unavailable",
    );
    conversion.diagnostics.push("trust-cg-feature=disabled".to_string());
    conversion.diagnostics.push("trust-cg-backend-unavailable=true".to_string());
    Ok(conversion)
}

fn rejected_trust_cg_conversion(
    metadata: &BinaryArtifactMetadata,
    function: Option<&DecompiledFunction>,
    feature: &str,
) -> TrustCgTextConversion {
    rejected_trust_cg_conversion_with_blocker(
        metadata,
        function,
        feature,
        "missing-lifted-trust_ir",
    )
}

fn rejected_trust_cg_conversion_with_blocker(
    metadata: &BinaryArtifactMetadata,
    function: Option<&DecompiledFunction>,
    feature: &str,
    blocker_code: &str,
) -> TrustCgTextConversion {
    let mut unsupported = UnsupportedLedger::default();
    unsupported.records.push(unsupported_record(
        "trust-cg-bridge",
        Some(&metadata.architecture),
        function.map(|function| function.entry),
        None,
        feature,
    ));
    let validation_records = vec![match function {
        Some(function) => rejected_trust_cg_unsupported_validation_record(function, feature),
        None => rejected_trust_cg_missing_validation_record(feature),
    }];
    TrustCgTextConversion {
        text: None,
        validation: ReconstructionValidationStatus::Failed,
        trust_level: TrustLevel::Rejected,
        validation_records,
        target_validation_blockers: rejected_trust_cg_target_validation_blockers(
            function,
            blocker_code,
            feature,
        ),
        preserved_symbolic_formulas: Vec::new(),
        target_proof_consumer_accepted: false,
        unsupported,
        diagnostics: rejected_conversion_diagnostics(TRUST_CG_VALIDATION_SUBSET)
            .into_iter()
            .chain([
                feature.to_string(),
                "trust-cg conversion failed closed; not proof-grade".to_string(),
            ])
            .collect(),
    }
}

fn rejected_trust_cg_unsupported_validation_record(
    function: &DecompiledFunction,
    feature: &str,
) -> ReconstructionValidationRecord {
    ReconstructionValidationRecord {
        target: DecompileTarget::TrustCg,
        function: Some(function.name.clone()),
        lifted_function: function.lifted.as_ref().map(|lifted| lifted.name.clone()),
        reconstructed_function: None,
        candidate: ReconstructionCandidateKind::StructuredTrustIr,
        status: ReconstructionValidationStatus::Failed,
        trust_level: TrustLevel::Rejected,
        forward: Some(trust_cg_validation_direction_record(ReconstructionValidationStatus::Failed)),
        reverse: None,
        evidence: vec![
            ReconstructionValidationEvidence::RejectedUnsupported,
            ReconstructionValidationEvidence::NoCheckedProofCertificate,
            ReconstructionValidationEvidence::NoBinaryProofObligation,
        ],
        diagnostics: rejected_conversion_diagnostics(TRUST_CG_VALIDATION_SUBSET)
            .into_iter()
            .chain([
                feature.to_string(),
                "trust-cg conversion rejected unsupported lifted feature(s); not proof-grade"
                    .to_string(),
            ])
            .collect(),
    }
}

fn rejected_trust_cg_missing_validation_record(feature: &str) -> ReconstructionValidationRecord {
    ReconstructionValidationRecord {
        target: DecompileTarget::TrustCg,
        function: None,
        lifted_function: None,
        reconstructed_function: None,
        candidate: ReconstructionCandidateKind::Missing,
        status: ReconstructionValidationStatus::Failed,
        trust_level: TrustLevel::Rejected,
        forward: Some(trust_cg_validation_direction_record(ReconstructionValidationStatus::Failed)),
        reverse: None,
        evidence: vec![
            ReconstructionValidationEvidence::MissingComparableTrustIr,
            ReconstructionValidationEvidence::NoCheckedProofCertificate,
            ReconstructionValidationEvidence::NoBinaryProofObligation,
        ],
        diagnostics: vec![
            feature.to_string(),
            "trust-cg conversion rejected missing binary-derived TrustIr; not proof-grade"
                .to_string(),
        ]
        .into_iter()
        .chain(rejected_conversion_diagnostics(TRUST_CG_VALIDATION_SUBSET))
        .collect(),
    }
}

#[cfg(feature = "trust-cg")]
fn accepted_trust_cg_validation_record(
    function: &DecompiledFunction,
    conversion: &BinaryTrustCgConversion,
) -> ReconstructionValidationRecord {
    ReconstructionValidationRecord {
        target: DecompileTarget::TrustCg,
        function: Some(function.name.clone()),
        lifted_function: function.lifted.as_ref().map(|lifted| lifted.name.clone()),
        reconstructed_function: Some(conversion.reconstructed_trust_ir.name.clone()),
        candidate: ReconstructionCandidateKind::StructuredTrustIr,
        status: ReconstructionValidationStatus::Validated,
        trust_level: TrustLevel::Rejected,
        forward: Some(trust_cg_validation_direction_record(ReconstructionValidationStatus::Validated)),
        reverse: None,
        evidence: vec![
            ReconstructionValidationEvidence::Other("trust_cg-lir-structural-validation".to_string()),
            ReconstructionValidationEvidence::NoCheckedProofCertificate,
            ReconstructionValidationEvidence::NoBinaryProofObligation,
        ],
        diagnostics: conversion
            .diagnostics
            .iter()
            .cloned()
            .chain(rejected_conversion_diagnostics(TRUST_CG_VALIDATION_SUBSET))
            .chain(std::iter::once(
                "trust-cg structural validation succeeded, but target validation is inspectable-rejected; not proof-grade".to_string(),
            ))
            .collect(),
    }
}

#[cfg(feature = "trust-cg")]
fn rejected_trust_cg_validation_record(
    function: &DecompiledFunction,
    error: &BinaryTrustCgConversionError,
) -> ReconstructionValidationRecord {
    let missing_lifted = matches!(error, BinaryTrustCgConversionError::MissingLiftedTrustIr { .. });
    let mut evidence = vec![
        ReconstructionValidationEvidence::NoCheckedProofCertificate,
        ReconstructionValidationEvidence::NoBinaryProofObligation,
    ];
    if missing_lifted {
        evidence.push(ReconstructionValidationEvidence::MissingComparableTrustIr);
    } else {
        evidence.push(ReconstructionValidationEvidence::RejectedUnsupported);
    }

    ReconstructionValidationRecord {
        target: DecompileTarget::TrustCg,
        function: Some(function.name.clone()),
        lifted_function: function.lifted.as_ref().map(|lifted| lifted.name.clone()),
        reconstructed_function: None,
        candidate: if missing_lifted {
            ReconstructionCandidateKind::Missing
        } else {
            ReconstructionCandidateKind::StructuredTrustIr
        },
        status: ReconstructionValidationStatus::Failed,
        trust_level: TrustLevel::Rejected,
        forward: Some(trust_cg_validation_direction_record(ReconstructionValidationStatus::Failed)),
        reverse: None,
        evidence,
        diagnostics: vec![
            error.to_string(),
            "trust-cg conversion rejected binary-derived TrustIr; not proof-grade".to_string(),
        ]
        .into_iter()
        .chain(rejected_conversion_diagnostics(TRUST_CG_VALIDATION_SUBSET))
        .collect(),
    }
}

fn trust_cg_validation_direction_record(
    status: ReconstructionValidationStatus,
) -> ReconstructionValidationDirectionRecord {
    ReconstructionValidationDirectionRecord {
        direction: ReconstructionValidationDirection::LiftedToOutput,
        status,
        vc_count: 0,
        counterexamples: 0,
        proof_certificates: 0,
        diagnostics: vec![
            "trust-cg bridge lowering plus structural LIR validation; no proof certificate"
                .to_string(),
        ],
    }
}

fn wasm_conversion_for_functions(
    metadata: &BinaryArtifactMetadata,
    functions: &[DecompiledFunction],
) -> WasmConversion {
    if let Some((function, feature)) = functions.iter().find_map(|function| {
        function
            .lifted
            .as_ref()
            .and_then(|_| unsupported_function_conversion_feature("Wasm", function))
            .map(|feature| (function, feature))
    }) {
        return annotate_wasm_conversion(rejected_wasm_conversion_for_unsupported_function(
            metadata, function, &feature,
        ));
    }

    if let Some(function) = functions.iter().find(|function| function.lifted.is_none()) {
        return annotate_wasm_conversion(reject_missing_lifted_trust_ir(Some(&function.name)));
    }

    let lifted: Vec<_> =
        functions.iter().filter_map(|function| function.lifted.as_ref().cloned()).collect();
    annotate_wasm_conversion(convert_functions_to_wat(&lifted))
}

fn rejected_wasm_conversion_for_unsupported_function(
    metadata: &BinaryArtifactMetadata,
    function: &DecompiledFunction,
    feature: &str,
) -> WasmConversion {
    let record = ReconstructionValidationRecord {
        target: DecompileTarget::Wasm,
        function: Some(function.name.clone()),
        lifted_function: function.lifted.as_ref().map(|lifted| lifted.name.clone()),
        reconstructed_function: None,
        candidate: ReconstructionCandidateKind::Other(WASM_VALIDATION_SUBSET.to_string()),
        status: ReconstructionValidationStatus::Failed,
        trust_level: TrustLevel::Rejected,
        forward: Some(wasm_validation_direction_record(ReconstructionValidationStatus::Failed)),
        reverse: None,
        evidence: vec![
            ReconstructionValidationEvidence::RejectedUnsupported,
            ReconstructionValidationEvidence::NoCheckedProofCertificate,
            ReconstructionValidationEvidence::NoBinaryProofObligation,
        ],
        diagnostics: rejected_conversion_diagnostics(WASM_VALIDATION_SUBSET)
            .into_iter()
            .chain([
                feature.to_string(),
                "Wasm conversion rejected unsupported lifted feature(s); not proof-grade"
                    .to_string(),
            ])
            .collect(),
    };

    let mut unsupported = UnsupportedLedger::default();
    unsupported.records.push(unsupported_record(
        "trust-wasm-bridge",
        Some(&metadata.architecture),
        Some(function.entry),
        None,
        feature,
    ));

    WasmConversion {
        wat: None,
        lifted_trust_ir_artifact_digest: None,
        bound_lifted_trust_ir_artifact_digest: None,
        validation: ReconstructionValidationStatus::Failed,
        wasm_validation: WasmTargetValidationStatus::Rejected,
        trust_level: TrustLevel::Rejected,
        validation_blockers: rejected_wasm_validation_blockers(feature),
        symbolic_formulas: Vec::new(),
        provenance_evidence: Vec::new(),
        checked_certificate_evidence: Vec::new(),
        proof_replay_evidence: Vec::new(),
        unsupported_ledger_evidence: Vec::new(),
        validation_records: vec![record],
        unsupported,
        diagnostics: rejected_conversion_diagnostics(WASM_VALIDATION_SUBSET)
            .into_iter()
            .chain([
                feature.to_string(),
                "Wasm conversion failed closed; not proof-grade".to_string(),
            ])
            .collect(),
    }
}

fn rejected_wasm_validation_blockers(feature: &str) -> Vec<WasmValidationBlocker> {
    vec![
        WasmValidationBlocker {
            code: "unsupported-wasm-subset".to_string(),
            detail: feature.to_string(),
        },
        WasmValidationBlocker {
            code: "missing-target-semantic-validation".to_string(),
            detail: "Wasm text has not been validated against executable Wasm target semantics"
                .to_string(),
        },
        WasmValidationBlocker {
            code: "missing-refinement-metadata".to_string(),
            detail: "Wasm text has no bidirectional refinement metadata tying it to lifted TrustIr"
                .to_string(),
        },
        WasmValidationBlocker {
            code: "missing-checked-proof-certificate".to_string(),
            detail: "Wasm conversion has no checked proof certificate for the emitted text"
                .to_string(),
        },
        WasmValidationBlocker {
            code: "missing-binary-proof-obligation".to_string(),
            detail: "Wasm conversion has not discharged machine-code proof obligations".to_string(),
        },
    ]
}

fn annotate_wasm_conversion(mut conversion: WasmConversion) -> WasmConversion {
    let diagnostics = conversion_record_diagnostics(
        WASM_VALIDATION_SUBSET,
        conversion.validation,
        conversion.trust_level,
    );
    conversion.diagnostics.extend(diagnostics.iter().cloned());
    for record in &mut conversion.validation_records {
        record.diagnostics.extend(diagnostics.iter().cloned());
    }
    if conversion.validation == ReconstructionValidationStatus::Validated
        && conversion.trust_level == TrustLevel::Partial
    {
        conversion.wat = conversion.wat.map(annotate_wasm_text_with_partial_metadata);
    }
    conversion
}

fn annotate_wasm_text_with_partial_metadata(wat: String) -> String {
    format!(
        ";; conversion_status={CONVERSION_STATUS_VALIDATED_PARTIAL}\n\
         ;; trust_level=partial\n\
         ;; proof_grade=false\n\
         ;; source={CONVERSION_SOURCE_BINARY_TRUST_IR}\n\
         ;; subset={WASM_VALIDATION_SUBSET}\n{wat}"
    )
}

fn wasm_validation_direction_record(
    status: ReconstructionValidationStatus,
) -> ReconstructionValidationDirectionRecord {
    ReconstructionValidationDirectionRecord {
        direction: ReconstructionValidationDirection::LiftedToOutput,
        status,
        vc_count: 0,
        counterexamples: 0,
        proof_certificates: 0,
        diagnostics: vec![
            "Wasm subset validation only; no solver VC or checked proof certificate".to_string(),
        ],
    }
}

#[derive(Serialize)]
struct TrustIrOutputView<'a> {
    metadata: &'a BinaryArtifactMetadata,
    source_provenance: TrustIrSourceProvenanceView<'a>,
    module: serde_json::Value,
    checked_certificate_bridge: TrustIrCheckedCertificateBridgeMetadata,
    functions: &'a [DecompiledFunction],
    call_graph: &'a CallGraph,
    memory_facts: &'a [MemoryAccessFact],
    unsupported: &'a UnsupportedLedger,
    trust_level: TrustLevel,
}

#[derive(Serialize)]
struct TrustIrSourceProvenanceView<'a> {
    status: &'a str,
    exact_mapping_count: usize,
    ambiguous_mapping_count: usize,
    diagnostics: &'a [String],
    source_backpropagation_allowed: bool,
    effective_source_backpropagation_allowed: bool,
    typed_diagnostics: Vec<BinarySourceProvenanceDiagnostic>,
}

impl<'a> TrustIrSourceProvenanceView<'a> {
    fn from_summary(summary: &'a BinarySourceProvenanceSummary) -> Self {
        Self {
            status: &summary.status,
            exact_mapping_count: summary.exact_mapping_count,
            ambiguous_mapping_count: summary.ambiguous_mapping_count,
            diagnostics: &summary.diagnostics,
            source_backpropagation_allowed: summary.source_backpropagation_allowed,
            effective_source_backpropagation_allowed: summary
                .effective_source_backpropagation_allowed(),
            typed_diagnostics: summary.typed_diagnostics(),
        }
    }
}

#[derive(Serialize)]
struct TrustIrCheckedCertificateBridgeMetadata {
    dispatches: Vec<TrustIrCheckedCertificateDispatchMetadata>,
    checked_dispatches: usize,
    invalid_checked_dispatches: usize,
    proof_grade_closed: bool,
    release_gate: TrustIrProofGradeReleaseGateMetadata,
    diagnostics: Vec<String>,
}

#[derive(Serialize)]
struct TrustIrProofGradeReleaseGateMetadata {
    accepted: bool,
    blockers: Vec<String>,
    unsupported_ledger_empty: bool,
    checked_certificates_accepted: bool,
    replay_accepted: bool,
    replay_identity_blockers: Vec<String>,
    source_provenance_accepted: bool,
    binary_artifact_identity_accepted: bool,
    target_reconstruction_accepted: bool,
    production_boundary_accepted: bool,
    production_boundary_blockers: Vec<String>,
}

#[derive(Serialize)]
struct TrustIrCheckedCertificateDispatchMetadata {
    id: String,
    function: Option<String>,
    origin: Option<BinaryOrigin>,
    binary_artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
    binary_artifact_digest_identity_accepted: bool,
    checker: Option<String>,
    format: Option<String>,
    sha256: Option<String>,
    replay: ReplayStatus,
    proof_grade_eligible: bool,
}

fn render_trust_ir_json(
    metadata: &BinaryArtifactMetadata,
    functions: &[DecompiledFunction],
    call_graph: &CallGraph,
    memory_facts: &[MemoryAccessFact],
    unsupported: &UnsupportedLedger,
    source_provenance: &BinarySourceProvenanceSummary,
    reconstruction: Option<&ReconstructionSummary>,
) -> Result<String, DecompileError> {
    let lifted: Vec<_> = functions.iter().filter_map(|function| function.lifted.as_ref()).collect();
    let module_name = metadata.path.as_deref().unwrap_or("binary");
    let module = lower_functions_to_trust_ir(module_name, lifted)?;
    let module = serde_json::to_value(module)?;
    let checked_certificate_bridge = trust_ir_checked_certificate_bridge_metadata(
        metadata,
        functions,
        unsupported,
        source_provenance,
        reconstruction,
    );

    Ok(serde_json::to_string_pretty(&TrustIrOutputView {
        metadata,
        source_provenance: TrustIrSourceProvenanceView::from_summary(source_provenance),
        module,
        checked_certificate_bridge,
        functions,
        call_graph,
        memory_facts,
        unsupported,
        trust_level: TrustLevel::Partial,
    })?)
}

fn trust_ir_checked_certificate_bridge_metadata(
    metadata: &BinaryArtifactMetadata,
    functions: &[DecompiledFunction],
    unsupported: &UnsupportedLedger,
    source_provenance: &BinarySourceProvenanceSummary,
    reconstruction: Option<&ReconstructionSummary>,
) -> TrustIrCheckedCertificateBridgeMetadata {
    let dispatches: Vec<_> = functions
        .iter()
        .flat_map(|function| function.verification.solver_dispatch.iter())
        .filter_map(|dispatch| {
            trust_ir_checked_certificate_dispatch_metadata(
                dispatch,
                metadata,
                functions,
                unsupported,
                source_provenance,
            )
        })
        .collect();
    let checked_dispatches =
        dispatches.iter().filter(|dispatch| dispatch.checker.is_some()).count();
    let invalid_checked_dispatches =
        dispatches.iter().filter(|dispatch| !dispatch.proof_grade_eligible).count();
    let release_gate = trust_ir_proof_grade_release_gate_metadata(
        metadata,
        functions,
        unsupported,
        source_provenance,
        reconstruction,
    );
    let proof_grade_closed =
        invalid_checked_dispatches > 0 || (checked_dispatches > 0 && !release_gate.accepted);
    let mut diagnostics = if proof_grade_closed {
        vec![
            "canonical TrustIr conversion preserved checked-certificate metadata, but proof-grade remains closed because at least one binary release-gate condition is missing"
                .to_string(),
        ]
    } else if checked_dispatches > 0 {
        vec![
            "canonical TrustIr conversion preserved checked-certificate metadata for binary-origin dispatches"
                .to_string(),
        ]
    } else {
        Vec::new()
    };
    diagnostics.extend(
        dispatches
            .iter()
            .filter(|dispatch| !dispatch.binary_artifact_digest_identity_accepted)
            .map(|dispatch| {
                format!(
                    "dispatch `{}` lacks binary artifact digest identity that exactly matches decompiled metadata; replay/proof evidence remains fail-closed",
                    dispatch.id
                )
            }),
    );
    diagnostics.extend(release_gate.replay_identity_blockers.iter().cloned());
    if !release_gate.production_boundary_accepted {
        diagnostics.push(format!(
            "production proof-grade boundary remains diagnostic-only and is not accepted: {}",
            release_gate.production_boundary_blockers.join(", ")
        ));
    }

    TrustIrCheckedCertificateBridgeMetadata {
        dispatches,
        checked_dispatches,
        invalid_checked_dispatches,
        proof_grade_closed,
        release_gate,
        diagnostics,
    }
}

fn trust_ir_checked_certificate_dispatch_metadata(
    dispatch: &SolverDispatchRecord,
    metadata: &BinaryArtifactMetadata,
    functions: &[DecompiledFunction],
    unsupported: &UnsupportedLedger,
    source_provenance: &BinarySourceProvenanceSummary,
) -> Option<TrustIrCheckedCertificateDispatchMetadata> {
    let ProofCertificateStatus::Checked { checker, format, sha256 } = &dispatch.certificate else {
        return None;
    };
    dispatch.origin.as_ref()?;

    let binary_artifact_digest_identity_accepted =
        dispatch_binary_artifact_digest_identity_matches_metadata(dispatch, metadata);

    Some(TrustIrCheckedCertificateDispatchMetadata {
        id: dispatch.id.clone(),
        function: dispatch.function.clone(),
        origin: dispatch.origin.clone(),
        binary_artifact_digest_identity: dispatch.binary_artifact_digest_identity.clone(),
        binary_artifact_digest_identity_accepted,
        checker: (!checker.trim().is_empty()).then(|| checker.clone()),
        format: (!format.trim().is_empty()).then(|| format.clone()),
        sha256: sha256.clone(),
        replay: dispatch.replay,
        proof_grade_eligible: trust_ir_dispatch_has_proof_grade_evidence(
            dispatch,
            metadata,
            functions,
            unsupported,
            source_provenance,
        ),
    })
}

fn trust_ir_dispatch_has_proof_grade_evidence(
    dispatch: &SolverDispatchRecord,
    metadata: &BinaryArtifactMetadata,
    functions: &[DecompiledFunction],
    unsupported: &UnsupportedLedger,
    source_provenance: &BinarySourceProvenanceSummary,
) -> bool {
    unsupported.records.is_empty()
        && source_provenance_allows_artifact_proof_grade(source_provenance)
        && binary_artifact_metadata_identity_allows_proof_grade(metadata)
        && dispatch_binary_artifact_digest_identity_matches_metadata(dispatch, metadata)
        && binary_dispatch_has_proof_grade_evidence(dispatch)
        && dispatch_has_accepted_source_provenance(dispatch, functions, metadata)
}

fn trust_ir_proof_grade_release_gate_metadata(
    metadata: &BinaryArtifactMetadata,
    functions: &[DecompiledFunction],
    unsupported: &UnsupportedLedger,
    source_provenance: &BinarySourceProvenanceSummary,
    reconstruction: Option<&ReconstructionSummary>,
) -> TrustIrProofGradeReleaseGateMetadata {
    let dispatches: Vec<_> = functions
        .iter()
        .flat_map(|function| function.verification.solver_dispatch.iter())
        .collect();
    let unsupported_ledger_empty = unsupported.records.is_empty();
    let checked_certificates_accepted = !dispatches.is_empty()
        && dispatches
            .iter()
            .all(|dispatch| checked_certificate_has_bridge_metadata(&dispatch.certificate));
    let replay_accepted = !dispatches.is_empty()
        && dispatches
            .iter()
            .all(|dispatch| binary_dispatch_satisfies_release_replay_semantics(dispatch));
    let replay_identity_blockers = trust_ir_replay_identity_blockers(&dispatches);
    let source_provenance_accepted =
        source_provenance_allows_artifact_proof_grade(source_provenance)
            && !dispatches.is_empty()
            && dispatches.iter().all(|dispatch| {
                dispatch_has_accepted_source_provenance(dispatch, functions, metadata)
            });
    let binary_artifact_identity_accepted =
        binary_artifact_metadata_identity_allows_proof_grade(metadata)
            && functions.iter().all(|function| {
                function_binary_origins_match_artifact_identity(function, metadata)
            })
            && dispatches.iter().all(|dispatch| {
                dispatch_binary_origin_matches_artifact_identity(dispatch, metadata)
                    && dispatch_binary_artifact_digest_identity_matches_metadata(dispatch, metadata)
            });
    let target_reconstruction_accepted = reconstruction.is_some_and(|reconstruction| {
        reconstruction_allows_binary_proof_grade(reconstruction, metadata)
    });
    let production_boundary_blockers = trust_ir_production_release_boundary_blockers(
        metadata,
        &dispatches,
        source_provenance,
        reconstruction,
    );
    let production_boundary_accepted = production_boundary_blockers.is_empty();

    let mut blockers = Vec::new();
    if !unsupported_ledger_empty {
        blockers.push("unsupported_ledger_not_empty".to_string());
    }
    if !checked_certificates_accepted {
        blockers.push("checked_certificates_not_accepted".to_string());
    }
    if !replay_accepted {
        blockers.push("replay_not_accepted".to_string());
    }
    if !source_provenance_accepted {
        blockers.push("source_provenance_not_accepted".to_string());
    }
    if !binary_artifact_identity_accepted {
        blockers.push("binary_artifact_identity_not_accepted".to_string());
    }
    if !target_reconstruction_accepted {
        blockers.push(if reconstruction.is_some() {
            "target_reconstruction_not_accepted".to_string()
        } else {
            "target_reconstruction_not_evaluated".to_string()
        });
    }

    let accepted = blockers.is_empty() && production_boundary_accepted;
    TrustIrProofGradeReleaseGateMetadata {
        accepted,
        blockers,
        unsupported_ledger_empty,
        checked_certificates_accepted,
        replay_accepted,
        replay_identity_blockers,
        source_provenance_accepted,
        binary_artifact_identity_accepted,
        target_reconstruction_accepted,
        production_boundary_accepted,
        production_boundary_blockers,
    }
}

fn trust_ir_replay_identity_blockers(dispatches: &[&SolverDispatchRecord]) -> Vec<String> {
    if dispatches.is_empty() {
        return vec![
            "no solver dispatches are available; source backprop requires symex source_backprop_replay_ready exact replay identity with matched instruction trace, matched root artifact digest, matched selected-image digest/range, explicit branch/call/return capability evidence, and no unchecked boundary evidence"
                .to_string(),
        ];
    }

    dispatches
        .iter()
        .filter(|dispatch| !binary_dispatch_satisfies_release_replay_semantics(dispatch))
        .map(|dispatch| {
            format!(
                "dispatch `{}` replay status {:?} is not replayed; source backprop requires symex source_backprop_replay_ready exact replay identity with matched instruction trace, matched root artifact digest, matched selected-image digest/range, explicit branch/call/return capability evidence, and no unchecked boundary evidence",
                dispatch.id, dispatch.replay
            )
        })
        .collect()
}

fn trust_ir_production_release_boundary_blockers(
    metadata: &BinaryArtifactMetadata,
    dispatches: &[&SolverDispatchRecord],
    source_provenance: &BinarySourceProvenanceSummary,
    reconstruction: Option<&ReconstructionSummary>,
) -> Vec<String> {
    let mut blockers = Vec::new();

    if !metadata_has_production_parser_identity(metadata) {
        blockers.push("parser_identity_not_production".to_string());
    }
    if !dispatches_have_production_checked_certificate_evidence(dispatches) {
        blockers.push("checked_certificate_not_production".to_string());
    }
    if !dispatches_have_production_replay_identity(dispatches, metadata) {
        blockers.push("replay_identity_not_production".to_string());
    }
    if !source_provenance_has_production_claims(source_provenance, metadata) {
        blockers.push("source_provenance_not_production".to_string());
    }
    if !reconstruction_has_production_target_consumer_acceptance(reconstruction) {
        blockers.push("target_consumer_not_production".to_string());
    }

    blockers
}

fn metadata_has_production_parser_identity(metadata: &BinaryArtifactMetadata) -> bool {
    binary_artifact_metadata_identity_allows_proof_grade(metadata)
        && metadata.path.as_deref().is_some_and(|path| !text_has_synthetic_release_marker(path))
        && metadata
            .build_id
            .as_deref()
            .is_some_and(|build_id| !text_has_synthetic_release_marker(build_id))
}

fn dispatches_have_production_checked_certificate_evidence(
    dispatches: &[&SolverDispatchRecord],
) -> bool {
    !dispatches.is_empty()
        && dispatches.iter().all(|dispatch| {
            let ProofCertificateStatus::Checked { checker, format, sha256 } = &dispatch.certificate
            else {
                return false;
            };
            !text_has_synthetic_release_marker(checker)
                && !text_has_synthetic_release_marker(format)
                && sha256.as_deref().is_some_and(is_canonical_sha256_hex)
        })
}

fn dispatches_have_production_replay_identity(
    dispatches: &[&SolverDispatchRecord],
    metadata: &BinaryArtifactMetadata,
) -> bool {
    !dispatches.is_empty()
        && dispatches.iter().all(|dispatch| {
            dispatch.replay == ReplayStatus::Replayed
                && dispatch_binary_artifact_digest_identity_matches_metadata(dispatch, metadata)
                && dispatch.binary_artifact_digest_identity.as_ref().is_some_and(|identity| {
                    let root = identity
                        .root_artifact_digest
                        .as_ref()
                        .map(|digest| digest.value.as_str())
                        .unwrap_or_default();
                    let selected = identity
                        .selected_image
                        .as_ref()
                        .map(|selected| selected.sha256.as_str())
                        .unwrap_or_default();
                    is_canonical_sha256_hex(root)
                        && is_canonical_sha256_hex(selected)
                        && !looks_like_synthetic_digest(root)
                        && !looks_like_synthetic_digest(selected)
                })
        })
}

fn source_provenance_has_production_claims(
    source_provenance: &BinarySourceProvenanceSummary,
    metadata: &BinaryArtifactMetadata,
) -> bool {
    source_provenance_allows_artifact_proof_grade(source_provenance)
        && metadata_has_production_parser_identity(metadata)
        && source_provenance
            .diagnostics
            .iter()
            .all(|diagnostic| !text_has_synthetic_release_marker(diagnostic))
}

fn reconstruction_has_production_target_consumer_acceptance(
    reconstruction: Option<&ReconstructionSummary>,
) -> bool {
    let Some(reconstruction) = reconstruction else {
        return false;
    };
    reconstruction_allows_artifact_proof_grade(reconstruction)
        && reconstruction.outputs.iter().any(|output| {
            output.target == reconstruction.target
                && output.target_validation_blockers.is_empty()
                && output_has_production_target_consumer_acceptance(output)
        })
}

fn output_has_production_target_consumer_acceptance(output: &DecompiledOutput) -> bool {
    let artifact_records = target_proof_consumer_artifact_digest_records(output);
    if !artifact_records.is_empty() {
        return artifact_records.iter().any(|record| {
            target_proof_consumer_artifact_digest_accepted_for_output(output, record)
                && target_proof_consumer_artifact_has_production_identity(record)
        });
    }

    !target_requires_structured_target_consumer_artifact(&output.target)
        && output.diagnostics.iter().any(|diagnostic| {
            target_consumer_acceptance_diagnostic(diagnostic)
                && !text_has_synthetic_release_marker(diagnostic)
        })
}

fn target_proof_consumer_artifact_has_production_identity(
    record: &TargetProofConsumerArtifactDigest,
) -> bool {
    record.artifact_digest.is_canonical_sha256()
        && !looks_like_synthetic_digest(&record.artifact_digest.value)
        && record.lifted_trust_ir_artifact.digest.is_canonical_sha256()
        && !looks_like_synthetic_digest(&record.lifted_trust_ir_artifact.digest.value)
        && !text_has_synthetic_release_marker(&record.target_output)
        && record
            .binary_artifact_digest_identity
            .as_ref()
            .is_some_and(binary_artifact_digest_identity_has_production_digests)
}

fn binary_artifact_digest_identity_has_production_digests(
    identity: &BinaryArtifactDigestIdentity,
) -> bool {
    identity.digest_identity_allows_replay()
        && identity.root_artifact_digest.as_ref().is_some_and(|digest| {
            digest.is_canonical_sha256() && !looks_like_synthetic_digest(&digest.value)
        })
        && identity.selected_image.as_ref().is_some_and(|selected| {
            is_canonical_sha256_hex(&selected.sha256)
                && !looks_like_synthetic_digest(&selected.sha256)
        })
}

fn text_has_synthetic_release_marker(text: &str) -> bool {
    let text = text.to_ascii_lowercase();
    ["synthetic", "fixture", "unit-test", "test-only", "checked externally", "mock"]
        .iter()
        .any(|marker| text.contains(marker))
}

fn is_canonical_sha256_hex(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn looks_like_synthetic_digest(value: &str) -> bool {
    if !is_canonical_sha256_hex(value) {
        return true;
    }
    let mut bytes = value.bytes();
    let Some(first) = bytes.next() else {
        return true;
    };
    bytes.all(|byte| byte == first)
}

fn render_trust_ir_text(
    metadata: &BinaryArtifactMetadata,
    functions: &[DecompiledFunction],
) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "binary format={} arch={} entry={}",
        lifted_format_name(metadata.format),
        metadata.architecture,
        metadata
            .entry_point
            .map(|entry| format!("0x{entry:x}"))
            .unwrap_or_else(|| "<none>".to_string())
    );

    for function in functions {
        let _ = writeln!(
            out,
            "fn {} @ 0x{:x} blocks={} instructions={} memory_facts={} trust={:?}",
            function.name,
            function.entry,
            function.lifted.as_ref().map_or(0, |lifted| lifted.body.blocks.len()),
            function.coverage.instructions_lifted,
            function.memory_accesses.len(),
            function.trust_level
        );
        if let Some(lifted) = &function.lifted {
            for block in &lifted.body.blocks {
                let _ = writeln!(out, "  block{}:", block.id.0);
                for stmt in &block.stmts {
                    let _ = writeln!(out, "    {stmt:?}");
                }
                let _ = writeln!(out, "    -> {:?}", block.terminator);
            }
        }
    }

    out
}

fn render_unsupported_conversion_placeholder(
    target: &str,
    metadata: &BinaryArtifactMetadata,
    unsupported: &UnsupportedLedger,
) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "{target} conversion from binary-derived TrustIr is unsupported in this build."
    );
    let _ = writeln!(out, "No proof-grade {target} artifact was produced.");
    let _ = writeln!(
        out,
        "binary format={} arch={} unsupported_records={}",
        lifted_format_name(metadata.format),
        metadata.architecture,
        unsupported.records.len()
    );
    out
}

fn render_rust_skeleton(
    metadata: &BinaryArtifactMetadata,
    functions: &[DecompiledFunction],
    unsupported: &UnsupportedLedger,
) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "// Exploratory partial Rust skeleton generated from lifted TrustIr.");
    let _ =
        writeln!(out, "// This is not validated Rust reconstruction; trust remains Exploratory.");
    let _ = writeln!(
        out,
        "// Binary: format={} arch={} unsupported_records={}",
        lifted_format_name(metadata.format),
        metadata.architecture,
        unsupported.records.len()
    );
    let _ = writeln!(out, "#![allow(dead_code, unused_variables, unreachable_code)]");
    let _ = writeln!(out);

    if functions.is_empty() {
        let _ = writeln!(out, "// No lifted functions are available for skeleton emission.");
        return out;
    }

    for (index, function) in functions.iter().enumerate() {
        let ident = rust_identifier(&function.name, index);
        let _ = writeln!(
            out,
            "/// Exploratory partial skeleton for `{}` at 0x{:x}.",
            function.name, function.entry
        );
        let _ = writeln!(
            out,
            "/// TrustIr blocks: {}; memory facts: {}; unsupported records: {}.",
            function.lifted.as_ref().map_or(0, |lifted| lifted.body.blocks.len()),
            function.memory_accesses.len(),
            unsupported.records.len()
        );
        let _ = writeln!(out, "pub unsafe fn {ident}() {{");
        let _ = writeln!(
            out,
            "    todo!(\"exploratory decompilation skeleton; inspect the TrustIr artifact\")"
        );
        let _ = writeln!(out, "}}");
        let _ = writeln!(out);
    }

    out
}

fn function_def_path(function: &LiftedFunction) -> String {
    format!("binary::{}", function.name)
}

fn unsupported_record(
    stage: &str,
    architecture: Option<&str>,
    function_entry: Option<u64>,
    instruction_address: Option<u64>,
    feature: &str,
) -> UnsupportedRecord {
    UnsupportedRecord {
        stage: stage.to_string(),
        architecture: architecture.map(str::to_string),
        origin: instruction_address.map(|address| BinaryOrigin {
            binary_path: None,
            function_entry,
            instruction_address: address,
            instruction_size: None,
            encoding: None,
            instruction_bytes: vec![],
            source: Some(SourceSpan::binary_address(address)),
        }),
        opcode: None,
        operand: None,
        feature: feature.to_string(),
    }
}

fn rust_identifier(name: &str, index: usize) -> String {
    let mut ident = String::new();
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            ident.push(ch);
        } else {
            ident.push('_');
        }
    }
    if ident.is_empty() {
        ident = format!("function_{index}");
    }
    if ident.as_bytes().first().is_some_and(u8::is_ascii_digit) {
        ident.insert_str(0, "function_");
    }
    if RUST_KEYWORDS.contains(&ident.as_str()) {
        ident.push_str("_fn");
    }
    ident
}

const RUST_KEYWORDS: &[&str] = &[
    "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum", "extern",
    "false", "fn", "for", "gen", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut",
    "pub", "ref", "return", "self", "Self", "static", "struct", "super", "trait", "true", "type",
    "union", "unsafe", "use", "where", "while",
];

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use super::*;

    #[test]
    fn default_options_request_entry_trust_ir_json() {
        let options = DecompileOptions::default();
        assert_eq!(options.lift, BinaryLiftOptions::default());
        assert_eq!(options.outputs, vec![DecompileOutputKind::TrustIrJson]);
    }

    #[test]
    fn rust_identifier_is_conservative() {
        assert_eq!(rust_identifier("trust_fixture_return", 0), "trust_fixture_return");
        assert_eq!(rust_identifier("123 bad-name", 0), "function_123_bad_name");
        assert_eq!(rust_identifier("fn", 0), "fn_fn");
        assert_eq!(rust_identifier("", 7), "function_7");
    }

    #[test]
    fn unsupported_pe_is_classified_as_lift_error() {
        let error = decompile_binary(&[b'M', b'Z', 0, 0], DecompileOptions::default()).unwrap_err();
        match error {
            DecompileError::Lift(LiftError::UnsupportedBinaryFormat {
                format: "PE/COFF", ..
            }) => {}
            DecompileError::Lift(LiftError::BinaryParserUnavailable) => {}
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[cfg(feature = "elf")]
    #[test]
    fn unsupported_elf32_i386_propagates_as_lift_error() {
        let error =
            decompile_binary(&minimal_elf32_i386(), DecompileOptions::default()).unwrap_err();
        match error {
            DecompileError::Lift(LiftError::UnsupportedBinaryFormat {
                format: "ELF",
                reason: "32-bit x86/i386 lifting is not implemented yet",
            }) => {}
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[cfg(feature = "elf")]
    #[test]
    fn aarch64_decompile_records_partial_boundary_in_unsupported_ledger() {
        let artifact = decompile_binary(
            &minimal_aarch64_elf_with_entry_instructions(&[
                0xD5033B9F, // DMB ISH: modeled only as an ordering boundary.
                0xD65F03C0, // RET
            ]),
            DecompileOptions::default(),
        )
        .expect("AArch64 DMB boundary should decompile with an explicit unsupported ledger");

        assert_eq!(artifact.binary.format, BinaryArtifactFormat::Elf);
        assert_eq!(artifact.binary.architecture, "AArch64");
        assert_eq!(artifact.functions.len(), 1);
        assert_eq!(artifact.functions[0].name, "_start");
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);

        let record = artifact
            .unsupported
            .records
            .iter()
            .find(|record| {
                record.stage == "trust-lift::semantic-lift"
                    && record.architecture.as_deref() == Some("aarch64")
                    && record.opcode.as_deref() == Some("Dmb")
            })
            .expect("AArch64 DMB must be visible in the artifact unsupported ledger");
        assert!(record.feature.contains("AArch64 synchronization boundary"));
        assert_eq!(record.origin.as_ref().map(|origin| origin.instruction_address), Some(0x400000));
        assert_eq!(record.origin.as_ref().and_then(|origin| origin.encoding), Some(0xD5033B9F));
        assert_eq!(
            record.origin.as_ref().map(|origin| origin.instruction_bytes.as_slice()),
            Some(&[0x9F, 0x3B, 0x03, 0xD5][..])
        );
        assert!(artifact.functions[0].unsupported.records.iter().any(|function_record| {
            function_record.stage == record.stage
                && function_record.opcode == record.opcode
                && function_record.origin == record.origin
        }));

        let trust_ir_json = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
            .expect("default decompile output should include TrustIr JSON");
        assert_eq!(trust_ir_json.target, DecompileTarget::TrustIr);
        assert_eq!(trust_ir_json.trust_level, TrustLevel::Partial);

        let trust_ir_json: serde_json::Value =
            serde_json::from_str(trust_ir_json.text.as_deref().expect("TrustIr JSON text"))
                .expect("TrustIr output should parse as JSON");
        let json_records = trust_ir_json["unsupported"]["records"]
            .as_array()
            .expect("TrustIr JSON should carry the unsupported ledger");
        assert!(json_records.iter().any(|json_record| {
            json_record["stage"] == "trust-lift::semantic-lift"
                && json_record["architecture"] == "aarch64"
                && json_record["opcode"] == "Dmb"
                && json_record["origin"]["instruction_address"] == 0x400000
                && json_record["origin"]["encoding"].as_u64() == Some(0xD5033B9F)
        }));
    }

    #[cfg(feature = "elf")]
    #[test]
    fn decompile_records_parser_identity_blocker_when_loader_identity_is_missing() {
        let artifact = decompile_binary(
            &minimal_aarch64_elf_with_entry_instructions(&[
                0xD65F03C0, // RET
            ]),
            DecompileOptions::default(),
        )
        .expect("AArch64 RET fixture should decompile with parser identity evidence");

        assert_eq!(artifact.binary.format, BinaryArtifactFormat::Elf);
        assert_eq!(artifact.binary.architecture, "AArch64");
        assert_eq!(artifact.binary.build_id, None);
        let parser_identity_record = artifact
            .unsupported
            .records
            .iter()
            .find(|record| record.stage == PARSER_ARTIFACT_IDENTITY_STAGE)
            .expect("missing loader identity must be recorded as a parser identity blocker");
        assert!(parser_identity_record.feature.contains("missing loader build-id"));
        assert!(!binary_artifact_metadata_identity_allows_proof_grade(&artifact.binary));

        let trust_ir_json = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
            .expect("default decompile output should include TrustIr JSON");
        let trust_ir_json: serde_json::Value =
            serde_json::from_str(trust_ir_json.text.as_deref().expect("TrustIr JSON text"))
                .expect("TrustIr output should parse as JSON");
        assert!(
            trust_ir_json["unsupported"]["records"]
                .as_array()
                .expect("TrustIr JSON should carry unsupported records")
                .iter()
                .any(|record| {
                    record["stage"] == PARSER_ARTIFACT_IDENTITY_STAGE
                        && record["feature"]
                            .as_str()
                            .is_some_and(|feature| feature.contains("missing loader build-id"))
                })
        );
    }

    #[cfg(feature = "elf")]
    #[test]
    fn x86_64_decompile_preserves_memory_fact_instruction_provenance() {
        let artifact = decompile_binary(
            &minimal_x86_64_elf_with_entry_bytes(&[
                0x55, // PUSH RBP
                0x48, 0x89, 0xE5, // MOV RBP, RSP
                0x5D, // POP RBP
                0xC3, // RET
            ]),
            DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]),
        )
        .expect("x86_64 stack fixture should decompile with exact memory provenance");

        assert_eq!(artifact.binary.format, BinaryArtifactFormat::Elf);
        assert_eq!(artifact.binary.architecture, "x86-64");
        assert_eq!(artifact.functions.len(), 1);
        assert_eq!(artifact.functions[0].name, "_start");

        let push = artifact.functions[0]
            .memory_accesses
            .iter()
            .find(|fact| fact.origin.instruction_address == 0x400000)
            .expect("PUSH RBP should emit a stack memory write fact");
        assert_eq!(push.kind, trust_types::MemoryAccessKind::Write);
        assert_eq!(push.origin.function_entry, Some(0x400000));
        assert_eq!(push.origin.instruction_size, Some(1));
        assert_eq!(push.origin.encoding, Some(0x55));
        assert_eq!(push.origin.instruction_bytes, vec![0x55]);

        let pop = artifact.functions[0]
            .memory_accesses
            .iter()
            .find(|fact| fact.origin.instruction_address == 0x400004)
            .expect("POP RBP should emit a stack memory read fact");
        assert_eq!(pop.kind, trust_types::MemoryAccessKind::Read);
        assert_eq!(pop.origin.function_entry, Some(0x400000));
        assert_eq!(pop.origin.instruction_size, Some(1));
        assert_eq!(pop.origin.encoding, Some(0x5D));
        assert_eq!(pop.origin.instruction_bytes, vec![0x5D]);

        assert!(artifact.memory_model.accesses.iter().any(|fact| fact.origin == push.origin));
        assert!(artifact.memory_model.accesses.iter().any(|fact| fact.origin == pop.origin));
    }

    #[cfg(feature = "elf")]
    #[test]
    fn decompile_json_preserves_source_and_instruction_provenance_for_aarch64_and_x86_64() {
        let trust_ir_json_output = |artifact: &DecompilationArtifact| -> serde_json::Value {
            let output = artifact
                .reconstruction
                .outputs
                .iter()
                .find(|output| output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
                .expect("TrustIr JSON output");
            serde_json::from_str(output.text.as_deref().expect("TrustIr JSON text"))
                .expect("TrustIr output should parse as JSON")
        };
        let assert_binary_address_only_source =
            |artifact_json: &serde_json::Value, architecture: &str| {
                assert_eq!(artifact_json["binary"]["architecture"], architecture);
                assert_eq!(artifact_json["source_provenance"]["status"], "unavailable");
                assert_eq!(artifact_json["source_provenance"]["exact_mapping_count"], 0);
                assert_eq!(artifact_json["source_provenance"]["ambiguous_mapping_count"], 0);
                assert_eq!(
                    artifact_json["source_provenance"]["source_backpropagation_allowed"],
                    false
                );
            };

        let aarch64_artifact = decompile_binary(
            &minimal_aarch64_elf_with_entry_instructions(&[
                0xD5033B9F, // DMB ISH: modeled only as an ordering boundary.
                0xD65F03C0, // RET
            ]),
            DecompileOptions::default(),
        )
        .expect("AArch64 fixture should decompile to a JSON report");
        let aarch64_report_json =
            serde_json::to_value(&aarch64_artifact).expect("AArch64 report should serialize");
        assert_binary_address_only_source(&aarch64_report_json, "AArch64");

        let aarch64_trust_ir_json = trust_ir_json_output(&aarch64_artifact);
        let aarch64_records = aarch64_trust_ir_json["unsupported"]["records"]
            .as_array()
            .expect("AArch64 TrustIr JSON should include unsupported records");
        assert!(aarch64_records.iter().any(|record| {
            record["stage"] == "trust-lift::semantic-lift"
                && record["architecture"] == "aarch64"
                && record["opcode"] == "Dmb"
                && record["origin"]["function_entry"] == 0x400000
                && record["origin"]["instruction_address"] == 0x400000
                && record["origin"]["instruction_size"] == 4
                && record["origin"]["encoding"].as_u64() == Some(0xD5033B9F)
                && record["origin"]["instruction_bytes"]
                    == serde_json::json!([0x9F, 0x3B, 0x03, 0xD5])
        }));

        let x86_64_artifact = decompile_binary(
            &minimal_x86_64_elf_with_entry_bytes(&[
                0x55, // PUSH RBP
                0x48, 0x89, 0xE5, // MOV RBP, RSP
                0x5D, // POP RBP
                0xC3, // RET
            ]),
            DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]),
        )
        .expect("x86_64 fixture should decompile to a JSON report");
        let x86_64_report_json =
            serde_json::to_value(&x86_64_artifact).expect("x86_64 report should serialize");
        assert_binary_address_only_source(&x86_64_report_json, "x86-64");

        let memory_facts = x86_64_report_json["functions"][0]["memory_accesses"]
            .as_array()
            .expect("x86_64 report JSON should include function memory facts");
        assert!(memory_facts.iter().any(|fact| {
            fact["kind"] == "Write"
                && fact["origin"]["function_entry"] == 0x400000
                && fact["origin"]["instruction_address"] == 0x400000
                && fact["origin"]["instruction_size"] == 1
                && fact["origin"]["encoding"] == 0x55
                && fact["origin"]["instruction_bytes"] == serde_json::json!([0x55])
        }));
        assert!(memory_facts.iter().any(|fact| {
            fact["kind"] == "Read"
                && fact["origin"]["function_entry"] == 0x400000
                && fact["origin"]["instruction_address"] == 0x400004
                && fact["origin"]["instruction_size"] == 1
                && fact["origin"]["encoding"] == 0x5D
                && fact["origin"]["instruction_bytes"] == serde_json::json!([0x5D])
        }));
        let memory_model_accesses = x86_64_report_json["memory_model"]["accesses"]
            .as_array()
            .expect("x86_64 report JSON should include memory-model accesses");
        assert_eq!(memory_model_accesses, memory_facts);
    }

    #[test]
    fn decompiled_x86_64_movabs_serializes_instruction_provenance() {
        let text_base: u64 = 0x401000;
        let movabs_bytes = [0x48, 0xB8, 0x78, 0x56, 0x34, 0x12, 0, 0, 0, 0];
        let mut text_section = Vec::new();
        text_section.extend_from_slice(&movabs_bytes);
        text_section.push(0xC3);

        let lifter = trust_lift::Lifter::new_with_arch(
            vec![trust_lift::FunctionBoundary {
                name: "return_imm".to_string(),
                start: text_base,
                size: text_section.len() as u64,
            }],
            text_base,
            text_section.len() as u64,
            0,
            LiftArch::X86_64,
        );
        let function = lifter
            .lift_function(&text_section, text_base)
            .expect("x86_64 MOVABS fixture should lift");
        let lifted = LiftedBinary {
            format: "ELF",
            architecture: "x86-64",
            endianness: trust_lift::binary::BinaryEndianness::Little,
            entry_point: Some(text_base),
            build_id: None,
            segments: vec![],
            memory_model: BinaryMemoryModel::default(),
            function_seeds: vec![trust_lift::LiftedFunctionSeed {
                name: Some("return_imm".to_string()),
                entry_point: text_base,
                size: Some(text_section.len() as u64),
                source: trust_lift::LiftedFunctionSeedSource::Symbol,
            }],
            source_provenance: trust_lift::LiftedSourceProvenance::default(),
            source_mappings: vec![],
            functions: vec![function],
            failures: vec![],
        };

        let artifact = decompilation_artifact_from_lifted(
            text_section.len(),
            &DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]),
            &lifted,
        )
        .expect("MOVABS lifted binary should become a decompilation artifact");

        let function = artifact.functions.first().expect("decompiled function");
        let provenance =
            function.instruction_provenance.first().expect("MOVABS instruction provenance");
        assert_eq!(provenance.instruction_address, text_base);
        assert_eq!(provenance.instruction_size, Some(10));
        assert_eq!(provenance.encoding, Some(0xB8));
        assert_eq!(provenance.instruction_bytes, movabs_bytes.to_vec());
        assert!(
            provenance
                .source
                .as_ref()
                .is_some_and(|source| source.binary_address_value() == Some(text_base))
        );

        let artifact_json = serde_json::to_value(&artifact).expect("artifact should serialize");
        assert_eq!(
            artifact_json["functions"][0]["instruction_provenance"][0]["instruction_bytes"],
            serde_json::json!(movabs_bytes.to_vec())
        );
        assert_eq!(
            artifact_json["functions"][0]["instruction_provenance"][0]["instruction_size"],
            10
        );

        let trust_ir_json_output = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
            .expect("TrustIr JSON output");
        let trust_ir_json: serde_json::Value =
            serde_json::from_str(trust_ir_json_output.text.as_deref().expect("TrustIr JSON text"))
                .expect("TrustIr output should parse as JSON");
        assert_eq!(
            trust_ir_json["functions"][0]["instruction_provenance"][0]["instruction_bytes"],
            serde_json::json!(movabs_bytes.to_vec())
        );
        assert_eq!(
            trust_ir_json["functions"][0]["instruction_provenance"][0]["instruction_size"],
            10
        );
    }

    #[test]
    fn initial_trust_ir_json_release_gate_reflects_reconstruction_summary() {
        let lifted = synthetic_lifted_binary(&[("plain_trust_ir", 0x401000)]);
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);

        let artifact =
            decompilation_artifact_from_lifted(8, &options, &lifted).expect("synthetic artifact");

        assert!(
            !reconstruction_allows_artifact_proof_grade(&artifact.reconstruction),
            "{:?}",
            artifact.reconstruction
        );

        let output = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
            .expect("TrustIr JSON output");
        let json: serde_json::Value =
            serde_json::from_str(output.text.as_deref().expect("TrustIr JSON text"))
                .expect("TrustIr output should parse as JSON");
        let gate = &json["checked_certificate_bridge"]["release_gate"];

        assert_eq!(gate["accepted"], false);
        assert_eq!(gate["target_reconstruction_accepted"], false);
        assert!(
            !gate["blockers"]
                .as_array()
                .expect("release-gate blockers")
                .iter()
                .any(|blocker| blocker == "target_reconstruction_not_evaluated"),
            "{gate:?}"
        );
        assert!(
            gate["blockers"]
                .as_array()
                .expect("release-gate blockers")
                .iter()
                .any(|blocker| blocker == "target_reconstruction_not_accepted"),
            "{gate:?}"
        );
        assert!(
            gate["blockers"]
                .as_array()
                .expect("release-gate blockers")
                .iter()
                .any(|blocker| blocker == "checked_certificates_not_accepted"),
            "{gate:?}"
        );
    }

    #[test]
    fn unsupported_conversion_outputs_are_rejected_not_proof_grade() {
        let metadata = BinaryArtifactMetadata {
            format: BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            entry_point: Some(0x401000),
            ..Default::default()
        };
        let mut unsupported = UnsupportedLedger::default();
        unsupported.records.push(unsupported_record(
            "trust-decompile",
            Some(&metadata.architecture),
            None,
            None,
            rejected_output_message(DecompileOutputKind::TrustCgUnsupported),
        ));

        let outputs = build_outputs(BuildOutputsInput {
            metadata: &metadata,
            functions: &[],
            call_graph: &CallGraph::new(),
            memory_facts: &[],
            unsupported: &unsupported,
            source_provenance: &BinarySourceProvenanceSummary::default(),
            requested: &[
                DecompileOutputKind::TrustCgUnsupported,
                DecompileOutputKind::WasmUnsupported,
            ],
            source_assumptions: &[],
            source_diagnostics: &[],
        })
        .expect("unsupported placeholder outputs should still materialize diagnostics");

        assert_eq!(outputs.len(), 2);
        for output in outputs {
            assert_eq!(output.trust_level, TrustLevel::Rejected);
            assert_eq!(output.validation, ReconstructionValidationStatus::Failed);
            assert_ne!(output.trust_level, TrustLevel::ProofGrade);
            assert!(output.diagnostics.iter().any(|diag| diag.contains("unsupported")));
            assert!(output.diagnostics.iter().any(|diag| diag.contains("not proof-grade")));
        }
    }

    #[test]
    fn wasm_text_output_emits_inspectable_constant_return_without_proof_grade() {
        let metadata = BinaryArtifactMetadata {
            format: BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            entry_point: Some(0x401000),
            ..Default::default()
        };
        let function = DecompiledFunction {
            name: "answer".to_string(),
            lifted: Some(constant_return_trust_ir("answer", 42)),
            ..Default::default()
        };

        let outputs = build_outputs(BuildOutputsInput {
            metadata: &metadata,
            functions: &[function],
            call_graph: &CallGraph::new(),
            memory_facts: &[],
            unsupported: &UnsupportedLedger::default(),
            source_provenance: &BinarySourceProvenanceSummary::default(),
            requested: &[DecompileOutputKind::WasmText],
            source_assumptions: &[],
            source_diagnostics: &[],
        })
        .expect("Wasm text output should build");

        assert_eq!(outputs.len(), 1);
        let wasm = &outputs[0];
        assert_eq!(wasm.target, DecompileTarget::Wasm);
        assert_eq!(wasm.validation, ReconstructionValidationStatus::Validated);
        assert_eq!(wasm.trust_level, TrustLevel::Rejected);
        assert_ne!(wasm.trust_level, TrustLevel::ProofGrade);
        let wasm_text = wasm.text.as_deref().expect("Wasm text");
        assert!(wasm_text.contains("i32.const 42"));
        assert!(
            wasm.diagnostics
                .iter()
                .any(|diagnostic| diagnostic == "validation is syntactic subset validation only; Wasm target gate rejects until proof metadata is available")
        );
        assert!(
            wasm.diagnostics
                .iter()
                .any(|diagnostic| diagnostic == "Wasm text is never proof-grade")
        );
        assert!(wasm.target_validation_blockers.iter().any(|blocker| {
            blocker.code == "missing-target-semantic-validation"
                && blocker.feature == "missing-target-semantic-validation"
                && blocker.reason.contains("Wasm target semantics")
        }));
        assert_eq!(wasm.validation_records.len(), 1);
        assert_eq!(wasm.validation_records[0].trust_level, TrustLevel::Rejected);
        assert!(
            wasm.validation_records[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic == "conversion-status=translation_rejected")
        );
    }

    #[test]
    fn wasm_text_output_rejects_missing_lifted_trust_ir() {
        let metadata = BinaryArtifactMetadata {
            format: BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            entry_point: Some(0x401000),
            ..Default::default()
        };
        let function = DecompiledFunction { name: "missing".to_string(), ..Default::default() };

        let outputs = build_outputs(BuildOutputsInput {
            metadata: &metadata,
            functions: &[function],
            call_graph: &CallGraph::new(),
            memory_facts: &[],
            unsupported: &UnsupportedLedger::default(),
            source_provenance: &BinarySourceProvenanceSummary::default(),
            requested: &[DecompileOutputKind::WasmText],
            source_assumptions: &[],
            source_diagnostics: &[],
        })
        .expect("rejected Wasm text output should still build diagnostics");

        assert_eq!(outputs.len(), 1);
        let wasm = &outputs[0];
        assert!(wasm.text.is_none());
        assert_eq!(wasm.validation, ReconstructionValidationStatus::Failed);
        assert_eq!(wasm.trust_level, TrustLevel::Rejected);
        assert_ne!(wasm.trust_level, TrustLevel::ProofGrade);
        assert_eq!(wasm.validation_records.len(), 1);
        assert_eq!(wasm.validation_records[0].trust_level, TrustLevel::Rejected);
    }

    #[cfg(not(feature = "trust-cg"))]
    #[test]
    fn trust_cg_text_output_fails_closed_when_bridge_feature_disabled() {
        let metadata = BinaryArtifactMetadata {
            format: BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            entry_point: Some(0x401000),
            ..Default::default()
        };
        let function = DecompiledFunction {
            name: "answer".to_string(),
            entry: 0x401000,
            lifted: Some(constant_return_trust_ir("answer", 42)),
            ..Default::default()
        };

        let outputs = build_outputs(BuildOutputsInput {
            metadata: &metadata,
            functions: &[function],
            call_graph: &CallGraph::new(),
            memory_facts: &[],
            unsupported: &UnsupportedLedger::default(),
            source_provenance: &BinarySourceProvenanceSummary::default(),
            requested: &[DecompileOutputKind::TrustCgText],
            source_assumptions: &[],
            source_diagnostics: &[],
        })
        .expect("disabled trust-cg backend should still emit rejected evidence");

        assert_eq!(outputs.len(), 1);
        let trust_cg = &outputs[0];
        assert_eq!(trust_cg.target, DecompileTarget::TrustCg);
        assert!(trust_cg.text.is_none());
        assert_eq!(trust_cg.validation, ReconstructionValidationStatus::Failed);
        assert_eq!(trust_cg.trust_level, TrustLevel::Rejected);
        assert!(
            trust_cg.diagnostics.iter().any(|diagnostic| diagnostic == "format=trust_cg-rejected")
        );
        assert!(
            trust_cg.diagnostics.iter().any(|diagnostic| diagnostic == "trust-cg-feature=disabled")
        );
        assert!(trust_cg.target_validation_blockers.iter().any(|blocker| {
            blocker.stage == "trust-cg-bridge::target-validation"
                && blocker.code == "trust-cg-backend-unavailable"
                && blocker.feature == "trust-cg-backend-unavailable"
                && blocker.reason.contains("enable feature `trust-cg`")
        }));
        assert_eq!(trust_cg.validation_records.len(), 1);
        assert_eq!(trust_cg.validation_records[0].candidate, ReconstructionCandidateKind::Missing);
        assert_eq!(trust_cg.validation_records[0].trust_level, TrustLevel::Rejected);
    }

    #[cfg(feature = "trust-cg")]
    #[test]
    fn trust_cg_text_output_emits_inspectable_rejected_lir_without_proof_grade() {
        let metadata = BinaryArtifactMetadata {
            format: BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            entry_point: Some(0x401000),
            ..Default::default()
        };
        let function = DecompiledFunction {
            name: "answer".to_string(),
            entry: 0x401000,
            lifted: Some(constant_return_trust_ir("answer", 42)),
            ..Default::default()
        };

        let outputs = build_outputs(BuildOutputsInput {
            metadata: &metadata,
            functions: &[function],
            call_graph: &CallGraph::new(),
            memory_facts: &[],
            unsupported: &UnsupportedLedger::default(),
            source_provenance: &BinarySourceProvenanceSummary::default(),
            requested: &[DecompileOutputKind::TrustCgText],
            source_assumptions: &[],
            source_diagnostics: &[],
        })
        .expect("trust-cg text output should build through bridge");

        assert_eq!(outputs.len(), 1);
        let trust_cg = &outputs[0];
        assert_eq!(trust_cg.target, DecompileTarget::TrustCg);
        assert_eq!(trust_cg.validation, ReconstructionValidationStatus::Validated);
        assert_eq!(trust_cg.trust_level, TrustLevel::Rejected);
        assert_ne!(trust_cg.trust_level, TrustLevel::ProofGrade);
        assert!(trust_cg.text.as_ref().is_some_and(|text| {
            text.contains("\"name\": \"answer\"") && text.contains("\"Iconst\"")
        }));
        let trust_cg_json: serde_json::Value =
            serde_json::from_str(trust_cg.text.as_deref().expect("trust-cg JSON text"))
                .expect("trust-cg output should be JSON");
        assert_eq!(trust_cg_json["validation"]["status"], "inspectable_rejected");
        assert_eq!(trust_cg_json["validation"]["trust_level"], "rejected");
        assert_eq!(trust_cg_json["validation"]["proof_grade"], false);
        assert_eq!(trust_cg_json["validation"]["source"], "binary-derived-trust_ir");
        assert_eq!(trust_cg_json["validation"]["subset"], "trust_cg-lir-structural");
        assert!(
            trust_cg_json["target_validation_blockers"]
                .as_array()
                .expect("trust-cg JSON should expose target validation blockers")
                .iter()
                .any(|blocker| {
                    blocker["code"] == "missing-target-semantic-validation"
                        && blocker["feature"] == "missing-target-semantic-validation"
                })
        );
        assert_eq!(trust_cg_json["validation_records"][0]["trust_level"], "Rejected");
        assert_eq!(trust_cg_json["validation_records"][0]["target"], "TrustCg");
        assert!(
            trust_cg_json["diagnostics"]
                .as_array()
                .expect("trust-cg JSON should expose conversion diagnostics")
                .iter()
                .any(|diagnostic| diagnostic == "trust_cg-validation=inspectable-rejected")
        );
        assert!(
            trust_cg.diagnostics.iter().any(|diagnostic| diagnostic == "format=trust_cg-lir-json")
        );
        assert!(
            trust_cg
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic == "conversion-status=translation_rejected")
        );
        assert!(
            trust_cg
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic == "trust_cg-validation=inspectable-rejected")
        );
        assert!(trust_cg.diagnostics.iter().any(|diagnostic| diagnostic == "proof-grade=false"));
        assert!(trust_cg.target_validation_blockers.iter().any(|blocker| {
            blocker.code == "missing-target-semantic-validation"
                && blocker.feature == "missing-target-semantic-validation"
        }));
        assert!(trust_cg.target_validation_blockers.iter().any(|blocker| {
            blocker.code == "missing-refinement-metadata"
                && blocker.feature == "missing-refinement-metadata"
        }));
        assert!(!trust_cg.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("format=trust_cg-unsupported")
                || diagnostic.contains("unsupported in this build")
        }));
        assert_eq!(trust_cg.validation_records.len(), 1);
        assert_eq!(trust_cg.validation_records[0].target, DecompileTarget::TrustCg);
        assert_eq!(trust_cg.validation_records[0].trust_level, TrustLevel::Rejected);
        assert_ne!(trust_cg.validation_records[0].trust_level, TrustLevel::ProofGrade);
        assert!(
            trust_cg.validation_records[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic == "trust_cg-validation=inspectable-rejected")
        );
    }

    #[cfg(feature = "trust-cg")]
    #[test]
    fn trust_cg_non_ground_symbolic_formula_fails_closed_with_preserved_metadata() {
        let metadata = BinaryArtifactMetadata {
            format: BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            entry_point: Some(0x401000),
            ..Default::default()
        };
        let function = DecompiledFunction {
            name: "symbolic_answer".to_string(),
            entry: 0x401000,
            lifted: Some(symbolic_return_trust_ir("symbolic_answer")),
            ..Default::default()
        };

        let outputs = build_outputs(BuildOutputsInput {
            metadata: &metadata,
            functions: &[function],
            call_graph: &CallGraph::new(),
            memory_facts: &[],
            unsupported: &UnsupportedLedger::default(),
            source_provenance: &BinarySourceProvenanceSummary::default(),
            requested: &[DecompileOutputKind::TrustCgText],
            source_assumptions: &[],
            source_diagnostics: &[],
        })
        .expect("trust-cg symbolic rejection should remain inspectable in the artifact");

        let trust_cg = &outputs[0];
        assert_eq!(trust_cg.validation, ReconstructionValidationStatus::Failed);
        assert_eq!(trust_cg.trust_level, TrustLevel::Rejected);
        assert!(trust_cg.text.is_none(), "rejected symbolic LIR must not be emitted");
        assert_eq!(trust_cg.preserved_symbolic_formulas.len(), 1);
        assert_eq!(
            trust_cg.preserved_symbolic_formulas[0].function.as_deref(),
            Some("symbolic_answer")
        );
        assert_eq!(trust_cg.preserved_symbolic_formulas[0].block, Some(0));
        assert_eq!(trust_cg.preserved_symbolic_formulas[0].statement_index, Some(0));
        assert!(
            trust_cg
                .target_validation_blockers
                .iter()
                .any(|blocker| blocker.code == "trust_cg-lowering-failed")
        );
        assert!(trust_cg.target_validation_blockers.iter().any(|blocker| {
            blocker.code == "symbolic-formula-proof-semantics"
                && blocker.function.as_deref() == Some("symbolic_answer")
        }));
        assert!(trust_cg.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("symbolic operand requires target-semantic lowering")
        }));
        assert!(
            trust_cg
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic == "format=trust_cg-rejected")
        );
        assert!(trust_cg.diagnostics.iter().any(|diagnostic| diagnostic == "proof-grade=false"));
    }

    #[test]
    fn trust_cg_and_wasm_text_outputs_fail_closed_on_unsupported_trust_ir() {
        let lifted = synthetic_lifted_binary(&[("unsupported_trust_ir", 0x401000)]);
        let options = DecompileOptions::default()
            .with_outputs([DecompileOutputKind::TrustCgText, DecompileOutputKind::WasmText]);

        let artifact =
            decompilation_artifact_from_lifted(16, &options, &lifted).expect("synthetic artifact");

        assert_eq!(artifact.target, DecompileTarget::TrustCg);
        assert!(
            artifact.unsupported.records.iter().any(|record| record.stage == "trust-cg-bridge")
        );
        assert!(
            artifact.unsupported.records.iter().any(|record| record.stage == "trust-wasm-bridge")
        );

        let trust_cg = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::TrustCg)
            .expect("trust-cg output");
        assert!(trust_cg.text.is_none());
        assert_eq!(trust_cg.validation, ReconstructionValidationStatus::Failed);
        assert_eq!(trust_cg.trust_level, TrustLevel::Rejected);
        assert_ne!(trust_cg.trust_level, TrustLevel::ProofGrade);
        assert!(
            trust_cg.diagnostics.iter().any(|diagnostic| diagnostic == "format=trust_cg-rejected")
        );
        assert_eq!(trust_cg.validation_records.len(), 1);
        assert_eq!(trust_cg.validation_records[0].trust_level, TrustLevel::Rejected);

        let wasm = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Wasm)
            .expect("Wasm output");
        assert!(wasm.text.is_none());
        assert_eq!(wasm.validation, ReconstructionValidationStatus::Failed);
        assert_eq!(wasm.trust_level, TrustLevel::Rejected);
        assert_ne!(wasm.trust_level, TrustLevel::ProofGrade);
        assert!(wasm.diagnostics.iter().any(|diagnostic| diagnostic == "format=wasm-rejected"));
        assert_eq!(wasm.validation_records.len(), 1);
        assert_eq!(wasm.validation_records[0].trust_level, TrustLevel::Rejected);
    }

    #[cfg(feature = "trust-cg")]
    #[test]
    fn trust_cg_text_output_stays_inspectable_when_lift_has_unsupported_records() {
        // When the lifted TrustIr still lowers structurally but the lift recorded
        // upstream unsupported features (e.g., a semantic-lift gap), trust-cg conversion
        // must NOT reclassify the lift-stage blocker as a trust-cg translation rejection.
        // The lift-stage blockers are surfaced as target_validation_blockers, but the
        // trust-cg output remains "inspectable rejected" (Validated/Rejected), with text
        // present, so downstream consumers can audit the structural reconstruction.
        let mut lifted = synthetic_lifted_binary(&[("partially_lifted", 0x401000)]);
        lifted.functions[0].trust_ir_body = constant_return_trust_ir("partially_lifted", 7).body;
        lifted.functions[0].unsupported.records.push(unsupported_record(
            "trust-lift",
            Some("x86-64"),
            Some(0x401000),
            Some(0x401000),
            "unsupported instruction side effect preserved in lifted coverage",
        ));
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustCgText]);

        let artifact =
            decompilation_artifact_from_lifted(16, &options, &lifted).expect("synthetic artifact");

        assert_eq!(artifact.trust_level, TrustLevel::Rejected);
        assert_eq!(artifact.reconstruction.trust_level, TrustLevel::Rejected);
        assert!(
            !artifact.unsupported.records.iter().any(|record| {
                record.stage == "trust-cg-bridge"
                    && record.feature.contains("unsupported lifted feature")
            }),
            "trust-cg must not reclassify the lift-stage blocker as a trust-cg translation rejection: {:?}",
            artifact.unsupported.records
        );

        let trust_cg = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::TrustCg)
            .expect("trust-cg output");
        assert!(
            trust_cg.text.is_some(),
            "lift-stage unsupported records must not suppress inspectable trust-cg output"
        );
        assert_eq!(trust_cg.validation, ReconstructionValidationStatus::Validated);
        assert_eq!(trust_cg.trust_level, TrustLevel::Rejected);
        // The lift-stage blocker is propagated as a target_validation_blocker so callers
        // can still see exactly why this conversion is not proof-grade.
        assert!(
            trust_cg.target_validation_blockers.iter().any(|blocker| {
                blocker.feature == "unsupported-trust_cg-subset"
                    && blocker.function.as_deref() == Some("partially_lifted")
            }),
            "lift-stage unsupported features must remain as target validation blockers"
        );
        assert!(
            trust_cg.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("trust-cg conversion rejected: function `partially_lifted`")
            }),
            "diagnostic trail must still expose the lift-stage blocker text"
        );
    }

    #[cfg(feature = "trust-cg")]
    #[test]
    fn trust_cg_text_output_keeps_inspectable_output_with_non_semantic_provenance_blockers() {
        let mut lifted = synthetic_lifted_binary(&[("provenance_blocked", 0x401000)]);
        lifted.functions[0].trust_ir_body = constant_return_trust_ir("provenance_blocked", 7).body;
        lifted.functions[0].unsupported.records.push(unsupported_record(
            "trust-lift::source-provenance",
            Some("x86-64"),
            Some(0x401000),
            Some(0x401000),
            "non-exact source provenance: unavailable",
        ));
        lifted.functions[0].unsupported.records.push(unsupported_record(
            "trust-lift::type-provenance",
            Some("x86-64"),
            Some(0x401000),
            Some(0x401000),
            "non-recovered debug type provenance: unavailable",
        ));
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustCgText]);

        let artifact =
            decompilation_artifact_from_lifted(16, &options, &lifted).expect("synthetic artifact");

        assert_eq!(artifact.trust_level, TrustLevel::Rejected);
        assert!(artifact.unsupported.records.iter().any(|record| {
            record.stage == "trust-lift::source-provenance"
                && record.feature.contains("non-exact source provenance")
        }));
        assert!(
            !artifact.unsupported.records.iter().any(|record| {
                record.stage == "trust-cg-bridge"
                    && record.feature.contains("unsupported lifted feature")
            }),
            "non-semantic provenance blockers must not be reclassified as translation failures"
        );

        let trust_cg = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::TrustCg)
            .expect("trust-cg output");
        assert!(trust_cg.text.is_some());
        assert_eq!(trust_cg.validation, ReconstructionValidationStatus::Validated);
        assert_eq!(trust_cg.trust_level, TrustLevel::Rejected);
        assert!(
            trust_cg.diagnostics.iter().any(|diagnostic| diagnostic == "format=trust_cg-lir-json")
        );
        assert!(
            trust_cg
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic == "conversion-status=translation_rejected" })
        );
        assert!(
            trust_cg
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic == "trust_cg-validation=inspectable-rejected" })
        );
        assert!(
            !trust_cg
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("unsupported lifted feature"))
        );

        let trust_cg_json: serde_json::Value =
            serde_json::from_str(trust_cg.text.as_deref().expect("trust-cg JSON text"))
                .expect("trust-cg text should be JSON");
        assert_eq!(trust_cg_json["validation"]["status"], "inspectable_rejected");
        assert_eq!(trust_cg_json["validation"]["trust_level"], "rejected");
        assert_eq!(trust_cg_json["validation"]["proof_grade"], false);
    }

    #[cfg(feature = "trust-cg")]
    #[test]
    fn trust_cg_and_wasm_outputs_expose_blockers_and_preserved_symbolic_formulas() {
        let mut lifted = synthetic_lifted_binary(&[("symbolic_blocked", 0x401000)]);
        lifted.functions[0].trust_ir_body = symbolic_return_trust_ir("symbolic_blocked").body;
        lifted.functions[0].unsupported.records.push(unsupported_record(
            "trust-lift",
            Some("x86-64"),
            Some(0x401000),
            Some(0x401000),
            "symbolic machine formula preserved for target inspection",
        ));
        let options = DecompileOptions::default()
            .with_outputs([DecompileOutputKind::TrustCgText, DecompileOutputKind::WasmText]);

        let artifact =
            decompilation_artifact_from_lifted(16, &options, &lifted).expect("synthetic artifact");

        for target in [DecompileTarget::TrustCg, DecompileTarget::Wasm] {
            let output = artifact
                .reconstruction
                .outputs
                .iter()
                .find(|output| output.target == target)
                .expect("target output");

            // Lift-stage unsupported records leave the trust-cg/Wasm output as
            // "inspectable rejected": structural validation succeeds (validation =
            // Validated) but trust_level stays Rejected and the lift-stage blockers
            // are reported as target_validation_blockers.
            assert_eq!(output.trust_level, TrustLevel::Rejected);
            assert!(!output.target_validation_blockers.is_empty());
            assert!(
                output.target_validation_blockers.iter().any(|blocker| blocker.target == target
                    && blocker.reason.contains("symbolic machine formula"))
            );
            assert!(output.target_validation_blockers.iter().any(|blocker| {
                blocker.target == target
                    && blocker.feature == "symbolic-formula-proof-semantics"
                    && blocker.function.as_deref() == Some("symbolic_blocked")
            }));
            assert_symbolic_proof_consumer_blocker(output, &target, "symbolic_blocked");
            assert_eq!(output.preserved_symbolic_formulas.len(), 1);
            assert_eq!(output.preserved_symbolic_formulas[0].target, target);
            assert_eq!(
                output.preserved_symbolic_formulas[0].function.as_deref(),
                Some("symbolic_blocked")
            );
            assert_eq!(output.preserved_symbolic_formulas[0].block, Some(0));
            assert_eq!(output.preserved_symbolic_formulas[0].statement_index, Some(0));
            assert!(matches!(
                &output.preserved_symbolic_formulas[0].formula,
                trust_types::Formula::Var(_, _)
            ));
        }

        let json = serde_json::to_value(&artifact).expect("artifact should serialize");
        let outputs = json["reconstruction"]["outputs"].as_array().expect("outputs array");
        assert!(outputs.iter().any(|output| {
            output["target"] == "TrustCg"
                && output["target_validation_blockers"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && output["preserved_symbolic_formulas"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
        }));
        assert!(outputs.iter().any(|output| {
            output["target"] == "Wasm"
                && output["target_validation_blockers"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
                && output["preserved_symbolic_formulas"]
                    .as_array()
                    .is_some_and(|items| !items.is_empty())
        }));
    }

    #[test]
    fn trust_ir_json_preserves_symbolic_aggregate_with_target_blocker() {
        let mut lifted = synthetic_lifted_binary(&[("symbolic_aggregate_blocked", 0x401000)]);
        lifted.functions[0].trust_ir_body =
            symbolic_aggregate_trust_ir("symbolic_aggregate_blocked").body;
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);

        let artifact =
            decompilation_artifact_from_lifted(16, &options, &lifted).expect("synthetic artifact");

        assert_eq!(artifact.trust_level, TrustLevel::Partial);
        assert_eq!(artifact.reconstruction.trust_level, TrustLevel::Partial);
        let output = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::TrustIr)
            .expect("TrustIr output");

        assert!(output.text.is_some());
        assert_eq!(output.validation, ReconstructionValidationStatus::Validated);
        assert_eq!(output.trust_level, TrustLevel::Partial);
        assert_ne!(output.trust_level, TrustLevel::ProofGrade);
        assert!(output.target_validation_blockers.iter().any(|blocker| {
            blocker.target == DecompileTarget::TrustIr
                && blocker.stage == "trust-ir-bridge::target-validation"
                && blocker.feature == "symbolic-formula-proof-semantics"
                && blocker.function.as_deref() == Some("symbolic_aggregate_blocked")
                && blocker.reason.contains("symbolic formula")
        }));
        assert_eq!(output.preserved_symbolic_formulas.len(), 1);
        assert_eq!(output.preserved_symbolic_formulas[0].target, DecompileTarget::TrustIr);
        assert_eq!(
            output.preserved_symbolic_formulas[0].function.as_deref(),
            Some("symbolic_aggregate_blocked")
        );
        assert_eq!(output.preserved_symbolic_formulas[0].block, Some(0));
        assert_eq!(output.preserved_symbolic_formulas[0].statement_index, Some(0));
    }

    #[test]
    fn trust_ir_json_preserves_copied_symbolic_aggregate_with_target_blocker() {
        let mut lifted = synthetic_lifted_binary(&[("symbolic_copy_blocked", 0x401000)]);
        lifted.functions[0].trust_ir_body =
            symbolic_copied_aggregate_trust_ir("symbolic_copy_blocked").body;
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);

        let artifact =
            decompilation_artifact_from_lifted(16, &options, &lifted).expect("synthetic artifact");

        assert_eq!(artifact.trust_level, TrustLevel::Partial);
        let output = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::TrustIr)
            .expect("TrustIr output");

        assert!(output.text.is_some());
        assert_eq!(output.validation, ReconstructionValidationStatus::Validated);
        assert_eq!(output.trust_level, TrustLevel::Partial);
        assert!(output.target_validation_blockers.iter().any(|blocker| {
            blocker.feature == "symbolic-formula-proof-semantics"
                && blocker.function.as_deref() == Some("symbolic_copy_blocked")
                && blocker.reason.contains("symbolic formula")
        }));
        assert_eq!(output.preserved_symbolic_formulas.len(), 1);
        assert_eq!(
            output.preserved_symbolic_formulas[0].function.as_deref(),
            Some("symbolic_copy_blocked")
        );
        assert_eq!(output.preserved_symbolic_formulas[0].statement_index, Some(0));
    }

    #[test]
    fn trust_ir_outputs_expose_preserved_symbolic_formulas_and_target_blockers() {
        let mut lifted = synthetic_lifted_binary(&[("symbolic_trust_ir", 0x401000)]);
        lifted.functions[0].trust_ir_body = symbolic_return_trust_ir("symbolic_trust_ir").body;
        let options = DecompileOptions::default()
            .with_outputs([DecompileOutputKind::TrustIrJson, DecompileOutputKind::TrustIrText]);

        let artifact =
            decompilation_artifact_from_lifted(16, &options, &lifted).expect("synthetic artifact");

        assert_eq!(artifact.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);

        let outputs = artifact
            .reconstruction
            .outputs
            .iter()
            .filter(|output| output.target == DecompileTarget::TrustIr)
            .collect::<Vec<_>>();
        assert_eq!(outputs.len(), 2);
        for output in outputs {
            assert_eq!(output.trust_level, TrustLevel::Partial);
            assert_eq!(output.preserved_symbolic_formulas.len(), 1);
            assert_eq!(output.preserved_symbolic_formulas[0].target, DecompileTarget::TrustIr);
            assert_eq!(
                output.preserved_symbolic_formulas[0].function.as_deref(),
                Some("symbolic_trust_ir")
            );
            assert!(output.target_validation_blockers.iter().any(|blocker| {
                blocker.target == DecompileTarget::TrustIr
                    && blocker.stage == "trust-ir-bridge::target-validation"
                    && blocker.feature == "symbolic-formula-proof-semantics"
                    && blocker.function.as_deref() == Some("symbolic_trust_ir")
            }));
            assert_symbolic_proof_consumer_blocker(
                output,
                &DecompileTarget::TrustIr,
                "symbolic_trust_ir",
            );
        }
    }

    #[test]
    fn trust_ir_outputs_block_layout_sensitive_casts_without_typed_layout_evidence() {
        let mut lifted = synthetic_lifted_binary(&[("layout_blocked", 0x401000)]);
        lifted.functions[0].trust_ir_body = layout_sensitive_cast_trust_ir("layout_blocked").body;
        let options = DecompileOptions::default()
            .with_outputs([DecompileOutputKind::TrustIrJson, DecompileOutputKind::TrustIrText]);

        let artifact =
            decompilation_artifact_from_lifted(16, &options, &lifted).expect("synthetic artifact");

        assert_eq!(artifact.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        let outputs = artifact
            .reconstruction
            .outputs
            .iter()
            .filter(|output| output.target == DecompileTarget::TrustIr)
            .collect::<Vec<_>>();
        assert_eq!(outputs.len(), 2);
        for output in outputs {
            assert_eq!(output.trust_level, TrustLevel::Partial);
            let blocker = output
                .target_validation_blockers
                .iter()
                .find(|blocker| {
                    blocker.target == DecompileTarget::TrustIr
                        && blocker.stage == "trust-ir-bridge::target-validation"
                        && blocker.feature == TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_FEATURE
                        && blocker.function.as_deref() == Some("layout_blocked")
                })
                .expect("layout-sensitive cast blocker");
            assert!(blocker.reason.contains("typed layout evidence"));
            assert!(blocker.reason.contains("has no concrete memory layout evidence"));
            assert!(
                blocker
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic == "required-evidence=typed-layout-cast-evidence")
            );
            assert!(blocker.diagnostics.iter().any(|diagnostic| diagnostic == "proof-grade=false"));
            assert!(blocker.diagnostics.iter().any(|diagnostic| {
                diagnostic
                    == "trust_ir-layout-evidence-commit=44a43e8a7ffe7c476ea83ec21352e098daf2dda3"
            }));
        }

        let artifact_json = serde_json::to_value(&artifact).expect("artifact should serialize");
        assert!(
            artifact_json["reconstruction"]["outputs"].as_array().expect("outputs").iter().any(
                |output| output["target"] == "TrustIr"
                    && output["target_validation_blockers"].as_array().is_some_and(|blockers| {
                        blockers.iter().any(|blocker| {
                            blocker["feature"] == TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_FEATURE
                        })
                    })
            )
        );
    }

    #[test]
    fn trust_ir_outputs_block_unconsumed_canonical_thread_local_address_semantics() {
        let mut lifted = synthetic_lifted_binary(&[("tls_unconsumed", 0x401000)]);
        lifted.functions[0].trust_ir_body = thread_local_ref_trust_ir("tls_unconsumed").body;
        let options = DecompileOptions::default()
            .with_outputs([DecompileOutputKind::TrustIrJson, DecompileOutputKind::TrustIrText]);

        let artifact =
            decompilation_artifact_from_lifted(16, &options, &lifted).expect("synthetic artifact");
        let outputs = artifact
            .reconstruction
            .outputs
            .iter()
            .filter(|output| output.target == DecompileTarget::TrustIr)
            .collect::<Vec<_>>();
        assert_eq!(outputs.len(), 2, "both TrustIr presentation paths must be covered");

        for output in outputs {
            let blocker = output
                .target_validation_blockers
                .iter()
                .find(|blocker| blocker.code == TRUST_IR_UNCONSUMED_THREAD_LOCAL_ADDR_BLOCKER)
                .expect("canonical TLS address must remain proof-grade blocked");
            assert_eq!(blocker.function.as_deref(), Some("tls_unconsumed"));
            assert_eq!(blocker.stage, "trust-ir-bridge::target-validation");
            assert!(blocker.reason.contains("remains unconsumed"));
            assert!(
                blocker
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic == "dialect-payload=canonical-v1")
            );
            assert!(blocker.diagnostics.iter().any(|diagnostic| {
                diagnostic == "required-evidence=checked-thread-local-address-semantics-consumer"
            }));
            assert!(blocker.diagnostics.iter().any(|diagnostic| diagnostic == "fail-closed=true"));
            assert!(blocker.diagnostics.iter().any(|diagnostic| diagnostic == "proof-grade=false"));
        }
    }

    #[test]
    fn trust_ir_text_blocks_failed_tls_lowering_while_json_keeps_its_hard_error() {
        let mut malformed = thread_local_ref_trust_ir("tls_malformed");
        let Statement::Assign {
            rvalue: Rvalue::Unsupported { operands, .. },
            ..
        } = &mut malformed.body.blocks[0].stmts[0]
        else {
            panic!("TLS fixture assignment disappeared");
        };
        operands.push(Operand::Constant(ConstValue::Int(0)));

        let mut lifted = synthetic_lifted_binary(&[("tls_malformed", 0x401000)]);
        lifted.functions[0].trust_ir_body = malformed.body;
        let text_options = DecompileOptions::default()
            .with_outputs([DecompileOutputKind::TrustIrText]);
        let artifact = decompilation_artifact_from_lifted(16, &text_options, &lifted)
            .expect("TrustIr text should remain inspectable with an explicit lowering blocker");
        let output = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::TrustIr)
            .expect("TrustIr text output");
        assert!(output.text.is_some());
        let blocker = output
            .target_validation_blockers
            .iter()
            .find(|blocker| blocker.code == TRUST_IR_TARGET_LOWERING_FAILED_BLOCKER)
            .expect("failed canonical lowering must create a target-validation blocker");
        assert!(blocker.reason.contains("Rvalue::ThreadLocalRef"));
        assert!(blocker.diagnostics.iter().any(|diagnostic| diagnostic == "fail-closed=true"));
        assert!(blocker.diagnostics.iter().any(|diagnostic| diagnostic == "proof-grade=false"));
        assert!(
            blocker
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic == "target-validation=not-run")
        );

        let json_options = DecompileOptions::default()
            .with_outputs([DecompileOutputKind::TrustIrJson]);
        let error = decompilation_artifact_from_lifted(16, &json_options, &lifted)
            .expect_err("TrustIr JSON must retain its existing canonical-lowering hard error");
        assert!(matches!(&error, DecompileError::TrustIrBridge(_)));
        assert!(error.to_string().contains("Rvalue::ThreadLocalRef"));
    }

    #[test]
    fn trust_ir_thread_local_address_schema_near_miss_stays_fail_closed() {
        let function = thread_local_ref_trust_ir("tls_schema_drift");
        let mut module = lower_functions_to_trust_ir("tls-schema-drift", [&function])
            .expect("canonical TLS fixture should lower");
        let op = module.functions[0].blocks[0]
            .body
            .iter_mut()
            .find_map(|node| match &mut node.inst {
                trust_ir::Inst::DialectOp(op)
                    if op.dialect == trust_ir::dialect::trust_rust::DIALECT
                        && op.op == trust_ir::dialect::trust_rust::THREAD_LOCAL_ADDR_OP =>
                {
                    Some(op)
                }
                _ => None,
            })
            .expect("TLS dialect op");
        op.version = 2;

        let blockers = trust_ir_thread_local_addr_target_validation_blockers(&module);
        assert_eq!(blockers.len(), 1);
        let blocker = &blockers[0];
        assert_eq!(blocker.code, TRUST_IR_UNCONSUMED_THREAD_LOCAL_ADDR_BLOCKER);
        assert!(blocker.reason.contains("noncanonical"));
        assert!(
            blocker
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic == "dialect-payload=noncanonical")
        );
        assert!(blocker.diagnostics.iter().any(|diagnostic| diagnostic == "fail-closed=true"));
        assert!(blocker.diagnostics.iter().any(|diagnostic| diagnostic == "proof-grade=false"));
        assert!(blocker.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("payload-error=")
                && diagnostic.contains("expected payload version 1, got 2")
        }));
    }

    #[test]
    fn trust_ir_thread_local_address_node_result_near_miss_stays_fail_closed() {
        let function = thread_local_ref_trust_ir("tls_result_drift");
        let mut module = lower_functions_to_trust_ir("tls-result-drift", [&function])
            .expect("canonical TLS fixture should lower");
        let node = module.functions[0].blocks[0]
            .body
            .iter_mut()
            .find(|node| {
                matches!(
                    &node.inst,
                    trust_ir::Inst::DialectOp(op)
                        if op.dialect == trust_ir::dialect::trust_rust::DIALECT
                            && op.op == trust_ir::dialect::trust_rust::THREAD_LOCAL_ADDR_OP
                )
            })
            .expect("TLS dialect op");
        node.results.clear();

        let blockers = trust_ir_thread_local_addr_target_validation_blockers(&module);
        assert_eq!(blockers.len(), 1);
        let blocker = &blockers[0];
        assert_eq!(blocker.code, TRUST_IR_UNCONSUMED_THREAD_LOCAL_ADDR_BLOCKER);
        assert!(blocker.reason.contains("0 results instead of exactly one"));
        assert!(
            blocker
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic == "dialect-payload=noncanonical")
        );
        assert!(
            blocker
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic == "node-result-count=0")
        );
        assert!(blocker.diagnostics.iter().any(|diagnostic| diagnostic == "fail-closed=true"));
        assert!(blocker.diagnostics.iter().any(|diagnostic| diagnostic == "proof-grade=false"));
    }

    #[test]
    fn trust_cg_text_output_rejects_empty_lift_without_silent_placeholder() {
        let lifted = synthetic_lifted_binary(&[]);
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustCgText]);

        let artifact =
            decompilation_artifact_from_lifted(16, &options, &lifted).expect("synthetic artifact");

        assert!(
            artifact.unsupported.records.iter().any(|record| record.stage == "trust-cg-bridge"
                && record.feature.contains("requires at least one lifted TrustIr function"))
        );
        let trust_cg = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::TrustCg)
            .expect("trust-cg output");
        assert!(trust_cg.text.is_none());
        assert_eq!(trust_cg.validation, ReconstructionValidationStatus::Failed);
        assert_eq!(trust_cg.trust_level, TrustLevel::Rejected);
        assert!(trust_cg.target_validation_blockers.iter().any(|blocker| {
            blocker.feature == "missing-lifted-trust_ir"
                && blocker.reason.contains("requires at least one lifted TrustIr function")
        }));
        assert!(
            trust_cg
                .target_validation_blockers
                .iter()
                .any(|blocker| { blocker.feature == "missing-target-semantic-validation" })
        );
        assert_eq!(trust_cg.validation_records.len(), 1);
        assert_eq!(trust_cg.validation_records[0].candidate, ReconstructionCandidateKind::Missing);
        assert_eq!(trust_cg.validation_records[0].trust_level, TrustLevel::Rejected);
        assert!(!trust_cg.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("format=trust_cg-unsupported")
                || diagnostic.contains("unsupported in this build")
        }));
    }

    #[test]
    fn rust_skeleton_output_carries_text_only_validation_record() {
        let lifted = synthetic_lifted_binary(&[("rust_like", 0x1000)]);
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::RustSkeleton]);

        let artifact =
            decompilation_artifact_from_lifted(8, &options, &lifted).expect("synthetic artifact");
        let rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust skeleton output");

        assert_eq!(artifact.reconstruction.validation, ReconstructionValidationStatus::Failed);
        assert_ne!(artifact.reconstruction.trust_level, TrustLevel::ProofGrade);
        assert_eq!(rust.validation, ReconstructionValidationStatus::NotAttempted);
        assert_eq!(rust.trust_level, TrustLevel::Exploratory);
        assert_eq!(rust.validation_records.len(), 1);

        let record = &rust.validation_records[0];
        assert_eq!(record.target, DecompileTarget::Rust);
        assert_eq!(record.function.as_deref(), Some("rust_like"));
        assert_eq!(record.lifted_function.as_deref(), Some("rust_like"));
        assert_eq!(record.reconstructed_function, None);
        assert_eq!(record.candidate, ReconstructionCandidateKind::TextOnly);
        assert_eq!(record.status, ReconstructionValidationStatus::NotAttempted);
        assert_eq!(record.trust_level, TrustLevel::Exploratory);
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::TextOnlyCandidateRejected)
        );
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::MissingComparableTrustIr)
        );
        assert!(record.forward.is_none());
        assert!(record.reverse.is_none());
        assert!(
            record
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("no structured reconstructed TrustIr"))
        );
        assert!(
            record
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("rejected as semantic validation evidence"))
        );
        assert!(
            rust.diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("semantic validation candidate rejected"))
        );

        let validated_rust = rust.validated_rust.as_ref().expect("validated Rust path metadata");
        assert_eq!(validated_rust.status, ReconstructionValidationStatus::Failed);
        assert_eq!(validated_rust.trust_level, TrustLevel::Rejected);
        assert_eq!(validated_rust.validation_records.len(), 1);
        assert_eq!(
            validated_rust.validation_records[0].candidate,
            ReconstructionCandidateKind::ValidatedRustStrictSubset
        );
        assert!(
            validated_rust.validation_records[0]
                .evidence
                .contains(&ReconstructionValidationEvidence::RejectedNonStraightLine)
        );
        assert!(
            artifact
                .reconstruction
                .validated_rust
                .as_ref()
                .is_some_and(|validated| validated.status == ReconstructionValidationStatus::Failed)
        );
    }

    #[test]
    fn validated_rust_path_marks_strict_straight_line_subset_eligible_but_not_attempted() {
        use trust_types::{BasicBlock, BlockId, VerifiableBody};

        let function = DecompiledFunction {
            name: "straight_line".to_string(),
            lifted: Some(VerifiableFunction {
                name: "straight_line".to_string(),
                def_path: "binary::straight_line".to_string(),
                span: SourceSpan::binary_address(0x1000),
                body: VerifiableBody {
                    locals: vec![],
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    }],
                    arg_count: 0,
                    return_ty: Ty::Unit,
                },
                contracts: vec![],
                preconditions: vec![],
                postconditions: vec![],
                spec: Default::default(),
            }),
            ..Default::default()
        };

        let validated = validated_rust_reconstruction(&[function]);

        assert_eq!(validated.status, ReconstructionValidationStatus::NotAttempted);
        assert_eq!(validated.trust_level, TrustLevel::Exploratory);
        assert_eq!(validated.eligibility.len(), 1);
        assert!(validated.eligibility[0].eligible);
        assert!(validated.eligibility[0].rejections.is_empty());
        assert_eq!(
            validated.validation_records[0].status,
            ReconstructionValidationStatus::NotAttempted
        );
        assert_eq!(validated.validation_records[0].trust_level, TrustLevel::Exploratory);
        assert!(
            validated.validation_records[0]
                .evidence
                .contains(&ReconstructionValidationEvidence::StrictRustSubsetEligible)
        );
        assert!(validated.validation_records[0].evidence.iter().any(|evidence| {
            matches!(
                evidence,
                ReconstructionValidationEvidence::Other(kind)
                    if kind == "compile-back-validation-missing"
            )
        }));
        assert!(validated.validation_records[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("strict subset eligibility is not semantic validation")
        }));
        assert!(validated.validation_records[0].forward.is_none());
        assert!(validated.validation_records[0].reverse.is_none());
    }

    #[test]
    fn strict_subset_candidate_emits_source_and_validation_input_for_primitive_one_block() {
        use trust_types::{BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, VerifiableBody};

        let lifted = VerifiableFunction {
            name: "add_one".to_string(),
            def_path: "binary::add_one".to_string(),
            span: SourceSpan::binary_address(0x1000),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".to_string()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(1)),
                            ),
                            span: SourceSpan::binary_address(0x1000),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: SourceSpan::binary_address(0x1001),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let function = DecompiledFunction {
            name: "add_one".to_string(),
            lifted: Some(lifted.clone()),
            ..Default::default()
        };

        let candidate = strict_rust_subset_candidate(&function);

        assert!(candidate.eligibility.eligible);
        assert_eq!(
            candidate.validation_input.as_ref().map(|input| &input.name),
            Some(&lifted.name)
        );
        let source = candidate.source_text.expect("strict subset source");
        assert!(source.contains("pub fn add_one(x: i32) -> i32"));
        assert!(source.contains("let mut _local2: i32;"));
        assert!(source.contains("_local2 = x + 1;"));
        assert!(source.contains("    _local2"));
    }

    #[test]
    fn compile_back_evidence_is_required_for_validated_rust_status() {
        use trust_types::{BasicBlock, BlockId, VerifiableBody};

        let function = DecompiledFunction {
            name: "unit_return".to_string(),
            lifted: Some(VerifiableFunction {
                name: "unit_return".to_string(),
                def_path: "binary::unit_return".to_string(),
                span: SourceSpan::binary_address(0x1000),
                body: VerifiableBody {
                    locals: vec![],
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    }],
                    arg_count: 0,
                    return_ty: Ty::Unit,
                },
                contracts: vec![],
                preconditions: vec![],
                postconditions: vec![],
                spec: Default::default(),
            }),
            ..Default::default()
        };
        let candidate = strict_rust_subset_candidate(&function);

        let missing =
            strict_rust_compile_back_validation(&candidate, RustCompileBackEvidence::Missing);
        assert_eq!(missing.status, ReconstructionValidationStatus::NotAttempted);
        assert_eq!(missing.trust_level, TrustLevel::Exploratory);
        assert!(missing.forward.is_none());
        assert!(missing.reverse.is_none());
        assert!(missing.evidence.iter().any(|evidence| {
            matches!(
                evidence,
                ReconstructionValidationEvidence::Other(kind)
                    if kind == "compile-back-validation-missing"
            )
        }));

        let partial = strict_rust_compile_back_validation(
            &candidate,
            RustCompileBackEvidence::ValidatedPartial { proof_certificates: 0 },
        );
        assert_eq!(partial.status, ReconstructionValidationStatus::Validated);
        assert_eq!(partial.trust_level, TrustLevel::Partial);
        assert!(partial.forward.is_some());
        assert!(partial.reverse.is_some());

        let proof_without_certificate = strict_rust_compile_back_validation(
            &candidate,
            RustCompileBackEvidence::ProofGrade { proof_certificates: 0 },
        );
        assert_eq!(proof_without_certificate.status, ReconstructionValidationStatus::Unknown);
        assert_ne!(proof_without_certificate.trust_level, TrustLevel::ProofGrade);

        let proof_grade = strict_rust_compile_back_validation(
            &candidate,
            RustCompileBackEvidence::ProofGrade { proof_certificates: 1 },
        );
        assert_eq!(proof_grade.status, ReconstructionValidationStatus::Validated);
        assert_eq!(proof_grade.trust_level, TrustLevel::ProofGrade);
    }

    #[test]
    fn strict_subset_candidate_rejects_non_primitive_emission_shape() {
        use trust_types::{BasicBlock, BlockId, LocalDecl, VerifiableBody};

        let function = DecompiledFunction {
            name: "tuple_return".to_string(),
            lifted: Some(VerifiableFunction {
                name: "tuple_return".to_string(),
                def_path: "binary::tuple_return".to_string(),
                span: SourceSpan::binary_address(0x1000),
                body: VerifiableBody {
                    locals: vec![LocalDecl {
                        index: 0,
                        ty: Ty::Tuple(vec![Ty::i32(), Ty::i32()]),
                        name: None,
                    }],
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    }],
                    arg_count: 0,
                    return_ty: Ty::Tuple(vec![Ty::i32(), Ty::i32()]),
                },
                contracts: vec![],
                preconditions: vec![],
                postconditions: vec![],
                spec: Default::default(),
            }),
            ..Default::default()
        };

        let candidate = strict_rust_subset_candidate(&function);

        assert!(!candidate.eligibility.eligible);
        assert!(candidate.source_text.is_none());
        assert!(candidate.validation_input.is_none());
        assert!(candidate.eligibility.rejections.contains(
            &RustReconstructionRejectionKind::Other("strict-subset-emission".to_string())
        ));
        assert!(
            candidate
                .eligibility
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("unsupported non-primitive type"))
        );
    }

    #[test]
    fn validated_rust_path_rejects_non_straight_line_memory_call_and_unsupported() {
        use trust_types::{
            BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, Statement, Terminator,
            VerifiableBody,
        };

        let mut unsupported = UnsupportedLedger::default();
        unsupported.records.push(unsupported_record(
            "trust-lift",
            Some("x86-64"),
            Some(0x1000),
            Some(0x1000),
            "fixture unsupported feature",
        ));
        let function = DecompiledFunction {
            name: "complex".to_string(),
            lifted: Some(VerifiableFunction {
                name: "complex".to_string(),
                def_path: "binary::complex".to_string(),
                span: SourceSpan::binary_address(0x1000),
                body: VerifiableBody {
                    locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
                    blocks: vec![
                        BasicBlock {
                            id: BlockId(0),
                            stmts: vec![Statement::Assign {
                                place: Place::local(0),
                                rvalue: Rvalue::AddressOf(false, Place::local(0)),
                                span: SourceSpan::binary_address(0x1000),
                            }],
                            terminator: Terminator::Call {
                                unwind: UnwindEdge::Unreachable,
                                is_unsafe_sig: false,
                                is_foreign: false,
                                func: "callee".to_string(),
                                args: vec![Operand::Copy(Place::local(0))],
                                dest: Place::local(0),
                                target: Some(BlockId(1)),
                                span: SourceSpan::binary_address(0x1000),
                                atomic: None,
                            },
                        },
                        BasicBlock {
                            id: BlockId(1),
                            stmts: vec![],
                            terminator: Terminator::Return,
                        },
                    ],
                    arg_count: 0,
                    return_ty: Ty::Unit,
                },
                contracts: vec![],
                preconditions: vec![],
                postconditions: vec![],
                spec: Default::default(),
            }),
            unsupported,
            ..Default::default()
        };

        let validated = validated_rust_reconstruction(&[function]);
        let eligibility = &validated.eligibility[0];
        let record = &validated.validation_records[0];

        assert_eq!(validated.status, ReconstructionValidationStatus::Failed);
        assert_eq!(validated.trust_level, TrustLevel::Rejected);
        assert!(!eligibility.eligible);
        assert!(eligibility.rejections.contains(&RustReconstructionRejectionKind::NonStraightLine));
        assert!(eligibility.rejections.contains(&RustReconstructionRejectionKind::MemoryAccess));
        assert!(eligibility.rejections.contains(&RustReconstructionRejectionKind::Call));
        assert!(eligibility.rejections.contains(&RustReconstructionRejectionKind::Unsupported));
        assert_eq!(record.status, ReconstructionValidationStatus::Failed);
        assert_eq!(record.trust_level, TrustLevel::Rejected);
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::RejectedNonStraightLine)
        );
        assert!(record.evidence.contains(&ReconstructionValidationEvidence::RejectedMemoryAccess));
        assert!(record.evidence.contains(&ReconstructionValidationEvidence::RejectedCall));
        assert!(record.evidence.contains(&ReconstructionValidationEvidence::RejectedUnsupported));
    }

    #[test]
    fn trust_ir_outputs_carry_structured_self_validation_records_without_proof_grade() {
        let lifted = synthetic_lifted_binary(&[("trust_ir_a", 0x1000), ("trust_ir_b", 0x2000)]);
        let options = DecompileOptions::default()
            .with_outputs([DecompileOutputKind::TrustIrJson, DecompileOutputKind::TrustIrText]);

        let artifact =
            decompilation_artifact_from_lifted(16, &options, &lifted).expect("synthetic artifact");

        assert_eq!(artifact.reconstruction.validation, ReconstructionValidationStatus::Validated);
        assert_ne!(artifact.reconstruction.trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert!(
            artifact
                .functions
                .iter()
                .all(|function| function.trust_level != TrustLevel::ProofGrade)
        );

        let outputs: Vec<_> = artifact
            .reconstruction
            .outputs
            .iter()
            .filter(|output| output.target == DecompileTarget::TrustIr)
            .collect();
        assert_eq!(outputs.len(), 2);

        for output in outputs {
            assert_eq!(output.validation, ReconstructionValidationStatus::Validated);
            assert_eq!(output.trust_level, TrustLevel::Partial);
            assert_ne!(output.trust_level, TrustLevel::ProofGrade);
            assert_eq!(output.validation_records.len(), 2);
            assert!(
                output.diagnostics.iter().any(|diagnostic| diagnostic.contains("not proof-grade"))
            );

            for record in &output.validation_records {
                assert_eq!(record.target, DecompileTarget::TrustIr);
                assert_eq!(record.candidate, ReconstructionCandidateKind::StructuredTrustIr);
                assert_eq!(record.status, ReconstructionValidationStatus::Validated);
                assert_eq!(record.trust_level, TrustLevel::Partial);
                assert_ne!(record.trust_level, TrustLevel::ProofGrade);
                assert!(
                    record
                        .evidence
                        .contains(&ReconstructionValidationEvidence::TrustIrIdentitySelfCheck)
                );
                assert!(
                    record.evidence.contains(
                        &ReconstructionValidationEvidence::BidirectionalTrustIrRefinement
                    )
                );
                assert!(
                    record
                        .evidence
                        .contains(&ReconstructionValidationEvidence::NoCheckedProofCertificate)
                );
                assert!(
                    record
                        .evidence
                        .contains(&ReconstructionValidationEvidence::NoBinaryProofObligation)
                );
                assert_eq!(record.lifted_function, record.reconstructed_function);
                assert!(matches!(
                    record.forward.as_ref().map(|direction| direction.direction),
                    Some(ReconstructionValidationDirection::LiftedToOutput)
                ));
                assert!(matches!(
                    record.reverse.as_ref().map(|direction| direction.direction),
                    Some(ReconstructionValidationDirection::OutputToLifted)
                ));
                assert_eq!(
                    record
                        .forward
                        .as_ref()
                        .map_or(usize::MAX, |direction| direction.proof_certificates),
                    0
                );
                assert_eq!(
                    record
                        .reverse
                        .as_ref()
                        .map_or(usize::MAX, |direction| direction.proof_certificates),
                    0
                );
                assert!(
                    record
                        .diagnostics
                        .iter()
                        .any(|diagnostic| diagnostic.contains("not proof-grade"))
                );
            }
        }
    }

    #[test]
    fn trust_ir_json_includes_real_multi_function_module_without_dropping_legacy_fields() {
        let lifted = synthetic_lifted_binary(&[("trust_ir_a", 0x1000), ("trust_ir_b", 0x2000)]);
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);

        let artifact =
            decompilation_artifact_from_lifted(16, &options, &lifted).expect("synthetic artifact");
        let output = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
            .expect("TrustIr JSON output");
        let json: serde_json::Value =
            serde_json::from_str(output.text.as_deref().expect("TrustIr JSON text"))
                .expect("TrustIr JSON should parse");

        assert!(json.get("metadata").is_some(), "legacy metadata field should remain");
        assert_eq!(json["functions"].as_array().expect("legacy functions").len(), 2);
        assert_eq!(json["call_graph"]["nodes"].as_array().expect("legacy call graph").len(), 2);

        let module = json.get("module").expect("serialized trust_ir::Module");
        assert_eq!(module["name"], "binary");
        let module_functions = module["functions"].as_array().expect("module functions");
        assert_eq!(module_functions.len(), 2);
        assert_eq!(module_functions[0]["name"], "trust_ir_a");
        assert_eq!(module_functions[1]["name"], "trust_ir_b");
        assert_eq!(module["func_types"].as_array().expect("module function types").len(), 2);
    }

    #[test]
    fn rust_skeleton_stays_text_only_when_trust_ir_output_self_validates() {
        let lifted = synthetic_lifted_binary(&[("mixed", 0x1000)]);
        let options = DecompileOptions::default()
            .with_outputs([DecompileOutputKind::TrustIrText, DecompileOutputKind::RustSkeleton]);

        let artifact =
            decompilation_artifact_from_lifted(8, &options, &lifted).expect("synthetic artifact");

        assert_eq!(artifact.trust_level, TrustLevel::Exploratory);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);

        let trust_ir = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::TrustIr)
            .expect("TrustIr output");
        assert_eq!(trust_ir.validation, ReconstructionValidationStatus::Validated);
        assert_eq!(trust_ir.trust_level, TrustLevel::Partial);
        assert_eq!(
            trust_ir.validation_records[0].candidate,
            ReconstructionCandidateKind::StructuredTrustIr
        );

        let rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust skeleton output");
        assert_eq!(rust.validation, ReconstructionValidationStatus::NotAttempted);
        assert_eq!(rust.trust_level, TrustLevel::Exploratory);
        assert_eq!(rust.validation_records.len(), 1);
        assert_eq!(rust.validation_records[0].candidate, ReconstructionCandidateKind::TextOnly);
        assert_eq!(rust.validation_records[0].trust_level, TrustLevel::Exploratory);
        assert!(rust.validation_records[0].forward.is_none());
        assert!(rust.validation_records[0].reverse.is_none());
    }

    fn assert_binary_address_only_provenance(
        artifact: &DecompilationArtifact,
        expected_detail: &str,
    ) {
        assert!(artifact.assumptions.iter().any(|assumption| {
            assumption.description.contains("binary-address-only")
                && assumption.description.contains(expected_detail)
        }));
        assert!(artifact.reconstruction.assumptions.iter().any(|assumption| {
            assumption.description.contains("binary-address-only")
                && assumption.description.contains(expected_detail)
        }));
        assert!(artifact.reconstruction.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("binary-address-only") && diagnostic.contains(expected_detail)
        }));

        for output in &artifact.reconstruction.outputs {
            assert!(output.assumptions.iter().any(|assumption| {
                assumption.description.contains("binary-address-only")
                    && assumption.description.contains(expected_detail)
            }));
            assert!(output.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("binary-address-only") && diagnostic.contains(expected_detail)
            }));
        }

        for function in &artifact.functions {
            assert!(function.assumptions.iter().any(|assumption| {
                assumption.description.contains("binary-address-only")
                    && assumption.description.contains(expected_detail)
            }));
            assert!(function.origin.as_ref().expect("origin").span().is_binary());
            assert!(function.lifted.as_ref().expect("lifted function").span.is_binary());
        }
    }

    #[test]
    fn absent_source_provenance_keeps_diagnostics_binary_address_only() {
        let lifted = synthetic_lifted_binary(&[("binary_only", 0x401000)]);
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);

        let artifact =
            decompilation_artifact_from_lifted(8, &options, &lifted).expect("synthetic artifact");
        let function = &artifact.functions[0];
        let origin_span = function.origin.as_ref().expect("origin").span();

        assert!(origin_span.is_binary());
        assert_eq!(origin_span.binary_address_value(), Some(0x401000));
        assert!(function.lifted.as_ref().expect("lifted function").span.is_binary());
        assert!(
            artifact
                .assumptions
                .iter()
                .any(|assumption| assumption.description.contains("binary-address-only"))
        );
        assert_eq!(artifact.source_provenance.status, "unavailable");
        assert_eq!(artifact.source_provenance.exact_mapping_count, 0);
        assert_eq!(artifact.source_provenance.ambiguous_mapping_count, 0);
        assert!(!artifact.source_provenance.source_backpropagation_allowed);
        assert_binary_address_only_provenance(&artifact, "unavailable");
        assert_eq!(artifact.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
    }

    #[test]
    fn ambiguous_source_provenance_stays_binary_address_only() {
        let lifted = synthetic_lifted_binary_with_source_provenance(
            &[("ambiguous", 0x401000)],
            trust_lift::LiftedSourceProvenance {
                status: trust_lift::LiftedSourceProvenanceStatus::Ambiguous,
                exact_mapping_count: 0,
                ambiguous_mapping_count: 1,
                diagnostics: vec![
                    "ambiguous debug/source rows were withheld; diagnostics remain binary-address-only"
                        .to_string(),
                ],
            },
            &[(0x401000, "src/ambiguous.rs", 11, 3)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);

        let artifact =
            decompilation_artifact_from_lifted(8, &options, &lifted).expect("synthetic artifact");
        let function = &artifact.functions[0];

        assert!(function.origin.as_ref().expect("origin").span().is_binary());
        assert!(function.lifted.as_ref().expect("lifted function").span.is_binary());
        assert_eq!(artifact.source_provenance.status, "ambiguous");
        assert_eq!(artifact.source_provenance.exact_mapping_count, 0);
        assert_eq!(artifact.source_provenance.ambiguous_mapping_count, 1);
        assert!(!artifact.source_provenance.source_backpropagation_allowed);
        assert_binary_address_only_provenance(&artifact, "ambiguous");
    }

    #[test]
    fn exact_status_without_mappings_keeps_source_backpropagation_closed() {
        let lifted = synthetic_lifted_binary_with_source_provenance(
            &[("exact_status_only", 0x401000)],
            trust_lift::LiftedSourceProvenance {
                status: trust_lift::LiftedSourceProvenanceStatus::Exact,
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: Vec::new(),
            },
            &[],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);

        let artifact =
            decompilation_artifact_from_lifted(8, &options, &lifted).expect("synthetic artifact");

        assert_eq!(artifact.source_provenance.status, "exact");
        assert_eq!(artifact.source_provenance.exact_mapping_count, 0);
        assert_eq!(artifact.source_provenance.ambiguous_mapping_count, 0);
        assert!(!artifact.source_provenance.source_backpropagation_allowed);
        assert!(!artifact.source_provenance.effective_source_backpropagation_allowed());
        assert!(artifact.functions[0].origin.as_ref().expect("origin").span().is_binary());
    }

    #[test]
    fn unsupported_source_provenance_stays_binary_address_only() {
        let lifted = synthetic_lifted_binary_with_source_provenance(
            &[("unsupported_debug", 0x401000)],
            trust_lift::LiftedSourceProvenance {
                status: trust_lift::LiftedSourceProvenanceStatus::Unsupported,
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "debug/source provenance could not be parsed safely; diagnostics remain binary-address-only"
                        .to_string(),
                ],
            },
            &[(0x401000, "src/unsupported.rs", 19, 7)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);

        let artifact =
            decompilation_artifact_from_lifted(8, &options, &lifted).expect("synthetic artifact");
        let function = &artifact.functions[0];

        assert!(function.origin.as_ref().expect("origin").span().is_binary());
        assert!(function.lifted.as_ref().expect("lifted function").span.is_binary());
        assert_eq!(artifact.source_provenance.status, "unsupported");
        assert!(!artifact.source_provenance.source_backpropagation_allowed);
        assert_binary_address_only_provenance(&artifact, "could not be parsed safely");
    }

    #[test]
    fn exact_source_provenance_is_exposed_without_heuristic_guessing() {
        let lifted = synthetic_lifted_binary_with_source(
            &[("source_mapped", 0x401000), ("unmapped", 0x402000)],
            &[(0x401000, "src/lib.rs", 27, 5)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);

        let artifact =
            decompilation_artifact_from_lifted(8, &options, &lifted).expect("synthetic artifact");
        let function = &artifact.functions[0];
        let origin_span = function.origin.as_ref().expect("origin").span();

        assert!(!origin_span.is_binary());
        assert_eq!(origin_span.file, "src/lib.rs");
        assert_eq!(origin_span.line_start, 27);
        assert_eq!(origin_span.col_start, 5);
        assert_eq!(function.lifted.as_ref().expect("lifted function").span.file, "src/lib.rs");
        assert_eq!(artifact.source_provenance.status, "exact");
        assert_eq!(artifact.source_provenance.exact_mapping_count, 1);
        assert_eq!(artifact.source_provenance.ambiguous_mapping_count, 0);
        assert!(!artifact.source_provenance.source_backpropagation_allowed);
        assert!(!artifact.source_provenance.effective_source_backpropagation_allowed());
        assert!(artifact.source_provenance.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("source-backpropagation-blocker=partial exact source mapping")
        }));
        assert!(artifact.unsupported.records.iter().any(|record| {
            record.stage == SOURCE_PROVENANCE_GATE_STAGE
                && record.feature.contains("partial exact source mapping")
        }));
        assert!(artifact.assumptions.is_empty());
        assert!(artifact.reconstruction.assumptions.is_empty());
        assert!(artifact.reconstruction.diagnostics.iter().all(|diagnostic| {
            !diagnostic.contains("binary-address-only") && !diagnostic.contains("debug/source")
        }));

        let unmapped = &artifact.functions[1];
        let unmapped_origin = unmapped.origin.as_ref().expect("origin").span();
        assert!(unmapped_origin.is_binary());
        assert_eq!(unmapped_origin.binary_address_value(), Some(0x402000));
        assert!(unmapped.lifted.as_ref().expect("lifted function").span.is_binary());
        assert!(unmapped.assumptions.is_empty());

        let output = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::TrustIr)
            .expect("TrustIr output");
        assert!(output.assumptions.is_empty());
        assert!(
            output.diagnostics.iter().all(|diagnostic| !diagnostic.contains("binary-address-only"))
        );
    }

    #[test]
    fn exact_source_provenance_effective_gate_is_serialized_and_fail_closed() {
        use trust_types::{BinarySourceProvenanceDiagnosticKind, ProofStrength, VcKind};

        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);
        let results = vec![(
            synthetic_vc("mapped", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];

        let partial_lifted = synthetic_lifted_binary_with_source(
            &[("mapped", 0x401000), ("unmapped", 0x402000)],
            &[(0x401000, "src/mapped.rs", 3, 1)],
        );
        let mut partial = decompilation_artifact_from_lifted_with_verification_results(
            16,
            &options,
            &partial_lifted,
            &results,
        )
        .expect("partial exact source map should still produce an artifact");
        install_test_binary_artifact_digest_metadata(&mut partial);
        mark_dispatches_checked_and_replayed(&mut partial.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut partial.functions[0].verification.solver_dispatch,
        );

        assert_source_backpropagation_fail_closed(
            &mut partial,
            "partial exact source mapping",
            BinarySourceProvenanceDiagnosticKind::SourceBackpropagationRejected,
        );

        let synthetic_lifted = synthetic_lifted_binary_with_source_provenance(
            &[("mapped", 0x401000)],
            trust_lift::LiftedSourceProvenance {
                status: trust_lift::LiftedSourceProvenanceStatus::Exact,
                exact_mapping_count: 1,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "synthetic source provenance fixture must not be accepted for source backprop"
                        .to_string(),
                ],
            },
            &[(0x401000, "src/synthetic/generated.rs", 5, 1)],
        );
        let mut synthetic = decompilation_artifact_from_lifted_with_verification_results(
            8,
            &options,
            &synthetic_lifted,
            &results,
        )
        .expect("synthetic exact source map should still produce an artifact");
        install_test_binary_artifact_digest_metadata(&mut synthetic);
        mark_dispatches_checked_and_replayed(&mut synthetic.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut synthetic.functions[0].verification.solver_dispatch,
        );

        assert_source_backpropagation_fail_closed(
            &mut synthetic,
            "synthetic source mapping marker",
            BinarySourceProvenanceDiagnosticKind::SourceBackpropagationRejected,
        );
    }

    #[test]
    fn partial_per_instruction_source_mapping_stays_fail_closed_for_backprop_and_release() {
        use trust_lift::cfg::ProofAnnotation;
        use trust_types::{BinarySourceProvenanceDiagnosticKind, ProofStrength, VcKind};

        const ENTRY: u64 = 0x401000;
        const NEXT: u64 = ENTRY + 1;

        let mut lifted = synthetic_lifted_binary_with_source(
            &[("two_instruction_fn", ENTRY)],
            &[(ENTRY, "src/two_instruction.rs", 10, 3)],
        );
        lifted.functions[0].annotations = vec![
            ProofAnnotation {
                block_id: 0,
                stmt_index: 0,
                binary_offset: ENTRY,
                encoding: 0x90,
                instruction_size: 1,
                instruction_bytes: vec![0x90],
            },
            ProofAnnotation {
                block_id: 0,
                stmt_index: 1,
                binary_offset: NEXT,
                encoding: 0x90,
                instruction_size: 1,
                instruction_bytes: vec![0x90],
            },
        ];
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);
        let results = vec![(
            synthetic_vc("two_instruction_fn", ENTRY, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];

        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            2, &options, &lifted, &results,
        )
        .expect("partially mapped per-instruction source fixture should produce an artifact");
        install_test_binary_artifact_digest_metadata(&mut artifact);
        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );

        let function = &artifact.functions[0];
        assert_eq!(
            function.origin.as_ref().expect("function entry origin").span().file,
            "src/two_instruction.rs"
        );
        assert_eq!(function.instruction_provenance.len(), 2);
        assert_eq!(
            function.instruction_provenance[0].source.as_ref().expect("entry source").file,
            "src/two_instruction.rs"
        );
        assert!(
            function.instruction_provenance[1]
                .source
                .as_ref()
                .expect("unmapped instruction source")
                .is_binary()
        );
        assert!(binary_dispatch_has_proof_grade_evidence(
            &artifact.verification.solver_dispatch[0]
        ));
        assert!(dispatch_has_accepted_source_provenance(
            &artifact.verification.solver_dispatch[0],
            &artifact.functions,
            &artifact.binary,
        ));

        assert_source_backpropagation_fail_closed(
            &mut artifact,
            "lifted instruction address(es) lack exact source spans",
            BinarySourceProvenanceDiagnosticKind::SourceBackpropagationRejected,
        );
    }

    #[test]
    fn synthetic_vc_results_populate_binary_solver_dispatch_summaries() {
        use trust_types::{BinaryVerificationStatus, Formula, ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary(&[("foo", 0x1000), ("bar", 0x2000)]);
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![
            (
                synthetic_vc("binary::foo", 0x1000, VcKind::DivisionByZero),
                VerificationResult::Proved {
                    solver: "ay".into(),
                    time_ms: 4,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            ),
            (
                synthetic_vc(
                    "foo",
                    0x1000,
                    VcKind::Assertion { message: "binary trap unreachable".to_string() },
                ),
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 7,
                    counterexample: None,
                },
            ),
            (
                synthetic_vc("bar", 0x2000, VcKind::IndexOutOfBounds),
                VerificationResult::Unknown {
                    solver: "ay".into(),
                    time_ms: 11,
                    reason: "incomplete bitvector model".to_string(),
                },
            ),
            (
                synthetic_vc("bar", 0x2000, VcKind::Assertion { message: "timeout".to_string() }),
                VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 30 },
            ),
        ];

        let artifact = decompilation_artifact_from_lifted_with_verification_results(
            16, &options, &lifted, &results,
        )
        .expect("synthetic lifted binary should produce an artifact");

        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Mixed);
        assert_eq!(artifact.verification.total_vcs, 4);
        assert_eq!(artifact.verification.proved, 1);
        assert_eq!(artifact.verification.failed, 1);
        assert_eq!(artifact.verification.unknown, 1);
        assert_eq!(artifact.verification.timeout, 1);
        assert_eq!(artifact.verification.replay, ReplayStatus::NotAttempted);
        assert_eq!(artifact.verification.trust_level, TrustLevel::Partial);

        let sat_dispatch = &artifact.verification.solver_dispatch[1];
        assert_eq!(sat_dispatch.status, SolverDispatchStatus::Sat);
        assert_eq!(sat_dispatch.query_semantics, SolverQuerySemantics::SatIsCounterexample);
        assert_eq!(sat_dispatch.replay, ReplayStatus::NotAttempted);
        assert!(
            sat_dispatch
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("SAT is a counterexample"))
        );
        assert_eq!(
            sat_dispatch.origin.as_ref().and_then(|origin| origin.function_entry),
            Some(0x1000)
        );

        let foo = artifact
            .functions
            .iter()
            .find(|function| function.name == "foo")
            .expect("foo function summary");
        assert_eq!(foo.verification.status, BinaryVerificationStatus::Mixed);
        assert_eq!(foo.verification.total_vcs, 2);
        assert_eq!(foo.verification.proved, 1);
        assert_eq!(foo.verification.failed, 1);
        assert_eq!(foo.verification.replay, ReplayStatus::NotAttempted);

        let bar = artifact
            .functions
            .iter()
            .find(|function| function.name == "bar")
            .expect("bar function summary");
        assert_eq!(bar.verification.status, BinaryVerificationStatus::Mixed);
        assert_eq!(bar.verification.total_vcs, 2);
        assert_eq!(bar.verification.unknown, 1);
        assert_eq!(bar.verification.timeout, 1);
        assert_eq!(bar.verification.solver_dispatch[1].timeout_ms, Some(30));

        assert_eq!(results[0].0.formula, Formula::Bool(true));
    }

    #[test]
    fn proved_binary_solver_results_do_not_raise_proof_grade() {
        use trust_types::{BinaryVerificationStatus, Formula, ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];

        let artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic proved artifact");

        assert_ne!(artifact.verification.status, BinaryVerificationStatus::Rejected);
        assert_eq!(artifact.verification.proved, 1);
        assert_eq!(artifact.verification.failed, 0);
        assert_eq!(artifact.verification.replay, ReplayStatus::NotAttempted);
        assert_ne!(artifact.verification.trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.functions[0].verification.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.verification.solver_dispatch[0].status, SolverDispatchStatus::Unsat);
        assert_eq!(
            artifact.verification.solver_dispatch[0].query_semantics,
            SolverQuerySemantics::SatIsCounterexample
        );
        assert_eq!(results[0].0.formula, Formula::Bool(true));
    }

    #[test]
    fn raw_solver_certificate_bytes_do_not_raise_proof_grade_without_checked_status() {
        use trust_types::{BinaryVerificationStatus, Formula, ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"unchecked solver proof bytes".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];

        let artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic proved artifact");

        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Proved);
        assert_eq!(artifact.verification.replay, ReplayStatus::NotAttempted);
        assert_eq!(
            artifact.verification.solver_dispatch[0].certificate,
            ProofCertificateStatus::Present {
                format: "solver-proof-bytes".to_string(),
                sha256: None,
                artifact_path: None,
            }
        );
        assert_eq!(artifact.verification.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert!(artifact.verification.solver_dispatch[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("proof-grade requires checked certificate evidence")
        }));
        assert_eq!(results[0].0.formula, Formula::Bool(true));
    }

    #[test]
    fn checked_certificate_and_full_replay_promote_binary_vcs_to_proof_grade() {
        use trust_types::{BinaryVerificationStatus, Formula, ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic proved artifact");

        install_test_binary_artifact_digest_metadata(&mut artifact);
        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );

        assert_eq!(artifact.reconstruction.validation, ReconstructionValidationStatus::Validated);
        assert!(
            source_provenance_allows_artifact_proof_grade(&artifact.source_provenance),
            "{:?}",
            artifact.source_provenance
        );
        assert!(artifact.unsupported.records.is_empty(), "{:?}", artifact.unsupported.records);
        assert!(
            binary_proof_grade_release_gate_accepts(&artifact.verification),
            "{:?}",
            artifact.verification.solver_dispatch
        );
        assert!(
            reconstruction_allows_artifact_proof_grade(&artifact.reconstruction),
            "{:?}",
            artifact.reconstruction
        );
        assert!(apply_binary_proof_grade_release_gate(&mut artifact));

        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Proved);
        assert_eq!(artifact.verification.trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.verification.replay, ReplayStatus::Replayed);
        let ProofCertificateStatus::Checked { sha256, .. } =
            &artifact.verification.proof_certificate
        else {
            panic!("proof-grade aggregate certificate should be checked");
        };
        assert!(sha256.as_deref().is_some_and(is_canonical_sha256_hex));
        assert_eq!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.functions[0].verification.trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);
        assert_eq!(results[0].0.formula, Formula::Bool(true));
    }

    #[test]
    fn digestless_checked_certificate_does_not_count_as_checked_release_evidence() {
        use trust_types::{BinaryVerificationStatus, ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic proved artifact");

        install_test_binary_artifact_digest_metadata(&mut artifact);
        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );
        for dispatch in artifact
            .verification
            .solver_dispatch
            .iter_mut()
            .chain(artifact.functions[0].verification.solver_dispatch.iter_mut())
        {
            dispatch.certificate = ProofCertificateStatus::Checked {
                checker: "ay-cert-check".to_string(),
                format: "lfsc".to_string(),
                sha256: None,
            };
        }

        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Proved);
        assert!(!binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(matches!(
            aggregate_checked_certificate_status(&artifact.verification.solver_dispatch),
            ProofCertificateStatus::Unavailable { .. }
        ));
        assert!(!apply_binary_proof_grade_release_gate(&mut artifact));
        assert_eq!(artifact.verification.trust_level, TrustLevel::Partial);
        assert!(matches!(
            artifact.verification.proof_certificate,
            ProofCertificateStatus::Unavailable { .. }
        ));
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].verification.trust_level, TrustLevel::ProofGrade);
    }

    #[test]
    fn minimal_synthetic_binary_release_gate_accepts_complete_proof_grade_evidence() {
        use trust_types::{BinaryVerificationStatus, ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::Assertion { message: "proved".into() }),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("minimal synthetic binary fixture should decompile");

        install_test_binary_artifact_digest_metadata(&mut artifact);
        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );

        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Proved);
        assert!(artifact.unsupported.records.is_empty(), "{:?}", artifact.unsupported.records);
        assert!(artifact.functions[0].unsupported.records.is_empty());
        assert!(
            binary_artifact_metadata_identity_allows_proof_grade(&artifact.binary),
            "{:?}",
            artifact.binary.digest_identity_blockers()
        );
        assert!(source_provenance_allows_artifact_proof_grade(&artifact.source_provenance));
        assert!(artifact_source_provenance_allows_binary_proof_grade(&artifact));
        assert!(binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(binary_proof_grade_release_gate_accepts(&artifact.functions[0].verification));
        assert!(reconstruction_allows_binary_proof_grade(
            &artifact.reconstruction,
            &artifact.binary
        ));
        assert!(artifact.reconstruction.outputs.iter().all(|output| {
            output.target_validation_blockers.is_empty()
                && output.validation == ReconstructionValidationStatus::Validated
        }));

        assert!(apply_binary_proof_grade_release_gate(&mut artifact));
        assert_eq!(artifact.verification.trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.functions[0].verification.trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);
        assert!(artifact.source_provenance.source_backpropagation_allowed);
        assert!(artifact.source_provenance.effective_source_backpropagation_allowed());

        let json = trust_ir_json_output_json(&artifact);
        assert_eq!(json["source_provenance"]["source_backpropagation_allowed"], true);
        assert_eq!(json["source_provenance"]["effective_source_backpropagation_allowed"], true);
        let bridge = trust_ir_checked_certificate_bridge_json(&artifact);
        assert_eq!(bridge["proof_grade_closed"], true);
        assert_eq!(bridge["release_gate"]["accepted"], false);
        assert_eq!(bridge["release_gate"]["blockers"], serde_json::json!([]));
        assert_eq!(bridge["release_gate"]["unsupported_ledger_empty"], true);
        assert_eq!(bridge["release_gate"]["checked_certificates_accepted"], true);
        assert_eq!(bridge["release_gate"]["replay_accepted"], true);
        assert_eq!(bridge["release_gate"]["source_provenance_accepted"], true);
        assert_eq!(bridge["release_gate"]["binary_artifact_identity_accepted"], true);
        assert_eq!(bridge["release_gate"]["target_reconstruction_accepted"], true);
        assert_eq!(bridge["release_gate"]["production_boundary_accepted"], false);
        assert!(
            bridge["release_gate"]["production_boundary_blockers"]
                .as_array()
                .expect("production boundary blockers")
                .iter()
                .any(|blocker| blocker == "parser_identity_not_production")
        );
        assert_eq!(bridge["dispatches"][0]["proof_grade_eligible"], true);
    }

    #[test]
    fn source_backpropagation_authority_requires_complete_binary_rewrite_inputs() {
        use trust_types::{BinaryTypeFact, Formula, ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::Assertion { message: "proved".into() }),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut baseline = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("minimal synthetic binary fixture should decompile");

        install_test_binary_artifact_digest_metadata(&mut baseline);
        mark_dispatches_checked_and_replayed(&mut baseline.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut baseline.functions[0].verification.solver_dispatch,
        );

        assert!(source_provenance_allows_artifact_proof_grade(&baseline.source_provenance));
        assert!(!baseline.source_provenance.source_backpropagation_allowed);
        assert!(apply_binary_proof_grade_release_gate(&mut baseline));
        assert!(baseline.source_provenance.source_backpropagation_allowed);

        let mut binary_address_only_type_fact = baseline.clone();
        let mut type_fact_origin =
            binary_address_only_type_fact.functions[0].origin.clone().expect("function origin");
        type_fact_origin.source =
            Some(SourceSpan::binary_address(type_fact_origin.instruction_address));
        binary_address_only_type_fact.type_facts.push(BinaryTypeFact {
            subject: BinaryFactSubject::Parameter { function: "proved_fn".to_string(), index: 0 },
            recovered_ty: Some(Ty::u64()),
            origin: Some(type_fact_origin),
            evidence: BinaryFactEvidence::DebugInfo,
            confidence: BinaryFactConfidence::Validated,
            ..Default::default()
        });
        assert!(
            binary_address_only_type_fact
                .type_fact_source_backpropagation_blockers()
                .iter()
                .any(|blocker| blocker.contains("binary-address-only"))
        );
        let _ = apply_binary_proof_grade_release_gate(&mut binary_address_only_type_fact);
        assert_source_rewrite_authority_closed(
            &binary_address_only_type_fact,
            "type fact source ownership",
        );

        let mut missing_decompile_digest_identity = baseline.clone();
        missing_decompile_digest_identity.binary.root_artifact_digest = None;
        let missing_decompile_digest_identity = assert_binary_release_gate_closed(
            missing_decompile_digest_identity,
            "decompile artifact digest identity",
        );
        assert_source_rewrite_authority_closed(
            &missing_decompile_digest_identity,
            "decompile artifact digest identity",
        );

        let mut missing_decompile_metadata_identity = baseline.clone();
        missing_decompile_metadata_identity.binary.build_id = None;
        let missing_decompile_metadata_identity = assert_binary_release_gate_closed(
            missing_decompile_metadata_identity,
            "decompile artifact metadata identity",
        );
        assert_source_rewrite_authority_closed(
            &missing_decompile_metadata_identity,
            "decompile artifact metadata identity",
        );

        let mut missing_exact_source_status = baseline.clone();
        missing_exact_source_status.source_provenance.status = "ambiguous".to_string();
        missing_exact_source_status.source_provenance.exact_mapping_count = 0;
        missing_exact_source_status.source_provenance.ambiguous_mapping_count = 1;
        let missing_exact_source_status =
            assert_binary_release_gate_closed(missing_exact_source_status, "exact source status");
        assert!(!missing_exact_source_status.source_provenance.source_backpropagation_allowed);
        assert!(
            !missing_exact_source_status
                .source_provenance
                .effective_source_backpropagation_allowed()
        );
        assert!(
            missing_exact_source_status
                .source_provenance
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.starts_with(SOURCE_REWRITE_AUTHORITY_BLOCKER_PREFIX)
                    && diagnostic.contains("exact source ownership"))
        );

        let mut missing_certificate_identity = baseline.clone();
        for dispatch in missing_certificate_identity.verification.solver_dispatch.iter_mut().chain(
            missing_certificate_identity.functions[0].verification.solver_dispatch.iter_mut(),
        ) {
            dispatch.certificate = ProofCertificateStatus::Checked {
                checker: "ay-cert-check".to_string(),
                format: "lfsc".to_string(),
                sha256: None,
            };
        }
        let missing_certificate_identity = assert_binary_release_gate_closed(
            missing_certificate_identity,
            "certificate digest identity",
        );
        assert_source_rewrite_authority_closed(
            &missing_certificate_identity,
            "checked certificate identity",
        );

        let mut missing_replay_status_identity = baseline.clone();
        for dispatch in
            missing_replay_status_identity.verification.solver_dispatch.iter_mut().chain(
                missing_replay_status_identity.functions[0].verification.solver_dispatch.iter_mut(),
            )
        {
            dispatch.replay = ReplayStatus::NotAttempted;
        }
        let missing_replay_status_identity = assert_binary_release_gate_closed(
            missing_replay_status_identity,
            "exact replay identity",
        );
        assert_source_rewrite_authority_closed(
            &missing_replay_status_identity,
            "replay byte/range identity",
        );

        let mut missing_replay_digest_identity = baseline.clone();
        for dispatch in
            missing_replay_digest_identity.verification.solver_dispatch.iter_mut().chain(
                missing_replay_digest_identity.functions[0].verification.solver_dispatch.iter_mut(),
            )
        {
            dispatch
                .binary_artifact_digest_identity
                .as_mut()
                .and_then(|identity| identity.selected_image.as_mut())
                .expect("selected image identity")
                .file_size += 1;
        }
        let missing_replay_digest_identity = assert_binary_release_gate_closed(
            missing_replay_digest_identity,
            "replay byte/range identity",
        );
        assert_source_rewrite_authority_closed(
            &missing_replay_digest_identity,
            "replay byte/range identity",
        );

        let mut missing_reconstruction_digest_identity = baseline.clone();
        for output in &mut missing_reconstruction_digest_identity.reconstruction.outputs {
            output.assumptions.retain(|assumption| {
                assumption.stage != RECONSTRUCTION_OUTPUT_BINARY_ARTIFACT_DIGEST_IDENTITY_STAGE
            });
        }
        let missing_reconstruction_digest_identity = assert_binary_release_gate_closed(
            missing_reconstruction_digest_identity,
            "reconstruction output binary artifact digest identity",
        );
        assert_source_rewrite_authority_closed(
            &missing_reconstruction_digest_identity,
            "reconstruction binary artifact identity",
        );

        let mut missing_target_consumer = baseline.clone();
        for output in &mut missing_target_consumer.reconstruction.outputs {
            output
                .diagnostics
                .retain(|diagnostic| !target_consumer_acceptance_diagnostic(diagnostic));
        }
        let missing_target_consumer = assert_binary_release_gate_closed(
            missing_target_consumer,
            "target consumer acceptance",
        );
        assert_source_rewrite_authority_closed(
            &missing_target_consumer,
            "target proof consumer acceptance",
        );

        let mut missing_formula_consumer = baseline.clone();
        let target_output = missing_formula_consumer
            .reconstruction
            .outputs
            .iter_mut()
            .find(|output| output.target == missing_formula_consumer.reconstruction.target)
            .expect("target output");
        target_output
            .diagnostics
            .retain(|diagnostic| !symbolic_formula_consumer_diagnostic(diagnostic));
        target_output.diagnostics.push(
            "target-consumer=accepted; target proof consumer accepted checked-certificate, replay, source provenance, and reconstruction evidence"
                .to_string(),
        );
        target_output.preserved_symbolic_formulas.push(PreservedSymbolicFormula {
            target: DecompileTarget::TrustIr,
            function: Some("proved_fn".to_string()),
            block: Some(0),
            statement_index: Some(0),
            location: "bb0[0]".to_string(),
            formula: Formula::Bool(true),
        });
        assert!(reconstruction_target_consumer_accepted_by_proof_model(
            &missing_formula_consumer.reconstruction
        ));
        assert!(!reconstruction_symbolic_formulas_consumed_by_proof_model(
            &missing_formula_consumer.reconstruction
        ));
        let missing_formula_consumer = assert_binary_release_gate_closed(
            missing_formula_consumer,
            "symbolic formula consumer",
        );
        assert_source_rewrite_authority_closed(
            &missing_formula_consumer,
            "symbolic formula consumer acceptance",
        );

        let mut unvalidated_reconstruction = baseline;
        unvalidated_reconstruction.reconstruction.validation =
            ReconstructionValidationStatus::NotAttempted;
        for output in &mut unvalidated_reconstruction.reconstruction.outputs {
            output.validation = ReconstructionValidationStatus::NotAttempted;
        }
        let unvalidated_reconstruction = assert_binary_release_gate_closed(
            unvalidated_reconstruction,
            "reconstruction validation",
        );
        assert_source_rewrite_authority_closed(
            &unvalidated_reconstruction,
            "reconstruction validation",
        );
    }

    #[test]
    fn release_gate_requires_explicit_target_consumer_acceptance() {
        use trust_types::{ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::Assertion { message: "proved".into() }),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("minimal synthetic binary fixture should decompile");

        install_test_binary_artifact_digest_metadata(&mut artifact);
        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );
        for output in &mut artifact.reconstruction.outputs {
            output
                .diagnostics
                .retain(|diagnostic| !target_consumer_acceptance_diagnostic(diagnostic));
        }

        assert!(binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(artifact_source_provenance_allows_binary_proof_grade(&artifact));
        assert!(!reconstruction_allows_artifact_proof_grade(&artifact.reconstruction));
        let artifact = assert_binary_release_gate_closed(artifact, "target consumer acceptance");
        let bridge = trust_ir_checked_certificate_bridge_json(&artifact);
        assert_eq!(bridge["release_gate"]["target_reconstruction_accepted"], false);
        assert_eq!(
            bridge["release_gate"]["blockers"],
            serde_json::json!(["target_reconstruction_not_accepted"])
        );
    }

    #[test]
    fn release_gate_replay_blocker_names_symex_source_backprop_replay_ready_identity() {
        use trust_types::{ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::Assertion { message: "proved".into() }),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("minimal synthetic binary fixture should decompile");

        install_test_binary_artifact_digest_metadata(&mut artifact);
        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );
        for dispatch in artifact
            .verification
            .solver_dispatch
            .iter_mut()
            .chain(artifact.functions[0].verification.solver_dispatch.iter_mut())
        {
            dispatch.replay = ReplayStatus::NotAttempted;
        }

        let artifact = assert_binary_release_gate_closed(
            artifact,
            "symex source_backprop_replay_ready exact replay identity",
        );
        let bridge = trust_ir_checked_certificate_bridge_json(&artifact);
        let release_gate = &bridge["release_gate"];
        let blockers =
            release_gate["replay_identity_blockers"].as_array().expect("replay identity blockers");

        assert_eq!(release_gate["accepted"], false);
        assert_eq!(release_gate["replay_accepted"], false);
        assert!(
            release_gate["blockers"]
                .as_array()
                .expect("release gate blockers")
                .iter()
                .any(|blocker| blocker == "replay_not_accepted"),
            "{release_gate:?}"
        );
        assert!(
            blockers.iter().any(|blocker| {
                let blocker = blocker.as_str().expect("blocker text");
                blocker.contains("source_backprop_replay_ready")
                    && blocker.contains("matched instruction trace")
                    && blocker.contains("matched root artifact digest")
                    && blocker.contains("matched selected-image digest/range")
                    && blocker.contains("explicit branch/call/return capability evidence")
                    && blocker.contains("no unchecked boundary evidence")
            }),
            "{blockers:?}"
        );
        assert!(
            bridge["diagnostics"].as_array().expect("bridge diagnostics").iter().any(
                |diagnostic| diagnostic
                    .as_str()
                    .is_some_and(|text| text.contains("source_backprop_replay_ready"))
            ),
            "{bridge:?}"
        );
    }

    #[test]
    fn release_gate_marks_synthetic_positive_fixture_as_non_production_boundary() {
        use trust_types::{BinaryVerificationStatus, ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::Assertion { message: "proved".into() }),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("minimal synthetic binary fixture should decompile");

        install_test_binary_artifact_digest_metadata(&mut artifact);
        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );

        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Proved);
        assert!(binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(artifact_source_provenance_allows_binary_proof_grade(&artifact));
        assert!(reconstruction_allows_binary_proof_grade(
            &artifact.reconstruction,
            &artifact.binary
        ));
        assert!(apply_binary_proof_grade_release_gate(&mut artifact));

        let bridge = trust_ir_checked_certificate_bridge_json(&artifact);
        assert_eq!(bridge["release_gate"]["accepted"], false);
        assert_eq!(bridge["release_gate"]["production_boundary_accepted"], false);
        let production_blockers = bridge["release_gate"]["production_boundary_blockers"]
            .as_array()
            .expect("production boundary blockers");
        for blocker in [
            "parser_identity_not_production",
            "checked_certificate_not_production",
            "replay_identity_not_production",
            "source_provenance_not_production",
            "target_consumer_not_production",
        ] {
            assert!(
                production_blockers.iter().any(|entry| entry == blocker),
                "missing production boundary blocker `{blocker}` in {production_blockers:?}"
            );
        }
        assert!(
            bridge["diagnostics"].as_array().expect("bridge diagnostics").iter().any(
                |diagnostic| diagnostic.as_str().is_some_and(|diagnostic| {
                    diagnostic.contains("production proof-grade boundary")
                        && diagnostic.contains("parser_identity_not_production")
                        && diagnostic.contains("target_consumer_not_production")
                })
            ),
            "{:?}",
            bridge["diagnostics"]
        );
    }

    #[test]
    fn release_gate_closes_synthetic_fixture_when_each_production_required_claim_is_removed() {
        use trust_types::{ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::Assertion { message: "proved".into() }),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut baseline = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("minimal synthetic binary fixture should decompile");

        install_test_binary_artifact_digest_metadata(&mut baseline);
        mark_dispatches_checked_and_replayed(&mut baseline.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut baseline.functions[0].verification.solver_dispatch,
        );

        let mut missing_parser_identity = baseline.clone();
        missing_parser_identity.binary.build_id = None;
        let missing_parser_identity =
            assert_binary_release_gate_closed(missing_parser_identity, "parser identity");
        assert_eq!(
            trust_ir_checked_certificate_bridge_json(&missing_parser_identity)["release_gate"]["binary_artifact_identity_accepted"],
            false
        );

        let mut missing_certificate = baseline.clone();
        for dispatch in &mut missing_certificate.verification.solver_dispatch {
            dispatch.certificate = ProofCertificateStatus::Present {
                format: "raw-solver-proof".to_string(),
                sha256: Some("raw-only".to_string()),
                artifact_path: None,
            };
        }
        for dispatch in &mut missing_certificate.functions[0].verification.solver_dispatch {
            dispatch.certificate = ProofCertificateStatus::Present {
                format: "raw-solver-proof".to_string(),
                sha256: Some("raw-only".to_string()),
                artifact_path: None,
            };
        }
        let missing_certificate =
            assert_binary_release_gate_closed(missing_certificate, "checked certificate");
        assert_eq!(
            trust_ir_checked_certificate_bridge_json(&missing_certificate)["release_gate"]["checked_certificates_accepted"],
            false
        );

        let mut missing_replay = baseline.clone();
        for dispatch in &mut missing_replay.verification.solver_dispatch {
            dispatch.replay = ReplayStatus::NotAttempted;
        }
        for dispatch in &mut missing_replay.functions[0].verification.solver_dispatch {
            dispatch.replay = ReplayStatus::NotAttempted;
        }
        let missing_replay = assert_binary_release_gate_closed(missing_replay, "exact replay");
        assert_eq!(
            trust_ir_checked_certificate_bridge_json(&missing_replay)["release_gate"]["replay_accepted"],
            false
        );

        let mut missing_source = baseline.clone();
        for dispatch in &mut missing_source.verification.solver_dispatch {
            dispatch.origin.as_mut().expect("artifact dispatch origin").source = None;
        }
        for dispatch in &mut missing_source.functions[0].verification.solver_dispatch {
            dispatch.origin.as_mut().expect("function dispatch origin").source = None;
        }
        let missing_source =
            assert_binary_release_gate_closed(missing_source, "exact source provenance");
        assert_eq!(
            trust_ir_checked_certificate_bridge_json(&missing_source)["release_gate"]["source_provenance_accepted"],
            false
        );

        let mut missing_target_consumer = baseline;
        missing_target_consumer.reconstruction.outputs[0].target_validation_blockers.push(
            TargetValidationBlocker {
                target: DecompileTarget::TrustIr,
                function: Some("proved_fn".to_string()),
                code: "target-proof-consumer-evidence".to_string(),
                stage: "trust-ir-bridge::target-validation".to_string(),
                feature: "target-proof-consumer-evidence".to_string(),
                reason: "synthetic fixture lacks explicit target consumer acceptance".to_string(),
                origin: None,
                diagnostics: vec![
                    "blocker-code=target-proof-consumer-evidence".to_string(),
                    "proof-grade=false".to_string(),
                ],
            },
        );
        let missing_target_consumer =
            assert_binary_release_gate_closed(missing_target_consumer, "target consumer");
        assert_eq!(
            trust_ir_checked_certificate_bridge_json(&missing_target_consumer)["release_gate"]["target_reconstruction_accepted"],
            false
        );
    }

    #[test]
    fn checked_replayed_binary_vcs_require_rust_compile_back_for_proof_grade() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();

        artifact.target = DecompileTarget::Rust;
        artifact.reconstruction.target = DecompileTarget::Rust;
        artifact.reconstruction.validation = ReconstructionValidationStatus::Validated;
        artifact.reconstruction.trust_level = TrustLevel::ProofGrade;
        artifact.reconstruction.validated_rust = Some(ValidatedRustReconstruction {
            status: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            diagnostics: vec![
                "forged Rust summary omitted compile-back TrustIr refinement records".to_string(),
            ],
            ..ValidatedRustReconstruction::default()
        });

        assert!(
            binary_proof_grade_release_gate_accepts(&artifact.verification),
            "{:?}",
            artifact.verification.solver_dispatch
        );
        assert!(artifact_source_provenance_allows_binary_proof_grade(&artifact));
        assert!(!reconstruction_allows_artifact_proof_grade(&artifact.reconstruction));
        assert_binary_release_gate_closed(
            artifact,
            "Rust compile-back TrustIr refinement evidence",
        );
    }

    #[test]
    fn checked_replayed_binary_vcs_require_non_refuted_rust_compile_back() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);

        let validated =
            artifact.reconstruction.validated_rust.as_mut().expect("validated Rust summary");
        let record = validated.validation_records.first_mut().expect("compile-back record");
        record.status = ReconstructionValidationStatus::Refuted;
        record.trust_level = TrustLevel::Rejected;
        record.diagnostics.push("compile-back reconstructed TrustIr mismatch".to_string());
        if let Some(forward) = record.forward.as_mut() {
            forward.status = ReconstructionValidationStatus::Refuted;
            forward.counterexamples = 1;
            forward.diagnostics.push("lifted-to-output compile-back mismatch".to_string());
        }

        assert!(binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(artifact_source_provenance_allows_binary_proof_grade(&artifact));
        assert!(!reconstruction_allows_artifact_proof_grade(&artifact.reconstruction));
        assert_binary_release_gate_closed(artifact, "non-refuted Rust compile-back evidence");
    }

    #[test]
    fn checked_replayed_binary_vcs_require_rust_compile_back_caller_acceptance() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);

        let validated =
            artifact.reconstruction.validated_rust.as_mut().expect("validated Rust summary");
        let record = validated.validation_records.first_mut().expect("compile-back record");
        record.evidence.retain(|evidence| {
            !matches!(
                evidence,
                ReconstructionValidationEvidence::Other(kind)
                    if kind == RUST_COMPILE_BACK_CHECKED_CERTIFICATE_IDENTITY_EVIDENCE
                        || kind == RUST_COMPILE_BACK_TARGET_CONSUMER_ACCEPTANCE_EVIDENCE
            )
        });

        assert!(binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(artifact_source_provenance_allows_binary_proof_grade(&artifact));
        assert!(!reconstruction_allows_artifact_proof_grade(&artifact.reconstruction));
        assert_binary_release_gate_closed(
            artifact,
            "Rust compile-back caller certificate identity and target consumer acceptance",
        );
    }

    #[test]
    fn checked_replayed_binary_vcs_require_rust_compile_back_binding_markers() {
        let cases = [
            (
                RUST_COMPILE_BACK_LIFTED_BINARY_TRUST_IR_BINDING_EVIDENCE,
                "Rust compile-back lifted-binary TrustIr binding",
            ),
            (
                RUST_COMPILE_BACK_CHECKED_CERTIFICATE_BINDING_EVIDENCE,
                "Rust compile-back checked certificate binding",
            ),
            (
                RUST_COMPILE_BACK_REPLAY_IDENTITY_BINDING_EVIDENCE,
                "Rust compile-back replay identity binding",
            ),
            (
                RUST_COMPILE_BACK_SOURCE_GATE_BINDING_EVIDENCE,
                "Rust compile-back source gate binding",
            ),
            (
                RUST_COMPILE_BACK_UNSUPPORTED_LEDGER_ELIMINATION_EVIDENCE,
                "Rust compile-back unsupported-ledger elimination binding",
            ),
        ];

        for (missing_marker, missing_gate) in cases {
            let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
            install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
            remove_rust_compile_back_evidence_marker(&mut artifact, missing_marker);

            assert!(binary_proof_grade_release_gate_accepts(&artifact.verification));
            assert!(artifact_source_provenance_allows_binary_proof_grade(&artifact));
            assert!(
                !reconstruction_allows_artifact_proof_grade(&artifact.reconstruction),
                "{missing_marker} should be proof-grade blocking"
            );
            assert_rust_reconstruction_release_gate_closed(artifact, missing_gate);
        }
    }

    #[test]
    fn checked_replayed_binary_vcs_require_rust_compile_back_artifact_digest_bindings() {
        let mut missing = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut missing);
        remove_rust_compile_back_evidence_marker(
            &mut missing,
            RUST_COMPILE_BACK_ARTIFACT_DIGEST_BINDING_EVIDENCE,
        );

        assert!(!rust_compile_back_artifact_digest_bindings_allow_source_backpropagation(&missing));
        assert_rust_reconstruction_release_gate_closed(
            missing,
            "Rust compile-back artifact digest binding",
        );

        let mut stale_lifted_trust_ir =
            synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut stale_lifted_trust_ir);
        stale_lifted_trust_ir.functions[0]
            .lifted
            .as_mut()
            .expect("lifted TrustIr")
            .def_path
            .push_str("::stale");

        assert!(!rust_compile_back_artifact_digest_bindings_allow_source_backpropagation(
            &stale_lifted_trust_ir
        ));
        assert_rust_reconstruction_release_gate_closed(
            stale_lifted_trust_ir,
            "Rust compile-back artifact digest binding",
        );

        let mut wrong_origin = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut wrong_origin);
        replace_rust_compile_back_evidence_value(
            &mut wrong_origin,
            RUST_COMPILE_BACK_ROOT_ARTIFACT_SHA256_EVIDENCE_PREFIX,
            &"f".repeat(64),
        );

        assert!(!rust_compile_back_artifact_digest_bindings_allow_source_backpropagation(
            &wrong_origin
        ));
        assert_rust_reconstruction_release_gate_closed(
            wrong_origin,
            "Rust compile-back artifact digest binding",
        );
    }

    #[test]
    fn checked_replayed_binary_vcs_cap_rust_reconstruction_without_release_inputs() {
        use trust_types::{BinaryTypeFact, Formula};

        let mut baseline = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut baseline);
        assert!(binary_proof_grade_release_gate_accepts(&baseline.verification));
        assert!(artifact_source_provenance_allows_binary_proof_grade(&baseline));
        assert!(
            rust_reconstruction_source_rewrite_authority_allows_proof_grade(&baseline),
            "blockers={:?}; source={:?}",
            source_rewrite_authority_blockers(&baseline),
            baseline.source_provenance
        );
        assert!(reconstruction_allows_artifact_proof_grade(&baseline.reconstruction));
        assert!(apply_binary_proof_grade_release_gate(&mut baseline.clone()));

        let mut missing_decompile_digest_identity = baseline.clone();
        missing_decompile_digest_identity.binary.root_artifact_digest = None;
        assert_rust_reconstruction_release_gate_closed(
            missing_decompile_digest_identity,
            "decompile artifact digest identity",
        );

        let mut missing_reconstruction_digest_identity = baseline.clone();
        for output in &mut missing_reconstruction_digest_identity.reconstruction.outputs {
            output.assumptions.retain(|assumption| {
                assumption.stage != RECONSTRUCTION_OUTPUT_BINARY_ARTIFACT_DIGEST_IDENTITY_STAGE
            });
        }
        assert_rust_reconstruction_release_gate_closed(
            missing_reconstruction_digest_identity,
            "Rust output binary artifact digest identity",
        );

        let mut missing_exact_source = baseline.clone();
        missing_exact_source.source_provenance.status = "ambiguous".to_string();
        missing_exact_source.source_provenance.exact_mapping_count = 0;
        missing_exact_source.source_provenance.ambiguous_mapping_count = 1;
        assert_rust_reconstruction_release_gate_closed(
            missing_exact_source,
            "exact Rust source ownership",
        );

        let mut binary_address_only_type_fact = baseline.clone();
        let mut type_fact_origin =
            binary_address_only_type_fact.functions[0].origin.clone().expect("function origin");
        type_fact_origin.source =
            Some(SourceSpan::binary_address(type_fact_origin.instruction_address));
        binary_address_only_type_fact.type_facts.push(BinaryTypeFact {
            subject: BinaryFactSubject::Parameter { function: "proved_fn".to_string(), index: 0 },
            recovered_ty: Some(Ty::u64()),
            origin: Some(type_fact_origin),
            evidence: BinaryFactEvidence::DebugInfo,
            confidence: BinaryFactConfidence::Validated,
            ..Default::default()
        });
        refresh_source_backpropagation_authority(&mut binary_address_only_type_fact);
        assert!(!rust_reconstruction_source_rewrite_authority_allows_proof_grade(
            &binary_address_only_type_fact
        ));
        assert_rust_reconstruction_release_gate_closed(
            binary_address_only_type_fact,
            "Rust type fact source ownership",
        );

        let mut missing_replay_attestation = baseline.clone();
        for dispatch in
            missing_replay_attestation.verification.solver_dispatch.iter_mut().chain(
                missing_replay_attestation.functions[0].verification.solver_dispatch.iter_mut(),
            )
        {
            dispatch.replay = ReplayStatus::NotAttempted;
        }
        assert_rust_reconstruction_release_gate_closed(
            missing_replay_attestation,
            "Rust replay attestation",
        );

        let mut missing_checked_certificate_identity = baseline.clone();
        for dispatch in
            missing_checked_certificate_identity.verification.solver_dispatch.iter_mut().chain(
                missing_checked_certificate_identity.functions[0]
                    .verification
                    .solver_dispatch
                    .iter_mut(),
            )
        {
            dispatch.certificate = ProofCertificateStatus::Checked {
                checker: "ay-cert-check".to_string(),
                format: "lfsc".to_string(),
                sha256: None,
            };
        }
        assert_rust_reconstruction_release_gate_closed(
            missing_checked_certificate_identity,
            "Rust checked certificate identity",
        );

        let mut missing_target_consumer = baseline.clone();
        for output in &mut missing_target_consumer.reconstruction.outputs {
            output
                .diagnostics
                .retain(|diagnostic| !target_consumer_acceptance_diagnostic(diagnostic));
        }
        assert_rust_reconstruction_release_gate_closed(
            missing_target_consumer,
            "Rust target consumer acceptance",
        );

        let mut missing_formula_consumer = baseline.clone();
        let rust_output = missing_formula_consumer
            .reconstruction
            .outputs
            .iter_mut()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust output");
        rust_output
            .diagnostics
            .retain(|diagnostic| !symbolic_formula_consumer_diagnostic(diagnostic));
        rust_output.diagnostics.push(
            "target-consumer=accepted; target proof consumer accepted Rust output".to_string(),
        );
        rust_output.preserved_symbolic_formulas.push(PreservedSymbolicFormula {
            target: DecompileTarget::Rust,
            function: Some("proved_fn".to_string()),
            block: Some(0),
            statement_index: Some(0),
            location: "rust-output::proved_fn".to_string(),
            formula: Formula::Bool(true),
        });
        assert!(!reconstruction_target_consumer_accepted_by_proof_model(
            &missing_formula_consumer.reconstruction
        ));
        assert!(!reconstruction_symbolic_formulas_consumed_by_proof_model(
            &missing_formula_consumer.reconstruction
        ));
        assert_rust_reconstruction_release_gate_closed(
            missing_formula_consumer,
            "Rust symbolic formula consumer acceptance",
        );
    }

    #[test]
    fn rust_reconstruction_requires_summary_output_trust_identity() {
        let mut baseline = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut baseline);

        let mut partial_output_trust = baseline.clone();
        partial_output_trust.reconstruction.outputs[0].trust_level = TrustLevel::Partial;
        assert!(!reconstruction_allows_artifact_proof_grade(&partial_output_trust.reconstruction));
        assert_rust_reconstruction_release_gate_closed(
            partial_output_trust,
            "Rust output proof-grade trust",
        );

        let mut missing_output_summary = baseline.clone();
        missing_output_summary.reconstruction.outputs[0].validated_rust = None;
        assert!(!reconstruction_allows_artifact_proof_grade(
            &missing_output_summary.reconstruction
        ));
        assert_rust_reconstruction_release_gate_closed(
            missing_output_summary,
            "Rust output validated summary identity",
        );

        let mut mixed_with_skeleton = baseline;
        let mut skeleton_output = DecompiledOutput {
            target: DecompileTarget::Rust,
            text: Some(render_rust_skeleton(
                &mixed_with_skeleton.binary,
                &mixed_with_skeleton.functions,
                &mixed_with_skeleton.unsupported,
            )),
            validation: ReconstructionValidationStatus::NotAttempted,
            trust_level: TrustLevel::Exploratory,
            validation_records: rust_skeleton_validation_records(&mixed_with_skeleton.functions),
            validated_rust: Some(validated_rust_reconstruction(&mixed_with_skeleton.functions)),
            diagnostics: vec![
                "format=rust-skeleton".to_string(),
                "exploratory output; not validated".to_string(),
                "validation-records=text-only".to_string(),
            ],
            ..Default::default()
        };
        attach_binary_artifact_digest_identity_to_output(
            &mut skeleton_output,
            &mixed_with_skeleton.binary,
        );
        mixed_with_skeleton.reconstruction.outputs.push(skeleton_output);

        assert!(!reconstruction_allows_artifact_proof_grade(&mixed_with_skeleton.reconstruction));
        assert_rust_reconstruction_release_gate_closed(
            mixed_with_skeleton,
            "Rust skeleton output in proof-grade reconstruction",
        );
    }

    #[test]
    fn checked_replayed_binary_vcs_accept_synthetic_rust_compile_back_fixture() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);

        assert_eq!(artifact.target, DecompileTarget::Rust);
        assert_eq!(artifact.reconstruction.target, DecompileTarget::Rust);
        assert!(binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(artifact_source_provenance_allows_binary_proof_grade(&artifact));
        assert!(
            reconstruction_allows_artifact_proof_grade(&artifact.reconstruction),
            "{:?}",
            artifact.reconstruction.validated_rust
        );

        let validated =
            artifact.reconstruction.validated_rust.as_ref().expect("validated Rust summary");
        assert_eq!(validated.status, ReconstructionValidationStatus::Validated);
        assert_eq!(validated.trust_level, TrustLevel::ProofGrade);
        let record = validated.validation_records.first().expect("compile-back record");
        assert_eq!(record.target, DecompileTarget::Rust);
        assert_eq!(record.candidate, ReconstructionCandidateKind::ValidatedRustStrictSubset);
        assert_eq!(record.status, ReconstructionValidationStatus::Validated);
        assert_eq!(record.trust_level, TrustLevel::ProofGrade);
        assert!(record.lifted_function.is_some());
        assert!(record.reconstructed_function.is_some());
        assert!(
            record
                .evidence
                .contains(&ReconstructionValidationEvidence::BidirectionalTrustIrRefinement)
        );
        assert!(record.evidence.iter().any(|evidence| {
            matches!(
                evidence,
                ReconstructionValidationEvidence::Other(kind) if kind == "compile-back-proof-grade"
            )
        }));
        for marker in [
            RUST_COMPILE_BACK_LIFTED_BINARY_TRUST_IR_BINDING_EVIDENCE,
            RUST_COMPILE_BACK_CHECKED_CERTIFICATE_BINDING_EVIDENCE,
            RUST_COMPILE_BACK_REPLAY_IDENTITY_BINDING_EVIDENCE,
            RUST_COMPILE_BACK_SOURCE_GATE_BINDING_EVIDENCE,
            RUST_COMPILE_BACK_UNSUPPORTED_LEDGER_ELIMINATION_EVIDENCE,
            RUST_COMPILE_BACK_ARTIFACT_DIGEST_BINDING_EVIDENCE,
        ] {
            assert!(
                record.evidence.iter().any(|evidence| {
                    matches!(evidence, ReconstructionValidationEvidence::Other(kind) if kind == marker)
                }),
                "missing explicit Rust compile-back binding marker {marker}"
            );
        }
        for prefix in [
            RUST_COMPILE_BACK_LIFTED_BINARY_TRUST_IR_SHA256_EVIDENCE_PREFIX,
            RUST_COMPILE_BACK_RUST_SOURCE_SHA256_EVIDENCE_PREFIX,
            RUST_COMPILE_BACK_RECONSTRUCTED_TRUST_IR_SHA256_EVIDENCE_PREFIX,
            RUST_COMPILE_BACK_REFINEMENT_ARTIFACT_SHA256_EVIDENCE_PREFIX,
            RUST_COMPILE_BACK_ROOT_ARTIFACT_SHA256_EVIDENCE_PREFIX,
            RUST_COMPILE_BACK_SELECTED_IMAGE_SHA256_EVIDENCE_PREFIX,
            RUST_COMPILE_BACK_SELECTED_IMAGE_RANGE_EVIDENCE_PREFIX,
        ] {
            assert!(
                record_other_evidence_value(record, prefix).is_some(),
                "missing Rust compile-back digest evidence with prefix {prefix}"
            );
        }
        assert!(rust_compile_back_artifact_digest_bindings_allow_source_backpropagation(&artifact));
        assert_eq!(record.forward.as_ref().map(|direction| direction.proof_certificates), Some(2));
        assert_eq!(record.reverse.as_ref().map(|direction| direction.proof_certificates), Some(2));

        assert!(apply_binary_proof_grade_release_gate(&mut artifact));
        assert_eq!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.verification.trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);
    }

    #[test]
    fn checked_replayed_binary_vcs_still_require_exact_source_provenance_for_proof_grade() {
        use trust_types::{ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary(&[("proved_fn", 0x401000)]);
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic proved artifact");

        install_test_binary_artifact_digest_metadata(&mut artifact);
        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );

        assert_eq!(artifact.source_provenance.status, "unavailable");
        assert!(!artifact.source_provenance.has_exact_debug_source_provenance());
        assert_eq!(artifact.unsupported.records.len(), 0);
        assert_eq!(artifact.reconstruction.validation, ReconstructionValidationStatus::Validated);
        assert!(!apply_binary_proof_grade_release_gate(&mut artifact));

        assert_eq!(artifact.verification.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].verification.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);
    }

    #[test]
    fn checked_replayed_binary_vcs_require_exact_instruction_provenance_for_proof_grade() {
        use trust_types::{ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic proved artifact");

        mark_dispatches_checked(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked(&mut artifact.functions[0].verification.solver_dispatch);
        for dispatch in &mut artifact.verification.solver_dispatch {
            dispatch.replay = ReplayStatus::Replayed;
            assert!(
                dispatch.origin.as_ref().is_some_and(|origin| {
                    origin.instruction_size.is_none() && origin.instruction_bytes.is_empty()
                }),
                "synthetic dispatch should not silently carry instruction bytes"
            );
        }
        for dispatch in &mut artifact.functions[0].verification.solver_dispatch {
            dispatch.replay = ReplayStatus::Replayed;
        }

        assert!(source_provenance_allows_artifact_proof_grade(&artifact.source_provenance));
        assert_eq!(artifact.reconstruction.validation, ReconstructionValidationStatus::Validated);
        assert!(!binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(!apply_binary_proof_grade_release_gate(&mut artifact));

        assert_eq!(artifact.verification.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].verification.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);
    }

    #[test]
    fn checked_binary_vcs_require_validated_reconstruction_for_proof_grade() {
        use trust_types::{BinaryVerificationStatus, ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic proved artifact");

        install_test_binary_artifact_digest_metadata(&mut artifact);
        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );
        artifact.reconstruction.validation = ReconstructionValidationStatus::NotAttempted;
        for output in &mut artifact.reconstruction.outputs {
            output.validation = ReconstructionValidationStatus::NotAttempted;
        }

        assert!(!apply_binary_proof_grade_release_gate(&mut artifact));

        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Proved);
        assert_eq!(artifact.verification.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].verification.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);
    }

    #[test]
    fn checked_binary_vcs_do_not_promote_unvalidated_derived_outputs_to_proof_grade() {
        use trust_types::{BinaryVerificationStatus, ProofStrength, VcKind};

        let mut cases = vec![(
            DecompileOutputKind::WasmText,
            DecompileTarget::Wasm,
            ReconstructionValidationStatus::Validated,
            "missing-target-semantic-validation",
            true,
        )];
        #[cfg(feature = "trust-cg")]
        cases.push((
            DecompileOutputKind::TrustCgText,
            DecompileTarget::TrustCg,
            ReconstructionValidationStatus::Validated,
            "missing-target-semantic-validation",
            true,
        ));
        #[cfg(not(feature = "trust-cg"))]
        cases.push((
            DecompileOutputKind::TrustCgText,
            DecompileTarget::TrustCg,
            ReconstructionValidationStatus::Failed,
            "trust-cg-backend-unavailable",
            false,
        ));

        for (
            output_kind,
            target,
            expected_validation,
            expected_blocker,
            expected_binary_gate_accepts,
        ) in cases
        {
            let mut lifted = synthetic_lifted_binary_with_source(
                &[("proved_fn", 0x401000)],
                &[(0x401000, "src/proved.rs", 1, 1)],
            );
            lifted.functions[0].trust_ir_body = constant_return_trust_ir("proved_fn", 7).body;
            let options = DecompileOptions::default().with_outputs([output_kind]);
            let results = vec![(
                synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
                VerificationResult::Proved {
                    solver: "ay".into(),
                    time_ms: 2,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: Some(b"checked externally".to_vec()),
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            )];
            let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
                8, &options, &lifted, &results,
            )
            .expect("synthetic proved artifact");

            install_test_binary_artifact_digest_metadata(&mut artifact);
            mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
            mark_dispatches_checked_and_replayed(
                &mut artifact.functions[0].verification.solver_dispatch,
            );

            assert_eq!(
                binary_proof_grade_release_gate_accepts(&artifact.verification),
                expected_binary_gate_accepts,
                "{:?}; unsupported={:?}",
                artifact.verification.solver_dispatch,
                artifact.verification.unsupported_ledger
            );
            assert!(
                source_provenance_allows_artifact_proof_grade(&artifact.source_provenance),
                "{:?}",
                artifact.source_provenance
            );
            assert_eq!(artifact.reconstruction.target, target);
            assert_eq!(artifact.reconstruction.outputs[0].validation, expected_validation);
            assert!(
                artifact.reconstruction.outputs[0]
                    .target_validation_blockers
                    .iter()
                    .any(|blocker| blocker.feature == expected_blocker),
                "{:?}",
                artifact.reconstruction.outputs[0].target_validation_blockers
            );
            #[cfg(not(feature = "trust-cg"))]
            if target == DecompileTarget::TrustCg {
                assert!(
                    artifact.reconstruction.outputs[0]
                        .diagnostics
                        .iter()
                        .any(|diagnostic| diagnostic == "trust-cg-feature=disabled"),
                    "{:?}",
                    artifact.reconstruction.outputs[0].diagnostics
                );
            }
            assert!(!reconstruction_allows_artifact_proof_grade(&artifact.reconstruction));

            assert!(!apply_binary_proof_grade_release_gate(&mut artifact));

            assert_ne!(artifact.verification.status, BinaryVerificationStatus::Rejected);
            assert_eq!(artifact.verification.trust_level, TrustLevel::Partial);
            assert_ne!(artifact.reconstruction.outputs[0].trust_level, TrustLevel::ProofGrade);
            assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
            assert_ne!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);
        }
    }

    #[cfg(feature = "trust-cg")]
    #[test]
    fn release_gate_recognizes_trust_cg_scalar_bool_target_consumer_without_symbolic_blocker() {
        let metadata = BinaryArtifactMetadata {
            path: Some("fixtures/scalar-bool-release-gate.bin".to_string()),
            format: BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            entry_point: Some(0x401000),
            byte_len: Some(8),
            build_id: Some("synthetic-loader-id:unit-test".to_string()),
            root_artifact_digest: test_binary_artifact_digest_identity().root_artifact_digest,
            selected_image: test_binary_artifact_digest_identity().selected_image,
            ..Default::default()
        };
        let origin = test_noop_binary_origin("scalar_bool", 0x401000);
        let mut verification =
            BinaryVerificationSummary::from_solver_dispatch(vec![checked_replayed_dispatch(
                "scalar_bool",
                origin.clone(),
            )]);
        verification.unsupported_ledger = UnsupportedLedger::default();
        verification.refresh_from_solver_dispatch();
        let function = DecompiledFunction {
            name: "scalar_bool".to_string(),
            entry: 0x401000,
            origin: Some(origin.clone()),
            instruction_provenance: vec![origin],
            lifted: Some(symbolic_bool_true_return_trust_ir("scalar_bool")),
            verification,
            ..Default::default()
        };

        let outputs = build_outputs(BuildOutputsInput {
            metadata: &metadata,
            functions: &[function],
            call_graph: &CallGraph::new(),
            memory_facts: &[],
            unsupported: &UnsupportedLedger::default(),
            source_provenance: &BinarySourceProvenanceSummary::default(),
            requested: &[DecompileOutputKind::TrustCgText],
            source_assumptions: &[],
            source_diagnostics: &[],
        })
        .expect("trust-cg scalar Bool fixture should build output");

        let trust_cg = &outputs[0];
        assert_eq!(trust_cg.target, DecompileTarget::TrustCg);
        assert_eq!(trust_cg.validation, ReconstructionValidationStatus::Validated);
        assert_eq!(trust_cg.trust_level, TrustLevel::Rejected);
        assert_eq!(trust_cg.preserved_symbolic_formulas.len(), 1);
        assert!(
            trust_cg
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("scalar-bool-true-trust_cg-target-consumed")),
            "{:?}",
            trust_cg.diagnostics
        );
        let target_artifacts = target_proof_consumer_artifact_digest_records(trust_cg);
        assert_eq!(target_artifacts.len(), 1, "{:?}", trust_cg.diagnostics);
        let target_artifact = &target_artifacts[0];
        assert_eq!(target_artifact.target, "trust-cg");
        assert_eq!(target_artifact.status, "accepted");
        assert!(target_artifact.target_semantics_consumed);
        assert!(target_artifact.artifact_digest.is_canonical_sha256());
        assert!(target_artifact.lifted_trust_ir_artifact.digest.is_canonical_sha256());
        assert_eq!(
            target_artifact.binary_artifact_digest_identity,
            Some(test_binary_artifact_digest_identity())
        );
        assert!(!target_artifact.binary_origins.is_empty());
        assert!(target_proof_consumer_artifact_digest_accepted_for_output(
            trust_cg,
            target_artifact
        ));
        let trust_cg_json: serde_json::Value =
            serde_json::from_str(trust_cg.text.as_deref().expect("trust-cg JSON text"))
                .expect("trust-cg output should be JSON");
        assert_eq!(trust_cg_json["target_proof_consumer_artifact_digest"]["target"], "trust-cg");
        assert_eq!(
            trust_cg_json["target_proof_consumer_artifact_digest"]["artifact_digest"]["value"]
                .as_str(),
            Some(target_artifact.artifact_digest.value.as_str())
        );
        assert_eq!(
            trust_cg_json["target_proof_consumer_artifact_digest"]["lifted_trust_ir_artifact"]["digest"]
                ["value"]
                .as_str(),
            Some(target_artifact.lifted_trust_ir_artifact.digest.value.as_str())
        );
        assert_eq!(
            trust_cg_json["target_proof_consumer_artifact_digest"]["binary_artifact_digest_identity"]
                ["selected_image"]["sha256"]
                .as_str(),
            target_artifact
                .binary_artifact_digest_identity
                .as_ref()
                .and_then(|identity| identity.selected_image.as_ref())
                .map(|selected| selected.sha256.as_str())
        );

        let mut target_consumer_candidate = trust_cg.clone();
        target_consumer_candidate.target_validation_blockers.clear();
        assert!(output_target_consumer_accepted_by_proof_model(&target_consumer_candidate));

        let mut missing_record = target_consumer_candidate.clone();
        missing_record.diagnostics.retain(|diagnostic| {
            !diagnostic.starts_with(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
        });
        missing_record.diagnostics.push(
            "target-consumer=accepted; target proof consumer accepted stale text-only claim"
                .to_string(),
        );
        assert!(!output_target_consumer_accepted_by_proof_model(&missing_record));
        assert!(!reconstruction_target_consumer_accepted_by_proof_model(&ReconstructionSummary {
            target: DecompileTarget::TrustCg,
            outputs: vec![missing_record],
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }));

        let mut stale_record = target_consumer_candidate.clone();
        let diagnostic_index = stale_record
            .diagnostics
            .iter()
            .position(|diagnostic| {
                diagnostic.starts_with(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
            })
            .expect("target proof-consumer artifact digest diagnostic");
        let json = stale_record.diagnostics[diagnostic_index]
            .strip_prefix(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
            .expect("target proof-consumer artifact digest json");
        let mut stale_artifact: TargetProofConsumerArtifactDigest =
            serde_json::from_str(json).expect("target artifact digest should parse");
        stale_artifact.target = "wasm".to_string();
        stale_record.diagnostics[diagnostic_index] = format!(
            "{TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX}{}",
            serde_json::to_string(&stale_artifact)
                .expect("stale target artifact digest should serialize")
        );
        assert!(!output_target_consumer_accepted_by_proof_model(&stale_record));
        assert!(!reconstruction_target_consumer_accepted_by_proof_model(&ReconstructionSummary {
            target: DecompileTarget::TrustCg,
            outputs: vec![stale_record],
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }));
        assert!(
            !trust_cg.target_validation_blockers.iter().any(|blocker| {
                blocker.feature == "symbolic-formula-proof-semantics"
                    || blocker.feature.contains("not-consumed-by-target-semantics")
            }),
            "{:?}",
            trust_cg.target_validation_blockers
        );
        assert!(
            trust_cg.target_validation_blockers.iter().any(|blocker| blocker.feature
                == "TrustCg validation blocker"
                && blocker.reason == "not-proof-grade"
                && blocker.diagnostics.iter().any(|diagnostic| {
                    diagnostic.contains("refinement_metadata")
                        && diagnostic.contains("scalar-bool-true-bidirectional-refinement-consumed")
                })),
            "{:?}",
            trust_cg.target_validation_blockers
        );
        assert!(!reconstruction_allows_artifact_proof_grade(&ReconstructionSummary {
            target: DecompileTarget::TrustCg,
            outputs,
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::Rejected,
            ..Default::default()
        }));
    }

    #[test]
    fn release_gate_keeps_wasm_non_empty_scalar_target_consumer_closed_and_rejected() {
        let metadata = BinaryArtifactMetadata {
            format: BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            entry_point: Some(0x401000),
            ..Default::default()
        };
        let function = DecompiledFunction {
            name: "wasm_scalar_one".to_string(),
            entry: 0x401000,
            lifted: Some(constant_return_trust_ir("wasm_scalar_one", 1)),
            ..Default::default()
        };

        let outputs = build_outputs(BuildOutputsInput {
            metadata: &metadata,
            functions: &[function],
            call_graph: &CallGraph::new(),
            memory_facts: &[],
            unsupported: &UnsupportedLedger::default(),
            source_provenance: &BinarySourceProvenanceSummary::default(),
            requested: &[DecompileOutputKind::WasmText],
            source_assumptions: &[],
            source_diagnostics: &[],
        })
        .expect("Wasm scalar fixture should build output");

        let wasm = &outputs[0];
        assert_eq!(wasm.target, DecompileTarget::Wasm);
        assert_eq!(wasm.validation, ReconstructionValidationStatus::Validated);
        assert_eq!(wasm.trust_level, TrustLevel::Rejected);
        assert_ne!(wasm.trust_level, TrustLevel::ProofGrade);
        assert!(wasm.text.as_deref().is_some_and(|text| text.contains("i32.const 1")));
        assert!(target_proof_consumer_artifact_digest_records(wasm).is_empty());
        assert!(!output_target_consumer_accepted_by_proof_model(wasm));
        assert!(
            wasm.target_validation_blockers.iter().any(|blocker| {
                blocker.feature == "non-empty-scalar-wasm-target-consumer-unavailable"
            }),
            "{:?}",
            wasm.target_validation_blockers
        );
        assert!(
            wasm.target_validation_blockers
                .iter()
                .any(|blocker| { blocker.feature == "missing-scalar-formula-target-op-binding" }),
            "{:?}",
            wasm.target_validation_blockers
        );
        assert!(!reconstruction_allows_artifact_proof_grade(&ReconstructionSummary {
            target: DecompileTarget::Wasm,
            outputs,
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::Rejected,
            ..Default::default()
        }));
    }

    #[test]
    fn release_gate_recognizes_wasm_scalar_bool_target_consumer_artifact_digest() {
        let function_name = "wasm_scalar_bool";
        let identity = test_binary_artifact_digest_identity();
        let metadata = BinaryArtifactMetadata {
            format: BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            byte_len: Some(8),
            root_artifact_digest: identity.root_artifact_digest.clone(),
            selected_image: identity.selected_image.clone(),
            ..Default::default()
        };
        let origin = test_noop_binary_origin(function_name, 0x1000);
        let function = DecompiledFunction {
            name: function_name.to_string(),
            entry: 0x1000,
            origin: Some(origin.clone()),
            instruction_provenance: vec![origin],
            lifted: Some(symbolic_bool_true_return_trust_ir(function_name)),
            ..Default::default()
        };
        let conversion = exact_wasm_non_empty_scalar_conversion(function_name);
        let proof_consumer = conversion.target_proof_consumer_evidence();
        assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Accepted);
        assert!(proof_consumer.target_semantics_consumed);
        assert!(proof_consumer.blockers.is_empty());

        let target_artifact = wasm_target_proof_consumer_artifact_digest(
            &metadata,
            std::slice::from_ref(&function),
            &conversion,
            &proof_consumer,
        )
        .expect("accepted Wasm proof consumer should produce artifact digest");
        assert_eq!(target_artifact.target, "wasm");
        assert_eq!(target_artifact.status, "accepted");
        assert!(target_artifact.target_semantics_consumed);
        assert_eq!(target_artifact.target_output, proof_consumer.binding.target_output);
        assert!(target_artifact.artifact_digest.is_canonical_sha256());
        assert_eq!(
            target_artifact.lifted_trust_ir_artifact.function.as_deref(),
            Some(function_name)
        );
        assert!(target_artifact.lifted_trust_ir_artifact.digest.is_canonical_sha256());
        assert_eq!(target_artifact.binary_artifact_digest_identity, Some(identity));
        assert!(!target_artifact.binary_origins.is_empty());
        assert!(target_proof_consumer_accepted_kind(&target_artifact, "target_semantics"));
        assert!(target_proof_consumer_accepted_kind(&target_artifact, "target_refinement"));
        assert!(target_proof_consumer_accepted_kind(&target_artifact, "symbolic_formula"));

        let diagnostic = target_proof_consumer_artifact_digest_diagnostic(&target_artifact)
            .expect("target artifact digest should serialize");
        let wasm = DecompiledOutput {
            target: DecompileTarget::Wasm,
            text: conversion.wat.clone(),
            validation: conversion.validation,
            trust_level: conversion.trust_level,
            preserved_symbolic_formulas: wasm_preserved_symbolic_formulas(
                &conversion.symbolic_formulas,
            ),
            diagnostics: vec![diagnostic],
            ..Default::default()
        };

        let target_artifacts = target_proof_consumer_artifact_digest_records(&wasm);
        assert_eq!(target_artifacts.len(), 1, "{:?}", wasm.diagnostics);
        assert!(target_proof_consumer_artifact_digest_accepted_for_output(
            &wasm,
            &target_artifacts[0]
        ));
        assert!(output_target_consumer_accepted_by_proof_model(&wasm));
        assert!(reconstruction_target_consumer_accepted_by_proof_model(&ReconstructionSummary {
            target: DecompileTarget::Wasm,
            outputs: vec![wasm.clone()],
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::Rejected,
            ..Default::default()
        }));

        let mut missing_record = wasm.clone();
        missing_record.diagnostics.retain(|diagnostic| {
            !diagnostic.starts_with(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
        });
        missing_record.diagnostics.push(
            "target-consumer=accepted; target proof consumer accepted stale text-only Wasm claim"
                .to_string(),
        );
        assert!(!output_target_consumer_accepted_by_proof_model(&missing_record));
        assert!(!reconstruction_target_consumer_accepted_by_proof_model(&ReconstructionSummary {
            target: DecompileTarget::Wasm,
            outputs: vec![missing_record],
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }));

        let mut stale_record = wasm.clone();
        let diagnostic_index = stale_record
            .diagnostics
            .iter()
            .position(|diagnostic| {
                diagnostic.starts_with(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
            })
            .expect("target proof-consumer artifact digest diagnostic");
        let json = stale_record.diagnostics[diagnostic_index]
            .strip_prefix(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
            .expect("target proof-consumer artifact digest json");
        let mut stale_artifact: TargetProofConsumerArtifactDigest =
            serde_json::from_str(json).expect("target artifact digest should parse");
        stale_artifact.target_output = "wat:emitted:bytes=0:functions=stale".to_string();
        stale_record.diagnostics[diagnostic_index] = format!(
            "{TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX}{}",
            serde_json::to_string(&stale_artifact)
                .expect("stale target artifact digest should serialize")
        );
        assert!(!output_target_consumer_accepted_by_proof_model(&stale_record));
        assert!(!reconstruction_target_consumer_accepted_by_proof_model(&ReconstructionSummary {
            target: DecompileTarget::Wasm,
            outputs: vec![stale_record],
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }));
    }

    #[cfg(feature = "trust-cg")]
    #[test]
    fn target_consumer_accepts_x86_empty_ledger_for_all_claimed_trust_cg_and_wasm_paths() {
        let trust_cg = accepted_trust_cg_scalar_bool_target_output("trust_cg_empty_ledger");
        let wasm = accepted_wasm_scalar_bool_target_output("wasm_empty_ledger");

        for output in [&trust_cg, &wasm] {
            assert!(output_target_consumer_accepted_by_proof_model(output));
            let target_artifacts = target_proof_consumer_artifact_digest_records(output);
            assert_eq!(target_artifacts.len(), 1, "{:?}", output.diagnostics);
            let target_artifact = &target_artifacts[0];
            assert!(target_proof_consumer_artifact_digest_accepted_for_output(
                output,
                target_artifact
            ));
            assert!(target_proof_consumer_accepted_kind(target_artifact, "unsupported_ledger"));
            assert!(target_proof_consumer_has_empty_unsupported_ledger_evidence(target_artifact));
            assert!(target_artifact.unsupported_ledger_evidence.iter().all(|ledger| {
                ledger.unsupported_records == 0
                    && ledger.verification_unsupported == 0
                    && ledger.unsupported_ledger_eliminated
            }));
        }

        assert!(reconstruction_target_consumer_accepted_by_proof_model(&ReconstructionSummary {
            target: DecompileTarget::TrustCg,
            outputs: vec![trust_cg, wasm],
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }));
    }

    #[test]
    fn target_consumer_rejects_missing_structured_target_digest() {
        let mut wasm = accepted_wasm_scalar_bool_target_output("wasm_missing_target_digest");
        wasm.diagnostics.retain(|diagnostic| {
            !diagnostic.starts_with(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
        });
        wasm.diagnostics.push(
            "target-consumer=accepted; target proof consumer accepted stale text-only Wasm claim"
                .to_string(),
        );

        assert!(target_proof_consumer_artifact_digest_records(&wasm).is_empty());
        assert!(!output_target_consumer_accepted_by_proof_model(&wasm));
        assert!(!reconstruction_target_consumer_accepted_by_proof_model(&ReconstructionSummary {
            target: DecompileTarget::Wasm,
            outputs: vec![wasm],
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }));
    }

    #[test]
    fn target_consumer_rejects_mismatched_artifact_digest() {
        let mut wasm = accepted_wasm_scalar_bool_target_output("wasm_mismatched_digest");
        let mut artifact = target_proof_consumer_artifact_digest_records(&wasm)
            .into_iter()
            .next()
            .expect("target proof-consumer artifact digest");
        artifact.artifact_digest = BinaryArtifactDigest::sha256(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        );
        replace_target_consumer_artifact_digest(&mut wasm, &artifact);

        assert!(!target_proof_consumer_artifact_digest_matches_material(&artifact));
        assert!(!output_target_consumer_accepted_by_proof_model(&wasm));
    }

    #[test]
    fn target_consumer_artifact_digest_content_addresses_all_consumed_evidence() {
        let wasm = accepted_wasm_scalar_bool_target_output("wasm_evidence_artifacts");
        let artifact = target_proof_consumer_artifact_digest_records(&wasm)
            .into_iter()
            .next()
            .expect("target proof-consumer artifact digest");

        for kind in [
            "binary_provenance",
            "checked_certificate",
            "proof_replay",
            "unsupported_ledger",
            "target_refinement",
            "symbolic_formula",
        ] {
            assert!(
                target_proof_consumer_accepted_evidence_kind(&artifact, kind),
                "missing accepted {kind} evidence artifact in {artifact:?}"
            );
        }
        assert!(
            artifact
                .evidence_artifacts
                .iter()
                .all(target_proof_consumer_evidence_artifact_digest_matches_material)
        );
        assert!(target_proof_consumer_formula_evidence_covers_output(&artifact, &wasm));
        assert!(output_target_consumer_accepted_by_proof_model(&wasm));
    }

    #[test]
    fn target_consumer_rejects_missing_consumed_formula_evidence_artifact() {
        let mut wasm = accepted_wasm_scalar_bool_target_output("wasm_missing_formula_evidence");
        let mut artifact = target_proof_consumer_artifact_digest_records(&wasm)
            .into_iter()
            .next()
            .expect("target proof-consumer artifact digest");
        artifact.evidence_artifacts.retain(|artifact| artifact.kind != "symbolic_formula");
        refresh_target_consumer_artifact_digest(&mut artifact);
        replace_target_consumer_artifact_digest(&mut wasm, &artifact);

        assert!(target_proof_consumer_artifact_digest_matches_material(&artifact));
        assert!(!target_proof_consumer_accepted_evidence_kind(&artifact, "symbolic_formula"));
        assert!(!target_proof_consumer_formula_evidence_covers_output(&artifact, &wasm));
        assert!(!target_proof_consumer_artifact_digest_accepted_for_output(&wasm, &artifact));
        assert!(!output_target_consumer_accepted_by_proof_model(&wasm));
    }

    #[test]
    fn target_consumer_rejects_stale_consumed_evidence_artifact_digest() {
        let mut wasm = accepted_wasm_scalar_bool_target_output("wasm_stale_evidence_digest");
        let mut artifact = target_proof_consumer_artifact_digest_records(&wasm)
            .into_iter()
            .next()
            .expect("target proof-consumer artifact digest");
        let evidence_artifact = artifact
            .evidence_artifacts
            .iter_mut()
            .find(|artifact| artifact.kind == "checked_certificate")
            .expect("checked-certificate evidence artifact");
        evidence_artifact.detail.push_str(":stale-detail");
        refresh_target_consumer_artifact_digest(&mut artifact);
        replace_target_consumer_artifact_digest(&mut wasm, &artifact);

        assert!(target_proof_consumer_artifact_digest_matches_material(&artifact));
        assert!(artifact.evidence_artifacts.iter().any(|artifact| {
            artifact.kind == "checked_certificate"
                && !target_proof_consumer_evidence_artifact_digest_matches_material(artifact)
        }));
        assert!(!target_proof_consumer_artifact_digest_accepted_for_output(&wasm, &artifact));
        assert!(!output_target_consumer_accepted_by_proof_model(&wasm));
    }

    #[test]
    fn target_consumer_rejects_nonempty_unsupported_ledger_evidence() {
        let mut wasm = accepted_wasm_scalar_bool_target_output("wasm_nonempty_unsupported");
        let mut artifact = target_proof_consumer_artifact_digest_records(&wasm)
            .into_iter()
            .next()
            .expect("target proof-consumer artifact digest");
        let ledger =
            artifact.unsupported_ledger_evidence.first_mut().expect("unsupported-ledger evidence");
        ledger.unsupported_records = 1;
        ledger.verification_unsupported = 1;
        ledger.unsupported_ledger_eliminated = false;
        artifact.artifact_digest = target_proof_consumer_artifact_digest(
            &TargetProofConsumerArtifactDigestMaterial::from_record(&artifact),
        )
        .expect("mutated target artifact digest should hash");
        replace_target_consumer_artifact_digest(&mut wasm, &artifact);

        assert!(target_proof_consumer_artifact_digest_matches_material(&artifact));
        assert!(!target_proof_consumer_has_empty_unsupported_ledger_evidence(&artifact));
        assert!(!target_proof_consumer_artifact_digest_accepted_for_output(&wasm, &artifact));
        assert!(!output_target_consumer_accepted_by_proof_model(&wasm));
    }

    #[cfg(feature = "trust-cg")]
    #[test]
    fn target_consumer_rejects_mixed_claimed_target_state() {
        let trust_cg = accepted_trust_cg_scalar_bool_target_output("mixed_trust_cg_accepted");
        let mut rejected_wasm = accepted_wasm_scalar_bool_target_output("mixed_wasm_rejected");
        rejected_wasm.diagnostics.retain(|diagnostic| {
            !diagnostic.starts_with(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
        });
        rejected_wasm.target_validation_blockers.push(TargetValidationBlocker {
            target: DecompileTarget::Wasm,
            function: Some("mixed_wasm_rejected".to_string()),
            code: "target-proof-consumer-artifact-digest".to_string(),
            stage: "trust-wasm-bridge::target-validation".to_string(),
            feature: "target-proof-consumer-artifact-digest".to_string(),
            reason: "claimed Wasm target path lacks accepted target proof-consumer digest"
                .to_string(),
            origin: None,
            diagnostics: vec!["proof-grade=false".to_string()],
        });

        assert!(output_target_consumer_accepted_by_proof_model(&trust_cg));
        assert!(!output_target_consumer_accepted_by_proof_model(&rejected_wasm));
        assert!(reconstruction_target_consumer_accepted_by_proof_model(&ReconstructionSummary {
            target: DecompileTarget::TrustCg,
            outputs: vec![trust_cg.clone()],
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }));
        assert!(!reconstruction_target_consumer_accepted_by_proof_model(&ReconstructionSummary {
            target: DecompileTarget::TrustCg,
            outputs: vec![trust_cg, rejected_wasm],
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }));
    }

    #[test]
    fn target_consumer_accepts_rust_reconstruction_artifact_digest() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
        let rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust proof-grade output");

        let target_artifacts = target_proof_consumer_artifact_digest_records(rust);
        assert_eq!(target_artifacts.len(), 1, "{:?}", rust.diagnostics);
        let target_artifact = &target_artifacts[0];
        assert_eq!(target_artifact.target, "rust");
        assert_eq!(target_artifact.status, "accepted");
        assert!(target_artifact.target_semantics_consumed);
        assert!(target_artifact.target_output.starts_with("rust-strict-subset:sha256="));
        assert!(target_artifact.artifact_digest.is_canonical_sha256());
        assert!(target_artifact.lifted_trust_ir_artifact.digest.is_canonical_sha256());
        assert_eq!(
            target_artifact.binary_artifact_digest_identity,
            Some(test_binary_artifact_digest_identity())
        );
        assert!(target_proof_consumer_accepted_kind(target_artifact, "target_semantics"));
        assert!(target_proof_consumer_accepted_kind(target_artifact, "target_refinement"));
        assert!(target_proof_consumer_accepted_kind(target_artifact, "unsupported_ledger"));
        for kind in [
            "binary_provenance",
            "checked_certificate",
            "proof_replay",
            "unsupported_ledger",
            "target_refinement",
        ] {
            assert!(
                target_proof_consumer_accepted_evidence_kind(target_artifact, kind),
                "missing accepted Rust {kind} evidence artifact in {target_artifact:?}"
            );
        }
        assert!(target_proof_consumer_has_empty_unsupported_ledger_evidence(target_artifact));
        assert!(rust_target_proof_consumer_evidence_covers_output(target_artifact, rust));
        assert!(target_proof_consumer_artifact_digest_accepted_for_output(rust, target_artifact));
        assert!(output_target_consumer_accepted_by_proof_model(rust));
        assert!(reconstruction_target_consumer_accepted_by_proof_model(&artifact.reconstruction));
        assert!(reconstruction_allows_artifact_proof_grade(&artifact.reconstruction));
    }

    #[test]
    fn target_consumer_rejects_rust_missing_compile_back_evidence_artifact() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
        let mut rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust proof-grade output")
            .clone();
        let mut target_artifact = target_proof_consumer_artifact_digest_records(&rust)
            .into_iter()
            .next()
            .expect("Rust target proof-consumer artifact digest");
        target_artifact
            .evidence_artifacts
            .retain(|artifact| artifact.kind != "checked_certificate");
        refresh_target_consumer_artifact_digest(&mut target_artifact);
        replace_target_consumer_artifact_digest(&mut rust, &target_artifact);

        assert!(target_proof_consumer_artifact_digest_matches_material(&target_artifact));
        assert!(!rust_target_proof_consumer_evidence_covers_output(&target_artifact, &rust));
        assert!(!target_proof_consumer_artifact_digest_accepted_for_output(
            &rust,
            &target_artifact
        ));
        assert!(!output_target_consumer_accepted_by_proof_model(&rust));
    }

    #[test]
    fn target_consumer_rejects_rust_stale_compile_back_evidence_with_fresh_digests() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
        let mut rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust proof-grade output")
            .clone();
        let mut target_artifact = target_proof_consumer_artifact_digest_records(&rust)
            .into_iter()
            .next()
            .expect("Rust target proof-consumer artifact digest");

        {
            let compile_back_evidence = target_artifact
                .evidence_artifacts
                .iter_mut()
                .find(|artifact| artifact.kind == "target_refinement")
                .expect("compile-back target refinement evidence artifact");
            let mut detail: RustCompileBackEvidenceArtifactDetail =
                serde_json::from_str(&compile_back_evidence.detail)
                    .expect("compile-back evidence detail should parse");
            detail.lifted_binary_trust_ir_sha256 =
                "0000000000000000000000000000000000000000000000000000000000000000".to_string();
            compile_back_evidence.detail =
                serde_json::to_string(&detail).expect("stale compile-back detail should serialize");
            refresh_target_consumer_evidence_artifact_digest(compile_back_evidence);
        }
        refresh_target_consumer_artifact_digest(&mut target_artifact);
        replace_target_consumer_artifact_digest(&mut rust, &target_artifact);

        assert!(target_proof_consumer_artifact_digest_matches_material(&target_artifact));
        assert!(
            target_artifact
                .evidence_artifacts
                .iter()
                .filter(|artifact| artifact.kind == "target_refinement")
                .all(target_proof_consumer_evidence_artifact_digest_matches_material)
        );
        assert!(!rust_target_proof_consumer_evidence_covers_output(&target_artifact, &rust));
        assert!(!target_proof_consumer_artifact_digest_accepted_for_output(
            &rust,
            &target_artifact
        ));
        assert!(!output_target_consumer_accepted_by_proof_model(&rust));
    }

    #[test]
    fn target_consumer_rejects_rust_stale_lifted_trust_ir_artifact_with_fresh_digest() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
        let mut rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust proof-grade output")
            .clone();
        let mut target_artifact = target_proof_consumer_artifact_digest_records(&rust)
            .into_iter()
            .next()
            .expect("Rust target proof-consumer artifact digest");
        target_artifact.lifted_trust_ir_artifact.digest = BinaryArtifactDigest::sha256(
            "3333333333333333333333333333333333333333333333333333333333333333",
        );
        refresh_target_consumer_artifact_digest(&mut target_artifact);
        replace_target_consumer_artifact_digest(&mut rust, &target_artifact);

        assert!(target_proof_consumer_artifact_digest_matches_material(&target_artifact));
        assert!(
            target_artifact
                .evidence_artifacts
                .iter()
                .all(target_proof_consumer_evidence_artifact_digest_matches_material)
        );
        assert!(!rust_target_proof_consumer_evidence_covers_output(&target_artifact, &rust));
        assert!(!target_proof_consumer_artifact_digest_accepted_for_output(
            &rust,
            &target_artifact
        ));
        assert!(!output_target_consumer_accepted_by_proof_model(&rust));
    }

    #[test]
    fn target_consumer_rejects_rust_stale_provenance_evidence_with_fresh_digests() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
        let mut rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust proof-grade output")
            .clone();
        let mut target_artifact = target_proof_consumer_artifact_digest_records(&rust)
            .into_iter()
            .next()
            .expect("Rust target proof-consumer artifact digest");

        {
            let provenance_evidence = target_artifact
                .evidence_artifacts
                .iter_mut()
                .find(|artifact| artifact.kind == "binary_provenance")
                .expect("binary provenance evidence artifact");
            let mut origin: BinaryOrigin = serde_json::from_str(&provenance_evidence.detail)
                .expect("binary provenance evidence detail should parse");
            origin.instruction_bytes = vec![0xff];
            provenance_evidence.detail =
                serde_json::to_string(&origin).expect("stale provenance detail should serialize");
            refresh_target_consumer_evidence_artifact_digest(provenance_evidence);
        }
        refresh_target_consumer_artifact_digest(&mut target_artifact);
        replace_target_consumer_artifact_digest(&mut rust, &target_artifact);

        assert!(target_proof_consumer_artifact_digest_matches_material(&target_artifact));
        assert!(
            target_artifact
                .evidence_artifacts
                .iter()
                .filter(|artifact| artifact.kind == "binary_provenance")
                .all(target_proof_consumer_evidence_artifact_digest_matches_material)
        );
        assert!(!rust_target_proof_consumer_evidence_covers_output(&target_artifact, &rust));
        assert!(!target_proof_consumer_artifact_digest_accepted_for_output(
            &rust,
            &target_artifact
        ));
        assert!(!output_target_consumer_accepted_by_proof_model(&rust));
    }

    #[test]
    fn target_consumer_accepts_rust_formula_evidence_continuity() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
        let formula = install_rust_preserved_formula_target_artifact(&mut artifact);
        let rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust proof-grade output");
        let target_artifact = target_proof_consumer_artifact_digest_records(rust)
            .into_iter()
            .next()
            .expect("Rust target proof-consumer artifact digest");
        let formula_evidence = target_artifact
            .evidence_artifacts
            .iter()
            .find(|artifact| artifact.kind == "symbolic_formula")
            .expect("symbolic formula evidence artifact");

        assert!(target_proof_consumer_accepted_kind(&target_artifact, "symbolic_formula"));
        assert!(target_proof_consumer_accepted_evidence_kind(&target_artifact, "symbolic_formula"));
        assert!(symbolic_formula_evidence_detail_matches_formula(
            &formula_evidence.detail,
            &formula
        ));
        assert!(target_proof_consumer_formula_evidence_covers_output(&target_artifact, rust));
        assert!(target_proof_consumer_artifact_digest_accepted_for_output(rust, &target_artifact));
        assert!(output_target_consumer_accepted_by_proof_model(rust));
        assert!(output_symbolic_formulas_consumed_by_proof_model(rust));
    }

    #[test]
    fn target_consumer_rejects_rust_missing_formula_evidence_artifact() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
        install_rust_preserved_formula_target_artifact(&mut artifact);
        let mut rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust proof-grade output")
            .clone();
        let mut target_artifact = target_proof_consumer_artifact_digest_records(&rust)
            .into_iter()
            .next()
            .expect("Rust target proof-consumer artifact digest");
        target_artifact.evidence_artifacts.retain(|artifact| artifact.kind != "symbolic_formula");
        refresh_target_consumer_artifact_digest(&mut target_artifact);
        replace_target_consumer_artifact_digest(&mut rust, &target_artifact);

        assert!(target_proof_consumer_artifact_digest_matches_material(&target_artifact));
        assert!(!target_proof_consumer_formula_evidence_covers_output(&target_artifact, &rust));
        assert!(!target_proof_consumer_artifact_digest_accepted_for_output(
            &rust,
            &target_artifact
        ));
        assert!(!output_target_consumer_accepted_by_proof_model(&rust));
    }

    #[test]
    fn target_consumer_rejects_rust_stale_formula_evidence_detail_with_fresh_digests() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
        let formula = install_rust_preserved_formula_target_artifact(&mut artifact);
        let mut rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust proof-grade output")
            .clone();
        let mut target_artifact = target_proof_consumer_artifact_digest_records(&rust)
            .into_iter()
            .next()
            .expect("Rust target proof-consumer artifact digest");
        let mut stale_formula = formula.clone();
        stale_formula.formula = trust_types::Formula::Bool(false);
        let target_output = target_artifact.target_output.clone();
        let stale_detail =
            target_proof_consumer_symbolic_formula_evidence_detail(&stale_formula, &target_output)
                .expect("stale formula evidence detail");
        let formula_evidence = target_artifact
            .evidence_artifacts
            .iter_mut()
            .find(|artifact| artifact.kind == "symbolic_formula")
            .expect("symbolic formula evidence artifact");
        formula_evidence.detail = stale_detail;
        formula_evidence.digest = target_proof_consumer_evidence_artifact_digest(
            &TargetProofConsumerEvidenceArtifactDigestMaterial::from_record(formula_evidence),
        )
        .expect("stale formula evidence artifact should hash");
        refresh_target_consumer_artifact_digest(&mut target_artifact);
        replace_target_consumer_artifact_digest(&mut rust, &target_artifact);

        assert!(target_proof_consumer_artifact_digest_matches_material(&target_artifact));
        assert!(target_artifact.evidence_artifacts.iter().any(|artifact| {
            artifact.kind == "symbolic_formula"
                && target_proof_consumer_evidence_artifact_digest_matches_material(artifact)
                && !target_proof_consumer_formula_evidence_matches_formula(artifact, &formula)
        }));
        assert!(!target_proof_consumer_formula_evidence_covers_output(&target_artifact, &rust));
        assert!(!target_proof_consumer_artifact_digest_accepted_for_output(
            &rust,
            &target_artifact
        ));
        assert!(!output_target_consumer_accepted_by_proof_model(&rust));
    }

    #[test]
    fn target_consumer_rejects_rust_extra_formula_evidence_artifact() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
        install_rust_preserved_formula_target_artifact(&mut artifact);
        let mut rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust proof-grade output")
            .clone();
        let mut target_artifact = target_proof_consumer_artifact_digest_records(&rust)
            .into_iter()
            .next()
            .expect("Rust target proof-consumer artifact digest");
        let extra_formula = PreservedSymbolicFormula {
            target: DecompileTarget::Rust,
            function: Some("extra_formula".to_string()),
            block: Some(0),
            statement_index: Some(1),
            location: "rust-output::extra_formula".to_string(),
            formula: trust_types::Formula::Bool(true),
        };
        let extra_detail = target_proof_consumer_symbolic_formula_evidence_detail(
            &extra_formula,
            &target_artifact.target_output,
        )
        .expect("extra formula evidence detail");
        let extra_artifact = target_proof_consumer_evidence_artifact(
            "rust",
            "symbolic_formula",
            &preserved_symbolic_formula_evidence_identifier(&extra_formula)
                .expect("extra formula identifier"),
            SYMBOLIC_FORMULA_SCHEMA,
            &target_artifact.target_output,
            true,
            &extra_detail,
        )
        .expect("extra formula evidence artifact");
        target_artifact.evidence_artifacts.push(extra_artifact);
        refresh_target_consumer_artifact_digest(&mut target_artifact);
        replace_target_consumer_artifact_digest(&mut rust, &target_artifact);

        assert!(target_proof_consumer_artifact_digest_matches_material(&target_artifact));
        assert!(
            target_artifact
                .evidence_artifacts
                .iter()
                .all(target_proof_consumer_evidence_artifact_digest_matches_material)
        );
        assert!(!target_proof_consumer_formula_evidence_covers_output(&target_artifact, &rust));
        assert!(!target_proof_consumer_artifact_digest_accepted_for_output(
            &rust,
            &target_artifact
        ));
        assert!(!output_target_consumer_accepted_by_proof_model(&rust));
    }

    #[test]
    fn target_consumer_rejects_rust_missing_structured_target_digest() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
        let mut rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust proof-grade output")
            .clone();
        rust.diagnostics.retain(|diagnostic| !target_consumer_acceptance_diagnostic(diagnostic));
        rust.diagnostics.push(
            "target-consumer=accepted; target proof consumer accepted stale text-only Rust claim"
                .to_string(),
        );

        assert!(target_proof_consumer_artifact_digest_records(&rust).is_empty());
        assert!(!output_target_consumer_accepted_by_proof_model(&rust));
        assert!(!reconstruction_target_consumer_accepted_by_proof_model(&ReconstructionSummary {
            target: DecompileTarget::Rust,
            outputs: vec![rust],
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }));
    }

    #[test]
    fn target_consumer_rejects_rust_stale_artifact_digest() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
        let mut rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust proof-grade output")
            .clone();
        let mut target_artifact = target_proof_consumer_artifact_digest_records(&rust)
            .into_iter()
            .next()
            .expect("Rust target proof-consumer artifact digest");
        target_artifact.target_output.push_str(":stale");
        replace_target_consumer_artifact_digest(&mut rust, &target_artifact);

        assert!(!target_proof_consumer_artifact_digest_matches_material(&target_artifact));
        assert!(!output_target_consumer_accepted_by_proof_model(&rust));
    }

    #[test]
    fn target_consumer_rejects_rust_unsupported_ledger_mismatch() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
        let mut rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust proof-grade output")
            .clone();
        let mut target_artifact = target_proof_consumer_artifact_digest_records(&rust)
            .into_iter()
            .next()
            .expect("Rust target proof-consumer artifact digest");
        let ledger = target_artifact
            .unsupported_ledger_evidence
            .first_mut()
            .expect("unsupported-ledger evidence");
        ledger.unsupported_records = 1;
        ledger.verification_unsupported = 1;
        ledger.unsupported_ledger_eliminated = false;
        target_artifact.artifact_digest = target_proof_consumer_artifact_digest(
            &TargetProofConsumerArtifactDigestMaterial::from_record(&target_artifact),
        )
        .expect("mutated Rust target artifact digest should hash");
        replace_target_consumer_artifact_digest(&mut rust, &target_artifact);

        assert!(target_proof_consumer_artifact_digest_matches_material(&target_artifact));
        assert!(!target_proof_consumer_has_empty_unsupported_ledger_evidence(&target_artifact));
        assert!(!target_proof_consumer_artifact_digest_accepted_for_output(
            &rust,
            &target_artifact
        ));
        assert!(!output_target_consumer_accepted_by_proof_model(&rust));
    }

    #[test]
    fn target_consumer_rejects_mixed_rust_and_rejected_wasm_claimed_targets() {
        let mut artifact = synthetic_checked_binary_artifact_for_rust_reconstruction_gate();
        install_synthetic_proof_grade_rust_reconstruction(&mut artifact);
        let rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust proof-grade output")
            .clone();
        let mut rejected_wasm = accepted_wasm_scalar_bool_target_output("mixed_rust_wasm_rejected");
        rejected_wasm.diagnostics.retain(|diagnostic| {
            !diagnostic.starts_with(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
        });
        rejected_wasm.target_validation_blockers.push(TargetValidationBlocker {
            target: DecompileTarget::Wasm,
            function: Some("mixed_rust_wasm_rejected".to_string()),
            code: "target-proof-consumer-artifact-digest".to_string(),
            stage: "trust-wasm-bridge::target-validation".to_string(),
            feature: "target-proof-consumer-artifact-digest".to_string(),
            reason: "claimed Wasm target path lacks accepted target proof-consumer digest"
                .to_string(),
            origin: None,
            diagnostics: vec!["proof-grade=false".to_string()],
        });

        assert!(output_target_consumer_accepted_by_proof_model(&rust));
        assert!(!output_target_consumer_accepted_by_proof_model(&rejected_wasm));
        assert!(!reconstruction_target_consumer_accepted_by_proof_model(&ReconstructionSummary {
            target: DecompileTarget::Rust,
            outputs: vec![rust, rejected_wasm],
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }));
    }

    #[test]
    fn wasm_target_proof_consumer_rejects_mismatched_lifted_trust_ir_artifact_digest() {
        const BOUND_TRUST_IR_DIGEST: &str =
            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
        let mut conversion = exact_wasm_non_empty_scalar_conversion("wasm_digest_binding");
        conversion.trust_level = TrustLevel::ProofGrade;
        let lifted_trust_ir_digest = conversion
            .lifted_trust_ir_artifact_digest
            .clone()
            .expect("exact Wasm fixture carries a lifted TrustIr digest");
        conversion.bound_lifted_trust_ir_artifact_digest = Some(BOUND_TRUST_IR_DIGEST.to_string());

        let proof_consumer = conversion.target_proof_consumer_evidence();

        assert_eq!(proof_consumer.status, trust_wasm_bridge::WasmProofConsumerStatus::Rejected);
        assert!(proof_consumer.target_semantics_consumed);
        assert_eq!(
            proof_consumer.binding.status,
            trust_wasm_bridge::WasmProofConsumerStatus::Rejected
        );
        assert_eq!(
            proof_consumer.binding.lifted_trust_ir_artifact_digest.as_deref(),
            Some(lifted_trust_ir_digest.as_str())
        );
        assert_eq!(
            proof_consumer.binding.bound_lifted_trust_ir_artifact_digest.as_deref(),
            Some(BOUND_TRUST_IR_DIGEST)
        );
        assert!(!proof_consumer.binding.lifted_trust_ir_artifact_digest_matched);
        assert!(proof_consumer.blockers.iter().any(|blocker| {
            blocker.code == "lifted-trust_ir-artifact-digest-mismatch"
                && blocker.detail.contains(&lifted_trust_ir_digest)
                && blocker.detail.contains(BOUND_TRUST_IR_DIGEST)
        }));
        assert!(!conversion.is_accepted());
    }

    #[cfg(feature = "trust-cg")]
    #[test]
    fn release_gate_recognizes_bounded_empty_trust_cg_and_wasm_consumed_targets() {
        let certificate_sha = "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
        let replay_sha = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
        let certificate_status = ProofCertificateStatus::Checked {
            checker: "trust-target-consumer-check".to_string(),
            format: "lfsc".to_string(),
            sha256: Some(certificate_sha.to_string()),
        };
        let certificate_json =
            serde_json::to_string(&certificate_status).expect("certificate status serializes");
        let certificate_attrs = format!(
            r#"[schema=str:"trust-types.CheckedCertificate@1"] [source=str:"bounded-empty-cert"] [status_json=str:{certificate_json:?}] [checker=str:"trust-target-consumer-check"] [format=str:"lfsc"] [sha256=str:"{certificate_sha}"] [certificate_checked=str:"true"] [target_semantics_consumed=str:"false"]"#
        );
        let replay_attrs = format!(
            r#"[schema=str:"trust-types.ProofReplay@1"] [source=str:"bounded-empty-replay"] [replay_status=str:"replayed"] [artifact_sha256=str:"{replay_sha}"] [exact_replay_checked=str:"true"] [target_semantics_consumed=str:"false"]"#
        );
        let canonical = canonical_bounded_empty_release_gate_trust_ir(
            "bounded_empty_release_gate",
            &trust_types::Formula::Bool(true),
            EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS,
            &certificate_attrs,
            &replay_attrs,
            EXACT_CANONICAL_UNSUPPORTED_LEDGER_ATTRS,
        );

        let trust_cg_conversion = trust_cg_bridge::lower_canonical_trust_ir_to_lir(&canonical)
            .expect("bounded empty trust_cg target consumer fixture should inspect");
        assert!(trust_cg_conversion.lir.is_empty());
        assert_eq!(
            trust_cg_conversion.trust_cg_validation,
            trust_cg_bridge::BinaryTrustCgValidationStatus::Rejected
        );
        assert_eq!(trust_cg_conversion.trust_level, TrustLevel::Rejected);
        assert!(trust_cg_conversion.provenance_evidence[0].target_semantics_consumed);
        assert!(trust_cg_conversion.checked_certificate_evidence[0].target_semantics_consumed);
        assert!(trust_cg_conversion.proof_replay_evidence[0].target_semantics_consumed);
        assert!(
            !trust_cg_conversion.validation_blockers.iter().any(|blocker| {
                matches!(
                    blocker.code.as_str(),
                    "binary-provenance-not-consumed-by-target-semantics"
                        | "checked-certificate-not-consumed-by-target-semantics"
                        | "proof-replay-not-consumed-by-target-semantics"
                )
            }),
            "{:?}",
            trust_cg_conversion.validation_blockers
        );
        let trust_cg_proof_consumer = trust_cg_conversion.target_proof_consumer_evidence();
        assert_eq!(
            trust_cg_proof_consumer.status,
            trust_cg_bridge::BinaryTrustCgProofConsumerStatus::Accepted
        );
        assert!(trust_cg_proof_consumer.target_semantics_consumed);
        assert!(trust_cg_proof_consumer.blockers.is_empty());
        assert_eq!(
            trust_cg_proof_consumer.binding.target_output,
            "trust_cg-lir:blocked:no-emitted-functions"
        );

        let wasm_conversion = trust_wasm_bridge::convert_canonical_trust_ir_to_wat(&canonical);
        assert!(wasm_conversion.wat.is_none());
        assert_eq!(
            wasm_conversion.wasm_validation,
            trust_wasm_bridge::WasmTargetValidationStatus::Rejected
        );
        assert_eq!(wasm_conversion.trust_level, TrustLevel::Rejected);
        assert!(wasm_conversion.provenance_evidence[0].target_semantics_consumed);
        assert!(wasm_conversion.checked_certificate_evidence[0].target_semantics_consumed);
        assert!(wasm_conversion.proof_replay_evidence[0].target_semantics_consumed);
        assert!(
            !wasm_conversion.validation_blockers.iter().any(|blocker| {
                matches!(
                    blocker.code.as_str(),
                    "binary-provenance-not-consumed-by-target-semantics"
                        | "checked-certificate-not-consumed-by-target-semantics"
                        | "proof-replay-not-consumed-by-target-semantics"
                )
            }),
            "{:?}",
            wasm_conversion.validation_blockers
        );
        let wasm_proof_consumer = wasm_conversion.target_proof_consumer_evidence();
        assert_eq!(
            wasm_proof_consumer.status,
            trust_wasm_bridge::WasmProofConsumerStatus::Rejected
        );
        assert!(wasm_proof_consumer.target_semantics_consumed);
        assert!(
            wasm_proof_consumer
                .blockers
                .iter()
                .any(|blocker| blocker.code == "unsupported-ledger-not-empty")
        );
        assert_eq!(wasm_proof_consumer.binding.target_output, "wat:blocked:no-emitted-module");
        assert_eq!(
            wasm_proof_consumer.binding.status,
            trust_wasm_bridge::WasmProofConsumerStatus::Rejected
        );
    }

    #[cfg(feature = "trust-cg")]
    #[test]
    fn release_gate_keeps_non_empty_unconsumed_target_blockers_closed() {
        use trust_types::{ProofStrength, VcKind};

        let mut lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        lifted.functions[0].trust_ir_body = constant_return_trust_ir("proved_fn", 7).body;
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustCgText]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic proved trust_cg artifact");

        install_test_binary_artifact_digest_metadata(&mut artifact);
        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );

        assert!(binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(artifact_source_provenance_allows_binary_proof_grade(&artifact));
        let trust_cg = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::TrustCg)
            .expect("trust-cg output");
        assert!(
            trust_cg
                .target_validation_blockers
                .iter()
                .any(|blocker| blocker.feature == "missing-target-semantic-validation"),
            "{:?}",
            trust_cg.target_validation_blockers
        );
        assert!(!reconstruction_allows_artifact_proof_grade(&artifact.reconstruction));
        assert!(!apply_binary_proof_grade_release_gate(&mut artifact));
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);
    }

    #[test]
    fn checked_replayed_binary_vcs_do_not_consume_symbolic_formula_target_semantics() {
        use trust_types::{BinaryVerificationStatus, ProofStrength, VcKind};

        let mut lifted = synthetic_lifted_binary_with_source(
            &[("symbolic_proved_fn", 0x401000)],
            &[(0x401000, "src/symbolic.rs", 1, 1)],
        );
        lifted.functions[0].trust_ir_body = symbolic_return_trust_ir("symbolic_proved_fn").body;
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            synthetic_vc("symbolic_proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic proved symbolic artifact");

        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );

        assert!(
            binary_proof_grade_release_gate_accepts(&artifact.verification),
            "{:?}",
            artifact.verification.solver_dispatch
        );
        assert!(
            source_provenance_allows_artifact_proof_grade(&artifact.source_provenance),
            "{:?}",
            artifact.source_provenance
        );
        assert_eq!(artifact.reconstruction.validation, ReconstructionValidationStatus::Validated);
        let output = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::TrustIr)
            .expect("TrustIr output");
        assert_eq!(output.preserved_symbolic_formulas.len(), 1);
        assert_symbolic_proof_consumer_blocker(
            output,
            &DecompileTarget::TrustIr,
            "symbolic_proved_fn",
        );
        assert!(
            !reconstruction_allows_artifact_proof_grade(&artifact.reconstruction),
            "symbolic formula target blockers must keep reconstruction fail-closed"
        );

        assert!(!apply_binary_proof_grade_release_gate(&mut artifact));

        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Proved);
        assert_eq!(artifact.verification.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].verification.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);
    }

    #[test]
    fn reconstruction_gate_requires_schema_aware_symbolic_formula_consumer_evidence() {
        let preserved_formula = PreservedSymbolicFormula {
            target: DecompileTarget::TrustIr,
            function: Some("symbolic_proved_fn".to_string()),
            block: Some(0),
            statement_index: Some(0),
            location: "bb0[0].rvalue".to_string(),
            formula: trust_types::Formula::Bool(true),
        };
        let unconsumed = ReconstructionSummary {
            target: DecompileTarget::TrustIr,
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            outputs: vec![DecompiledOutput {
                target: DecompileTarget::TrustIr,
                validation: ReconstructionValidationStatus::Validated,
                trust_level: TrustLevel::ProofGrade,
                preserved_symbolic_formulas: vec![preserved_formula.clone()],
                ..Default::default()
            }],
            ..Default::default()
        };
        let untyped_consumption_claim = ReconstructionSummary {
            outputs: vec![DecompiledOutput {
                diagnostics: vec![
                    "target-consumer=accepted; trust_symbolic.formula=consumed".to_string(),
                ],
                ..unconsumed.outputs[0].clone()
            }],
            ..unconsumed.clone()
        };
        let consumed = ReconstructionSummary {
            outputs: vec![DecompiledOutput {
                diagnostics: vec![schema_aware_symbolic_formula_consumer_diagnostic(
                    &preserved_formula,
                )],
                ..unconsumed.outputs[0].clone()
            }],
            ..unconsumed.clone()
        };

        assert!(!reconstruction_symbolic_formulas_consumed_by_proof_model(&unconsumed));
        assert!(!reconstruction_allows_artifact_proof_grade(&unconsumed));
        assert!(!reconstruction_symbolic_formulas_consumed_by_proof_model(
            &untyped_consumption_claim
        ));
        assert!(!reconstruction_allows_artifact_proof_grade(&untyped_consumption_claim));
        assert!(reconstruction_symbolic_formulas_consumed_by_proof_model(&consumed));
        assert!(reconstruction_allows_artifact_proof_grade(&consumed));
    }

    #[test]
    fn checked_unsat_certificate_without_replay_keeps_binary_release_gate_closed() {
        use trust_types::{BinaryVerificationStatus, ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic proved artifact");

        mark_dispatches_checked_with_exact_instruction_provenance(
            &mut artifact.verification.solver_dispatch,
        );
        mark_dispatches_checked_with_exact_instruction_provenance(
            &mut artifact.functions[0].verification.solver_dispatch,
        );

        assert_eq!(artifact.verification.replay, ReplayStatus::NotAttempted);
        assert!(!binary_dispatch_satisfies_release_replay_semantics(
            &artifact.verification.solver_dispatch[0]
        ));
        assert!(!binary_dispatch_has_proof_grade_evidence(
            &artifact.verification.solver_dispatch[0]
        ));
        assert!(!binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(!apply_binary_proof_grade_release_gate(&mut artifact));

        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Proved);
        assert_eq!(artifact.verification.trust_level, TrustLevel::Partial);
        assert_eq!(artifact.verification.replay, ReplayStatus::NotAttempted);
        assert_eq!(artifact.verification.solver_dispatch[0].replay, ReplayStatus::NotAttempted);
        assert!(artifact.verification.proof_certificate.is_checked());
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].verification.trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.functions[0].verification.replay, ReplayStatus::NotAttempted);
        assert_ne!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);
    }

    #[test]
    fn solver_dispatch_records_copy_binary_artifact_digest_identity_from_metadata() {
        use trust_types::{ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact =
            decompilation_artifact_from_lifted(8, &options, &lifted).expect("synthetic artifact");
        install_test_binary_artifact_digest_metadata(&mut artifact);

        attach_binary_verification_results(&mut artifact, &lifted, &results);

        let expected = Some(test_binary_artifact_digest_identity());
        let artifact_dispatch = &artifact.verification.solver_dispatch[0];
        let function_dispatch = &artifact.functions[0].verification.solver_dispatch[0];
        assert_eq!(artifact_dispatch.binary_artifact_digest_identity, expected);
        assert_eq!(function_dispatch.binary_artifact_digest_identity, expected);
        assert!(artifact_dispatch.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("binary artifact digest identity attached to solver dispatch")
        }));
        assert!(binary_dispatch_has_replay_digest_identity(artifact_dispatch));
    }

    #[test]
    fn sat_witness_requires_actual_replay_even_with_checked_unsat_certificate_only_evidence() {
        use trust_types::{
            BinaryVerificationStatus, Counterexample, CounterexampleValue, ProofStrength, VcKind,
        };

        let lifted = synthetic_lifted_binary_with_source(
            &[("mixed_fn", 0x401000)],
            &[(0x401000, "src/mixed.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![
            (
                synthetic_vc("mixed_fn", 0x401000, VcKind::DivisionByZero),
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 3,
                    counterexample: Some(Counterexample::new(vec![(
                        "denominator".to_string(),
                        CounterexampleValue::Uint(0),
                    )])),
                },
            ),
            (
                synthetic_vc(
                    "mixed_fn",
                    0x401000,
                    VcKind::Assertion { message: "guard holds".to_string() },
                ),
                VerificationResult::Proved {
                    solver: "ay".into(),
                    time_ms: 2,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: Some(b"checked externally".to_vec()),
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            ),
        ];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic mixed artifact");

        mark_dispatches_with_exact_instruction_provenance(
            &mut artifact.verification.solver_dispatch,
        );
        mark_dispatches_with_exact_instruction_provenance(
            &mut artifact.functions[0].verification.solver_dispatch,
        );
        mark_unsat_dispatches_checked(&mut artifact.verification.solver_dispatch);
        mark_unsat_dispatches_checked(&mut artifact.functions[0].verification.solver_dispatch);

        let sat_dispatch = artifact
            .verification
            .solver_dispatch
            .iter()
            .find(|dispatch| dispatch.status == SolverDispatchStatus::Sat)
            .expect("SAT dispatch");
        let unsat_dispatch = artifact
            .verification
            .solver_dispatch
            .iter()
            .find(|dispatch| dispatch.status == SolverDispatchStatus::Unsat)
            .expect("UNSAT dispatch");

        assert!(!binary_dispatch_satisfies_release_replay_semantics(unsat_dispatch));
        assert!(!binary_dispatch_satisfies_release_replay_semantics(sat_dispatch));
        let mut replayed_unsat_dispatch = unsat_dispatch.clone();
        replayed_unsat_dispatch.replay = ReplayStatus::Replayed;
        assert!(binary_dispatch_satisfies_release_replay_semantics(&replayed_unsat_dispatch));
        assert!(binary_dispatch_has_proof_grade_evidence(&replayed_unsat_dispatch));
        let mut replayed_sat_dispatch = sat_dispatch.clone();
        replayed_sat_dispatch.replay = ReplayStatus::Replayed;
        assert!(binary_dispatch_satisfies_release_replay_semantics(&replayed_sat_dispatch));
        assert!(!binary_dispatch_has_proof_grade_evidence(&replayed_sat_dispatch));

        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Mixed);
        assert!(!binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(!apply_binary_proof_grade_release_gate(&mut artifact));

        assert_eq!(artifact.verification.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].verification.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);
    }

    #[cfg(feature = "elf")]
    #[test]
    fn synthetic_real_binary_gate_requires_all_readback_inputs_to_align() {
        let aligned = synthetic_real_binary_release_gate_artifact();

        assert_eq!(aligned.binary.format, BinaryArtifactFormat::Elf);
        assert_eq!(aligned.binary.architecture, "AArch64");
        assert!(aligned.unsupported.records.is_empty(), "{:?}", aligned.unsupported.records);
        assert!(aligned.functions[0].unsupported.records.is_empty());
        assert_eq!(aligned.source_provenance.status, "exact");
        assert!(
            aligned.binary.digest_identity_allows_proof_grade(),
            "{:?}",
            aligned.binary.digest_identity_blockers()
        );
        assert!(artifact_source_provenance_allows_binary_proof_grade(&aligned));
        assert!(binary_proof_grade_release_gate_accepts(&aligned.verification));
        assert!(reconstruction_allows_artifact_proof_grade(&aligned.reconstruction));
        assert!(reconstruction_outputs_carry_binary_artifact_digest_identity(
            &aligned.reconstruction,
            &aligned.binary
        ));

        let mut promoted = aligned.clone();
        assert!(apply_binary_proof_grade_release_gate(&mut promoted));
        assert_eq!(promoted.verification.trust_level, TrustLevel::ProofGrade);
        assert_eq!(promoted.trust_level, TrustLevel::ProofGrade);
        assert_eq!(promoted.functions[0].verification.trust_level, TrustLevel::ProofGrade);
        assert_eq!(promoted.functions[0].trust_level, TrustLevel::ProofGrade);

        let bridge = trust_ir_checked_certificate_bridge_json(&promoted);
        let dispatches = bridge["dispatches"].as_array().expect("checked dispatch readback");
        assert_eq!(bridge["checked_dispatches"], 1);
        assert_eq!(bridge["invalid_checked_dispatches"], 0);
        assert_eq!(bridge["proof_grade_closed"], false);
        assert_eq!(bridge["release_gate"]["accepted"], true);
        assert_eq!(bridge["release_gate"]["blockers"], serde_json::json!([]));
        assert_eq!(bridge["release_gate"]["binary_artifact_identity_accepted"], true);
        assert_eq!(bridge["release_gate"]["target_reconstruction_accepted"], true);
        assert_eq!(bridge["release_gate"]["production_boundary_accepted"], true);
        assert_eq!(dispatches.len(), 1);
        assert_eq!(dispatches[0]["checker"], "ay-cert-readback");
        assert_eq!(dispatches[0]["format"], "lfsc-v1");
        assert_eq!(
            dispatches[0]["sha256"],
            "1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
        );
        assert_eq!(dispatches[0]["replay"], "Replayed");
        assert_eq!(dispatches[0]["proof_grade_eligible"], true);
        assert_eq!(dispatches[0]["origin"]["source"]["file"], "src/real_binary_gate.rs");
        assert_eq!(
            dispatches[0]["origin"]["instruction_bytes"],
            serde_json::json!([0xC0, 0x03, 0x5F, 0xD6])
        );

        let mut missing_certificate = aligned.clone();
        for dispatch in &mut missing_certificate.verification.solver_dispatch {
            dispatch.certificate = ProofCertificateStatus::Present {
                format: "raw-solver-proof".to_string(),
                sha256: Some("raw-only".to_string()),
                artifact_path: None,
            };
        }
        for dispatch in &mut missing_certificate.functions[0].verification.solver_dispatch {
            dispatch.certificate = ProofCertificateStatus::Present {
                format: "raw-solver-proof".to_string(),
                sha256: Some("raw-only".to_string()),
                artifact_path: None,
            };
        }
        assert!(!binary_proof_grade_release_gate_accepts(&missing_certificate.verification));
        let missing_certificate =
            assert_binary_release_gate_closed(missing_certificate, "checked certificate readback");
        let bridge = trust_ir_checked_certificate_bridge_json(&missing_certificate);
        assert_eq!(bridge["checked_dispatches"], 0);
        assert!(matches!(
            missing_certificate.verification.proof_certificate,
            ProofCertificateStatus::Unavailable { .. }
        ));

        let mut missing_replay = aligned.clone();
        for dispatch in &mut missing_replay.verification.solver_dispatch {
            dispatch.replay = ReplayStatus::NotAttempted;
        }
        for dispatch in &mut missing_replay.functions[0].verification.solver_dispatch {
            dispatch.replay = ReplayStatus::NotAttempted;
        }
        assert!(!binary_proof_grade_release_gate_accepts(&missing_replay.verification));
        let missing_replay = assert_binary_release_gate_closed(missing_replay, "exact replay");
        let bridge = trust_ir_checked_certificate_bridge_json(&missing_replay);
        assert_eq!(bridge["checked_dispatches"], 1);
        assert_eq!(bridge["invalid_checked_dispatches"], 1);
        assert_eq!(bridge["proof_grade_closed"], true);

        let mut missing_instruction_provenance = aligned.clone();
        for dispatch in &mut missing_instruction_provenance.verification.solver_dispatch {
            let origin = dispatch.origin.as_mut().expect("artifact dispatch origin");
            origin.instruction_size = Some(4);
            origin.instruction_bytes.clear();
        }
        for dispatch in
            &mut missing_instruction_provenance.functions[0].verification.solver_dispatch
        {
            let origin = dispatch.origin.as_mut().expect("function dispatch origin");
            origin.instruction_size = Some(4);
            origin.instruction_bytes.clear();
        }
        assert!(!binary_proof_grade_release_gate_accepts(
            &missing_instruction_provenance.verification
        ));
        let missing_instruction_provenance = assert_binary_release_gate_closed(
            missing_instruction_provenance,
            "exact instruction provenance",
        );
        let bridge = trust_ir_checked_certificate_bridge_json(&missing_instruction_provenance);
        assert_eq!(bridge["checked_dispatches"], 1);
        assert_eq!(bridge["invalid_checked_dispatches"], 1);
        assert_eq!(bridge["proof_grade_closed"], true);
        assert_eq!(bridge["dispatches"][0]["proof_grade_eligible"], false);

        let mut source_mismatch = aligned.clone();
        let forged_source = SourceSpan {
            file: "src/forged_gate.rs".to_string(),
            line_start: 88,
            col_start: 1,
            line_end: 88,
            col_end: 12,
        };
        for dispatch in &mut source_mismatch.verification.solver_dispatch {
            dispatch.origin.as_mut().expect("artifact dispatch origin").source =
                Some(forged_source.clone());
        }
        for dispatch in &mut source_mismatch.functions[0].verification.solver_dispatch {
            dispatch.origin.as_mut().expect("function dispatch origin").source =
                Some(forged_source.clone());
        }
        assert!(binary_proof_grade_release_gate_accepts(&source_mismatch.verification));
        assert!(!artifact_source_provenance_allows_binary_proof_grade(&source_mismatch));
        let source_mismatch =
            assert_binary_release_gate_closed(source_mismatch, "source provenance mismatch");
        let bridge = trust_ir_checked_certificate_bridge_json(&source_mismatch);
        assert_eq!(bridge["checked_dispatches"], 1);
        assert_eq!(bridge["invalid_checked_dispatches"], 1);
        assert_eq!(bridge["proof_grade_closed"], true);
        assert_eq!(bridge["dispatches"][0]["origin"]["source"]["file"], "src/forged_gate.rs");

        let mut binary_origin_mismatch = aligned.clone();
        for dispatch in &mut binary_origin_mismatch.verification.solver_dispatch {
            dispatch.origin.as_mut().expect("artifact dispatch origin").instruction_bytes =
                vec![0xC0, 0x03, 0x5F, 0xD7];
        }
        for dispatch in &mut binary_origin_mismatch.functions[0].verification.solver_dispatch {
            dispatch.origin.as_mut().expect("function dispatch origin").instruction_bytes =
                vec![0xC0, 0x03, 0x5F, 0xD7];
        }
        assert!(binary_proof_grade_release_gate_accepts(&binary_origin_mismatch.verification));
        assert!(!artifact_source_provenance_allows_binary_proof_grade(&binary_origin_mismatch));
        let binary_origin_mismatch = assert_binary_release_gate_closed(
            binary_origin_mismatch,
            "exact binary origin binding",
        );
        let bridge = trust_ir_checked_certificate_bridge_json(&binary_origin_mismatch);
        assert_eq!(bridge["checked_dispatches"], 1);
        assert_eq!(bridge["invalid_checked_dispatches"], 1);
        assert_eq!(bridge["proof_grade_closed"], true);
        assert_eq!(bridge["dispatches"][0]["proof_grade_eligible"], false);
        assert_eq!(
            bridge["dispatches"][0]["origin"]["instruction_bytes"],
            serde_json::json!([0xC0, 0x03, 0x5F, 0xD7])
        );

        let mut binary_artifact_identity_mismatch = aligned.clone();
        let forged_binary_path = Some("fixtures/forged-aarch64-ret.elf".to_string());
        binary_artifact_identity_mismatch.functions[0]
            .origin
            .as_mut()
            .expect("function origin")
            .binary_path = forged_binary_path.clone();
        for origin in &mut binary_artifact_identity_mismatch.functions[0].instruction_provenance {
            origin.binary_path = forged_binary_path.clone();
        }
        for dispatch in &mut binary_artifact_identity_mismatch.verification.solver_dispatch {
            dispatch.origin.as_mut().expect("artifact dispatch origin").binary_path =
                forged_binary_path.clone();
        }
        for dispatch in
            &mut binary_artifact_identity_mismatch.functions[0].verification.solver_dispatch
        {
            dispatch.origin.as_mut().expect("function dispatch origin").binary_path =
                forged_binary_path.clone();
        }
        assert!(binary_proof_grade_release_gate_accepts(
            &binary_artifact_identity_mismatch.verification
        ));
        assert!(!artifact_source_provenance_allows_binary_proof_grade(
            &binary_artifact_identity_mismatch
        ));
        let binary_artifact_identity_mismatch = assert_binary_release_gate_closed(
            binary_artifact_identity_mismatch,
            "binary artifact identity binding",
        );
        let bridge = trust_ir_checked_certificate_bridge_json(&binary_artifact_identity_mismatch);
        assert_eq!(bridge["checked_dispatches"], 1);
        assert_eq!(bridge["invalid_checked_dispatches"], 1);
        assert_eq!(bridge["proof_grade_closed"], true);
        assert_eq!(bridge["release_gate"]["accepted"], false);
        assert_eq!(bridge["release_gate"]["binary_artifact_identity_accepted"], false);
        assert!(
            bridge["release_gate"]["blockers"]
                .as_array()
                .expect("release gate blockers")
                .iter()
                .any(|blocker| blocker == "binary_artifact_identity_not_accepted")
        );
        assert_eq!(
            bridge["dispatches"][0]["origin"]["binary_path"],
            "fixtures/forged-aarch64-ret.elf"
        );

        let mut missing_parser_identity = aligned.clone();
        missing_parser_identity.binary.build_id = None;
        assert!(binary_proof_grade_release_gate_accepts(&missing_parser_identity.verification));
        assert!(!artifact_source_provenance_allows_binary_proof_grade(&missing_parser_identity));
        let missing_parser_identity = assert_binary_release_gate_closed(
            missing_parser_identity,
            "parser artifact identity binding",
        );
        assert_source_rewrite_authority_closed(
            &missing_parser_identity,
            "decompile artifact metadata identity",
        );
        let bridge = trust_ir_checked_certificate_bridge_json(&missing_parser_identity);
        assert_eq!(bridge["checked_dispatches"], 1);
        assert_eq!(bridge["invalid_checked_dispatches"], 1);
        assert_eq!(bridge["proof_grade_closed"], true);
        assert_eq!(bridge["release_gate"]["accepted"], false);
        assert_eq!(bridge["release_gate"]["binary_artifact_identity_accepted"], false);
        assert_eq!(bridge["dispatches"][0]["proof_grade_eligible"], false);
        assert!(
            bridge["release_gate"]["blockers"]
                .as_array()
                .expect("release gate blockers")
                .iter()
                .any(|blocker| blocker == "binary_artifact_identity_not_accepted")
        );

        let mut missing_root_digest = aligned.clone();
        missing_root_digest.binary.root_artifact_digest = None;
        assert!(binary_proof_grade_release_gate_accepts(&missing_root_digest.verification));
        assert!(!artifact_source_provenance_allows_binary_proof_grade(&missing_root_digest));
        let missing_root_digest =
            assert_binary_release_gate_closed(missing_root_digest, "root artifact digest");
        let bridge = trust_ir_checked_certificate_bridge_json(&missing_root_digest);
        assert_eq!(bridge["release_gate"]["binary_artifact_identity_accepted"], false);
        assert_eq!(bridge["dispatches"][0]["proof_grade_eligible"], false);
        assert!(
            missing_root_digest
                .binary
                .digest_identity_blockers()
                .iter()
                .any(|blocker| blocker == "missing root artifact SHA-256 digest")
        );

        let mut missing_selected_image = aligned.clone();
        missing_selected_image.binary.selected_image = None;
        assert!(binary_proof_grade_release_gate_accepts(&missing_selected_image.verification));
        assert!(!artifact_source_provenance_allows_binary_proof_grade(&missing_selected_image));
        let missing_selected_image =
            assert_binary_release_gate_closed(missing_selected_image, "selected image digest");
        let bridge = trust_ir_checked_certificate_bridge_json(&missing_selected_image);
        assert_eq!(bridge["release_gate"]["binary_artifact_identity_accepted"], false);
        assert_eq!(bridge["dispatches"][0]["proof_grade_eligible"], false);
        assert!(
            missing_selected_image
                .binary
                .digest_identity_blockers()
                .iter()
                .any(|blocker| blocker == "missing selected image digest/range")
        );

        let mut dispatch_selected_image_mismatch = aligned.clone();
        for dispatch in &mut dispatch_selected_image_mismatch.verification.solver_dispatch {
            dispatch
                .binary_artifact_digest_identity
                .as_mut()
                .and_then(|identity| identity.selected_image.as_mut())
                .expect("artifact dispatch selected image")
                .file_offset += 1;
        }
        for dispatch in
            &mut dispatch_selected_image_mismatch.functions[0].verification.solver_dispatch
        {
            dispatch
                .binary_artifact_digest_identity
                .as_mut()
                .and_then(|identity| identity.selected_image.as_mut())
                .expect("function dispatch selected image")
                .file_offset += 1;
        }
        assert!(binary_proof_grade_release_gate_accepts(
            &dispatch_selected_image_mismatch.verification
        ));
        assert!(!artifact_source_provenance_allows_binary_proof_grade(
            &dispatch_selected_image_mismatch
        ));
        let dispatch_selected_image_mismatch = assert_binary_release_gate_closed(
            dispatch_selected_image_mismatch,
            "matching selected image digest/range",
        );
        let bridge = trust_ir_checked_certificate_bridge_json(&dispatch_selected_image_mismatch);
        assert_eq!(bridge["release_gate"]["binary_artifact_identity_accepted"], false);
        assert_eq!(bridge["dispatches"][0]["binary_artifact_digest_identity_accepted"], false);

        let mut forged_root_digest = aligned.clone();
        forged_root_digest.binary.root_artifact_digest = Some(BinaryArtifactDigest::sha256(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        ));
        assert!(binary_proof_grade_release_gate_accepts(&forged_root_digest.verification));
        assert!(!artifact_source_provenance_allows_binary_proof_grade(&forged_root_digest));
        let forged_root_digest =
            assert_binary_release_gate_closed(forged_root_digest, "exact root artifact digest");
        let bridge = trust_ir_checked_certificate_bridge_json(&forged_root_digest);
        assert_eq!(bridge["release_gate"]["binary_artifact_identity_accepted"], false);
        assert_eq!(bridge["dispatches"][0]["proof_grade_eligible"], false);
        assert!(forged_root_digest.binary.digest_identity_blockers().iter().any(|blocker| {
            blocker == "root artifact digest does not match whole-file selected image digest"
        }));

        let mut missing_output_digest_identity = aligned.clone();
        for output in &mut missing_output_digest_identity.reconstruction.outputs {
            output.assumptions.retain(|assumption| {
                assumption.stage != RECONSTRUCTION_OUTPUT_BINARY_ARTIFACT_DIGEST_IDENTITY_STAGE
            });
        }
        assert!(binary_proof_grade_release_gate_accepts(
            &missing_output_digest_identity.verification
        ));
        assert!(artifact_source_provenance_allows_binary_proof_grade(
            &missing_output_digest_identity
        ));
        assert!(reconstruction_allows_artifact_proof_grade(
            &missing_output_digest_identity.reconstruction
        ));
        assert!(!reconstruction_outputs_carry_binary_artifact_digest_identity(
            &missing_output_digest_identity.reconstruction,
            &missing_output_digest_identity.binary
        ));
        let missing_output_digest_identity = assert_binary_release_gate_closed(
            missing_output_digest_identity,
            "reconstruction output binary artifact digest identity",
        );
        let bridge = trust_ir_checked_certificate_bridge_json(&missing_output_digest_identity);
        assert_eq!(bridge["checked_dispatches"], 1);
        assert_eq!(bridge["invalid_checked_dispatches"], 0);
        assert_eq!(bridge["proof_grade_closed"], true);
        assert_eq!(bridge["release_gate"]["target_reconstruction_accepted"], false);
        assert!(
            bridge["release_gate"]["blockers"]
                .as_array()
                .expect("release gate blockers")
                .iter()
                .any(|blocker| blocker == "target_reconstruction_not_accepted")
        );

        let mut unvalidated_reconstruction = aligned.clone();
        unvalidated_reconstruction.reconstruction.validation =
            ReconstructionValidationStatus::NotAttempted;
        for output in &mut unvalidated_reconstruction.reconstruction.outputs {
            output.validation = ReconstructionValidationStatus::NotAttempted;
        }
        assert!(binary_proof_grade_release_gate_accepts(&unvalidated_reconstruction.verification));
        assert!(artifact_source_provenance_allows_binary_proof_grade(&unvalidated_reconstruction));
        assert!(!reconstruction_allows_artifact_proof_grade(
            &unvalidated_reconstruction.reconstruction
        ));
        let unvalidated_reconstruction = assert_binary_release_gate_closed(
            unvalidated_reconstruction,
            "validated reconstruction",
        );
        let bridge = trust_ir_checked_certificate_bridge_json(&unvalidated_reconstruction);
        assert_eq!(bridge["checked_dispatches"], 1);
        assert_eq!(bridge["invalid_checked_dispatches"], 0);
        assert_eq!(bridge["proof_grade_closed"], true);
        assert_eq!(bridge["release_gate"]["accepted"], false);
        assert_eq!(bridge["release_gate"]["target_reconstruction_accepted"], false);
        assert!(
            bridge["release_gate"]["blockers"]
                .as_array()
                .expect("release gate blockers")
                .iter()
                .any(|blocker| blocker == "target_reconstruction_not_accepted")
        );

        let mut unsupported = aligned.clone();
        let record = unsupported_record(
            "trust-lift::semantic-lift",
            Some("aarch64"),
            Some(unsupported.functions[0].entry),
            Some(unsupported.functions[0].entry),
            "synthetic unsupported proof-grade blocker",
        );
        unsupported.unsupported.records.push(record.clone());
        unsupported.functions[0].unsupported.records.push(record);
        unsupported.verification.unsupported_ledger = unsupported.unsupported.clone();
        unsupported.functions[0].verification.unsupported_ledger =
            unsupported.functions[0].unsupported.clone();
        unsupported.verification.refresh_from_solver_dispatch();
        unsupported.functions[0].verification.refresh_from_solver_dispatch();
        assert!(!binary_proof_grade_release_gate_accepts(&unsupported.verification));
        let unsupported =
            assert_binary_release_gate_closed(unsupported, "empty unsupported ledger");
        let bridge = trust_ir_checked_certificate_bridge_json(&unsupported);
        assert_eq!(bridge["checked_dispatches"], 1);
        assert_eq!(bridge["invalid_checked_dispatches"], 1);
        assert_eq!(bridge["proof_grade_closed"], true);
    }

    #[cfg(feature = "elf")]
    #[test]
    fn trust_ir_bridge_fails_closed_without_dispatch_digest_identity() {
        let mut artifact = synthetic_real_binary_release_gate_artifact();
        assert!(binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(artifact_source_provenance_allows_binary_proof_grade(&artifact));

        for dispatch in &mut artifact.verification.solver_dispatch {
            dispatch.binary_artifact_digest_identity = None;
        }
        for dispatch in &mut artifact.functions[0].verification.solver_dispatch {
            dispatch.binary_artifact_digest_identity = None;
        }

        assert!(!binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(!artifact_source_provenance_allows_binary_proof_grade(&artifact));
        let artifact =
            assert_binary_release_gate_closed(artifact, "solver dispatch artifact digest identity");
        let bridge = trust_ir_checked_certificate_bridge_json(&artifact);
        assert_eq!(bridge["release_gate"]["binary_artifact_identity_accepted"], false);
        assert_eq!(
            bridge["dispatches"][0]["binary_artifact_digest_identity"],
            serde_json::Value::Null
        );
        assert_eq!(bridge["dispatches"][0]["binary_artifact_digest_identity_accepted"], false);
        assert!(bridge["diagnostics"].as_array().expect("bridge diagnostics").iter().any(
            |diagnostic| {
                diagnostic
                    .as_str()
                    .is_some_and(|text| text.contains("binary artifact digest identity"))
            }
        ));
    }

    #[cfg(feature = "elf")]
    #[test]
    fn trust_ir_bridge_fails_closed_on_dispatch_digest_identity_mismatch() {
        let mut artifact = synthetic_real_binary_release_gate_artifact();
        for dispatch in &mut artifact.verification.solver_dispatch {
            dispatch.binary_artifact_digest_identity =
                Some(mismatched_test_binary_artifact_digest_identity());
        }
        for dispatch in &mut artifact.functions[0].verification.solver_dispatch {
            dispatch.binary_artifact_digest_identity =
                Some(mismatched_test_binary_artifact_digest_identity());
        }

        assert!(!artifact_source_provenance_allows_binary_proof_grade(&artifact));
        let artifact =
            assert_binary_release_gate_closed(artifact, "matching solver dispatch artifact digest");
        let bridge = trust_ir_checked_certificate_bridge_json(&artifact);
        assert_eq!(bridge["release_gate"]["binary_artifact_identity_accepted"], false);
        assert_eq!(bridge["dispatches"][0]["binary_artifact_digest_identity_accepted"], false);
        assert_ne!(
            bridge["dispatches"][0]["binary_artifact_digest_identity"]["root_artifact_digest"]["value"],
            "1111111111111111111111111111111111111111111111111111111111111111"
        );
    }

    #[cfg(feature = "elf")]
    #[test]
    fn synthetic_real_binary_gate_requires_target_proof_consumer_acceptance() {
        let mut artifact = synthetic_real_binary_release_gate_artifact();
        assert!(binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(artifact_source_provenance_allows_binary_proof_grade(&artifact));
        assert!(reconstruction_allows_artifact_proof_grade(&artifact.reconstruction));

        let function_name = artifact.functions[0].name.clone();
        let origin = artifact.functions[0].origin.clone();
        let target_output = artifact
            .reconstruction
            .outputs
            .iter_mut()
            .find(|output| output.target == artifact.reconstruction.target)
            .expect("release target output");
        assert_eq!(target_output.validation, ReconstructionValidationStatus::Validated);
        target_output.target_validation_blockers.push(TargetValidationBlocker {
            target: DecompileTarget::TrustIr,
            function: Some(function_name),
            code: "target-proof-consumer-evidence".to_string(),
            stage: "trust-ir-bridge::target-validation".to_string(),
            feature: "target-proof-consumer-evidence".to_string(),
            reason:
                "TrustIr target proof consumer has not accepted formula, checked-certificate, replay, and provenance evidence together"
                    .to_string(),
            origin,
            diagnostics: vec![
                "blocker-code=target-proof-consumer-evidence".to_string(),
                "target-semantics-consumer=missing".to_string(),
                "checked-certificate=accepted".to_string(),
                "replay=accepted".to_string(),
                "source-provenance=accepted".to_string(),
                "reconstruction=validated".to_string(),
                "proof-grade=false".to_string(),
            ],
        });

        assert!(binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(artifact_source_provenance_allows_binary_proof_grade(&artifact));
        assert!(!reconstruction_allows_artifact_proof_grade(&artifact.reconstruction));

        let artifact =
            assert_binary_release_gate_closed(artifact, "target proof-consumer evidence");
        let bridge = trust_ir_checked_certificate_bridge_json(&artifact);
        assert_eq!(bridge["checked_dispatches"], 1);
        assert_eq!(bridge["invalid_checked_dispatches"], 0);
        assert_eq!(bridge["proof_grade_closed"], true);
        assert_eq!(bridge["release_gate"]["accepted"], false);
        assert_eq!(bridge["release_gate"]["unsupported_ledger_empty"], true);
        assert_eq!(bridge["release_gate"]["checked_certificates_accepted"], true);
        assert_eq!(bridge["release_gate"]["replay_accepted"], true);
        assert_eq!(bridge["release_gate"]["source_provenance_accepted"], true);
        assert_eq!(bridge["release_gate"]["binary_artifact_identity_accepted"], true);
        assert_eq!(bridge["release_gate"]["target_reconstruction_accepted"], false);
        assert_eq!(
            bridge["release_gate"]["blockers"],
            serde_json::json!(["target_reconstruction_not_accepted"])
        );
        assert_eq!(bridge["dispatches"][0]["proof_grade_eligible"], true);
    }

    #[test]
    fn trust_ir_json_preserves_checked_certificate_metadata_after_canonical_conversion() {
        use trust_types::{ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic proved artifact");

        install_test_binary_artifact_digest_metadata(&mut artifact);
        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );

        assert!(artifact.unsupported.records.is_empty(), "{:?}", artifact.unsupported.records);
        assert!(
            artifact_source_provenance_allows_binary_proof_grade(&artifact),
            "{:?}",
            artifact.source_provenance
        );
        assert!(
            reconstruction_allows_artifact_proof_grade(&artifact.reconstruction),
            "{:?}",
            artifact.reconstruction
        );
        assert!(apply_binary_proof_grade_release_gate(&mut artifact));
        assert_eq!(artifact.verification.trust_level, TrustLevel::ProofGrade);
        assert_eq!(artifact.trust_level, TrustLevel::ProofGrade);

        let output = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
            .expect("TrustIr JSON output");
        let json: serde_json::Value =
            serde_json::from_str(output.text.as_deref().expect("TrustIr JSON text"))
                .expect("TrustIr JSON should parse");
        let bridge = &json["checked_certificate_bridge"];
        let dispatches = bridge["dispatches"].as_array().expect("certificate dispatch metadata");

        assert_eq!(json["module"]["name"], "binary");
        assert_eq!(bridge["checked_dispatches"], 1);
        assert_eq!(bridge["invalid_checked_dispatches"], 0);
        assert_eq!(bridge["proof_grade_closed"], true);
        assert_eq!(bridge["release_gate"]["accepted"], false);
        assert_eq!(bridge["release_gate"]["production_boundary_accepted"], false);
        assert_eq!(dispatches.len(), 1);
        assert_eq!(dispatches[0]["id"], "proved_fn:0");
        assert_eq!(dispatches[0]["function"], "proved_fn");
        assert_eq!(dispatches[0]["checker"], "ay-cert-check");
        assert_eq!(dispatches[0]["format"], "lfsc");
        assert_eq!(dispatches[0]["sha256"], "checked-0");
        assert_eq!(dispatches[0]["replay"], "Replayed");
        assert_eq!(dispatches[0]["proof_grade_eligible"], true);
        assert_eq!(dispatches[0]["origin"]["instruction_address"], 0x401000);
        assert_eq!(dispatches[0]["origin"]["source"]["file"], "src/proved.rs");
    }

    #[test]
    fn exact_source_mismatch_keeps_trust_ir_proof_grade_closed() {
        use trust_types::{ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic proved artifact");

        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );
        let mismatched_source = SourceSpan {
            file: "src/forged.rs".to_string(),
            line_start: 99,
            col_start: 7,
            line_end: 99,
            col_end: 7,
        };
        for dispatch in artifact
            .verification
            .solver_dispatch
            .iter_mut()
            .chain(artifact.functions[0].verification.solver_dispatch.iter_mut())
        {
            dispatch.origin.as_mut().expect("binary origin").source =
                Some(mismatched_source.clone());
        }

        assert!(
            binary_proof_grade_release_gate_accepts(&artifact.verification),
            "binary evidence alone should be otherwise release-gate eligible"
        );
        assert!(source_provenance_allows_artifact_proof_grade(&artifact.source_provenance));
        assert!(!artifact_source_provenance_allows_binary_proof_grade(&artifact));
        assert!(artifact.unsupported.records.is_empty(), "{:?}", artifact.unsupported.records);
        assert_eq!(artifact.reconstruction.validation, ReconstructionValidationStatus::Validated);

        assert!(!apply_binary_proof_grade_release_gate(&mut artifact));

        assert_eq!(artifact.verification.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].verification.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);

        let output = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
            .expect("TrustIr JSON output");
        let json: serde_json::Value =
            serde_json::from_str(output.text.as_deref().expect("TrustIr JSON text"))
                .expect("TrustIr JSON should parse");
        let bridge = &json["checked_certificate_bridge"];
        let dispatches = bridge["dispatches"].as_array().expect("certificate dispatch metadata");

        assert_eq!(bridge["checked_dispatches"], 1);
        assert_eq!(bridge["invalid_checked_dispatches"], 1);
        assert_eq!(bridge["proof_grade_closed"], true);
        assert_eq!(bridge["release_gate"]["source_provenance_accepted"], false);
        assert_eq!(dispatches.len(), 1);
        assert_eq!(dispatches[0]["origin"]["source"]["file"], "src/forged.rs");
        assert_eq!(dispatches[0]["proof_grade_eligible"], false);
        assert!(bridge["diagnostics"].as_array().expect("diagnostics").iter().any(|diagnostic| {
            diagnostic
                .as_str()
                .is_some_and(|diagnostic| diagnostic.contains("proof-grade remains closed"))
        }));
    }

    #[test]
    fn checked_certificate_missing_checker_metadata_keeps_trust_ir_proof_grade_closed() {
        use trust_types::{ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary(&[("proved_fn", 0x401000)]);
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic proved artifact");

        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );
        for dispatch in artifact
            .verification
            .solver_dispatch
            .iter_mut()
            .chain(artifact.functions[0].verification.solver_dispatch.iter_mut())
        {
            dispatch.certificate = ProofCertificateStatus::Checked {
                checker: " ".to_string(),
                format: "".to_string(),
                sha256: Some("checked-0".to_string()),
            };
        }

        assert!(!apply_binary_proof_grade_release_gate(&mut artifact));

        assert_eq!(artifact.verification.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_eq!(
            artifact.verification.proof_certificate,
            ProofCertificateStatus::Unavailable {
                reason: Some(
                    "proof-grade binary release requires checked certificate evidence with checker identity, format/version metadata, and certificate digest identity for every VC"
                        .to_string()
                )
            }
        );

        let output = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
            .expect("TrustIr JSON output");
        let json: serde_json::Value =
            serde_json::from_str(output.text.as_deref().expect("TrustIr JSON text"))
                .expect("TrustIr JSON should parse");
        let bridge = &json["checked_certificate_bridge"];
        let dispatches = bridge["dispatches"].as_array().expect("certificate dispatch metadata");

        assert_eq!(json["module"]["name"], "binary");
        assert_eq!(bridge["checked_dispatches"], 0);
        assert_eq!(bridge["invalid_checked_dispatches"], 1);
        assert_eq!(bridge["proof_grade_closed"], true);
        assert_eq!(dispatches.len(), 1);
        assert!(dispatches[0]["checker"].is_null());
        assert!(dispatches[0]["format"].is_null());
        assert_eq!(dispatches[0]["sha256"], "checked-0");
        assert_eq!(dispatches[0]["proof_grade_eligible"], false);
        assert!(bridge["diagnostics"].as_array().expect("diagnostics").iter().any(|diagnostic| {
            diagnostic
                .as_str()
                .is_some_and(|diagnostic| diagnostic.contains("proof-grade remains closed"))
        }));
    }

    #[test]
    fn unsupported_records_prevent_proved_verification_summary() {
        use trust_types::{BinaryVerificationStatus, ProofStrength, VcKind};

        let mut lifted = synthetic_lifted_binary(&[("partial_fn", 0x401000)]);
        lifted.functions[0].unsupported.records.push(unsupported_record(
            "trust-lift",
            Some("x86-64"),
            Some(0x401000),
            Some(0x401000),
            "unsupported instruction side effect",
        ));
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            synthetic_vc("partial_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];

        let artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic artifact");

        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Mixed);
        assert_eq!(artifact.verification.proved, 1);
        assert_eq!(artifact.verification.unsupported, 1);
        assert_eq!(artifact.verification.unsupported_ledger.records.len(), 1);
        assert_eq!(artifact.functions[0].verification.status, BinaryVerificationStatus::Mixed);
        assert_eq!(artifact.functions[0].verification.unsupported, 1);
    }

    #[test]
    fn aarch64_memory_order_lift_failures_are_visible_in_unsupported_ledger() {
        use trust_types::{ProofStrength, VcKind};

        let cases = [
            (
                "ldar_fail",
                0x402000,
                0xC8DFFC20u32,
                "Ldar",
                "LDAR has acquire memory-ordering semantics",
            ),
            (
                "stlr_fail",
                0x402010,
                0xC89FFC20u32,
                "Stlr",
                "STLR has release memory-ordering semantics",
            ),
            ("ldaxr_fail", 0x402020, 0xC85FFC20u32, "Ldaxr", "LDAXR combines acquire ordering"),
            ("stlxr_fail", 0x402030, 0xC802FC20u32, "Stlxr", "STLXR combines release ordering"),
        ];

        let mut lifted = synthetic_lifted_binary(&[("retained_supported_fn", 0x401000)]);
        lifted.architecture = "aarch64";
        lifted.failures = cases
            .iter()
            .map(|(name, address, encoding, opcode, detail)| {
                let bytes = encoding.to_le_bytes();
                trust_lift::LiftedFunctionFailure {
                    name: Some((*name).to_string()),
                    entry_point: *address,
                    error: format!(
                        "unsupported instruction semantics at binary:0x{address:x} size 4 encoding 0x{encoding:08x} bytes [0x{:02x}, 0x{:02x}, 0x{:02x}, 0x{:02x}] opcode {opcode}: AArch64 atomic/exclusive semantics are unsupported fail-closed ({detail})",
                        bytes[0], bytes[1], bytes[2], bytes[3]
                    ),
                }
            })
            .collect();
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);
        let results = vec![(
            synthetic_vc("retained_supported_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];

        let artifact = decompilation_artifact_from_lifted_with_verification_results(
            16, &options, &lifted, &results,
        )
        .expect("synthetic artifact");

        assert_eq!(artifact.binary.architecture, "aarch64");
        assert_eq!(artifact.unsupported.records.len(), cases.len());
        assert_eq!(artifact.verification.unsupported, cases.len());
        assert_eq!(artifact.verification.unsupported_ledger.records.len(), cases.len());
        assert_eq!(artifact.trust_level, TrustLevel::Partial);
        assert!(
            artifact.reconstruction.diagnostics.iter().any(|diagnostic| {
                diagnostic == &format!("unsupported records: {}", cases.len())
            })
        );

        for (name, address, encoding, opcode, detail) in cases {
            let record = artifact
                .unsupported
                .records
                .iter()
                .find(|record| record.feature.contains(&format!("failed to lift function {name}:")))
                .unwrap_or_else(|| panic!("{name} should be visible in the unsupported ledger"));

            assert_eq!(record.stage, "trust-lift");
            assert_eq!(record.architecture.as_deref(), Some("aarch64"));
            assert_eq!(
                record.origin.as_ref().map(|origin| origin.instruction_address),
                Some(address)
            );
            assert!(record.feature.contains(&format!("opcode {opcode}")));
            assert!(record.feature.contains(&format!("encoding 0x{encoding:08x}")));
            assert!(record.feature.contains("unsupported fail-closed"));
            assert!(record.feature.contains(detail));
            assert!(
                artifact
                    .verification
                    .unsupported_ledger
                    .records
                    .iter()
                    .any(|verification_record| verification_record.feature == record.feature),
                "{name} should be copied into the verification unsupported ledger"
            );
        }
    }

    #[test]
    fn aarch64_supported_stack_load_stays_out_of_unsupported_ledger_with_exact_origin() {
        use trust_types::{MemoryAccessKind, MemoryRegionKind, ProofStrength, VcKind};

        const FUNCTION: &str = "aarch64_supported_stack_load";
        const ENTRY: u64 = 0x402000;
        const LDR_X2_SP_8: u32 = 0xF94007E2;
        const RET: u32 = 0xD65F03C0;

        let mut text = Vec::new();
        text.extend_from_slice(&LDR_X2_SP_8.to_le_bytes());
        text.extend_from_slice(&RET.to_le_bytes());

        let lifter = trust_lift::Lifter::new(
            vec![trust_lift::FunctionBoundary {
                name: FUNCTION.to_string(),
                start: ENTRY,
                size: text.len() as u64,
            }],
            ENTRY,
            text.len() as u64,
            0,
        );
        let lifted_function =
            lifter.lift_function(&text, ENTRY).expect("supported AArch64 stack load should lift");
        assert!(lifted_function.unsupported.is_empty());

        let lifted = LiftedBinary {
            format: "ELF",
            architecture: "aarch64",
            endianness: trust_lift::binary::BinaryEndianness::Little,
            entry_point: Some(ENTRY),
            build_id: None,
            segments: vec![],
            memory_model: BinaryMemoryModel::default(),
            function_seeds: vec![trust_lift::LiftedFunctionSeed {
                name: Some(FUNCTION.to_string()),
                entry_point: ENTRY,
                size: Some(text.len() as u64),
                source: trust_lift::LiftedFunctionSeedSource::Symbol,
            }],
            source_provenance: trust_lift::LiftedSourceProvenance {
                status: trust_lift::LiftedSourceProvenanceStatus::Exact,
                exact_mapping_count: 2,
                ambiguous_mapping_count: 0,
                diagnostics: vec!["exact source provenance recovered for supported LDR".into()],
            },
            source_mappings: vec![
                trust_lift::LiftedSourceMapping {
                    binary_address: ENTRY,
                    source: SourceSpan {
                        file: "src/aarch64.rs".to_string(),
                        line_start: 12,
                        col_start: 9,
                        line_end: 12,
                        col_end: 9,
                    },
                },
                trust_lift::LiftedSourceMapping {
                    binary_address: ENTRY + 4,
                    source: SourceSpan {
                        file: "src/aarch64.rs".to_string(),
                        line_start: 13,
                        col_start: 9,
                        line_end: 13,
                        col_end: 9,
                    },
                },
            ],
            functions: vec![lifted_function],
            failures: vec![],
        };
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]);
        let results = vec![(
            synthetic_vc(FUNCTION, ENTRY, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];

        let artifact = decompilation_artifact_from_lifted_with_verification_results(
            text.len(),
            &options,
            &lifted,
            &results,
        )
        .expect("supported AArch64 decompilation artifact");

        assert_eq!(artifact.binary.architecture, "aarch64");
        assert_eq!(artifact.functions.len(), 1);
        assert_eq!(artifact.functions[0].coverage.instructions_lifted, 2);
        assert_eq!(artifact.source_provenance.status, "exact");
        assert!(!artifact.source_provenance.source_backpropagation_allowed);
        assert!(!artifact.source_provenance.effective_source_backpropagation_allowed());
        assert!(source_provenance_allows_artifact_proof_grade(&artifact.source_provenance));
        assert!(artifact.unsupported.records.is_empty());
        assert_eq!(artifact.verification.unsupported, 0);
        assert!(artifact.verification.unsupported_ledger.records.is_empty());
        assert!(artifact.functions[0].unsupported.records.is_empty());
        assert!(artifact.functions[0].verification.unsupported_ledger.records.is_empty());

        let function_span = artifact.functions[0].origin.as_ref().expect("function origin").span();
        assert_eq!(function_span.file, "src/aarch64.rs");
        assert_eq!(function_span.line_start, 12);
        assert_eq!(function_span.col_start, 9);

        let load = artifact.functions[0]
            .memory_accesses
            .iter()
            .find(|access| access.origin.instruction_address == ENTRY)
            .expect("supported LDR should carry a memory-read origin");
        assert_eq!(load.kind, MemoryAccessKind::Read);
        assert_eq!(load.region, MemoryRegionKind::Stack);
        assert_eq!(load.width_bytes, 8);
        assert_eq!(load.origin.function_entry, Some(ENTRY));
        assert_eq!(load.origin.instruction_address, ENTRY);
        assert_eq!(load.origin.instruction_size, Some(4));
        assert_eq!(load.origin.encoding, Some(LDR_X2_SP_8));
        assert_eq!(load.origin.instruction_bytes, LDR_X2_SP_8.to_le_bytes().to_vec());

        let trust_ir_json = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
            .expect("TrustIr JSON output");
        let json: serde_json::Value =
            serde_json::from_str(trust_ir_json.text.as_deref().expect("TrustIr JSON text"))
                .expect("TrustIr output should parse as JSON");
        assert_eq!(json["metadata"]["architecture"], "aarch64");
        assert_eq!(
            json["unsupported"]["records"].as_array().expect("unsupported records").len(),
            0
        );
    }

    #[test]
    fn unsupported_records_remain_partial_not_rejected_and_prevent_checked_proof_grade() {
        use trust_types::{BinaryVerificationStatus, ProofStrength, VcKind};

        let mut lifted = synthetic_lifted_binary_with_source(
            &[("partial_fn", 0x401000)],
            &[(0x401000, "src/partial.rs", 1, 1)],
        );
        lifted.functions[0].unsupported.records.push(unsupported_record(
            "trust-lift::semantic-lift",
            Some("x86-64"),
            Some(0x401000),
            Some(0x401004),
            "partial instruction semantics remain proof-grade blocking",
        ));
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            synthetic_vc("partial_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic artifact");

        assert!(source_provenance_allows_artifact_proof_grade(&artifact.source_provenance));
        assert_eq!(artifact.unsupported.records.len(), 1);
        assert_eq!(artifact.unsupported.records[0].stage, "trust-lift::semantic-lift");
        assert_eq!(
            artifact.unsupported.records[0]
                .origin
                .as_ref()
                .map(|origin| origin.instruction_address),
            Some(0x401004)
        );
        assert_eq!(artifact.verification.unsupported_ledger.records.len(), 1);
        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Mixed);
        assert_ne!(artifact.verification.status, BinaryVerificationStatus::Rejected);
        assert_eq!(artifact.verification.rejected, 0);
        assert_eq!(artifact.functions[0].verification.status, BinaryVerificationStatus::Mixed);
        assert!(
            artifact
                .reconstruction
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic == "unsupported records: 1")
        );

        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );

        assert!(!binary_proof_grade_release_gate_accepts(&artifact.verification));
        assert!(!apply_binary_proof_grade_release_gate(&mut artifact));
        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Mixed);
        assert_eq!(artifact.verification.trust_level, TrustLevel::Partial);
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].verification.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.functions[0].trust_level, TrustLevel::ProofGrade);
    }

    #[test]
    fn non_binary_vcs_are_rejected_as_binary_evidence() {
        use trust_types::{BinaryVerificationStatus, Formula, ProofStrength, VcKind};

        let lifted = synthetic_lifted_binary(&[("foo", 0x401000)]);
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            source_vc("foo", VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];

        let artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic artifact");

        assert_eq!(artifact.verification.status, BinaryVerificationStatus::Rejected);
        assert_eq!(artifact.verification.rejected, 1);
        assert_eq!(artifact.verification.solver_dispatch[0].status, SolverDispatchStatus::Rejected);
        assert!(artifact.verification.solver_dispatch[0].origin.is_none());
        assert!(artifact.verification.solver_dispatch[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("rejected non-binary verification condition")
        }));
        assert_eq!(artifact.functions[0].verification.status, BinaryVerificationStatus::NotRun);
        assert_eq!(results[0].0.formula, Formula::Bool(true));
    }

    fn constant_return_trust_ir(name: &str, value: i128) -> VerifiableFunction {
        use trust_types::{BasicBlock, BlockId, LocalDecl, Place, VerifiableBody};

        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("binary::{name}"),
            span: SourceSpan::binary_address(0x401000),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(value))),
                        span: SourceSpan::binary_address(0x401000),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn layout_sensitive_cast_trust_ir(name: &str) -> VerifiableFunction {
        use trust_types::{BasicBlock, BlockId, LocalDecl, Place, VerifiableBody};

        let pair_ty = Ty::Tuple(vec![Ty::u64(), Ty::u64()]);
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("binary::{name}"),
            span: SourceSpan::binary_address(0x401000),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u64(), name: None },
                    LocalDecl { index: 1, ty: pair_ty, name: Some("pair".to_string()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u64()),
                        span: SourceSpan::binary_address(0x401000),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u64(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn thread_local_ref_trust_ir(name: &str) -> VerifiableFunction {
        use trust_types::{BasicBlock, BlockId, LocalDecl, Place, VerifiableBody};

        let reference_ty = Ty::Ref { mutable: false, inner: Box::new(Ty::usize()) };
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("binary::{name}"),
            span: SourceSpan::binary_address(0x401000),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: reference_ty.clone(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Unsupported {
                            kind: "Rvalue::ThreadLocalRef".to_string(),
                            detail: "thread-local reference to binary::TLS".to_string(),
                            operands: vec![],
                        },
                        span: SourceSpan::binary_address(0x401000),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: reference_ty,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn symbolic_return_trust_ir(name: &str) -> VerifiableFunction {
        let mut function = constant_return_trust_ir(name, 0);
        function.body.blocks[0].stmts[0] = Statement::Assign {
            place: trust_types::Place::local(0),
            rvalue: Rvalue::Use(Operand::Symbolic(trust_types::Formula::Var(
                "lifted_rax".to_string(),
                trust_types::Sort::Int,
            ))),
            span: SourceSpan::binary_address(0x401000),
        };
        function
    }

    fn symbolic_bool_true_return_trust_ir(name: &str) -> VerifiableFunction {
        let mut function = constant_return_trust_ir(name, 0);
        function.span = SourceSpan {
            file: format!("src/{name}.rs"),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 8,
        };
        function.body.locals[0].ty = Ty::Bool;
        function.body.return_ty = Ty::Bool;
        function.body.blocks[0].stmts[0] = Statement::Assign {
            place: trust_types::Place::local(0),
            rvalue: Rvalue::Use(Operand::Symbolic(trust_types::Formula::Bool(true))),
            span: SourceSpan {
                file: format!("src/{name}.rs"),
                line_start: 1,
                col_start: 1,
                line_end: 1,
                col_end: 8,
            },
        };
        function
    }

    #[cfg(feature = "trust-cg")]
    const EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS: &str = r#"[schema=str:"trust-types.BinaryProvenance@1"] [source=str:"unit-test"] [binary_path=str:"fixture.bin"] [function_entry=str:"0x401000"] [instruction_address=str:"0x401004"] [instruction_size=str:"4"] [encoding=str:"0xd503201f"] [instruction_bytes=str:"1f2003d5"]"#;
    #[cfg(feature = "trust-cg")]
    const EXACT_CANONICAL_UNSUPPORTED_LEDGER_ATTRS: &str = r#"[schema=str:"trust-types.UnsupportedLedger@1"] [source=str:"bounded-empty-unsupported-ledger"] [unsupported_records=str:"0"] [verification_unsupported=str:"0"] [target_semantics_consumed=str:"false"]"#;

    #[cfg(feature = "trust-cg")]
    fn canonical_bounded_empty_release_gate_trust_ir(
        function: &str,
        formula: &trust_types::Formula,
        provenance_attrs: &str,
        certificate_attrs: &str,
        replay_attrs: &str,
        unsupported_ledger_attrs: &str,
    ) -> String {
        let formula_json = serde_json::to_string(formula).expect("formula should serialize");
        let formula_smtlib = formula.to_smtlib();
        let formula_sort = trust_types::infer_sort(formula).to_smtlib();
        format!(
            r#"; TrustIr text format v1
module "{function}"

fn @{function}(functy.0) {{
bb0(%0: bool):
        %1 = dialect_op trust_symbolic.formula() -> bool [schema=str:"trust-types.Formula@1"] [formula_json=str:{formula_json:?}] [formula.smtlib2=str:{formula_smtlib:?}] [formula.sort=str:{formula_sort:?}]
        %2 = dialect_op trust_binary.provenance() -> i32 {provenance_attrs}
        %3 = dialect_op trust_proof.checked_certificate() -> i32 {certificate_attrs}
        %4 = dialect_op trust_proof.proof_replay() -> i32 {replay_attrs}
        %5 = dialect_op trust_proof.unsupported_ledger() -> i32 {unsupported_ledger_attrs}
        ret %0
}}
"#
        )
    }

    fn symbolic_aggregate_trust_ir(name: &str) -> VerifiableFunction {
        let mut function = constant_return_trust_ir(name, 0);
        function.body.locals[0].ty = Ty::Tuple(vec![Ty::i32(), Ty::Bool]);
        function.body.return_ty = Ty::Tuple(vec![Ty::i32(), Ty::Bool]);
        function.body.blocks[0].stmts[0] = Statement::Assign {
            place: trust_types::Place::local(0),
            rvalue: Rvalue::Aggregate(
                trust_types::AggregateKind::Tuple,
                vec![
                    Operand::Symbolic(trust_types::Formula::Var(
                        "lifted_rax".to_string(),
                        trust_types::Sort::Int,
                    )),
                    Operand::Constant(ConstValue::Bool(true)),
                ],
            ),
            span: SourceSpan::binary_address(0x401000),
        };
        function
    }

    fn symbolic_copied_aggregate_trust_ir(name: &str) -> VerifiableFunction {
        let mut function = constant_return_trust_ir(name, 0);
        function.body.locals = vec![
            trust_types::LocalDecl {
                index: 0,
                ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]),
                name: None,
            },
            trust_types::LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".to_string()) },
        ];
        function.body.return_ty = Ty::Tuple(vec![Ty::i32(), Ty::Bool]);
        function.body.blocks[0].stmts = vec![
            Statement::Assign {
                place: trust_types::Place::local(1),
                rvalue: Rvalue::Use(Operand::Symbolic(trust_types::Formula::Var(
                    "lifted_rax".to_string(),
                    trust_types::Sort::Int,
                ))),
                span: SourceSpan::binary_address(0x401000),
            },
            Statement::Assign {
                place: trust_types::Place::local(0),
                rvalue: Rvalue::Aggregate(
                    trust_types::AggregateKind::Tuple,
                    vec![
                        Operand::Copy(trust_types::Place::local(1)),
                        Operand::Constant(ConstValue::Bool(true)),
                    ],
                ),
                span: SourceSpan::binary_address(0x401000),
            },
        ];
        function
    }

    fn assert_symbolic_proof_consumer_blocker(
        output: &DecompiledOutput,
        target: &DecompileTarget,
        function: &str,
    ) {
        let blocker = output
            .target_validation_blockers
            .iter()
            .find(|blocker| {
                &blocker.target == target
                    && blocker.feature == "symbolic-formula-proof-semantics"
                    && blocker.function.as_deref() == Some(function)
            })
            .expect("symbolic proof-consumer blocker");

        assert!(blocker.reason.contains("target proof semantics"));
        assert!(blocker.reason.contains("checked certificate"));
        assert!(blocker.reason.contains("replay metadata"));
        assert!(blocker.diagnostics.iter().any(|diagnostic| {
            diagnostic == "required-evidence=formula-specific-checked-certificate"
        }));
        assert!(
            blocker
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic == "required-evidence=formula-specific-replay" })
        );
        assert!(
            blocker
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic == "target-semantics-consumer=missing" })
        );
        assert!(blocker.diagnostics.iter().any(|diagnostic| diagnostic == "proof-grade=false"));
        assert!(blocker.diagnostics.iter().any(|diagnostic| {
            diagnostic == &format!("formula.schema={SYMBOLIC_FORMULA_SCHEMA}")
        }));
        assert!(
            blocker.diagnostics.iter().any(|diagnostic| diagnostic.starts_with("formula_json="))
        );
        assert!(
            blocker.diagnostics.iter().any(|diagnostic| diagnostic.starts_with("formula.smtlib2="))
        );
        assert!(
            blocker.diagnostics.iter().any(|diagnostic| diagnostic.starts_with("formula.sort="))
        );
    }

    fn schema_aware_symbolic_formula_consumer_diagnostic(
        formula: &PreservedSymbolicFormula,
    ) -> String {
        let formula_json =
            serde_json::to_string(&formula.formula).expect("formula should serialize");
        let formula_smtlib = formula.formula.to_smtlib();
        let formula_sort = trust_types::infer_sort(&formula.formula).to_smtlib();
        let formula_evidence = formula.evidence();
        let function = formula.function.as_deref().unwrap_or("unknown");
        let block = formula.block.unwrap_or(usize::MAX);
        let statement_index = formula.statement_index.unwrap_or(usize::MAX);

        format!(
            "target-consumer=accepted; symbolic-formula-proof-consumer=accepted; trust_symbolic.formula=consumed; function={function}; block={block}; statement_index={statement_index}; location={}; formula.schema={}; formula_json={formula_json}; formula.smtlib2={formula_smtlib}; formula.sort={formula_sort}; formula.digest={}; formula.origin={}",
            formula.location,
            formula_evidence.schema,
            formula_evidence.digest,
            formula_evidence.origin
        )
    }

    #[cfg(feature = "elf")]
    fn minimal_elf32_i386() -> Vec<u8> {
        let mut buf = Vec::new();
        buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']);
        buf.push(1); // ELFCLASS32
        buf.push(1); // ELFDATA2LSB
        buf.push(1); // EV_CURRENT
        buf.push(0); // OS/ABI
        buf.extend_from_slice(&[0u8; 8]);
        buf.extend_from_slice(&2u16.to_le_bytes()); // ET_EXEC
        buf.extend_from_slice(&3u16.to_le_bytes()); // EM_386
        buf.extend_from_slice(&1u32.to_le_bytes()); // e_version
        buf.extend_from_slice(&0u32.to_le_bytes()); // e_entry
        buf.extend_from_slice(&0u32.to_le_bytes()); // e_phoff
        buf.extend_from_slice(&0u32.to_le_bytes()); // e_shoff
        buf.extend_from_slice(&0u32.to_le_bytes()); // e_flags
        buf.extend_from_slice(&52u16.to_le_bytes()); // e_ehsize
        buf.extend_from_slice(&32u16.to_le_bytes()); // e_phentsize
        buf.extend_from_slice(&0u16.to_le_bytes()); // e_phnum
        buf.extend_from_slice(&40u16.to_le_bytes()); // e_shentsize
        buf.extend_from_slice(&0u16.to_le_bytes()); // e_shnum
        buf.extend_from_slice(&0u16.to_le_bytes()); // e_shstrndx
        buf
    }

    #[cfg(feature = "elf")]
    fn minimal_aarch64_elf_with_entry_instructions(instructions: &[u32]) -> Vec<u8> {
        assert!(!instructions.is_empty());
        assert!(instructions.len() <= 8);

        let mut buf = Vec::new();
        let shstrtab = b"\0.shstrtab\0.symtab\0.strtab\0.text\0";
        let strtab = b"\0_start\0";
        let phdr_off: u64 = 0x40;
        let text_off: u64 = 0x78;
        let text_size: u64 = 0x20;
        let shstrtab_off: u64 = 0x98;
        let strtab_off: u64 = 0xC0;
        let symtab_off: u64 = 0xD0;
        let shdr_off: u64 = 0x100;
        let file_size: u64 = 0x240;
        let text_vaddr: u64 = 0x400000;
        let entry_size = (instructions.len() * 4) as u64;

        buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']);
        buf.push(2); // ELFCLASS64
        buf.push(1); // ELFDATA2LSB
        buf.push(1); // EV_CURRENT
        buf.push(0); // OS/ABI
        buf.extend_from_slice(&[0u8; 8]);
        buf.extend_from_slice(&2u16.to_le_bytes()); // ET_EXEC
        buf.extend_from_slice(&0xB7u16.to_le_bytes()); // EM_AARCH64
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.extend_from_slice(&text_vaddr.to_le_bytes());
        buf.extend_from_slice(&phdr_off.to_le_bytes());
        buf.extend_from_slice(&shdr_off.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&64u16.to_le_bytes());
        buf.extend_from_slice(&56u16.to_le_bytes());
        buf.extend_from_slice(&1u16.to_le_bytes());
        buf.extend_from_slice(&64u16.to_le_bytes());
        buf.extend_from_slice(&5u16.to_le_bytes());
        buf.extend_from_slice(&1u16.to_le_bytes());
        assert_eq!(buf.len(), 0x40);

        buf.extend_from_slice(&1u32.to_le_bytes()); // PT_LOAD
        buf.extend_from_slice(&5u32.to_le_bytes()); // PF_R | PF_X
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&text_vaddr.to_le_bytes());
        buf.extend_from_slice(&text_vaddr.to_le_bytes());
        buf.extend_from_slice(&file_size.to_le_bytes());
        buf.extend_from_slice(&file_size.to_le_bytes());
        buf.extend_from_slice(&0x1000u64.to_le_bytes());
        assert_eq!(buf.len(), text_off as usize);

        for instruction in instructions {
            buf.extend_from_slice(&instruction.to_le_bytes());
        }
        while buf.len() < (text_off + text_size) as usize {
            buf.extend_from_slice(&0xD65F03C0u32.to_le_bytes());
        }

        buf.extend_from_slice(shstrtab);
        while buf.len() < strtab_off as usize {
            buf.push(0);
        }
        buf.extend_from_slice(strtab);
        while buf.len() < symtab_off as usize {
            buf.push(0);
        }

        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.push(0);
        buf.push(0);
        buf.extend_from_slice(&0u16.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&1u32.to_le_bytes()); // "_start"
        buf.push((1 << 4) | 2); // STB_GLOBAL | STT_FUNC
        buf.push(0);
        buf.extend_from_slice(&4u16.to_le_bytes());
        buf.extend_from_slice(&text_vaddr.to_le_bytes());
        buf.extend_from_slice(&entry_size.to_le_bytes());
        assert_eq!(buf.len(), shdr_off as usize);

        write_elf64_shdr(&mut buf, Elf64SectionHeader::default());
        write_elf64_shdr(
            &mut buf,
            Elf64SectionHeader {
                name: 1,
                section_type: 3,
                offset: shstrtab_off,
                size: shstrtab.len() as u64,
                addralign: 1,
                ..Default::default()
            },
        );
        write_elf64_shdr(
            &mut buf,
            Elf64SectionHeader {
                name: 11,
                section_type: 2,
                offset: symtab_off,
                size: 48,
                link: 3,
                info: 1,
                addralign: 8,
                entsize: 24,
                ..Default::default()
            },
        );
        write_elf64_shdr(
            &mut buf,
            Elf64SectionHeader {
                name: 19,
                section_type: 3,
                offset: strtab_off,
                size: strtab.len() as u64,
                addralign: 1,
                ..Default::default()
            },
        );
        write_elf64_shdr(
            &mut buf,
            Elf64SectionHeader {
                name: 27,
                section_type: 1,
                flags: 0x6,
                addr: text_vaddr,
                offset: text_off,
                size: text_size,
                addralign: 16,
                ..Default::default()
            },
        );
        assert_eq!(buf.len(), file_size as usize);
        buf
    }

    #[cfg(feature = "elf")]
    fn minimal_x86_64_elf_with_entry_bytes(entry_bytes: &[u8]) -> Vec<u8> {
        assert!(!entry_bytes.is_empty());
        assert!(entry_bytes.len() <= 0x20);

        let mut buf = Vec::new();
        let shstrtab = b"\0.shstrtab\0.symtab\0.strtab\0.text\0";
        let strtab = b"\0_start\0";
        let phdr_off: u64 = 0x40;
        let text_off: u64 = 0x78;
        let text_size: u64 = 0x20;
        let shstrtab_off: u64 = 0x98;
        let strtab_off: u64 = 0xC0;
        let symtab_off: u64 = 0xD0;
        let shdr_off: u64 = 0x100;
        let file_size: u64 = 0x240;
        let text_vaddr: u64 = 0x400000;

        buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']);
        buf.push(2); // ELFCLASS64
        buf.push(1); // ELFDATA2LSB
        buf.push(1); // EV_CURRENT
        buf.push(0); // OS/ABI
        buf.extend_from_slice(&[0u8; 8]);
        buf.extend_from_slice(&2u16.to_le_bytes()); // ET_EXEC
        buf.extend_from_slice(&0x3Eu16.to_le_bytes()); // EM_X86_64
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.extend_from_slice(&text_vaddr.to_le_bytes());
        buf.extend_from_slice(&phdr_off.to_le_bytes());
        buf.extend_from_slice(&shdr_off.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&64u16.to_le_bytes());
        buf.extend_from_slice(&56u16.to_le_bytes());
        buf.extend_from_slice(&1u16.to_le_bytes());
        buf.extend_from_slice(&64u16.to_le_bytes());
        buf.extend_from_slice(&5u16.to_le_bytes());
        buf.extend_from_slice(&1u16.to_le_bytes());
        assert_eq!(buf.len(), 0x40);

        buf.extend_from_slice(&1u32.to_le_bytes()); // PT_LOAD
        buf.extend_from_slice(&5u32.to_le_bytes()); // PF_R | PF_X
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&text_vaddr.to_le_bytes());
        buf.extend_from_slice(&text_vaddr.to_le_bytes());
        buf.extend_from_slice(&file_size.to_le_bytes());
        buf.extend_from_slice(&file_size.to_le_bytes());
        buf.extend_from_slice(&0x1000u64.to_le_bytes());
        assert_eq!(buf.len(), text_off as usize);

        buf.extend_from_slice(entry_bytes);
        while buf.len() < (text_off + text_size) as usize {
            buf.push(0x90);
        }

        buf.extend_from_slice(shstrtab);
        while buf.len() < strtab_off as usize {
            buf.push(0);
        }
        buf.extend_from_slice(strtab);
        while buf.len() < symtab_off as usize {
            buf.push(0);
        }

        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.push(0);
        buf.push(0);
        buf.extend_from_slice(&0u16.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&1u32.to_le_bytes()); // "_start"
        buf.push((1 << 4) | 2); // STB_GLOBAL | STT_FUNC
        buf.push(0);
        buf.extend_from_slice(&4u16.to_le_bytes());
        buf.extend_from_slice(&text_vaddr.to_le_bytes());
        buf.extend_from_slice(&(entry_bytes.len() as u64).to_le_bytes());
        assert_eq!(buf.len(), shdr_off as usize);

        write_elf64_shdr(&mut buf, Elf64SectionHeader::default());
        write_elf64_shdr(
            &mut buf,
            Elf64SectionHeader {
                name: 1,
                section_type: 3,
                offset: shstrtab_off,
                size: shstrtab.len() as u64,
                addralign: 1,
                ..Default::default()
            },
        );
        write_elf64_shdr(
            &mut buf,
            Elf64SectionHeader {
                name: 11,
                section_type: 2,
                offset: symtab_off,
                size: 48,
                link: 3,
                info: 1,
                addralign: 8,
                entsize: 24,
                ..Default::default()
            },
        );
        write_elf64_shdr(
            &mut buf,
            Elf64SectionHeader {
                name: 19,
                section_type: 3,
                offset: strtab_off,
                size: strtab.len() as u64,
                addralign: 1,
                ..Default::default()
            },
        );
        write_elf64_shdr(
            &mut buf,
            Elf64SectionHeader {
                name: 27,
                section_type: 1,
                flags: 0x6,
                addr: text_vaddr,
                offset: text_off,
                size: text_size,
                addralign: 16,
                ..Default::default()
            },
        );
        assert_eq!(buf.len(), file_size as usize);
        buf
    }

    #[cfg(feature = "elf")]
    #[derive(Default)]
    struct Elf64SectionHeader {
        name: u32,
        section_type: u32,
        flags: u64,
        addr: u64,
        offset: u64,
        size: u64,
        link: u32,
        info: u32,
        addralign: u64,
        entsize: u64,
    }

    #[cfg(feature = "elf")]
    fn write_elf64_shdr(buf: &mut Vec<u8>, header: Elf64SectionHeader) {
        buf.extend_from_slice(&header.name.to_le_bytes());
        buf.extend_from_slice(&header.section_type.to_le_bytes());
        buf.extend_from_slice(&header.flags.to_le_bytes());
        buf.extend_from_slice(&header.addr.to_le_bytes());
        buf.extend_from_slice(&header.offset.to_le_bytes());
        buf.extend_from_slice(&header.size.to_le_bytes());
        buf.extend_from_slice(&header.link.to_le_bytes());
        buf.extend_from_slice(&header.info.to_le_bytes());
        buf.extend_from_slice(&header.addralign.to_le_bytes());
        buf.extend_from_slice(&header.entsize.to_le_bytes());
    }

    fn synthetic_lifted_binary(functions: &[(&str, u64)]) -> LiftedBinary {
        synthetic_lifted_binary_with_source(functions, &[])
    }

    fn synthetic_lifted_binary_with_source(
        functions: &[(&str, u64)],
        source_mappings: &[(u64, &str, u32, u32)],
    ) -> LiftedBinary {
        let source_provenance = if source_mappings.is_empty() {
            trust_lift::LiftedSourceProvenance::default()
        } else {
            trust_lift::LiftedSourceProvenance {
                status: trust_lift::LiftedSourceProvenanceStatus::Exact,
                exact_mapping_count: source_mappings.len(),
                ambiguous_mapping_count: 0,
                diagnostics: vec![format!(
                    "exact source provenance recovered for {} address(es)",
                    source_mappings.len()
                )],
            }
        };

        synthetic_lifted_binary_with_source_provenance(
            functions,
            source_provenance,
            source_mappings,
        )
    }

    fn synthetic_lifted_binary_with_source_provenance(
        functions: &[(&str, u64)],
        source_provenance: trust_lift::LiftedSourceProvenance,
        source_mappings: &[(u64, &str, u32, u32)],
    ) -> LiftedBinary {
        let source_mappings: Vec<_> = source_mappings
            .iter()
            .map(|(address, file, line, column)| trust_lift::LiftedSourceMapping {
                binary_address: *address,
                source: SourceSpan {
                    file: (*file).to_string(),
                    line_start: *line,
                    col_start: *column,
                    line_end: *line,
                    col_end: *column,
                },
            })
            .collect();

        LiftedBinary {
            format: "ELF",
            architecture: "x86-64",
            endianness: trust_lift::binary::BinaryEndianness::Little,
            entry_point: functions.first().map(|(_, entry)| *entry),
            build_id: Some("synthetic-loader-id:unit-test".to_string()),
            segments: vec![],
            memory_model: BinaryMemoryModel::default(),
            function_seeds: functions
                .iter()
                .map(|(name, entry)| trust_lift::LiftedFunctionSeed {
                    name: Some((*name).to_string()),
                    entry_point: *entry,
                    size: None,
                    source: trust_lift::LiftedFunctionSeedSource::Symbol,
                })
                .collect(),
            source_provenance,
            source_mappings,
            functions: functions
                .iter()
                .map(|(name, entry)| synthetic_lifted_function(name, *entry))
                .collect(),
            failures: vec![],
        }
    }

    fn synthetic_lifted_function(name: &str, entry: u64) -> LiftedFunction {
        use trust_lift::cfg::{Cfg, LiftedBlock};
        use trust_types::VerifiableBody;

        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: entry,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        LiftedFunction {
            name: name.to_string(),
            entry_point: entry,
            cfg,
            trust_ir_body: VerifiableBody {
                locals: vec![],
                blocks: vec![],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            ssa: None,
            annotations: vec![],
            memory_accesses: vec![],
            trust_level: TrustLevel::Partial,
            unsupported: UnsupportedLedger::default(),
        }
    }

    fn synthetic_vc(
        function: &str,
        address: u64,
        kind: trust_types::VcKind,
    ) -> VerificationCondition {
        use trust_types::{Formula, Symbol};

        VerificationCondition {
            kind,
            function: Symbol::intern(function),
            location: SourceSpan::binary_address(address),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn source_vc(function: &str, kind: trust_types::VcKind) -> VerificationCondition {
        use trust_types::{Formula, Symbol};

        VerificationCondition {
            kind,
            function: Symbol::intern(function),
            location: SourceSpan {
                file: "src/lib.rs".into(),
                line_start: 1,
                col_start: 1,
                line_end: 1,
                col_end: 10,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn mark_dispatches_checked(dispatches: &mut [SolverDispatchRecord]) {
        for (index, dispatch) in dispatches.iter_mut().enumerate() {
            dispatch.certificate = ProofCertificateStatus::Checked {
                checker: "ay-cert-check".to_string(),
                format: "lfsc".to_string(),
                sha256: Some(format!("checked-{index}")),
            };
        }
    }

    fn mark_unsat_dispatches_checked(dispatches: &mut [SolverDispatchRecord]) {
        for (index, dispatch) in dispatches.iter_mut().enumerate() {
            if dispatch.status == SolverDispatchStatus::Unsat {
                dispatch.certificate = ProofCertificateStatus::Checked {
                    checker: "ay-cert-check".to_string(),
                    format: "lfsc".to_string(),
                    sha256: Some(format!("checked-{index}")),
                };
            }
        }
    }

    fn mark_dispatches_with_exact_instruction_provenance(dispatches: &mut [SolverDispatchRecord]) {
        for dispatch in dispatches {
            if let Some(origin) = dispatch.origin.as_mut() {
                origin.instruction_size = Some(1);
                origin.encoding = Some(0x90);
                origin.instruction_bytes = vec![0x90];
            }
            dispatch.binary_artifact_digest_identity = Some(test_binary_artifact_digest_identity());
        }
    }

    fn mark_dispatches_checked_with_exact_instruction_provenance(
        dispatches: &mut [SolverDispatchRecord],
    ) {
        mark_dispatches_checked(dispatches);
        mark_dispatches_with_exact_instruction_provenance(dispatches);
    }

    fn mark_dispatches_checked_and_replayed(dispatches: &mut [SolverDispatchRecord]) {
        mark_dispatches_checked_with_exact_instruction_provenance(dispatches);
        for dispatch in dispatches {
            dispatch.replay = ReplayStatus::Replayed;
        }
    }

    fn test_binary_artifact_digest_identity() -> BinaryArtifactDigestIdentity {
        const DIGEST: &str = "1111111111111111111111111111111111111111111111111111111111111111";
        BinaryArtifactDigestIdentity {
            root_artifact_digest: Some(BinaryArtifactDigest::sha256(DIGEST)),
            selected_image: Some(BinarySelectedImageIdentity {
                file_offset: 0,
                file_size: 8,
                sha256: DIGEST.to_string(),
            }),
        }
    }

    fn test_noop_binary_origin(function: &str, address: u64) -> BinaryOrigin {
        BinaryOrigin {
            binary_path: Some("fixtures/scalar-bool-release-gate.bin".to_string()),
            function_entry: Some(address),
            instruction_address: address,
            instruction_size: Some(1),
            encoding: Some(0x90),
            instruction_bytes: vec![0x90],
            source: Some(SourceSpan {
                file: format!("src/{function}.rs"),
                line_start: 1,
                col_start: 1,
                line_end: 1,
                col_end: 8,
            }),
        }
    }

    fn wasm_unconsumed_target_semantics() -> trust_wasm_bridge::WasmTargetSemanticConsumptionEvidence
    {
        trust_wasm_bridge::WasmTargetSemanticConsumptionEvidence {
            consumer: "trust-wasm-bridge::target-semantic-consumption-gate".to_string(),
            target_semantics_consumed: false,
            input_claimed_target_semantics_consumed: None,
            code: "no-wasm-target-semantic-consumer".to_string(),
            detail: "unit test fixture has no bridge-owned Wasm target consumption".to_string(),
        }
    }

    fn exact_wasm_non_empty_scalar_conversion(function: &str) -> WasmConversion {
        const CERTIFICATE_SHA: &str =
            "abababababababababababababababababababababababababababababababab";
        const REPLAY_SHA: &str = "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd";
        const LIFTED_TRUST_IR_SHA: &str =
            "1212121212121212121212121212121212121212121212121212121212121212";

        let proof_source = format!("solver_dispatch:vc:{function}");
        WasmConversion {
            wat: Some(format!(
                "(module\n  (func ${function} (result i32)\n    i32.const 1)\n  (export \"{function}\" (func ${function}))\n)\n"
            )),
            lifted_trust_ir_artifact_digest: Some(LIFTED_TRUST_IR_SHA.to_string()),
            bound_lifted_trust_ir_artifact_digest: Some(LIFTED_TRUST_IR_SHA.to_string()),
            validation: ReconstructionValidationStatus::Validated,
            wasm_validation: WasmTargetValidationStatus::InspectableRejected,
            trust_level: TrustLevel::Rejected,
            validation_blockers: Vec::new(),
            symbolic_formulas: vec![WasmSymbolicFormula {
                function: function.to_string(),
                block: 0,
                statement_index: 0,
                operand: "use".to_string(),
                formula: trust_types::Formula::Bool(true),
                sort: "Bool".to_string(),
                bit_width: None,
            }],
            provenance_evidence: vec![trust_wasm_bridge::WasmProvenanceEvidence {
                function: function.to_string(),
                source: proof_source.clone(),
                block: Some(0),
                statement_index: Some(0),
                origin: BinaryOrigin {
                    binary_path: Some("fixture.bin".to_string()),
                    function_entry: Some(0x1000),
                    instruction_address: 0x1004,
                    instruction_size: Some(4),
                    encoding: Some(0xd503_201f),
                    instruction_bytes: vec![0x1f, 0x20, 0x03, 0xd5],
                    source: Some(SourceSpan::binary_address(0x1004)),
                },
                target_semantic_consumption: wasm_unconsumed_target_semantics(),
                target_semantics_consumed: false,
            }],
            checked_certificate_evidence: vec![trust_wasm_bridge::WasmCheckedCertificateEvidence {
                function: function.to_string(),
                source: proof_source.clone(),
                block: None,
                statement_index: None,
                certificate: ProofCertificateStatus::Checked {
                    checker: "trust-proof-cert-check".to_string(),
                    format: "lrat".to_string(),
                    sha256: Some(CERTIFICATE_SHA.to_string()),
                },
                target_semantic_consumption: wasm_unconsumed_target_semantics(),
                target_semantics_consumed: false,
            }],
            proof_replay_evidence: vec![trust_wasm_bridge::WasmProofReplayEvidence {
                function: function.to_string(),
                source: proof_source,
                block: None,
                statement_index: None,
                replay: ReplayStatus::Replayed,
                artifact_sha256: Some(REPLAY_SHA.to_string()),
                exact_replay_checked: true,
                target_semantic_consumption: wasm_unconsumed_target_semantics(),
                target_semantics_consumed: false,
            }],
            unsupported_ledger_evidence: vec![trust_wasm_bridge::WasmUnsupportedLedgerEvidence {
                function: function.to_string(),
                source: "decompiled.unsupported_ledger".to_string(),
                block: None,
                statement_index: None,
                unsupported_records: 0,
                verification_unsupported: 0,
                unsupported_ledger_eliminated: true,
                target_semantic_consumption: wasm_unconsumed_target_semantics(),
                target_semantics_consumed: false,
            }],
            validation_records: Vec::new(),
            unsupported: UnsupportedLedger::default(),
            diagnostics: Vec::new(),
        }
    }

    #[cfg(feature = "trust-cg")]
    fn checked_replayed_dispatch(function: &str, origin: BinaryOrigin) -> SolverDispatchRecord {
        SolverDispatchRecord {
            id: format!("{function}:0"),
            function: Some(function.to_string()),
            origin: Some(origin),
            vc_kind: Some(trust_types::VcKind::Assertion {
                message: "target consumer fixture".to_string(),
            }),
            solver: "fixture-ay".to_string(),
            backend: Some("fixture-target-consumer".to_string()),
            status: SolverDispatchStatus::Unsat,
            query_semantics: SolverQuerySemantics::SatIsCounterexample,
            binary_artifact_digest_identity: Some(test_binary_artifact_digest_identity()),
            replay: ReplayStatus::Replayed,
            certificate: ProofCertificateStatus::Checked {
                checker: "fixture-cert-check".to_string(),
                format: "lfsc-v1".to_string(),
                sha256: Some("fixture-checked-scalar-bool".to_string()),
            },
            diagnostics: vec!["checked certificate metadata read back from fixture".to_string()],
            ..Default::default()
        }
    }

    #[cfg(feature = "trust-cg")]
    fn accepted_trust_cg_scalar_bool_target_output(function_name: &str) -> DecompiledOutput {
        let metadata = BinaryArtifactMetadata {
            path: Some("fixtures/scalar-bool-release-gate.bin".to_string()),
            format: BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            entry_point: Some(0x401000),
            byte_len: Some(8),
            build_id: Some("synthetic-loader-id:unit-test".to_string()),
            root_artifact_digest: test_binary_artifact_digest_identity().root_artifact_digest,
            selected_image: test_binary_artifact_digest_identity().selected_image,
            ..Default::default()
        };
        let origin = test_noop_binary_origin(function_name, 0x401000);
        let mut verification =
            BinaryVerificationSummary::from_solver_dispatch(vec![checked_replayed_dispatch(
                function_name,
                origin.clone(),
            )]);
        verification.unsupported_ledger = UnsupportedLedger::default();
        verification.refresh_from_solver_dispatch();
        let function = DecompiledFunction {
            name: function_name.to_string(),
            entry: 0x401000,
            origin: Some(origin.clone()),
            instruction_provenance: vec![origin],
            lifted: Some(symbolic_bool_true_return_trust_ir(function_name)),
            verification,
            ..Default::default()
        };

        let mut outputs = build_outputs(BuildOutputsInput {
            metadata: &metadata,
            functions: &[function],
            call_graph: &CallGraph::new(),
            memory_facts: &[],
            unsupported: &UnsupportedLedger::default(),
            source_provenance: &BinarySourceProvenanceSummary::default(),
            requested: &[DecompileOutputKind::TrustCgText],
            source_assumptions: &[],
            source_diagnostics: &[],
        })
        .expect("trust-cg scalar Bool fixture should build output");
        let mut output = outputs.pop().expect("trust-cg output");
        output.target_validation_blockers.clear();
        output
    }

    fn accepted_wasm_scalar_bool_target_output(function_name: &str) -> DecompiledOutput {
        let identity = test_binary_artifact_digest_identity();
        let metadata = BinaryArtifactMetadata {
            format: BinaryArtifactFormat::Elf,
            architecture: "x86-64".to_string(),
            byte_len: Some(8),
            root_artifact_digest: identity.root_artifact_digest.clone(),
            selected_image: identity.selected_image.clone(),
            ..Default::default()
        };
        let origin = test_noop_binary_origin(function_name, 0x1000);
        let function = DecompiledFunction {
            name: function_name.to_string(),
            entry: 0x1000,
            origin: Some(origin.clone()),
            instruction_provenance: vec![origin],
            lifted: Some(symbolic_bool_true_return_trust_ir(function_name)),
            ..Default::default()
        };
        let conversion = exact_wasm_non_empty_scalar_conversion(function_name);
        let proof_consumer = conversion.target_proof_consumer_evidence();
        let target_artifact = wasm_target_proof_consumer_artifact_digest(
            &metadata,
            std::slice::from_ref(&function),
            &conversion,
            &proof_consumer,
        )
        .expect("accepted Wasm proof consumer should produce artifact digest");
        let diagnostic = target_proof_consumer_artifact_digest_diagnostic(&target_artifact)
            .expect("target artifact digest should serialize");

        DecompiledOutput {
            target: DecompileTarget::Wasm,
            text: conversion.wat.clone(),
            validation: conversion.validation,
            trust_level: conversion.trust_level,
            preserved_symbolic_formulas: wasm_preserved_symbolic_formulas(
                &conversion.symbolic_formulas,
            ),
            diagnostics: vec![diagnostic],
            ..Default::default()
        }
    }

    fn replace_target_consumer_artifact_digest(
        output: &mut DecompiledOutput,
        artifact: &TargetProofConsumerArtifactDigest,
    ) {
        let diagnostic_index = output
            .diagnostics
            .iter()
            .position(|diagnostic| {
                diagnostic.starts_with(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
            })
            .expect("target proof-consumer artifact digest diagnostic");
        output.diagnostics[diagnostic_index] =
            target_proof_consumer_artifact_digest_diagnostic(artifact)
                .expect("target artifact digest should serialize");
    }

    fn refresh_target_consumer_artifact_digest(artifact: &mut TargetProofConsumerArtifactDigest) {
        artifact.artifact_digest = target_proof_consumer_artifact_digest(
            &TargetProofConsumerArtifactDigestMaterial::from_record(artifact),
        )
        .expect("target proof-consumer artifact digest should hash");
    }

    fn refresh_target_consumer_evidence_artifact_digest(
        artifact: &mut TargetProofConsumerEvidenceArtifactDigest,
    ) {
        artifact.digest = target_proof_consumer_evidence_artifact_digest(
            &TargetProofConsumerEvidenceArtifactDigestMaterial::from_record(artifact),
        )
        .expect("target proof-consumer evidence artifact digest should hash");
    }

    fn mismatched_test_binary_artifact_digest_identity() -> BinaryArtifactDigestIdentity {
        let mut identity = test_binary_artifact_digest_identity();
        identity.root_artifact_digest = Some(BinaryArtifactDigest::sha256(
            "2222222222222222222222222222222222222222222222222222222222222222",
        ));
        identity
    }

    fn install_test_binary_artifact_digest_metadata(artifact: &mut DecompilationArtifact) {
        let identity = test_binary_artifact_digest_identity();
        artifact.binary.byte_len = Some(8);
        artifact.binary.root_artifact_digest = identity.root_artifact_digest;
        artifact.binary.selected_image = identity.selected_image;
        for output in &mut artifact.reconstruction.outputs {
            attach_binary_artifact_digest_identity_to_output(output, &artifact.binary);
        }
        accept_test_target_consumer_for_reconstruction(&mut artifact.reconstruction);
    }

    fn accept_test_target_consumer_for_reconstruction(reconstruction: &mut ReconstructionSummary) {
        for output in &mut reconstruction.outputs {
            if output.target != reconstruction.target {
                continue;
            }
            if !output
                .diagnostics
                .iter()
                .any(|diagnostic| target_consumer_acceptance_diagnostic(diagnostic))
            {
                output.diagnostics.push(
                    "synthetic target-consumer=accepted; target proof consumer accepted checked-certificate, replay, source provenance, symbolic formula, and reconstruction evidence"
                        .to_string(),
                );
            }

            for formula in output.preserved_symbolic_formulas.clone() {
                if !output.diagnostics.iter().any(|diagnostic| {
                    symbolic_formula_consumer_diagnostic_for_formula(diagnostic, &formula)
                }) {
                    output
                        .diagnostics
                        .push(schema_aware_symbolic_formula_consumer_diagnostic(&formula));
                }
            }
        }
    }

    fn install_rust_target_consumer_artifact_digest(artifact: &mut DecompilationArtifact) {
        if artifact.reconstruction.target != DecompileTarget::Rust {
            return;
        }

        let unsupported_records = artifact.unsupported.records.len();
        let verification_unsupported = artifact.verification.unsupported_ledger.records.len();
        for output in &mut artifact.reconstruction.outputs {
            if output.target != DecompileTarget::Rust {
                continue;
            }
            output.diagnostics.retain(|diagnostic| {
                !diagnostic.starts_with(TARGET_PROOF_CONSUMER_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
            });
            let Some(artifact_digest) = rust_target_proof_consumer_artifact_digest(
                &artifact.binary,
                &artifact.functions,
                output,
                unsupported_records,
                verification_unsupported,
            ) else {
                continue;
            };
            output.diagnostics.push(
                target_proof_consumer_artifact_digest_diagnostic(&artifact_digest)
                    .expect("Rust target proof-consumer artifact digest should serialize"),
            );

            for formula in output.preserved_symbolic_formulas.clone() {
                if !output.diagnostics.iter().any(|diagnostic| {
                    symbolic_formula_consumer_diagnostic_for_formula(diagnostic, &formula)
                }) {
                    output
                        .diagnostics
                        .push(schema_aware_symbolic_formula_consumer_diagnostic(&formula));
                }
            }
        }
    }

    fn install_rust_preserved_formula_target_artifact(
        artifact: &mut DecompilationArtifact,
    ) -> PreservedSymbolicFormula {
        let formula = PreservedSymbolicFormula {
            target: DecompileTarget::Rust,
            function: Some("proved_fn".to_string()),
            block: Some(0),
            statement_index: Some(0),
            location: "rust-output::proved_fn".to_string(),
            formula: trust_types::Formula::Bool(true),
        };
        let rust_output = artifact
            .reconstruction
            .outputs
            .iter_mut()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust output");
        rust_output.preserved_symbolic_formulas.clear();
        rust_output.preserved_symbolic_formulas.push(formula.clone());
        rust_output.diagnostics.retain(|diagnostic| {
            !target_consumer_acceptance_diagnostic(diagnostic)
                && !symbolic_formula_consumer_diagnostic(diagnostic)
        });
        install_rust_target_consumer_artifact_digest(artifact);
        formula
    }

    fn remove_rust_compile_back_evidence_marker(
        artifact: &mut DecompilationArtifact,
        marker: &str,
    ) {
        fn retain_marker(record: &mut ReconstructionValidationRecord, marker: &str) {
            record.evidence.retain(|evidence| {
                !matches!(evidence, ReconstructionValidationEvidence::Other(kind) if kind == marker)
            });
        }

        if let Some(validated) = artifact.reconstruction.validated_rust.as_mut() {
            for record in &mut validated.validation_records {
                retain_marker(record, marker);
            }
        }
        for output in &mut artifact.reconstruction.outputs {
            for record in &mut output.validation_records {
                retain_marker(record, marker);
            }
            if let Some(validated) = output.validated_rust.as_mut() {
                for record in &mut validated.validation_records {
                    retain_marker(record, marker);
                }
            }
        }
    }

    fn replace_rust_compile_back_evidence_value(
        artifact: &mut DecompilationArtifact,
        prefix: &str,
        replacement: &str,
    ) {
        fn replace_value(
            record: &mut ReconstructionValidationRecord,
            prefix: &str,
            replacement: &str,
        ) {
            for evidence in &mut record.evidence {
                let ReconstructionValidationEvidence::Other(kind) = evidence else {
                    continue;
                };
                if kind.starts_with(prefix) {
                    *kind = format!("{prefix}{replacement}");
                }
            }
        }

        if let Some(validated) = artifact.reconstruction.validated_rust.as_mut() {
            for record in &mut validated.validation_records {
                replace_value(record, prefix, replacement);
            }
        }
        for output in &mut artifact.reconstruction.outputs {
            for record in &mut output.validation_records {
                replace_value(record, prefix, replacement);
            }
            if let Some(validated) = output.validated_rust.as_mut() {
                for record in &mut validated.validation_records {
                    replace_value(record, prefix, replacement);
                }
            }
        }
    }

    fn synthetic_checked_binary_artifact_for_rust_reconstruction_gate() -> DecompilationArtifact {
        use trust_types::{ProofStrength, VcKind};

        let mut lifted = synthetic_lifted_binary_with_source(
            &[("proved_fn", 0x401000)],
            &[(0x401000, "src/proved.rs", 1, 1)],
        );
        lifted.functions[0].trust_ir_body = constant_return_trust_ir("proved_fn", 7).body;
        let options = DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrText]);
        let results = vec![(
            synthetic_vc("proved_fn", 0x401000, VcKind::DivisionByZero),
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"checked externally".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];
        let mut artifact = decompilation_artifact_from_lifted_with_verification_results(
            8, &options, &lifted, &results,
        )
        .expect("synthetic checked artifact");

        install_test_binary_artifact_digest_metadata(&mut artifact);
        mark_dispatches_checked_and_replayed(&mut artifact.verification.solver_dispatch);
        mark_dispatches_checked_and_replayed(
            &mut artifact.functions[0].verification.solver_dispatch,
        );
        artifact
    }

    fn install_synthetic_proof_grade_rust_reconstruction(artifact: &mut DecompilationArtifact) {
        let validated = synthetic_proof_grade_rust_reconstruction(&artifact.functions);
        let rust_text = artifact
            .functions
            .iter()
            .filter_map(|function| function.lifted.as_ref())
            .map(|lifted| {
                let function = DecompiledFunction {
                    name: lifted.name.clone(),
                    lifted: Some(lifted.clone()),
                    ..Default::default()
                };
                emit_strict_rust_subset(&function, lifted).expect("strict Rust fixture emission")
            })
            .collect::<Vec<_>>()
            .join("\n");

        artifact.target = DecompileTarget::Rust;
        artifact.reconstruction.target = DecompileTarget::Rust;
        artifact.reconstruction.validation = validated.status;
        artifact.reconstruction.trust_level = validated.trust_level;
        artifact.reconstruction.validated_rust = Some(validated.clone());
        artifact.reconstruction.outputs = vec![DecompiledOutput {
            target: DecompileTarget::Rust,
            text: Some(rust_text),
            validation: validated.status,
            trust_level: validated.trust_level,
            validation_records: validated.validation_records.clone(),
            validated_rust: Some(validated),
            diagnostics: vec![
                "synthetic strict Rust compile-back fixture".to_string(),
                "compile-back TrustIr refinement evidence is proof-grade".to_string(),
            ],
            ..DecompiledOutput::default()
        }];
        for output in &mut artifact.reconstruction.outputs {
            attach_binary_artifact_digest_identity_to_output(output, &artifact.binary);
        }
        attach_rust_compile_back_artifact_digest_bindings(artifact);
        install_rust_target_consumer_artifact_digest(artifact);
        refresh_source_backpropagation_authority(artifact);
    }

    fn synthetic_proof_grade_rust_reconstruction(
        functions: &[DecompiledFunction],
    ) -> ValidatedRustReconstruction {
        let candidates: Vec<_> = functions.iter().map(strict_rust_subset_candidate).collect();
        assert!(
            candidates.iter().all(|candidate| candidate.eligibility.eligible),
            "{:?}",
            candidates
        );
        let eligibility =
            candidates.iter().map(|candidate| candidate.eligibility.clone()).collect();
        let validation_records = candidates
            .iter()
            .map(|candidate| {
                rust_compile_back_validation_record(
                    candidate,
                    RustCompileBackEvidence::ProofGrade { proof_certificates: 2 },
                )
            })
            .collect::<Vec<_>>();
        assert!(
            validation_records.iter().all(rust_compile_back_record_allows_proof_grade),
            "{:?}",
            validation_records
        );

        ValidatedRustReconstruction {
            status: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            eligibility,
            validation_records,
            diagnostics: vec![
                "synthetic strict Rust reconstruction compiled back to TrustIr".to_string(),
                "both compile-back refinement directions have checked proof certificate evidence"
                    .to_string(),
            ],
        }
    }

    #[cfg(feature = "elf")]
    fn synthetic_real_binary_release_gate_artifact() -> DecompilationArtifact {
        const RET_ENCODING: u32 = 0xD65F03C0;
        let is_replaced_provenance_stage = |stage: &str| {
            matches!(stage, "trust-lift::source-provenance" | "trust-lift::type-provenance")
                || stage == PARSER_ARTIFACT_IDENTITY_STAGE
        };
        let is_replaced_target_blocker = |blocker: &TargetValidationBlocker| {
            is_replaced_provenance_stage(&blocker.stage)
                || (blocker.stage == "trust-ir-bridge::target-validation"
                    && blocker.feature == "symbolic-formula-proof-semantics")
        };
        let mut artifact = decompile_binary(
            &minimal_aarch64_elf_with_entry_instructions(&[RET_ENCODING]),
            DecompileOptions::default().with_outputs([DecompileOutputKind::TrustIrJson]),
        )
        .expect("AArch64 RET fixture should decompile through the public API");
        artifact.binary.path = Some("release/aarch64-ret-release-gate.elf".to_string());
        artifact.binary.build_id = Some("build-id:aarch64-ret-release-gate".to_string());

        assert_eq!(artifact.functions.len(), 1);
        assert!(
            artifact
                .unsupported
                .records
                .iter()
                .all(|record| is_replaced_provenance_stage(&record.stage)),
            "{:?}",
            artifact.unsupported.records
        );
        assert!(
            artifact.functions[0]
                .unsupported
                .records
                .iter()
                .all(|record| is_replaced_provenance_stage(&record.stage)),
            "{:?}",
            artifact.functions[0].unsupported.records
        );

        let entry = artifact.functions[0].entry;
        let function_name = artifact.functions[0].name.clone();
        let source = SourceSpan {
            file: "src/real_binary_gate.rs".to_string(),
            line_start: 11,
            col_start: 5,
            line_end: 11,
            col_end: 18,
        };
        let origin = BinaryOrigin {
            binary_path: artifact.binary.path.clone(),
            function_entry: Some(entry),
            instruction_address: entry,
            instruction_size: Some(4),
            encoding: Some(RET_ENCODING),
            instruction_bytes: RET_ENCODING.to_le_bytes().to_vec(),
            source: Some(source.clone()),
        };

        artifact.source_provenance = BinarySourceProvenanceSummary {
            status: "exact".to_string(),
            exact_mapping_count: 1,
            ambiguous_mapping_count: 0,
            diagnostics: vec![
                "recovered exact source provenance for AArch64 RET release-gate binary".to_string(),
            ],
            source_backpropagation_allowed: true,
        };
        artifact.unsupported.records.clear();
        artifact.functions[0].unsupported.records.clear();
        artifact.reconstruction.diagnostics.retain(|diagnostic| {
            !diagnostic.starts_with("unsupported records:")
                && !diagnostic.contains("source provenance")
                && !diagnostic.contains("symbolic formula")
        });
        for output in &mut artifact.reconstruction.outputs {
            assert!(
                output.target_validation_blockers.iter().all(&is_replaced_target_blocker),
                "{:?}",
                output.target_validation_blockers
            );
            output.target_validation_blockers.clear();
            output.preserved_symbolic_formulas.clear();
            output.diagnostics.retain(|diagnostic| {
                !diagnostic.starts_with("unsupported records:")
                    && !diagnostic.contains("source provenance")
                    && !diagnostic.contains("symbolic formula")
                    && !diagnostic.contains("formula-specific")
            });
        }
        for output in &mut artifact.reconstruction.outputs {
            if output.target != artifact.reconstruction.target {
                continue;
            }
            output
                .diagnostics
                .retain(|diagnostic| !target_consumer_acceptance_diagnostic(diagnostic));
            output.diagnostics.push(
                "target-consumer=accepted; target proof consumer accepted checked-certificate, replay, source provenance, symbolic formula, and reconstruction evidence"
                    .to_string(),
            );
        }

        {
            let function = &mut artifact.functions[0];
            function.origin = Some(origin.clone());
            function.instruction_provenance = vec![origin.clone()];
            let mut lifted = constant_return_trust_ir(&function.name, 0);
            lifted.span = source;
            function.lifted = Some(lifted);
        }

        let dispatch = SolverDispatchRecord {
            id: format!("{function_name}:0"),
            function: Some(function_name),
            origin: Some(origin),
            vc_kind: Some(trust_types::VcKind::Assertion {
                message: "AArch64 RET fixture proof obligation".to_string(),
            }),
            solver: "ay".to_string(),
            backend: Some("trust-bmc".to_string()),
            status: SolverDispatchStatus::Unsat,
            query_semantics: SolverQuerySemantics::SatIsCounterexample,
            binary_artifact_digest_identity: BinaryArtifactDigestIdentity::from_metadata(
                &artifact.binary,
            ),
            elapsed_ms: Some(1),
            replay: ReplayStatus::Replayed,
            certificate: ProofCertificateStatus::Checked {
                checker: "ay-cert-readback".to_string(),
                format: "lfsc-v1".to_string(),
                sha256: Some(
                    "1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef".to_string(),
                ),
            },
            diagnostics: vec![
                "checked certificate metadata read back from release gate".to_string(),
            ],
            ..Default::default()
        };

        artifact.verification =
            BinaryVerificationSummary::from_solver_dispatch(vec![dispatch.clone()]);
        artifact.verification.unsupported_ledger = artifact.unsupported.clone();
        artifact.verification.refresh_from_solver_dispatch();

        artifact.functions[0].verification =
            BinaryVerificationSummary::from_solver_dispatch(vec![dispatch]);
        artifact.functions[0].verification.unsupported_ledger =
            artifact.functions[0].unsupported.clone();
        artifact.functions[0].verification.refresh_from_solver_dispatch();

        refresh_trust_ir_json_outputs(&mut artifact);
        artifact
    }

    fn assert_source_backpropagation_fail_closed(
        artifact: &mut DecompilationArtifact,
        expected_blocker: &str,
        expected_kind: trust_types::BinarySourceProvenanceDiagnosticKind,
    ) {
        assert_eq!(artifact.source_provenance.status, "exact");
        assert!(artifact.source_provenance.has_exact_debug_source_provenance());
        assert!(!artifact.source_provenance.source_backpropagation_allowed);
        assert!(!artifact.source_provenance.effective_source_backpropagation_allowed());
        assert!(artifact.source_provenance.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("effective-source-backpropagation-allowed=false")
        }));
        assert!(artifact.source_provenance.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("source-backpropagation-blocker")
                && diagnostic.contains(expected_blocker)
        }));
        assert!(artifact.source_provenance.typed_diagnostics().iter().any(|diagnostic| {
            diagnostic.kind == expected_kind
                && !diagnostic.source_backpropagation_allowed
                && diagnostic.message.contains(expected_blocker)
        }));
        assert!(artifact.unsupported.records.iter().any(|record| {
            record.stage == SOURCE_PROVENANCE_GATE_STAGE
                && record.feature.contains(expected_blocker)
        }));
        assert!(!source_provenance_allows_artifact_proof_grade(&artifact.source_provenance));
        assert!(!artifact_source_provenance_allows_binary_proof_grade(artifact));
        assert!(!apply_binary_proof_grade_release_gate(artifact));
        assert_ne!(artifact.trust_level, TrustLevel::ProofGrade);
        assert_ne!(artifact.verification.trust_level, TrustLevel::ProofGrade);
        assert!(
            artifact
                .functions
                .iter()
                .all(|function| function.trust_level != TrustLevel::ProofGrade)
        );

        let json = trust_ir_json_output_json(artifact);
        let source = &json["source_provenance"];
        assert_eq!(source["status"], "exact");
        assert_eq!(source["source_backpropagation_allowed"], false);
        assert_eq!(source["effective_source_backpropagation_allowed"], false);
        assert!(
            source["diagnostics"]
                .as_array()
                .expect("serialized source provenance diagnostics")
                .iter()
                .any(|diagnostic| diagnostic
                    .as_str()
                    .is_some_and(|diagnostic| diagnostic.contains(expected_blocker))),
            "{source:?}"
        );
        assert!(
            source["typed_diagnostics"]
                .as_array()
                .expect("serialized source provenance typed diagnostics")
                .iter()
                .any(|diagnostic| {
                    diagnostic["kind"] == "source_backpropagation_rejected"
                        && diagnostic["source_backpropagation_allowed"] == false
                        && diagnostic["message"]
                            .as_str()
                            .is_some_and(|message| message.contains(expected_blocker))
                }),
            "{source:?}"
        );
    }

    fn assert_source_rewrite_authority_closed(
        artifact: &DecompilationArtifact,
        expected_blocker: &str,
    ) {
        assert_eq!(artifact.source_provenance.status, "exact");
        assert!(source_provenance_allows_artifact_proof_grade(&artifact.source_provenance));
        assert!(!artifact.source_provenance.source_backpropagation_allowed);
        assert!(!artifact.source_provenance.effective_source_backpropagation_allowed());
        assert!(
            artifact.source_provenance.diagnostics.iter().any(|diagnostic| {
                diagnostic.starts_with(SOURCE_REWRITE_AUTHORITY_BLOCKER_PREFIX)
                    && diagnostic.contains(expected_blocker)
            }),
            "{:?}",
            artifact.source_provenance.diagnostics
        );

        let json = trust_ir_json_output_json(artifact);
        let source = &json["source_provenance"];
        assert_eq!(source["source_backpropagation_allowed"], false);
        assert_eq!(source["effective_source_backpropagation_allowed"], false);
        assert!(
            source["diagnostics"]
                .as_array()
                .expect("serialized source provenance diagnostics")
                .iter()
                .any(|diagnostic| diagnostic.as_str().is_some_and(|diagnostic| {
                    diagnostic.starts_with(SOURCE_REWRITE_AUTHORITY_BLOCKER_PREFIX)
                        && diagnostic.contains(expected_blocker)
                })),
            "{source:?}"
        );
    }

    fn assert_binary_release_gate_closed(
        mut artifact: DecompilationArtifact,
        missing_gate: &str,
    ) -> DecompilationArtifact {
        assert!(
            !apply_binary_proof_grade_release_gate(&mut artifact),
            "proof-grade gate should remain closed without {missing_gate}"
        );
        assert_ne!(
            artifact.verification.trust_level,
            TrustLevel::ProofGrade,
            "artifact verification promoted without {missing_gate}"
        );
        assert_ne!(
            artifact.trust_level,
            TrustLevel::ProofGrade,
            "artifact promoted without {missing_gate}"
        );
        assert!(
            artifact
                .functions
                .iter()
                .all(|function| function.verification.trust_level != TrustLevel::ProofGrade
                    && function.trust_level != TrustLevel::ProofGrade),
            "function promoted without {missing_gate}"
        );
        artifact
    }

    fn assert_rust_reconstruction_release_gate_closed(
        artifact: DecompilationArtifact,
        missing_gate: &str,
    ) -> DecompilationArtifact {
        let artifact = assert_binary_release_gate_closed(artifact, missing_gate);
        assert_ne!(
            artifact.reconstruction.trust_level,
            TrustLevel::ProofGrade,
            "Rust reconstruction summary promoted without {missing_gate}"
        );
        if let Some(validated_rust) = artifact.reconstruction.validated_rust.as_ref() {
            assert_ne!(
                validated_rust.trust_level,
                TrustLevel::ProofGrade,
                "validated Rust summary promoted without {missing_gate}"
            );
        }
        for output in artifact
            .reconstruction
            .outputs
            .iter()
            .filter(|output| output.target == DecompileTarget::Rust)
        {
            assert_ne!(
                output.trust_level,
                TrustLevel::ProofGrade,
                "Rust output promoted without {missing_gate}"
            );
            if let Some(validated_rust) = output.validated_rust.as_ref() {
                assert_ne!(
                    validated_rust.trust_level,
                    TrustLevel::ProofGrade,
                    "Rust output validation summary promoted without {missing_gate}"
                );
            }
        }
        artifact
    }

    fn trust_ir_json_output_json(artifact: &DecompilationArtifact) -> serde_json::Value {
        let output = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
            .expect("TrustIr JSON output");
        serde_json::from_str(output.text.as_deref().expect("TrustIr JSON text"))
            .expect("TrustIr JSON should parse")
    }

    fn trust_ir_checked_certificate_bridge_json(
        artifact: &DecompilationArtifact,
    ) -> serde_json::Value {
        let json = trust_ir_json_output_json(artifact);
        json["checked_certificate_bridge"].clone()
    }

    #[cfg(feature = "elf")]
    #[test]
    fn decompiles_checked_in_x86_64_fixture_with_memory_origin_provenance() {
        const FIXTURE_SYMBOL: &str = "trust_fixture_x86_load";
        let bytes = decode_hex_fixture(include_str!(
            "../../../tests/fixtures/binary_decomp/x86_64-load-elf.hex"
        ));

        let artifact = decompile_binary(
            &bytes,
            DecompileOptions::with_lift(BinaryLiftOptions::functions_by_name([FIXTURE_SYMBOL]))
                .with_outputs([DecompileOutputKind::TrustIrJson]),
        )
        .expect("checked-in x86_64 ELF fixture should decompile through the public API");

        assert_eq!(artifact.binary.format, BinaryArtifactFormat::Elf);
        assert_eq!(artifact.binary.architecture, "x86-64");
        assert_eq!(artifact.binary.byte_len, Some(bytes.len() as u64));
        assert_eq!(artifact.functions.len(), 1);
        assert_eq!(artifact.source_provenance.status, "unavailable");
        assert!(!artifact.source_provenance.source_backpropagation_allowed);

        let function = &artifact.functions[0];
        assert_eq!(function.name, FIXTURE_SYMBOL);
        assert_eq!(function.coverage.instructions_discovered, 2);
        assert_eq!(function.coverage.instructions_lifted, 2);
        assert!(function.origin.as_ref().expect("function origin").span().is_binary());
        assert_eq!(function.lifted.as_ref().expect("lifted function").body.locals.len(), 24);
        assert_eq!(function.signature.calling_convention, BinaryCallingConvention::SystemV);
        assert!(
            function.signature.returns.iter().any(|return_slot| {
                matches!(
                    &return_slot.storage,
                    BinaryStorageLocation::Register { name, bit_width }
                        if name == "RAX" && *bit_width == Some(64)
                )
            }),
            "x86_64 return storage should preserve the SysV RAX default"
        );
        assert!(
            function.signature.parameters.iter().any(|parameter| {
                parameter.index == 0
                    && matches!(
                        &parameter.storage,
                        BinaryStorageLocation::Register { name, bit_width }
                            if name == "RDI" && *bit_width == Some(64)
                    )
            }),
            "x86_64 memory-base read should remain an observed RDI argument fact"
        );

        let load = function
            .memory_accesses
            .iter()
            .find(|access| access.origin.instruction_address == function.entry)
            .expect("MOV r64, [r/m64] should emit a memory-read fact");
        assert_eq!(load.kind, trust_types::MemoryAccessKind::Read);
        assert_eq!(load.width_bytes, 8);
        assert_eq!(load.region, trust_types::MemoryRegionKind::Unknown);
        assert_eq!(load.origin.instruction_size, Some(3));
        assert_eq!(load.origin.encoding, Some(0x89));
        assert_eq!(load.origin.instruction_bytes, vec![0x48, 0x8b, 0x07]);

        assert!(
            artifact.unsupported.records.iter().any(|record| {
                record.stage == "trust-lift::memory-provenance"
                    && record.architecture.as_deref() == Some("x86-64")
                    && record.feature == "unclassified memory region"
                    && record.origin.as_ref().is_some_and(|origin| {
                        origin.function_entry == Some(function.entry)
                            && origin.instruction_address == function.entry
                            && origin.instruction_size == Some(3)
                            && origin.encoding == Some(0x89)
                            && origin.instruction_bytes == vec![0x48, 0x8b, 0x07]
                    })
            }),
            "unsupported ledger should preserve x86_64 variable-length instruction provenance"
        );

        let trust_ir_json = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
            .expect("TrustIr JSON output");
        assert_eq!(trust_ir_json.validation, ReconstructionValidationStatus::Validated);
        assert_eq!(trust_ir_json.trust_level, TrustLevel::Partial);
        let json: serde_json::Value =
            serde_json::from_str(trust_ir_json.text.as_deref().expect("TrustIr JSON text"))
                .expect("TrustIr output should parse as JSON");
        assert_eq!(json["metadata"]["architecture"], "x86-64");
        assert_eq!(
            json["unsupported"]["records"].as_array().expect("unsupported records").len(),
            artifact.unsupported.records.len()
        );
    }

    #[cfg(feature = "elf")]
    #[test]
    fn decompiles_checked_in_x86_64_empty_ledger_slice_with_binary_evidence() {
        const FIXTURE_SYMBOL: &str = "trust_fixture_x86_empty_ledger";
        let bytes = decode_hex_fixture(include_str!(
            "../../../tests/fixtures/binary_decomp/x86_64-empty-ledger-nop-elf.hex"
        ));

        let artifact = decompile_binary(
            &bytes,
            DecompileOptions::with_lift(BinaryLiftOptions::functions_by_name([FIXTURE_SYMBOL]))
                .with_outputs([DecompileOutputKind::TrustIrJson]),
        )
        .expect("checked-in x86_64 empty-ledger ELF fixture should decompile");

        assert_eq!(artifact.binary.format, BinaryArtifactFormat::Elf);
        assert_eq!(artifact.binary.architecture, "x86-64");
        assert_eq!(artifact.binary.entry_point, Some(0x400000));
        assert_eq!(artifact.binary.byte_len, Some(bytes.len() as u64));
        assert_eq!(
            artifact.binary.build_id.as_deref(),
            Some("elf-gnu-build-id:000102030405060708090a0b0c0d0e0f10111213")
        );
        assert!(artifact.binary.digest_identity_allows_proof_grade());
        assert!(artifact.unsupported.records.is_empty(), "{:?}", artifact.unsupported.records);
        assert!(artifact.verification.unsupported_ledger.records.is_empty());
        assert_eq!(artifact.trust_level, TrustLevel::Partial);
        assert_eq!(artifact.functions.len(), 1);
        assert_eq!(artifact.functions[0].name, FIXTURE_SYMBOL);
        assert_eq!(artifact.functions[0].coverage.instructions_lifted, 1);
        assert!(artifact.functions[0].unsupported.records.is_empty());
        assert_eq!(artifact.source_provenance.status, "unavailable");
        assert!(!artifact.source_provenance.source_backpropagation_allowed);

        let json = trust_ir_json_output_json(&artifact);
        assert_eq!(json["metadata"]["architecture"], "x86-64");
        assert_eq!(json["unsupported"]["records"].as_array().unwrap().len(), 0);
        assert!(json["metadata"]["root_artifact_digest"]["value"].as_str().is_some());
        assert_eq!(json["metadata"]["selected_image"]["file_offset"], 0);
        assert_eq!(json["metadata"]["selected_image"]["file_size"], bytes.len() as u64);
    }

    #[cfg(feature = "elf")]
    fn decode_hex_fixture(text: &str) -> Vec<u8> {
        let compact: Vec<_> = text.bytes().filter(|byte| !byte.is_ascii_whitespace()).collect();
        assert_eq!(compact.len() % 2, 0, "hex fixture should contain whole bytes");
        compact.chunks(2).map(|pair| (hex_nibble(pair[0]) << 4) | hex_nibble(pair[1])).collect()
    }

    #[cfg(feature = "elf")]
    fn hex_nibble(byte: u8) -> u8 {
        match byte {
            b'0'..=b'9' => byte - b'0',
            b'a'..=b'f' => byte - b'a' + 10,
            b'A'..=b'F' => byte - b'A' + 10,
            _ => panic!("non-hex byte in fixture: {byte}"),
        }
    }

    #[cfg(feature = "elf")]
    #[test]
    fn decompiles_generated_elf_to_trust_ir_and_exploratory_rust_skeleton() {
        use std::fs;
        use std::path::{Path, PathBuf};
        use std::process::{Command, Output};

        const FIXTURE_SYMBOL: &str = "trust_fixture_return";
        const X86_64_RET_ASM: &str = r#"
    .text
    .byte 0x90
    .globl trust_fixture_return
    .type trust_fixture_return,@function
trust_fixture_return:
    movq %rdi, %rax
    retq
    .size trust_fixture_return, .-trust_fixture_return
    .section .note.GNU-stack,"",@progbits
"#;

        let tmp = tempfile::tempdir().expect("create temp fixture dir");
        let elf_path = match build_x86_64_elf_fixture(tmp.path(), X86_64_RET_ASM) {
            Ok(path) => path,
            Err(reason) => {
                eprintln!("SKIP: {reason}");
                return;
            }
        };

        let bytes = fs::read(&elf_path)
            .unwrap_or_else(|e| panic!("failed to read fixture {}: {e}", elf_path.display()));
        let artifact = decompile_binary(
            &bytes,
            DecompileOptions::with_lift(BinaryLiftOptions::functions_by_name([FIXTURE_SYMBOL]))
                .with_outputs([
                    DecompileOutputKind::TrustIrJson,
                    DecompileOutputKind::TrustIrText,
                    DecompileOutputKind::RustSkeleton,
                ]),
        )
        .expect("generated ELF fixture should decompile through the public API");

        assert_eq!(artifact.binary.format, BinaryArtifactFormat::Elf);
        assert_eq!(artifact.binary.architecture, "x86-64");
        assert_eq!(artifact.functions.len(), 1);
        assert_eq!(artifact.functions[0].name, FIXTURE_SYMBOL);
        assert_eq!(artifact.functions[0].entry, artifact.binary.symbols[0].address);
        assert!(artifact.functions[0].lifted.is_some());
        assert_eq!(
            &artifact.functions[0].signature.calling_convention,
            &BinaryCallingConvention::SystemV
        );
        assert_eq!(artifact.functions[0].signature.trust_level, TrustLevel::Partial);
        assert!(
            artifact.functions[0]
                .signature
                .assumptions
                .iter()
                .any(|assumption| assumption.stage == "trust-lift::summarize_function_signature")
        );
        assert!(
            artifact.functions[0]
                .signature
                .assumptions
                .iter()
                .any(|assumption| assumption.description.contains("not proof assumptions"))
        );

        let return_slot =
            artifact.functions[0].signature.returns.first().expect("ABI default return register");
        assert_eq!(return_slot.evidence, BinaryFactEvidence::AbiDefault);
        assert!(is_register(&return_slot.storage, "RAX"));

        let arg0 = artifact.functions[0]
            .signature
            .parameters
            .iter()
            .find(|parameter| parameter.index == 0)
            .expect("observed first argument register");
        assert_eq!(arg0.evidence, BinaryFactEvidence::RegisterUse);
        assert!(is_register(&arg0.storage, "RDI"));

        assert!(artifact.functions[0].abi_facts.iter().any(|fact| matches!(
            &fact.kind,
            BinaryAbiFactKind::CallingConvention(BinaryCallingConvention::SystemV)
        ) && fact.evidence
            == BinaryFactEvidence::AbiDefault
            && fact.confidence == BinaryFactConfidence::Heuristic
            && fact.trust_level == TrustLevel::Partial));
        assert!(artifact.functions[0].abi_facts.iter().any(|fact| matches!(
            &fact.kind,
            BinaryAbiFactKind::Return { index, location }
                if *index == 0 && is_register(location, "RAX")
        ) && fact.evidence
            == BinaryFactEvidence::AbiDefault
            && fact.confidence == BinaryFactConfidence::Heuristic));
        assert!(artifact.functions[0].abi_facts.iter().any(|fact| matches!(
            &fact.kind,
            BinaryAbiFactKind::Parameter { index, location }
                if *index == 0 && is_register(location, "RDI")
        ) && fact.evidence
            == BinaryFactEvidence::RegisterUse
            && fact.confidence == BinaryFactConfidence::Inferred));
        assert!(artifact.functions[0].storage_facts.iter().any(|fact| matches!(
            &fact.subject,
            BinaryFactSubject::Parameter { function, index }
                if function == FIXTURE_SYMBOL && *index == 0
        ) && is_register(
            &fact.location,
            "RDI"
        ) && fact.evidence
            == BinaryFactEvidence::RegisterUse
            && fact.confidence == BinaryFactConfidence::Inferred
            && fact.trust_level == TrustLevel::Partial));
        assert!(artifact.functions[0].abi_facts.iter().all(|fact| {
            fact.evidence != BinaryFactEvidence::Assumption
                && fact.trust_level == TrustLevel::Partial
        }));
        assert_eq!(artifact.abi_facts, artifact.functions[0].abi_facts);
        assert_eq!(artifact.storage_facts, artifact.functions[0].storage_facts);
        assert_eq!(artifact.call_graph.nodes.len(), 1);
        assert_eq!(artifact.trust_level, TrustLevel::Exploratory);
        assert_ne!(artifact.reconstruction.validation, ReconstructionValidationStatus::Validated);
        assert_ne!(artifact.reconstruction.trust_level, TrustLevel::ProofGrade);
        assert!(
            artifact
                .unsupported
                .records
                .iter()
                .any(|record| record.feature.contains("Rust skeleton is exploratory"))
        );

        let trust_ir_json = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.diagnostics.iter().any(|diag| diag == "format=trust_ir-json"))
            .expect("TrustIr JSON output");
        assert_eq!(trust_ir_json.target, DecompileTarget::TrustIr);
        assert_eq!(trust_ir_json.validation, ReconstructionValidationStatus::Validated);
        assert_eq!(trust_ir_json.trust_level, TrustLevel::Partial);
        assert_eq!(trust_ir_json.validation_records.len(), 1);
        assert_eq!(
            trust_ir_json.validation_records[0].candidate,
            ReconstructionCandidateKind::StructuredTrustIr
        );
        assert_eq!(trust_ir_json.validation_records[0].trust_level, TrustLevel::Partial);
        assert_ne!(trust_ir_json.validation_records[0].trust_level, TrustLevel::ProofGrade);
        assert!(trust_ir_json.validation_records[0].forward.is_some());
        assert!(trust_ir_json.validation_records[0].reverse.is_some());
        let trust_ir_json_text = trust_ir_json.text.as_deref().expect("TrustIr JSON text");
        assert!(trust_ir_json_text.contains(FIXTURE_SYMBOL));
        serde_json::from_str::<serde_json::Value>(trust_ir_json_text)
            .expect("TrustIr output should be JSON");

        let rust = artifact
            .reconstruction
            .outputs
            .iter()
            .find(|output| output.target == DecompileTarget::Rust)
            .expect("Rust skeleton output");
        assert_eq!(rust.validation, ReconstructionValidationStatus::NotAttempted);
        assert_eq!(rust.trust_level, TrustLevel::Exploratory);
        assert_ne!(rust.validation, ReconstructionValidationStatus::Validated);
        assert!(
            rust.diagnostics.iter().any(|diag| diag.contains("not validated")),
            "Rust skeleton output must stay explicitly unvalidated"
        );
        assert_eq!(rust.validation_records.len(), 1);
        let rust_validation = &rust.validation_records[0];
        assert_eq!(rust_validation.target, DecompileTarget::Rust);
        assert_eq!(rust_validation.function.as_deref(), Some(FIXTURE_SYMBOL));
        assert_eq!(rust_validation.lifted_function.as_deref(), Some(FIXTURE_SYMBOL));
        assert_eq!(rust_validation.candidate, ReconstructionCandidateKind::TextOnly);
        assert_eq!(rust_validation.status, ReconstructionValidationStatus::NotAttempted);
        assert_eq!(rust_validation.trust_level, TrustLevel::Exploratory);
        assert!(rust_validation.forward.is_none());
        assert!(rust_validation.reverse.is_none());
        assert!(
            rust_validation
                .diagnostics
                .iter()
                .any(|diag| diag.contains("no structured reconstructed TrustIr candidate")),
            "Rust skeleton validation record must make text-only status explicit"
        );
        let rust_text = rust.text.as_deref().expect("Rust skeleton text");
        assert!(rust_text.contains("Exploratory partial Rust skeleton"));
        assert!(rust_text.contains("not validated Rust reconstruction"));
        assert!(rust_text.contains("pub unsafe fn trust_fixture_return()"));

        fn build_x86_64_elf_fixture(dir: &Path, asm: &str) -> Result<PathBuf, String> {
            let asm_path = dir.join("trust_decompile_return.s");
            let obj_path = dir.join("trust_decompile_return.o");
            fs::write(&asm_path, asm).map_err(|e| {
                format!("could not write fixture assembly {}: {e}", asm_path.display())
            })?;

            let mut attempts = Vec::new();
            for compiler in candidate_compilers() {
                for args in compiler_arg_sets() {
                    let _ = fs::remove_file(&obj_path);
                    let mut cmd = Command::new(&compiler);
                    cmd.args(&args).arg("-c").arg("-x").arg("assembler").arg(&asm_path);
                    cmd.arg("-o").arg(&obj_path);

                    match cmd.output() {
                        Ok(output) if output.status.success() && obj_path.exists() => {
                            return Ok(obj_path);
                        }
                        Ok(output) => attempts.push(format_attempt(&compiler, &args, &output)),
                        Err(e) => attempts.push(format!("{compiler} {:?}: {e}", args)),
                    }
                }
            }

            Err(format!(
                "could not build deterministic x86_64 ELF fixture; tried {}",
                attempts.join("; ")
            ))
        }

        fn candidate_compilers() -> Vec<String> {
            let mut compilers = Vec::new();
            if let Ok(cc) = std::env::var("TRUST_TEST_CC")
                && !cc.trim().is_empty()
            {
                compilers.push(cc);
            }
            compilers.push("clang".to_string());
            compilers.push("cc".to_string());
            compilers.dedup();
            compilers
        }

        fn compiler_arg_sets() -> Vec<Vec<&'static str>> {
            let mut arg_sets = vec![vec!["--target=x86_64-unknown-linux-gnu"]];
            if std::env::consts::OS == "linux" && std::env::consts::ARCH == "x86_64" {
                arg_sets.push(vec![]);
            }
            arg_sets
        }

        fn format_attempt(compiler: &str, args: &[&str], output: &Output) -> String {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stderr = stderr.trim();
            let detail =
                if stderr.is_empty() { "no stderr".to_string() } else { stderr.to_string() };
            format!("{compiler} {args:?} exited with {} ({detail})", output.status)
        }

        fn is_register(location: &BinaryStorageLocation, expected: &str) -> bool {
            matches!(
                location,
                BinaryStorageLocation::Register { name, bit_width }
                    if name == expected && *bit_width == Some(64)
            )
        }
    }
}
