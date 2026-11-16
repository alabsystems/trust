// trust_vcgen/binary_analysis/relift.rs: compiled-binary relift verification API
//
// Takes compiled binary bytes, re-lifts them through trust-lift, generates
// binary verification conditions, and returns a reusable diagnostic summary.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::path::Path;

use serde::{Deserialize, Serialize};
use trust_lift::{
    BinaryLiftOptions, LiftError as TrustLiftError, LiftedBinary, LiftedFunction,
    LiftedSourceProvenanceStatus, lift_binary_to_trust_ir,
};
use trust_types::{
    BinaryArtifactDigest, BinaryArtifactMetadata, BinaryImageKind, BinarySelectedImageIdentity,
    BinarySourceProvenanceSummary, BinaryVerificationSummary, ReplayStatus, SerializableVc,
    SolverDispatchRecord, SolverDispatchStatus, SourceSpan, UnsupportedLedger, VcKind,
    VerifiableFunction, VerificationCondition, stable_sha256_hex,
};

use crate::{
    binary_security_family_counts, classify_binary_security_vc, generate_binary_vcs,
    lift_to_verifiable,
};

/// Options for compiled-binary relift analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(Default)]
pub struct BinaryReliftOptions {
    /// Function selection and strictness forwarded to `trust-lift`.
    pub lift: BinaryLiftOptions,
    /// Optional path recorded in binary metadata and diagnostics.
    pub binary_path: Option<String>,
}

impl BinaryReliftOptions {
    /// Analyze all recovered function symbols in best-effort mode.
    #[must_use]
    pub fn all_functions_best_effort() -> Self {
        Self { lift: BinaryLiftOptions::all_functions().best_effort(), ..Self::default() }
    }

    /// Attach a binary path for metadata only.
    #[must_use]
    pub fn with_binary_path(mut self, path: impl AsRef<Path>) -> Self {
        self.binary_path = Some(path.as_ref().display().to_string());
        self
    }
}

/// Severity for relift diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BinaryReliftDiagnosticSeverity {
    Info,
    Warning,
    Error,
}

/// One binary relift diagnostic.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryReliftDiagnostic {
    /// Stable machine-readable diagnostic code.
    pub code: String,
    /// Diagnostic severity.
    pub severity: BinaryReliftDiagnosticSeverity,
    /// Function associated with the diagnostic, if known.
    pub function: Option<String>,
    /// Binary or exact source location associated with the diagnostic.
    pub location: SourceSpan,
    /// Human-readable diagnostic text.
    pub message: String,
    /// Source backpropagation is never granted by diagnostics alone.
    pub source_backpropagation_allowed: bool,
}

/// Re-lifted TrustIr plus generated binary VCs and gate summaries.
#[derive(Debug, Clone)]
pub struct BinaryReliftAnalysis {
    /// Metadata and TrustIr produced by `trust-lift`.
    pub lifted: LiftedBinary,
    /// Lifted functions converted to `trust-types::VerifiableFunction`.
    pub verifiable_functions: Vec<VerifiableFunction>,
    /// Generated binary verification conditions.
    pub vcs: Vec<VerificationCondition>,
    /// Conservative VC summary. Relift alone does not prove VCs.
    pub verification: BinaryVerificationSummary,
    /// Source provenance summary derived from exact debug/source mappings.
    pub source_provenance: BinarySourceProvenanceSummary,
    /// Binary artifact metadata and replay-grade digest identity material.
    pub binary: BinaryArtifactMetadata,
    /// Stable counts grouped by binary security family.
    pub binary_security_family_counts: BTreeMap<String, usize>,
    /// Human-readable and machine-readable diagnostics.
    pub diagnostics: Vec<BinaryReliftDiagnostic>,
}

impl BinaryReliftAnalysis {
    /// True only when the lifted binary carried complete exact source mappings.
    ///
    /// This is a provenance readiness bit, not rewrite permission. Source
    /// rewriting still requires `trust-backprop` evidence gates.
    #[must_use]
    pub fn source_provenance_allows_backpropagation(&self) -> bool {
        self.source_provenance.effective_source_backpropagation_allowed()
    }
}

/// Error from compiled-binary relift analysis.
#[derive(Debug, thiserror::Error)]
pub enum BinaryReliftError {
    /// Binary parsing or lifting failed.
    #[error("binary relift failed: {0}")]
    Lift(#[from] TrustLiftError),
}

/// Take compiled binary bytes, re-lift them to TrustIr, and generate binary VCs.
///
/// The returned verification summary is intentionally conservative: generated
/// VCs are marked `NotDispatched`/`Unknown` until an external solver and
/// checked-certificate path proves them.
///
/// # Errors
///
/// Returns [`BinaryReliftError`] if binary parsing/lifting fails.
pub fn analyze_compiled_binary(
    bytes: &[u8],
    options: BinaryReliftOptions,
) -> Result<BinaryReliftAnalysis, BinaryReliftError> {
    let lifted = lift_binary_to_trust_ir(bytes, options.lift)?;
    Ok(analyze_lifted_binary(bytes, lifted, options.binary_path))
}

/// Generate binary VCs and diagnostics from an already lifted binary.
#[must_use]
pub fn analyze_lifted_binary(
    bytes: &[u8],
    lifted: LiftedBinary,
    binary_path: Option<String>,
) -> BinaryReliftAnalysis {
    let verifiable_functions = lifted.functions.iter().map(lift_to_verifiable).collect::<Vec<_>>();
    let vcs = lifted.functions.iter().flat_map(generate_binary_vcs).collect::<Vec<_>>();
    let binary = binary_metadata(bytes, &lifted, binary_path);
    let unsupported_ledger = unsupported_ledger(&lifted);
    let source_provenance = source_provenance_summary(&lifted);
    let verification = verification_summary(&vcs, unsupported_ledger);
    let binary_security_family_counts = binary_security_family_counts(&vcs);
    let diagnostics = diagnostics_for_relift(&lifted, &vcs, &source_provenance, &verification);

    BinaryReliftAnalysis {
        lifted,
        verifiable_functions,
        vcs,
        verification,
        source_provenance,
        binary,
        binary_security_family_counts,
        diagnostics,
    }
}

fn binary_metadata(
    bytes: &[u8],
    lifted: &LiftedBinary,
    binary_path: Option<String>,
) -> BinaryArtifactMetadata {
    let sha256 = stable_sha256_hex(bytes);
    BinaryArtifactMetadata {
        path: binary_path,
        format: binary_format(lifted.format),
        image_kind: BinaryImageKind::Executable,
        architecture: lifted.architecture.to_string(),
        base_address: lifted.segments.iter().map(|segment| segment.virtual_range.start).min(),
        entry_point: lifted.entry_point,
        byte_len: u64::try_from(bytes.len()).ok(),
        build_id: lifted.build_id.clone(),
        root_artifact_digest: Some(BinaryArtifactDigest::sha256(sha256.clone())),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: 0,
            file_size: u64::try_from(bytes.len()).unwrap_or(0),
            sha256,
        }),
        segments: lifted.segments.clone(),
        symbols: vec![],
    }
}

fn binary_format(format: &str) -> trust_types::BinaryArtifactFormat {
    match format {
        "ELF" | "elf" => trust_types::BinaryArtifactFormat::Elf,
        "Mach-O" | "MachO" | "macho" => trust_types::BinaryArtifactFormat::MachO,
        "Fat Mach-O" | "FatMachO" | "fat_macho" => trust_types::BinaryArtifactFormat::FatMachO,
        "PE/COFF" | "PE" | "pe" => trust_types::BinaryArtifactFormat::Pe,
        _ => trust_types::BinaryArtifactFormat::Unknown,
    }
}

fn unsupported_ledger(lifted: &LiftedBinary) -> UnsupportedLedger {
    let mut ledger = UnsupportedLedger::default();
    for function in &lifted.functions {
        ledger.records.extend(function.unsupported.records.iter().cloned());
    }
    ledger
}

fn source_provenance_summary(lifted: &LiftedBinary) -> BinarySourceProvenanceSummary {
    let blockers = source_backpropagation_gate_blockers(lifted);
    let source_backpropagation_allowed = lifted.source_provenance.status
        == LiftedSourceProvenanceStatus::Exact
        && lifted.source_provenance.exact_mapping_count > 0
        && lifted.source_provenance.ambiguous_mapping_count == 0
        && blockers.is_empty();

    let mut diagnostics = lifted.source_provenance.diagnostics.clone();
    diagnostics
        .push(format!("source-provenance-status={}", lifted.source_provenance.status.name()));
    diagnostics.push(format!("source-backpropagation-allowed={source_backpropagation_allowed}"));
    diagnostics
        .extend(blockers.iter().map(|blocker| format!("source-backpropagation-blocker={blocker}")));

    BinarySourceProvenanceSummary {
        status: lifted.source_provenance.status.name().to_string(),
        exact_mapping_count: lifted.source_provenance.exact_mapping_count,
        ambiguous_mapping_count: lifted.source_provenance.ambiguous_mapping_count,
        diagnostics,
        source_backpropagation_allowed,
    }
}

fn source_backpropagation_gate_blockers(lifted: &LiftedBinary) -> Vec<String> {
    if lifted.source_provenance.status != LiftedSourceProvenanceStatus::Exact {
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

    let unmapped_functions = lifted
        .functions
        .iter()
        .filter(|function| exact_non_binary_source_span(lifted, function.entry_point).is_none())
        .map(|function| format!("{}@0x{:x}", function.name, function.entry_point))
        .collect::<Vec<_>>();
    if !unmapped_functions.is_empty() {
        blockers.push(format!(
            "partial exact source mapping: {} lifted function entry address(es) lack exact source spans: {}",
            unmapped_functions.len(),
            unmapped_functions.join(", ")
        ));
    }

    let unmapped_instructions = lifted
        .functions
        .iter()
        .flat_map(|function| {
            instruction_addresses(function)
                .into_iter()
                .filter(|&address| exact_non_binary_source_span(lifted, address).is_none())
                .map(|address| format!("{}@0x{address:x}", function.name))
        })
        .collect::<Vec<_>>();
    if !unmapped_instructions.is_empty() {
        blockers.push(format!(
            "partial exact source mapping: {} lifted instruction address(es) lack exact source spans: {}",
            unmapped_instructions.len(),
            unmapped_instructions.join(", ")
        ));
    }

    blockers
}

fn exact_non_binary_source_span(lifted: &LiftedBinary, address: u64) -> Option<SourceSpan> {
    lifted.exact_source_span(address).filter(|span| !span.is_binary())
}

fn instruction_addresses(function: &LiftedFunction) -> Vec<u64> {
    function
        .cfg
        .blocks
        .iter()
        .flat_map(|block| block.instructions.iter().map(|instruction| instruction.address))
        .chain(function.annotations.iter().map(|annotation| annotation.binary_offset))
        .collect()
}

fn verification_summary(
    vcs: &[VerificationCondition],
    unsupported_ledger: UnsupportedLedger,
) -> BinaryVerificationSummary {
    let mut summary = BinaryVerificationSummary::from_solver_dispatch(
        vcs.iter().enumerate().map(dispatch_record_for_vc).collect(),
    );
    summary.unsupported_ledger = unsupported_ledger;
    summary.refresh_from_solver_dispatch();
    summary
}

fn dispatch_record_for_vc((index, vc): (usize, &VerificationCondition)) -> SolverDispatchRecord {
    SolverDispatchRecord {
        id: format!("relift-vc-{index:06}"),
        function: Some(vc.function.as_str().to_string()),
        origin: None,
        vc_kind: Some(vc.kind.clone()),
        vc: Some(SerializableVc::from_vc(vc)),
        solver: "trust_vcgen::relift".to_string(),
        status: SolverDispatchStatus::NotDispatched,
        query_semantics: Default::default(),
        replay: ReplayStatus::NotAttempted,
        diagnostics: vec![
            "compiled binary was re-lifted and VC was generated; solver dispatch and checked certificate evidence are still required".to_string(),
        ],
        ..SolverDispatchRecord::default()
    }
}

fn diagnostics_for_relift(
    lifted: &LiftedBinary,
    vcs: &[VerificationCondition],
    source_provenance: &BinarySourceProvenanceSummary,
    verification: &BinaryVerificationSummary,
) -> Vec<BinaryReliftDiagnostic> {
    let mut diagnostics = Vec::with_capacity(2 + lifted.failures.len() + vcs.len());
    diagnostics.push(BinaryReliftDiagnostic {
        code: "binary-relift-complete".to_string(),
        severity: BinaryReliftDiagnosticSeverity::Info,
        function: None,
        location: lifted.entry_point.map_or_else(SourceSpan::default, SourceSpan::binary_address),
        message: format!(
            "re-lifted {} function(s), generated {} binary VC(s); verification status is {:?}",
            lifted.functions.len(),
            vcs.len(),
            verification.status
        ),
        source_backpropagation_allowed: false,
    });

    diagnostics.extend(lifted.failures.iter().map(|failure| BinaryReliftDiagnostic {
        code: "binary-function-lift-failed".to_string(),
        severity: BinaryReliftDiagnosticSeverity::Error,
        function: failure.name.clone(),
        location: SourceSpan::binary_address(failure.entry_point),
        message: failure.error.clone(),
        source_backpropagation_allowed: false,
    }));

    if !source_provenance.effective_source_backpropagation_allowed() {
        diagnostics.push(BinaryReliftDiagnostic {
            code: "source-backpropagation-provenance-gate-closed".to_string(),
            severity: BinaryReliftDiagnosticSeverity::Warning,
            function: None,
            location: lifted
                .entry_point
                .map_or_else(SourceSpan::default, SourceSpan::binary_address),
            message: format!(
                "source backpropagation remains closed: status={}, exact_mappings={}, ambiguous_mappings={}",
                source_provenance.status,
                source_provenance.exact_mapping_count,
                source_provenance.ambiguous_mapping_count
            ),
            source_backpropagation_allowed: false,
        });
    }

    diagnostics.extend(vcs.iter().map(diagnostic_for_vc));
    diagnostics
}

fn diagnostic_for_vc(vc: &VerificationCondition) -> BinaryReliftDiagnostic {
    let (code, severity) = match &vc.kind {
        VcKind::UnsupportedMir { .. } => {
            ("binary-vc-unsupported-semantics".to_string(), BinaryReliftDiagnosticSeverity::Error)
        }
        _ => match classify_binary_security_vc(vc) {
            Some(classification) => (
                format!("binary-security-vc-{}", classification.family.stable_id()),
                BinaryReliftDiagnosticSeverity::Error,
            ),
            None => ("binary-vc-generated".to_string(), BinaryReliftDiagnosticSeverity::Warning),
        },
    };

    BinaryReliftDiagnostic {
        code,
        severity,
        function: Some(vc.function.as_str().to_string()),
        location: vc.location.clone(),
        message: vc.kind.description(),
        source_backpropagation_allowed: false,
    }
}

#[cfg(test)]
mod tests {
    use trust_lift::binary::{
        BinaryEndianness, LiftedFunctionSeed, LiftedFunctionSeedSource, LiftedSourceMapping,
        LiftedSourceProvenance,
    };
    use trust_lift::cfg::{Cfg, LiftedBlock};
    use trust_types::{
        BasicBlock, BinaryMemoryModel, BlockId, LocalDecl, Operand, Place, Rvalue, Statement,
        Terminator, Ty, VerifiableBody,
    };

    use super::*;

    fn test_lifted_function(span: SourceSpan) -> LiftedFunction {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x401000,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        LiftedFunction {
            name: "test_add".to_string(),
            entry_point: 0x401000,
            cfg,
            trust_ir_body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u64(), name: Some("_0".to_string()) },
                    LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".to_string()) },
                    LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".to_string()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            trust_types::BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span,
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::u64(),
                datatype_defs: Default::default(),
            },
            ssa: None,
            annotations: vec![],
            memory_accesses: vec![],
            trust_level: trust_types::TrustLevel::Partial,
            unsupported: UnsupportedLedger::default(),
        }
    }

    fn test_lifted_binary(source_provenance: LiftedSourceProvenance) -> LiftedBinary {
        LiftedBinary {
            format: "ELF",
            architecture: "x86-64",
            endianness: BinaryEndianness::Little,
            entry_point: Some(0x401000),
            build_id: Some("test-build".to_string()),
            segments: vec![],
            memory_model: BinaryMemoryModel::default(),
            function_seeds: vec![LiftedFunctionSeed {
                name: Some("test_add".to_string()),
                entry_point: 0x401000,
                size: Some(4),
                source: LiftedFunctionSeedSource::Symbol,
            }],
            source_mappings: vec![LiftedSourceMapping {
                binary_address: 0x401000,
                source: SourceSpan {
                    file: "src/lib.rs".to_string(),
                    line_start: 3,
                    col_start: 1,
                    line_end: 3,
                    col_end: 10,
                },
            }],
            functions: vec![test_lifted_function(SourceSpan::binary_address(0x401000))],
            failures: vec![],
            source_provenance,
        }
    }

    #[test]
    fn relift_analysis_generates_vc_summary_without_proof_grade_claim() {
        let lifted = test_lifted_binary(LiftedSourceProvenance::default());
        let analysis = analyze_lifted_binary(b"\x90", lifted, Some("target/debug/app".into()));

        assert!(!analysis.vcs.is_empty());
        assert_eq!(analysis.verification.total_vcs, analysis.vcs.len());
        assert_eq!(analysis.verification.proved, 0);
        assert_eq!(analysis.verification.unknown, analysis.vcs.len());
        assert!(!analysis.source_provenance.effective_source_backpropagation_allowed());
        assert!(
            analysis.diagnostics.iter().any(
                |diagnostic| diagnostic.code == "source-backpropagation-provenance-gate-closed"
            )
        );
    }

    #[test]
    fn exact_source_provenance_requires_materialized_mapping_for_every_entry() {
        let mut lifted = test_lifted_binary(LiftedSourceProvenance {
            status: LiftedSourceProvenanceStatus::Exact,
            exact_mapping_count: 1,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
        });
        lifted.source_mappings.clear();

        let analysis = analyze_lifted_binary(b"\x90", lifted, None);

        assert_eq!(analysis.source_provenance.status, "exact");
        assert!(!analysis.source_provenance.effective_source_backpropagation_allowed());
        assert!(analysis.source_provenance.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("exact source mapping count 1 does not match 0")
        }));
    }

    #[test]
    fn complete_exact_source_provenance_opens_provenance_readiness_only() {
        let lifted = test_lifted_binary(LiftedSourceProvenance {
            status: LiftedSourceProvenanceStatus::Exact,
            exact_mapping_count: 1,
            ambiguous_mapping_count: 0,
            diagnostics: vec!["exact test provenance".to_string()],
        });

        let analysis = analyze_lifted_binary(b"\x90", lifted, None);

        assert!(analysis.source_provenance.effective_source_backpropagation_allowed());
        assert!(analysis.source_provenance_allows_backpropagation());
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|diagnostic| { !diagnostic.source_backpropagation_allowed })
        );
    }

    #[test]
    fn binary_metadata_records_replay_digest_identity() {
        let lifted = test_lifted_binary(LiftedSourceProvenance::default());
        let analysis = analyze_lifted_binary(b"abc", lifted, Some("bin/app".into()));

        assert_eq!(analysis.binary.path.as_deref(), Some("bin/app"));
        assert_eq!(analysis.binary.byte_len, Some(3));
        assert!(analysis.binary.digest_identity_allows_proof_grade());
        assert_eq!(analysis.binary.selected_image.as_ref().map(|image| image.file_size), Some(3));
    }

    #[test]
    fn source_mapping_to_binary_span_is_not_exact_source_evidence() {
        let mut lifted = test_lifted_binary(LiftedSourceProvenance {
            status: LiftedSourceProvenanceStatus::Exact,
            exact_mapping_count: 1,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
        });
        lifted.source_mappings[0].source = SourceSpan {
            file: "binary:0x401000".to_string(),
            line_start: 0,
            col_start: 0,
            line_end: 0,
            col_end: 0,
        };

        let analysis = analyze_lifted_binary(b"\x90", lifted, None);

        assert!(!analysis.source_provenance.effective_source_backpropagation_allowed());
        assert!(
            analysis
                .source_provenance
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.contains("lack exact source spans") })
        );
    }

    /// `analyze_compiled_binary` on REAL bytes: parse -> lift -> analyze.
    ///
    /// The tests above feed `analyze_lifted_binary` a hand-built `LiftedBinary`.
    /// These feed the public entry point real ELF and Mach-O images, the path
    /// that trust-lift's default-on `elf`/`macho` features (cdcc3bee15) made live:
    /// before that commit every call here returned
    /// `LiftError::BinaryParserUnavailable`.
    mod compiled_binary {
        use trust_lift::LiftError as TrustLiftError;
        use trust_types::{
            BinaryArtifactDigest, BinaryArtifactFormat, BinaryVerificationStatus,
            ProofCertificateStatus, ReplayStatus, SolverDispatchStatus, TrustLevel, Ty, VcKind,
            VerificationCondition, stable_sha256_hex,
        };

        use super::super::{
            BinaryReliftAnalysis, BinaryReliftError, BinaryReliftOptions, analyze_compiled_binary,
            analyze_lifted_binary,
        };

        /// x86-64 ELF, 576 bytes: `trust_fixture_x86_load` = `mov rax, [rdi]; ret`
        /// at 0x400000 (also `e_entry`). Shared with trust-integration-tests,
        /// trust-symex and trust-decompile, which pin the same digest.
        const X86_64_LOAD_ELF_HEX: &str =
            include_str!("../../../../tests/fixtures/binary_decomp/x86_64-load-elf.hex");
        const X86_64_LOAD_ELF_SHA256: &str =
            "251757e36749c41d81a42feb4764e9ed80c354990f9de66858a498e549524000";
        const X86_64_LOAD_ELF_ENTRY: u64 = 0x40_0000;

        /// AArch64 Mach-O, 288 bytes: `_trust_fixture_aarch64_load` =
        /// `ldr x0, [x0]; ret` at 0x1_0000_00e8 (also LC_MAIN). The file documents
        /// every field and how it was produced.
        const AARCH64_LOAD_MACHO_HEX: &str =
            include_str!("../../tests/fixtures/relift_aarch64_load_macho.hex");
        const AARCH64_LOAD_MACHO_SHA256: &str =
            "e541ad3162bd438840e7ea9f05e117755f57d5948f96f943f6f382392b82df77";
        const AARCH64_LOAD_MACHO_ENTRY: u64 = 0x1_0000_00e8;

        /// Decode a hex fixture (`#` starts a comment) and pin its digest, so a
        /// drifted fixture fails here instead of silently testing other bytes.
        fn fixture_bytes(hex_text: &str, expected_sha256: &str) -> Vec<u8> {
            let hex = hex_text
                .lines()
                .map(|line| line.split('#').next().unwrap_or_default())
                .flat_map(str::chars)
                .filter(|ch| !ch.is_whitespace())
                .collect::<String>();
            assert!(!hex.is_empty() && hex.len() % 2 == 0, "malformed hex fixture");
            let bytes = (0..hex.len())
                .step_by(2)
                .map(|index| {
                    u8::from_str_radix(&hex[index..index + 2], 16)
                        .unwrap_or_else(|error| panic!("bad hex at {index}: {error}"))
                })
                .collect::<Vec<_>>();
            assert_eq!(stable_sha256_hex(&bytes), expected_sha256, "fixture bytes drifted");
            bytes
        }

        fn elf_bytes() -> Vec<u8> {
            fixture_bytes(X86_64_LOAD_ELF_HEX, X86_64_LOAD_ELF_SHA256)
        }

        fn macho_bytes() -> Vec<u8> {
            fixture_bytes(AARCH64_LOAD_MACHO_HEX, AARCH64_LOAD_MACHO_SHA256)
        }

        fn relift(bytes: &[u8]) -> BinaryReliftAnalysis {
            analyze_compiled_binary(bytes, BinaryReliftOptions::default())
                .unwrap_or_else(|error| panic!("real fixture must relift: {error}"))
        }

        /// THE SOUNDNESS PROMISE of `analyze_compiled_binary`: relift generates
        /// VCs but never discharges one. Every VC is `NotDispatched` and counted
        /// `unknown`; nothing is proved, refuted, certified or replayed, and no
        /// lifted function or summary claims `ProofGrade`. Non-vacuous: the
        /// fixture must yield at least one lifted function AND at least one VC.
        fn assert_no_vc_is_claimed_discharged(analysis: &BinaryReliftAnalysis, label: &str) {
            assert!(!analysis.lifted.functions.is_empty(), "{label}: no function lifted");
            assert!(
                !analysis.vcs.is_empty(),
                "{label}: no VC generated, the check would be vacuous"
            );
            assert_eq!(analysis.verifiable_functions.len(), analysis.lifted.functions.len());

            let verification = &analysis.verification;
            assert_eq!(verification.total_vcs, analysis.vcs.len(), "{label}");
            assert_eq!(verification.solver_dispatch.len(), analysis.vcs.len(), "{label}");
            for record in &verification.solver_dispatch {
                assert_eq!(
                    record.status,
                    SolverDispatchStatus::NotDispatched,
                    "{label}: {} claims a solver outcome without a solver",
                    record.id
                );
                assert!(record.result.is_none(), "{label}: {} carries a verdict", record.id);
                assert_eq!(record.certificate, ProofCertificateStatus::NotRequested, "{label}");
                assert_eq!(record.replay, ReplayStatus::NotAttempted, "{label}");
            }

            assert_eq!(verification.proved, 0, "{label}: relift reported a VC PROVED");
            assert_eq!(verification.failed, 0, "{label}: relift reported a VC REFUTED");
            assert_eq!(verification.unknown, analysis.vcs.len(), "{label}: not all VCs unknown");
            // `unsupported` counts ledger records on top of the VCs; with any, the
            // aggregate is `Mixed` (unknown + unsupported), never `Proved`.
            let expected_status = if verification.unsupported == 0 {
                BinaryVerificationStatus::Unknown
            } else {
                BinaryVerificationStatus::Mixed
            };
            assert_eq!(verification.status, expected_status, "{label}");
            assert_ne!(verification.trust_level, TrustLevel::ProofGrade, "{label}");
            assert_eq!(verification.proof_certificate, ProofCertificateStatus::NotRequested);
            assert_eq!(verification.replay, ReplayStatus::NotAttempted, "{label}");
            assert!(verification.claims.is_empty(), "{label}: relift issued a compiler claim");
            assert!(
                analysis
                    .lifted
                    .functions
                    .iter()
                    .all(|function| function.trust_level != TrustLevel::ProofGrade),
                "{label}: a lifted function claims ProofGrade"
            );
            assert!(
                analysis
                    .diagnostics
                    .iter()
                    .all(|diagnostic| !diagnostic.source_backpropagation_allowed),
                "{label}: a relift diagnostic granted source backpropagation"
            );
        }

        #[test]
        fn real_elf_relift_generates_vcs_and_discharges_none() {
            assert_no_vc_is_claimed_discharged(&relift(&elf_bytes()), "x86-64 ELF");
        }

        #[test]
        fn real_macho_relift_generates_vcs_and_discharges_none() {
            assert_no_vc_is_claimed_discharged(&relift(&macho_bytes()), "AArch64 Mach-O");
        }

        fn is_malformed_trust_ir(vc: &VerificationCondition) -> bool {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "MalformedTrustIr")
        }

        /// Every lifted body was once self-contradictory — return place `_0: u64`
        /// against `return_ty: ()` — so `validate_function` refused it and the
        /// whole standard VC pipeline collapsed to one `MalformedTrustIr` row per
        /// function. The real fixtures' bodies are now well-typed, and the
        /// return place has the declared (unit) return type.
        #[test]
        fn real_relift_bodies_are_well_typed_and_emit_no_malformed_trust_ir() {
            for (label, bytes) in [("x86-64 ELF", elf_bytes()), ("AArch64 Mach-O", macho_bytes())] {
                let analysis = relift(&bytes);
                for function in &analysis.verifiable_functions {
                    crate::validate_function(function)
                        .unwrap_or_else(|error| panic!("{label}: {error}"));
                    assert_eq!(function.body.return_ty, Ty::Unit, "{label}");
                    assert_eq!(function.body.locals[0].ty, function.body.return_ty, "{label}");
                }
                assert!(
                    !analysis.vcs.iter().any(is_malformed_trust_ir),
                    "{label}: a relifted body is still malformed: {:#?}",
                    analysis.vcs
                );
            }
        }

        /// The validation that fired is still armed: re-introduce the same kind
        /// of disagreement between the return place and the declared return type
        /// — in either direction — into a real relifted body, and relift analysis
        /// reports `MalformedTrustIr` again.
        #[test]
        fn a_return_place_that_disagrees_with_return_ty_is_still_malformed() {
            type Mutation = fn(&mut trust_types::VerifiableBody);
            let mutations: [(&str, Mutation); 2] = [
                ("return place u64, return type ()", |body| body.locals[0].ty = Ty::u64()),
                ("return place (), return type u64", |body| body.return_ty = Ty::u64()),
            ];
            for (label, bytes) in [("x86-64 ELF", elf_bytes()), ("AArch64 Mach-O", macho_bytes())] {
                for (mutation_label, mutate) in mutations {
                    let mut lifted = relift(&bytes).lifted;
                    mutate(&mut lifted.functions[0].trust_ir_body);
                    let analysis = analyze_lifted_binary(&bytes, lifted, None);
                    let malformed =
                        analysis.vcs.iter().find(|vc| is_malformed_trust_ir(vc)).unwrap_or_else(
                            || panic!("{label}/{mutation_label}: malformation went unreported"),
                        );
                    assert!(
                        matches!(&malformed.kind, VcKind::UnsupportedMir { detail, .. }
                            if detail.contains("return-place local has type")),
                        "{label}/{mutation_label}: {malformed:?}"
                    );
                    assert_no_vc_is_claimed_discharged(&analysis, label);
                }
            }
        }

        /// Neither fixture moves SP (`ldr x0, [x0]; ret`, `mov rax, [rdi]; ret`),
        /// so the stack-discipline violation must be UNSAT — and it is, when a
        /// solver is asked. Relift itself still asks none: the same VC stays
        /// `NotDispatched`/unknown in the analysis, which is the relift promise.
        #[test]
        fn real_relift_stack_vc_is_unsat_for_a_solver_but_not_dispatched_by_relift() {
            use trust_router::{InProcessAyBackend, VerificationBackend};
            use trust_types::VerificationResult;

            for (label, bytes) in [("x86-64 ELF", elf_bytes()), ("AArch64 Mach-O", macho_bytes())] {
                let analysis = relift(&bytes);
                let stack_vcs = analysis
                    .vcs
                    .iter()
                    .enumerate()
                    .filter(|(_, vc)| {
                        matches!(&vc.kind, VcKind::Assertion { message }
                            if message.starts_with("stack pointer not restored"))
                    })
                    .collect::<Vec<_>>();
                assert_eq!(stack_vcs.len(), 1, "{label}: one return block, one stack VC");
                let (index, vc) = stack_vcs[0];

                let backend = InProcessAyBackend::new();
                assert!(backend.can_handle(vc), "{label}");
                let result = backend.verify(vc);
                assert!(
                    matches!(result, VerificationResult::Proved { .. }),
                    "{label}: SP is untouched, the violation must be UNSAT; got {result:?} for {:?}",
                    vc.formula
                );

                let record_id = format!("relift-vc-{index:06}");
                let record = analysis
                    .verification
                    .solver_dispatch
                    .iter()
                    .find(|record| record.id == record_id)
                    .unwrap_or_else(|| panic!("{label}: no dispatch record {record_id}"));
                assert_eq!(record.status, SolverDispatchStatus::NotDispatched, "{label}");
                assert!(record.result.is_none(), "{label}");
                assert_no_vc_is_claimed_discharged(&analysis, label);
            }
        }

        /// Metadata is read from the input, not invented: format, architecture
        /// and entry come from the parsed image, and the digest and length are
        /// of the exact bytes passed in (checked against digests computed
        /// independently when the fixtures were checked in).
        #[test]
        fn real_binary_relift_metadata_matches_input_format_digest_and_length() {
            let cases = [
                (
                    elf_bytes(),
                    X86_64_LOAD_ELF_SHA256,
                    BinaryArtifactFormat::Elf,
                    "ELF",
                    "x86-64",
                    X86_64_LOAD_ELF_ENTRY,
                ),
                (
                    macho_bytes(),
                    AARCH64_LOAD_MACHO_SHA256,
                    BinaryArtifactFormat::MachO,
                    "Mach-O",
                    "AArch64",
                    AARCH64_LOAD_MACHO_ENTRY,
                ),
            ];
            for (bytes, sha256, format, lifted_format, architecture, entry) in cases {
                let options = BinaryReliftOptions::default().with_binary_path("fixtures/app");
                let analysis = analyze_compiled_binary(&bytes, options)
                    .unwrap_or_else(|error| panic!("{lifted_format} must relift: {error}"));
                let binary = &analysis.binary;
                let len = u64::try_from(bytes.len()).expect("fixture length fits u64");

                assert_eq!(binary.format, format, "{lifted_format}");
                assert_eq!(analysis.lifted.format, lifted_format);
                assert_eq!(binary.architecture, architecture, "{lifted_format}");
                assert_eq!(binary.entry_point, Some(entry), "{lifted_format}");
                assert_eq!(analysis.lifted.functions[0].entry_point, entry, "{lifted_format}");
                assert_eq!(binary.path.as_deref(), Some("fixtures/app"), "{lifted_format}");
                assert_eq!(binary.byte_len, Some(len), "{lifted_format}");
                assert_eq!(
                    binary.root_artifact_digest,
                    Some(BinaryArtifactDigest::sha256(sha256)),
                    "{lifted_format}"
                );
                let image = binary.selected_image.as_ref().expect("selected image identity");
                assert_eq!(image.sha256, sha256, "{lifted_format}");
                assert_eq!(image.file_size, len, "{lifted_format}");
                assert_eq!(image.file_offset, 0, "{lifted_format}");
            }
        }

        /// Bytes that are not a supported binary fail with
        /// `BinaryReliftError::Lift` carrying a real parse/lift error: no panic,
        /// no `Ok` with nothing in it, and not `BinaryParserUnavailable` (which
        /// would mean the parsers were compiled out again). Best-effort mode is
        /// used on purpose: it tolerates per-function failures, so it is the
        /// mode that could turn garbage into an empty success.
        #[test]
        fn garbage_bytes_fail_relift_with_lift_error_not_panic_or_empty_success() {
            let elf = elf_bytes();
            let macho = macho_bytes();
            let cases: [(&str, &[u8]); 5] = [
                ("empty", &[]),
                ("text", b"this is not an executable image, just some prose"),
                ("zeros", &[0u8; 256]),
                ("truncated ELF header", &elf[..24]),
                ("truncated Mach-O load commands", &macho[..48]),
            ];
            for (label, bytes) in cases {
                let result = analyze_compiled_binary(
                    bytes,
                    BinaryReliftOptions::all_functions_best_effort(),
                );
                match result {
                    Err(BinaryReliftError::Lift(TrustLiftError::BinaryParserUnavailable)) => {
                        panic!("{label}: binary parsers are compiled out")
                    }
                    Err(BinaryReliftError::Lift(_)) => {}
                    Ok(analysis) => panic!(
                        "{label}: garbage relifted to Ok with {} function(s), {} VC(s)",
                        analysis.lifted.functions.len(),
                        analysis.vcs.len()
                    ),
                }
            }
        }
    }
}
