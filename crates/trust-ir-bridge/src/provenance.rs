//! Canonical TrustIr binary provenance transport.
//!
//! This module preserves binary instruction origins as explicit TrustIr dialect
//! records. The records are intentionally metadata-only: downstream target
//! conversions must provide their own accepted consumer evidence before these
//! records can contribute to proof-grade acceptance.

use std::fmt::Write as _;

use trust_ir::dialect::{AttrValue, DialectInst};
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::{Block as TrustIrBlock, Function as TrustIrFunction, Module};
use trust_types::{
    BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinaryArtifactMetadata, BinaryOrigin,
    BinarySelectedImageIdentity, BinarySourceProvenanceSummary, DecompilationArtifact,
    DecompiledFunction, SourceSpan, Statement, VerifiableFunction, stable_sha256_hex,
};

use crate::layout_evidence::ensure_layout_sensitive_cast_evidence;
use crate::lower::{BridgeError, lower_functions_to_trust_ir};

/// TrustIr dialect namespace for canonical binary provenance records.
pub const BINARY_PROVENANCE_DIALECT: &str = "trust_binary";
/// Dialect op emitted for canonical binary provenance.
pub const BINARY_PROVENANCE_OP: &str = "provenance";
/// Schema id for the provenance op payload.
pub const BINARY_PROVENANCE_SCHEMA: &str = "trust-types.BinaryProvenance@1";

/// Attribute carrying the schema id.
pub const BINARY_PROVENANCE_ATTR_SCHEMA: &str = "schema";
/// Attribute carrying the producer/source label for the provenance row.
pub const BINARY_PROVENANCE_ATTR_SOURCE: &str = "source";
/// Attribute carrying the source-provenance summary status.
pub const BINARY_PROVENANCE_ATTR_SOURCE_STATUS: &str = "source_status";
/// Attribute carrying the checked/exact status for this provenance row.
pub const BINARY_PROVENANCE_ATTR_PROVENANCE_STATUS: &str = "provenance_status";
/// Attribute carrying the canonical function name.
pub const BINARY_PROVENANCE_ATTR_FUNCTION_NAME: &str = "function_name";
/// Attribute carrying the source TrustIr block id.
pub const BINARY_PROVENANCE_ATTR_BLOCK_ID: &str = "block_id";
/// Attribute carrying the source statement index within the block.
pub const BINARY_PROVENANCE_ATTR_STATEMENT_INDEX: &str = "statement_index";
/// Attribute carrying the binary path.
pub const BINARY_PROVENANCE_ATTR_BINARY_PATH: &str = "binary_path";
/// Attribute carrying the function entry address.
pub const BINARY_PROVENANCE_ATTR_FUNCTION_ENTRY: &str = "function_entry";
/// Attribute carrying the instruction address.
pub const BINARY_PROVENANCE_ATTR_INSTRUCTION_ADDRESS: &str = "instruction_address";
/// Attribute carrying the instruction size in bytes.
pub const BINARY_PROVENANCE_ATTR_INSTRUCTION_SIZE: &str = "instruction_size";
/// Attribute carrying the decoded instruction encoding when available.
pub const BINARY_PROVENANCE_ATTR_ENCODING: &str = "encoding";
/// Attribute carrying exact instruction bytes as lowercase hex.
pub const BINARY_PROVENANCE_ATTR_INSTRUCTION_BYTES: &str = "instruction_bytes";
/// Attribute carrying the source file, including `binary:0x...` pseudo-files.
pub const BINARY_PROVENANCE_ATTR_SOURCE_FILE: &str = "source_file";
/// Attribute carrying the source start line.
pub const BINARY_PROVENANCE_ATTR_SOURCE_LINE_START: &str = "source_line_start";
/// Attribute carrying the source start column.
pub const BINARY_PROVENANCE_ATTR_SOURCE_COL_START: &str = "source_col_start";
/// Attribute carrying the source end line.
pub const BINARY_PROVENANCE_ATTR_SOURCE_LINE_END: &str = "source_line_end";
/// Attribute carrying the source end column.
pub const BINARY_PROVENANCE_ATTR_SOURCE_COL_END: &str = "source_col_end";
/// Attribute carrying the root artifact SHA-256 digest.
pub const BINARY_PROVENANCE_ATTR_ARTIFACT_SHA256: &str = "artifact_sha256";
/// Attribute carrying the selected image file offset.
pub const BINARY_PROVENANCE_ATTR_SELECTED_IMAGE_FILE_OFFSET: &str = "selected_image_file_offset";
/// Attribute carrying the selected image file size.
pub const BINARY_PROVENANCE_ATTR_SELECTED_IMAGE_FILE_SIZE: &str = "selected_image_file_size";
/// Attribute carrying the selected image SHA-256 digest.
pub const BINARY_PROVENANCE_ATTR_SELECTED_IMAGE_SHA256: &str = "selected_image_sha256";
/// Attribute carrying the canonical SHA-256 digest of the row payload.
pub const BINARY_PROVENANCE_ATTR_RECORD_DIGEST: &str = "record_digest";
/// Untrusted target-consumption claim copied for audit only.
pub const BINARY_PROVENANCE_ATTR_TARGET_SEMANTICS_CONSUMED: &str = "target_semantics_consumed";

const PRODUCER_SOURCE: &str = "trust-ir-bridge.decompilation-artifact";
/// Provenance row has exact non-binary source ownership accepted by the producer gate.
pub const BINARY_PROVENANCE_STATUS_CHECKED_EXACT: &str = "checked_exact";
/// Provenance row is tied to ambiguous source ownership and must remain fail-closed.
pub const BINARY_PROVENANCE_STATUS_AMBIGUOUS: &str = "ambiguous";
/// Provenance row lacks accepted exact source ownership and must remain fail-closed.
pub const BINARY_PROVENANCE_STATUS_UNAVAILABLE: &str = "unavailable";

/// A parsed canonical binary provenance record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalBinaryProvenanceRecord {
    /// Function that owns the source statement.
    pub function: String,
    /// Source TrustIr block id.
    pub block: usize,
    /// Source statement index within the TrustIr block.
    pub statement_index: usize,
    /// Physical statement index of the carrier dialect op after parsing.
    pub carrier_statement_index: Option<usize>,
    /// Original binary instruction origin.
    pub origin: BinaryOrigin,
    /// Digest identity of the binary artifact selected for lifting.
    pub artifact_digest_identity: BinaryArtifactDigestIdentity,
    /// Source/debug provenance status from the decompilation artifact.
    pub source_status: String,
    /// Row-level checked/exact provenance status.
    pub provenance_status: String,
    /// Producer/source label carried by the dialect op.
    pub source: Option<String>,
    /// Canonical SHA-256 digest of the row payload.
    pub record_digest: String,
    /// Untrusted target-consumption input claim, if present.
    pub input_claimed_target_semantics_consumed: Option<bool>,
}

/// A rejected canonical binary provenance row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalBinaryProvenanceRejection {
    /// Function containing the rejected row.
    pub function: String,
    /// TrustIr block containing the rejected row.
    pub block: usize,
    /// Physical statement index of the rejected row.
    pub carrier_statement_index: usize,
    /// Stable rejection detail.
    pub reason: String,
}

/// Parsed provenance records and fail-closed rejections.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CanonicalBinaryProvenanceReport {
    /// Valid canonical records.
    pub records: Vec<CanonicalBinaryProvenanceRecord>,
    /// Rows that looked like binary provenance but failed schema/digest checks.
    pub rejections: Vec<CanonicalBinaryProvenanceRejection>,
}

/// Bridge-owned evidence that a target consumer accepted one provenance record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalBinaryProvenanceAcceptance {
    /// Accepted provenance row digest.
    pub record_digest: String,
    /// Component that made the authoritative target-consumption decision.
    pub consumer: String,
}

/// Lower a decompilation artifact into TrustIr and attach canonical provenance rows.
///
/// This is intentionally strict: every function must have a lifted TrustIr body,
/// every instruction provenance row must bind to a statement span, and the
/// artifact must carry replay-grade digest identity.
pub fn lower_decompilation_artifact_to_trust_ir(
    artifact: &DecompilationArtifact,
) -> Result<Module, BridgeError> {
    let lifted = artifact
        .functions
        .iter()
        .map(|function| {
            function.lifted.as_ref().ok_or_else(|| {
                BridgeError::UnsupportedOp(format!(
                    "function `{}` is missing lifted TrustIr for canonical binary provenance",
                    function.name
                ))
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let module_name = artifact.binary.path.as_deref().unwrap_or("binary");
    let mut module = lower_functions_to_trust_ir(module_name, lifted)?;
    attach_decompilation_binary_provenance(&mut module, artifact)?;
    ensure_layout_sensitive_cast_evidence(&module)?;
    Ok(module)
}

/// Attach canonical binary provenance records to an already lowered module.
pub fn attach_decompilation_binary_provenance(
    module: &mut Module,
    artifact: &DecompilationArtifact,
) -> Result<Vec<CanonicalBinaryProvenanceRecord>, BridgeError> {
    validate_source_status(&artifact.source_provenance.status).map_err(|reason| {
        BridgeError::UnsupportedOp(format!(
            "canonical binary provenance requires recognized source provenance status: {reason}"
        ))
    })?;
    let digest_identity = BinaryArtifactDigestIdentity::from_metadata(&artifact.binary)
        .ok_or_else(|| {
            BridgeError::UnsupportedOp(
                "canonical binary provenance requires binary artifact digest identity".to_string(),
            )
        })?;
    let digest_blockers = artifact.binary.digest_identity_blockers();
    if !digest_blockers.is_empty() {
        return Err(BridgeError::UnsupportedOp(format!(
            "canonical binary provenance requires replay-grade artifact digest identity: {}",
            digest_blockers.join(", ")
        )));
    }

    let mut emitted = Vec::new();
    for function in &artifact.functions {
        let Some(lifted) = &function.lifted else {
            return Err(BridgeError::UnsupportedOp(format!(
                "function `{}` is missing lifted TrustIr for canonical binary provenance",
                function.name
            )));
        };

        let records = records_for_function(
            &artifact.binary,
            &digest_identity,
            &artifact.source_provenance,
            function,
            lifted,
        )?;
        insert_records(module, &function.name, &records)?;
        emitted.extend(records);
    }

    Ok(emitted)
}

/// Collect and validate canonical binary provenance rows from a TrustIr module.
#[must_use]
pub fn collect_canonical_binary_provenance(module: &Module) -> CanonicalBinaryProvenanceReport {
    let mut report = CanonicalBinaryProvenanceReport::default();
    for function in &module.functions {
        for block in &function.blocks {
            for (carrier_statement_index, node) in block.body.iter().enumerate() {
                let Inst::DialectOp(op) = &node.inst else {
                    continue;
                };
                if op.dialect != BINARY_PROVENANCE_DIALECT || op.op != BINARY_PROVENANCE_OP {
                    continue;
                }

                match parse_record(function, block, carrier_statement_index, op) {
                    Ok(record) => report.records.push(record),
                    Err(reason) => report.rejections.push(CanonicalBinaryProvenanceRejection {
                        function: function.name.clone(),
                        block: block.id.as_usize(),
                        carrier_statement_index,
                        reason,
                    }),
                }
            }
        }
    }
    report
}

/// Fail-closed target-consumer blockers for canonical binary provenance.
#[must_use]
pub fn canonical_binary_provenance_target_blockers(
    records: &[CanonicalBinaryProvenanceRecord],
    acceptances: &[CanonicalBinaryProvenanceAcceptance],
) -> Vec<String> {
    if records.is_empty() {
        return vec!["target conversion has no canonical binary provenance records".to_string()];
    }

    let mut blockers = Vec::new();
    for record in records {
        let accepted = acceptances.iter().any(|acceptance| {
            acceptance.record_digest == record.record_digest
                && !acceptance.consumer.trim().is_empty()
        });
        if !accepted {
            blockers.push(format!(
                "canonical binary provenance record {} for {}::bb{}::stmt{} at 0x{:x} is not accepted by a target proof consumer",
                record.record_digest,
                record.function,
                record.block,
                record.statement_index,
                record.origin.instruction_address
            ));
        }
    }

    blockers
}

fn records_for_function(
    metadata: &BinaryArtifactMetadata,
    digest_identity: &BinaryArtifactDigestIdentity,
    source_provenance: &BinarySourceProvenanceSummary,
    function: &DecompiledFunction,
    lifted: &VerifiableFunction,
) -> Result<Vec<CanonicalBinaryProvenanceRecord>, BridgeError> {
    function
        .instruction_provenance
        .iter()
        .enumerate()
        .map(|(index, origin)| {
            let (block, statement_index) =
                bind_origin_to_statement(function, lifted, origin, index)?;
            let mut origin = origin.clone();
            if origin.binary_path.as_ref().is_none_or(|path| path.trim().is_empty()) {
                origin.binary_path = metadata.path.clone();
            }
            if origin.function_entry.is_none() {
                origin.function_entry = Some(function.entry);
            }
            if origin.source.is_none() {
                origin.source = Some(SourceSpan::binary_address(origin.instruction_address));
            }
            validate_origin_matches_binary_metadata(metadata, &origin, &function.name, index)?;

            let blockers = origin.canonical_provenance_blockers();
            if !blockers.is_empty() {
                return Err(BridgeError::UnsupportedOp(format!(
                    "canonical binary provenance for `{}` instruction[{index}] is malformed: {}",
                    function.name,
                    blockers.join(", ")
                )));
            }
            let provenance_status =
                provenance_status_for_origin(source_provenance, &origin).to_string();

            let mut record = CanonicalBinaryProvenanceRecord {
                function: function.name.clone(),
                block,
                statement_index,
                carrier_statement_index: None,
                origin,
                artifact_digest_identity: digest_identity.clone(),
                source_status: source_provenance.status.clone(),
                provenance_status,
                source: Some(PRODUCER_SOURCE.to_string()),
                record_digest: String::new(),
                input_claimed_target_semantics_consumed: Some(false),
            };
            record.record_digest = record_digest(&record);
            Ok(record)
        })
        .collect()
}

fn validate_origin_matches_binary_metadata(
    metadata: &BinaryArtifactMetadata,
    origin: &BinaryOrigin,
    function_name: &str,
    instruction_index: usize,
) -> Result<(), BridgeError> {
    let Some(expected_path) =
        metadata.path.as_deref().map(str::trim).filter(|path| !path.is_empty())
    else {
        return Ok(());
    };
    if origin.binary_path.as_deref() == Some(expected_path) {
        return Ok(());
    }

    Err(BridgeError::UnsupportedOp(format!(
        "canonical binary provenance for `{function_name}` instruction[{instruction_index}] names binary path `{}` but artifact binary path is `{expected_path}`",
        origin.binary_path.as_deref().unwrap_or("<missing>")
    )))
}

fn provenance_status_for_origin(
    source_provenance: &BinarySourceProvenanceSummary,
    origin: &BinaryOrigin,
) -> &'static str {
    let has_exact_source_mapping = origin.source.as_ref().is_some_and(|source| !source.is_binary());
    if source_provenance.effective_source_backpropagation_allowed() && has_exact_source_mapping {
        return BINARY_PROVENANCE_STATUS_CHECKED_EXACT;
    }
    if source_provenance.status == "ambiguous" || source_provenance.ambiguous_mapping_count > 0 {
        return BINARY_PROVENANCE_STATUS_AMBIGUOUS;
    }

    BINARY_PROVENANCE_STATUS_UNAVAILABLE
}

fn bind_origin_to_statement(
    function: &DecompiledFunction,
    lifted: &VerifiableFunction,
    origin: &BinaryOrigin,
    instruction_index: usize,
) -> Result<(usize, usize), BridgeError> {
    let mut matches = Vec::new();
    for block in &lifted.body.blocks {
        for (statement_index, statement) in block.stmts.iter().enumerate() {
            let Some(span) = statement_span(statement) else {
                continue;
            };
            if span_matches_origin(span, origin) {
                matches.push((block.id.0, statement_index));
            }
        }
    }

    match matches.as_slice() {
        [binding] => Ok(*binding),
        [] => Err(BridgeError::UnsupportedOp(format!(
            "canonical binary provenance for `{}` instruction[{instruction_index}] at 0x{:x} cannot be bound to a lifted TrustIr statement span",
            function.name, origin.instruction_address
        ))),
        _ => Err(BridgeError::UnsupportedOp(format!(
            "canonical binary provenance for `{}` instruction[{instruction_index}] at 0x{:x} ambiguously matches multiple lifted TrustIr statements",
            function.name, origin.instruction_address
        ))),
    }
}

fn statement_span(statement: &Statement) -> Option<&SourceSpan> {
    match statement {
        Statement::Assign { span, .. } | Statement::Unsupported { span, .. } => Some(span),
        _ => None,
    }
}

fn span_matches_origin(span: &SourceSpan, origin: &BinaryOrigin) -> bool {
    span.binary_address_value() == Some(origin.instruction_address)
        || origin.source.as_ref().is_some_and(|source| source == span)
}

fn insert_records(
    module: &mut Module,
    function_name: &str,
    records: &[CanonicalBinaryProvenanceRecord],
) -> Result<(), BridgeError> {
    let function =
        module.functions.iter_mut().find(|function| function.name == function_name).ok_or_else(
            || {
                BridgeError::UnsupportedOp(format!(
                    "lowered TrustIr module has no function `{function_name}` for binary provenance"
                ))
            },
        )?;

    for record in records {
        let block = function
            .blocks
            .iter_mut()
            .find(|block| block.id.as_usize() == record.block)
            .ok_or_else(|| {
                BridgeError::UnsupportedOp(format!(
                    "lowered TrustIr function `{function_name}` has no bb{} for binary provenance",
                    record.block
                ))
            })?;
        block.body.insert(0, InstrNode::new(Inst::DialectOp(Box::new(record_to_op(record)))));
    }

    Ok(())
}

fn record_to_op(record: &CanonicalBinaryProvenanceRecord) -> DialectInst {
    let mut op = DialectInst::new(BINARY_PROVENANCE_DIALECT, BINARY_PROVENANCE_OP)
        .with_attr(BINARY_PROVENANCE_ATTR_SCHEMA, attr_str(BINARY_PROVENANCE_SCHEMA))
        .with_attr(
            BINARY_PROVENANCE_ATTR_SOURCE,
            attr_str(record.source.as_deref().unwrap_or(PRODUCER_SOURCE)),
        )
        .with_attr(BINARY_PROVENANCE_ATTR_SOURCE_STATUS, attr_str(&record.source_status))
        .with_attr(BINARY_PROVENANCE_ATTR_PROVENANCE_STATUS, attr_str(&record.provenance_status))
        .with_attr(BINARY_PROVENANCE_ATTR_FUNCTION_NAME, attr_str(&record.function))
        .with_attr(BINARY_PROVENANCE_ATTR_BLOCK_ID, attr_str(record.block.to_string()))
        .with_attr(
            BINARY_PROVENANCE_ATTR_STATEMENT_INDEX,
            attr_str(record.statement_index.to_string()),
        );

    if let Some(path) = &record.origin.binary_path {
        op = op.with_attr(BINARY_PROVENANCE_ATTR_BINARY_PATH, attr_str(path));
    }
    if let Some(entry) = record.origin.function_entry {
        op = op.with_attr(BINARY_PROVENANCE_ATTR_FUNCTION_ENTRY, attr_str(hex_u64(entry)));
    }
    op = op
        .with_attr(
            BINARY_PROVENANCE_ATTR_INSTRUCTION_ADDRESS,
            attr_str(hex_u64(record.origin.instruction_address)),
        )
        .with_attr(
            BINARY_PROVENANCE_ATTR_INSTRUCTION_SIZE,
            attr_str(
                record.origin.instruction_size.map_or_else(String::new, |size| size.to_string()),
            ),
        );
    if let Some(encoding) = record.origin.encoding {
        op = op.with_attr(BINARY_PROVENANCE_ATTR_ENCODING, attr_str(hex_u64(u64::from(encoding))));
    }
    op = op.with_attr(
        BINARY_PROVENANCE_ATTR_INSTRUCTION_BYTES,
        attr_str(hex_bytes(&record.origin.instruction_bytes)),
    );

    if let Some(source) = &record.origin.source {
        op = op
            .with_attr(BINARY_PROVENANCE_ATTR_SOURCE_FILE, attr_str(&source.file))
            .with_attr(
                BINARY_PROVENANCE_ATTR_SOURCE_LINE_START,
                attr_str(source.line_start.to_string()),
            )
            .with_attr(
                BINARY_PROVENANCE_ATTR_SOURCE_COL_START,
                attr_str(source.col_start.to_string()),
            )
            .with_attr(
                BINARY_PROVENANCE_ATTR_SOURCE_LINE_END,
                attr_str(source.line_end.to_string()),
            )
            .with_attr(BINARY_PROVENANCE_ATTR_SOURCE_COL_END, attr_str(source.col_end.to_string()));
    }

    if let Some(root) = &record.artifact_digest_identity.root_artifact_digest {
        op = op.with_attr(BINARY_PROVENANCE_ATTR_ARTIFACT_SHA256, attr_str(&root.value));
    }
    if let Some(selected) = &record.artifact_digest_identity.selected_image {
        op = op
            .with_attr(
                BINARY_PROVENANCE_ATTR_SELECTED_IMAGE_FILE_OFFSET,
                attr_str(selected.file_offset.to_string()),
            )
            .with_attr(
                BINARY_PROVENANCE_ATTR_SELECTED_IMAGE_FILE_SIZE,
                attr_str(selected.file_size.to_string()),
            )
            .with_attr(BINARY_PROVENANCE_ATTR_SELECTED_IMAGE_SHA256, attr_str(&selected.sha256));
    }

    op.with_attr(BINARY_PROVENANCE_ATTR_RECORD_DIGEST, attr_str(&record.record_digest))
        .with_attr(BINARY_PROVENANCE_ATTR_TARGET_SEMANTICS_CONSUMED, attr_str("false"))
}

fn parse_record(
    function: &TrustIrFunction,
    block: &TrustIrBlock,
    carrier_statement_index: usize,
    op: &DialectInst,
) -> Result<CanonicalBinaryProvenanceRecord, String> {
    let schema = required_attr(op, BINARY_PROVENANCE_ATTR_SCHEMA)?;
    if schema != BINARY_PROVENANCE_SCHEMA {
        return Err(format!(
            "unsupported binary provenance schema `{schema}`; expected `{BINARY_PROVENANCE_SCHEMA}`"
        ));
    }

    let function_name = required_attr(op, BINARY_PROVENANCE_ATTR_FUNCTION_NAME)?;
    if function_name != function.name {
        return Err(format!(
            "function_name attr `{function_name}` does not match containing function `{}`",
            function.name
        ));
    }

    let record_block = required_usize_attr(op, BINARY_PROVENANCE_ATTR_BLOCK_ID)?;
    if record_block != block.id.as_usize() {
        return Err(format!(
            "block_id attr `{record_block}` does not match containing bb{}",
            block.id.as_usize()
        ));
    }

    let statement_index = required_usize_attr(op, BINARY_PROVENANCE_ATTR_STATEMENT_INDEX)?;
    let source_status = required_attr(op, BINARY_PROVENANCE_ATTR_SOURCE_STATUS)?;
    validate_source_status(&source_status)?;
    let provenance_status = required_attr(op, BINARY_PROVENANCE_ATTR_PROVENANCE_STATUS)?;
    validate_provenance_status_name(&provenance_status)?;

    let instruction_address = required_u64_attr(op, BINARY_PROVENANCE_ATTR_INSTRUCTION_ADDRESS)?;
    let instruction_bytes = required_hex_bytes_attr(op, BINARY_PROVENANCE_ATTR_INSTRUCTION_BYTES)?;
    let instruction_size = required_u64_attr(op, BINARY_PROVENANCE_ATTR_INSTRUCTION_SIZE)
        .and_then(|size| {
            u8::try_from(size).map_err(|_| {
                format!("instruction_size attr `{size}` does not fit in canonical u8 size")
            })
        })?;
    let encoding = optional_u64_attr(op, BINARY_PROVENANCE_ATTR_ENCODING)
        .transpose()?
        .map(|encoding| {
            u32::try_from(encoding).map_err(|_| {
                format!("encoding attr `{encoding}` does not fit in canonical u32 encoding")
            })
        })
        .transpose()?;

    let origin = BinaryOrigin {
        binary_path: optional_attr(op, BINARY_PROVENANCE_ATTR_BINARY_PATH),
        function_entry: optional_u64_attr(op, BINARY_PROVENANCE_ATTR_FUNCTION_ENTRY).transpose()?,
        instruction_address,
        instruction_size: Some(instruction_size),
        encoding,
        instruction_bytes,
        source: parse_source_span(op, instruction_address)?,
    };
    let origin_blockers = origin.canonical_provenance_blockers();
    if !origin_blockers.is_empty() {
        return Err(format!("binary origin is not canonical: {}", origin_blockers.join(", ")));
    }

    let artifact_digest_identity = parse_digest_identity(op)?;
    let digest_blockers = artifact_digest_identity.digest_identity_blockers();
    if !digest_blockers.is_empty() {
        return Err(format!(
            "binary artifact digest identity is not replay-grade: {}",
            digest_blockers.join(", ")
        ));
    }

    let claimed_record_digest = required_attr(op, BINARY_PROVENANCE_ATTR_RECORD_DIGEST)?;
    let mut record = CanonicalBinaryProvenanceRecord {
        function: function.name.clone(),
        block: block.id.as_usize(),
        statement_index,
        carrier_statement_index: Some(carrier_statement_index),
        origin,
        artifact_digest_identity,
        source_status,
        provenance_status,
        source: optional_attr(op, BINARY_PROVENANCE_ATTR_SOURCE),
        record_digest: claimed_record_digest.clone(),
        input_claimed_target_semantics_consumed: optional_bool_attr(
            op,
            BINARY_PROVENANCE_ATTR_TARGET_SEMANTICS_CONSUMED,
        )
        .transpose()?,
    };
    validate_record_provenance_status(&record)?;
    let expected_digest = record_digest(&record);
    if claimed_record_digest != expected_digest {
        return Err(format!(
            "record_digest `{claimed_record_digest}` does not match canonical payload digest `{expected_digest}`"
        ));
    }
    record.record_digest = expected_digest;
    Ok(record)
}

fn parse_digest_identity(op: &DialectInst) -> Result<BinaryArtifactDigestIdentity, String> {
    let root_artifact_digest =
        optional_attr(op, BINARY_PROVENANCE_ATTR_ARTIFACT_SHA256).map(BinaryArtifactDigest::sha256);
    let selected_image = match (
        optional_u64_attr(op, BINARY_PROVENANCE_ATTR_SELECTED_IMAGE_FILE_OFFSET).transpose()?,
        optional_u64_attr(op, BINARY_PROVENANCE_ATTR_SELECTED_IMAGE_FILE_SIZE).transpose()?,
        optional_attr(op, BINARY_PROVENANCE_ATTR_SELECTED_IMAGE_SHA256),
    ) {
        (Some(file_offset), Some(file_size), Some(sha256)) => {
            Some(BinarySelectedImageIdentity { file_offset, file_size, sha256 })
        }
        (None, None, None) => None,
        _ => {
            return Err(
                "selected image digest identity must include file offset, file size, and sha256"
                    .to_string(),
            );
        }
    };

    Ok(BinaryArtifactDigestIdentity { root_artifact_digest, selected_image })
}

fn parse_source_span(
    op: &DialectInst,
    instruction_address: u64,
) -> Result<Option<SourceSpan>, String> {
    let Some(file) = optional_attr(op, BINARY_PROVENANCE_ATTR_SOURCE_FILE) else {
        return Ok(Some(SourceSpan::binary_address(instruction_address)));
    };

    Ok(Some(SourceSpan {
        file,
        line_start: required_u32_attr(op, BINARY_PROVENANCE_ATTR_SOURCE_LINE_START)?,
        col_start: required_u32_attr(op, BINARY_PROVENANCE_ATTR_SOURCE_COL_START)?,
        line_end: required_u32_attr(op, BINARY_PROVENANCE_ATTR_SOURCE_LINE_END)?,
        col_end: required_u32_attr(op, BINARY_PROVENANCE_ATTR_SOURCE_COL_END)?,
    }))
}

fn validate_source_status(status: &str) -> Result<(), String> {
    match status {
        "unavailable" | "exact" | "ambiguous" | "unsupported" => Ok(()),
        other => Err(format!("source_status `{other}` is not recognized")),
    }
}

fn validate_provenance_status_name(status: &str) -> Result<(), String> {
    match status {
        BINARY_PROVENANCE_STATUS_CHECKED_EXACT
        | BINARY_PROVENANCE_STATUS_AMBIGUOUS
        | BINARY_PROVENANCE_STATUS_UNAVAILABLE => Ok(()),
        other => Err(format!("provenance_status `{other}` is not recognized")),
    }
}

fn validate_record_provenance_status(
    record: &CanonicalBinaryProvenanceRecord,
) -> Result<(), String> {
    match record.provenance_status.as_str() {
        BINARY_PROVENANCE_STATUS_CHECKED_EXACT => {
            if record.source_status != "exact" {
                return Err(format!(
                    "provenance_status `{}` requires source_status `exact`",
                    BINARY_PROVENANCE_STATUS_CHECKED_EXACT
                ));
            }
            if record.origin.source.as_ref().is_none_or(|source| source.is_binary()) {
                return Err(format!(
                    "provenance_status `{}` requires a non-binary source span",
                    BINARY_PROVENANCE_STATUS_CHECKED_EXACT
                ));
            }
            Ok(())
        }
        BINARY_PROVENANCE_STATUS_AMBIGUOUS => {
            if record.source_status != "ambiguous" {
                return Err(format!(
                    "provenance_status `{}` requires source_status `ambiguous`",
                    BINARY_PROVENANCE_STATUS_AMBIGUOUS
                ));
            }
            Ok(())
        }
        BINARY_PROVENANCE_STATUS_UNAVAILABLE => Ok(()),
        other => Err(format!("provenance_status `{other}` is not recognized")),
    }
}

fn record_digest(record: &CanonicalBinaryProvenanceRecord) -> String {
    stable_sha256_hex(record_digest_material(record).as_bytes())
}

fn record_digest_material(record: &CanonicalBinaryProvenanceRecord) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "schema={BINARY_PROVENANCE_SCHEMA}");
    let _ = writeln!(out, "source={}", record.source.as_deref().unwrap_or(""));
    let _ = writeln!(out, "source_status={}", record.source_status);
    let _ = writeln!(out, "provenance_status={}", record.provenance_status);
    let _ = writeln!(out, "function_name={}", record.function);
    let _ = writeln!(out, "block_id={}", record.block);
    let _ = writeln!(out, "statement_index={}", record.statement_index);
    let _ = writeln!(out, "binary_path={}", record.origin.binary_path.as_deref().unwrap_or(""));
    let _ = writeln!(
        out,
        "function_entry={}",
        record.origin.function_entry.map(hex_u64).unwrap_or_default()
    );
    let _ = writeln!(out, "instruction_address={}", hex_u64(record.origin.instruction_address));
    let _ = writeln!(
        out,
        "instruction_size={}",
        record.origin.instruction_size.map_or_else(String::new, |size| size.to_string())
    );
    let _ = writeln!(
        out,
        "encoding={}",
        record.origin.encoding.map(|encoding| hex_u64(u64::from(encoding))).unwrap_or_default()
    );
    let _ = writeln!(out, "instruction_bytes={}", hex_bytes(&record.origin.instruction_bytes));
    if let Some(source) = &record.origin.source {
        let _ = writeln!(out, "source_file={}", source.file);
        let _ = writeln!(out, "source_line_start={}", source.line_start);
        let _ = writeln!(out, "source_col_start={}", source.col_start);
        let _ = writeln!(out, "source_line_end={}", source.line_end);
        let _ = writeln!(out, "source_col_end={}", source.col_end);
    } else {
        let _ = writeln!(out, "source_file=");
        let _ = writeln!(out, "source_line_start=");
        let _ = writeln!(out, "source_col_start=");
        let _ = writeln!(out, "source_line_end=");
        let _ = writeln!(out, "source_col_end=");
    }
    if let Some(root) = &record.artifact_digest_identity.root_artifact_digest {
        let _ = writeln!(out, "artifact_sha256={}", root.value);
    } else {
        let _ = writeln!(out, "artifact_sha256=");
    }
    if let Some(selected) = &record.artifact_digest_identity.selected_image {
        let _ = writeln!(out, "selected_image_file_offset={}", selected.file_offset);
        let _ = writeln!(out, "selected_image_file_size={}", selected.file_size);
        let _ = writeln!(out, "selected_image_sha256={}", selected.sha256);
    } else {
        let _ = writeln!(out, "selected_image_file_offset=");
        let _ = writeln!(out, "selected_image_file_size=");
        let _ = writeln!(out, "selected_image_sha256=");
    }
    out
}

fn required_attr(op: &DialectInst, name: &str) -> Result<String, String> {
    optional_attr(op, name).ok_or_else(|| format!("missing `{name}` attr"))
}

fn optional_attr(op: &DialectInst, name: &str) -> Option<String> {
    op.attr(name).and_then(|value| match value {
        AttrValue::Str(value) => Some(value.clone()),
        AttrValue::U64(value) => Some(value.to_string()),
        AttrValue::I64(value) => Some(value.to_string()),
        AttrValue::Bool(value) => Some(value.to_string()),
        AttrValue::F64(_) | AttrValue::Bytes(_) | AttrValue::Ty(_) => None,
    })
}

fn required_usize_attr(op: &DialectInst, name: &str) -> Result<usize, String> {
    let value = required_u64_attr(op, name)?;
    usize::try_from(value).map_err(|_| format!("`{name}` attr `{value}` does not fit in usize"))
}

fn required_u32_attr(op: &DialectInst, name: &str) -> Result<u32, String> {
    let value = required_u64_attr(op, name)?;
    u32::try_from(value).map_err(|_| format!("`{name}` attr `{value}` does not fit in u32"))
}

fn required_u64_attr(op: &DialectInst, name: &str) -> Result<u64, String> {
    parse_canonical_u64(&required_attr(op, name)?)
        .ok_or_else(|| format!("`{name}` attr is not a canonical u64"))
}

fn optional_u64_attr(op: &DialectInst, name: &str) -> Option<Result<u64, String>> {
    optional_attr(op, name).map(|value| {
        parse_canonical_u64(&value).ok_or_else(|| format!("`{name}` attr is not a canonical u64"))
    })
}

fn optional_bool_attr(op: &DialectInst, name: &str) -> Option<Result<bool, String>> {
    optional_attr(op, name).map(|value| match value.trim() {
        "true" => Ok(true),
        "false" => Ok(false),
        _ => Err(format!("`{name}` attr is not a canonical bool")),
    })
}

fn required_hex_bytes_attr(op: &DialectInst, name: &str) -> Result<Vec<u8>, String> {
    parse_canonical_hex_bytes(&required_attr(op, name)?)
        .ok_or_else(|| format!("`{name}` attr is not canonical hex bytes"))
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

fn hex_bytes(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn hex_u64(value: u64) -> String {
    format!("0x{value:x}")
}

fn attr_str(value: impl Into<String>) -> AttrValue {
    AttrValue::Str(value.into())
}
