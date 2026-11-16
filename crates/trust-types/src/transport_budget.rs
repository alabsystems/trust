//! Trust (TRANSPORT-LINE-BUDGET-1, 2026-11-01): the size bound on one `TRUST_JSON`
//! transport line, and the fail-closed ladder that fits one function's report under it.
//!
//! WHY. trustc writes each function's verification report as ONE stderr line. Targo
//! reads that stream with a per-line cap (`VERIFIED_TARGO_MAX_CHILD_LINE_BYTES` in
//! `src/tools/targo/crates/targo-core/src/compiler/mod.rs`, `MAX_CARGO_JSON_LINE_BYTES` in
//! `targo-trust/src/input_limits.rs`, both 128 MiB), and the cap is right: it bounds
//! what one compiler unit can make targo hold. Nothing bounded the line on the
//! compiler's side, so a function whose report passed the cap made targo close the
//! pipe, trustc died of SIGPIPE on its next write, and EVERY function of the crate
//! lost its rows (ay-sat's `reset_search_state_incremental`, astream-digest's
//! eight-call `compress`; docs/issues/2026-10-22-…-incomplete-report.md).
//!
//! THE BOUND. [`TRANSPORT_LINE_BUDGET_BYTES`], half of targo's cap, is the most bytes
//! one emitted transport line may take, framing included ([`TransportLineFraming`]: the
//! JSON diagnostic's span `file_name` is counted exactly, since a long crate-root path or
//! a `--remap-path-prefix` target can outgrow any fixed allowance).
//! The other half is margin for the Cargo envelope targo-trust reads around the
//! diagnostic and for any re-serialization on the way. A test may LOWER the budget
//! ([`lowered_line_budget`]); nothing raises it or switches it off.
//!
//! THE LADDER ([`fit_function_result`]), cheapest loss first, each step only when the
//! one before it did not fit:
//!
//! 1. [`TransportBudgetStep::WithheldDiagnosticPayloads`]: withhold each row's
//!    `original_vc_snapshot` ("serialized diagnostic data, never authority"; no
//!    production reader decodes it, and targo-trust only copies it or tests its
//!    presence), from the rows that carry the most of it, until the line fits. No row
//!    changes outcome.
//! 2. [`TransportBudgetStep::WithheldProofEvidence`]: withhold the PAYLOADS of a row's
//!    `proof_evidence` and `native_trust_ir` (every artifact's `materialization` and
//!    `metadata`: the bytes, CIC terms and engine inputs), first from the rows that
//!    claim nothing favorable (largest first), then from the `proved` and
//!    `runtime_checked` rows (largest first). The records themselves stay: their
//!    status, suite, backend, ids, diagnostics and artifact descriptors (kind, format,
//!    id, digest, uri), so every reader that keys on their presence, their status or
//!    their diagnostics reads the row as before, and an Error diagnostic
//!    ([`TRANSPORT_LINE_BUDGET_EVIDENCE_DIAGNOSTIC`]) is added to each, as the 32 MiB
//!    materialization cap already does. Every row it touches loses its grade, and a
//!    favorable row is DEMOTED by [`demoted_outcome`] and says why: a consumer
//!    re-derives authority from those payloads, so a row may not keep a favorable label
//!    without them, and may not lose a refutation the evidence carried. A favorable row
//!    of a conditional-evidence kind ([`is_conditional_evidence_row`]) is never
//!    touched: the gate already refuses its favorable label, and demoting it to
//!    `unknown` would move it into the conditional bucket.
//! 3. [`TransportBudgetStep::ReportReplaced`]: when even that does not fit, the rows
//!    are replaced by ONE fail-closed row ([`TRANSPORT_LINE_BUDGET_ROW_KIND`]) that is
//!    `failed` if any replaced row was refuted and `unknown` otherwise, and that names
//!    the counts it replaces. This is the function-level fallback: it costs that
//!    function its rows, and no other function anything.
//!
//! Every step is stated on the envelope ([`TransportBudgetDisclosure`]): which fields
//! were withheld from which rows, which rows were demoted, what was replaced. A
//! consumer never sees shorter evidence without that marker, and a marker it cannot
//! reconcile with the rows ([`TransportBudgetDisclosure::defect`]) is a defect.
//!
//! Steps 1 and 2 never touch an envelope-shape row ([`is_envelope_shape_row`]): a
//! consumer elides such a row when it matches an exact shape that includes "no claim
//! field present", so withholding a field from a lookalike could complete the shape.
//!
//! What the ladder never does: truncate a string, drop a row while the rows fit,
//! touch another function's line, or raise any row's outcome.

use serde::{Deserialize, Serialize};

use crate::{FunctionTransportResult, Outcome, SourceSpan, TransportObligationResult};

/// The most bytes one emitted `TRUST_JSON` line may take, framing and newline included:
/// half of targo's 128 MiB per-line cap.
pub const TRANSPORT_LINE_BUDGET_BYTES: u64 = 64 * 1024 * 1024;

/// The lowest budget a test knob may set. Low enough that a regression test can push an
/// ordinary function over it; high enough that the step-3 fallback row (whose size is
/// the function's identity strings and seven counts) always fits.
pub const MIN_TRANSPORT_LINE_BUDGET_BYTES: u64 = 16 * 1024;

/// Upper bound on the bytes rustc's JSON emitter adds around a transport note's message,
/// OTHER than its span's `file_name`: `{"$message_type":"diagnostic","message":"`, the
/// closing quote, the `"code":{"code":"trust_verification_transport_v1","explanation":null}`,
/// level, the one span's positions and null fields, empty children, the short `rendered`
/// the emitter states for a transport note (`rustc_errors::json`, `// Trust:`), and the
/// newline: about 450 bytes today. The span's `file_name` is the one part whose length
/// the compile chooses (the crate root's path, after `--remap-path-prefix`), so it is
/// counted exactly ([`TransportLineFraming::json_diagnostic`]) instead of assumed short.
pub const JSON_DIAGNOSTIC_FRAMING_OVERHEAD_BYTES: u64 = 4 * 1024;

/// The fallback row's kind (step 3). Not a VC kind: it names a report that could not
/// be transported, and grants nothing.
pub const TRANSPORT_LINE_BUDGET_ROW_KIND: &str = "transport_line_budget";
/// The fallback row's solver label.
pub const TRANSPORT_LINE_BUDGET_ROW_SOLVER: &str = "trust-transport";
/// The prefix of the `reason` of every row step 2 demoted.
pub const TRANSPORT_LINE_BUDGET_DEMOTION_PREFIX: &str = "transport line budget:";

/// The effective budget given an optional test request: the request when it is LOWER
/// than [`TRANSPORT_LINE_BUDGET_BYTES`] (never below [`MIN_TRANSPORT_LINE_BUDGET_BYTES`]),
/// the default otherwise. A request can only lower the bound.
#[must_use]
pub fn lowered_line_budget(requested: Option<u64>) -> u64 {
    requested.map_or(TRANSPORT_LINE_BUDGET_BYTES, |bytes| {
        bytes.clamp(MIN_TRANSPORT_LINE_BUDGET_BYTES, TRANSPORT_LINE_BUDGET_BYTES)
    })
}

/// How a transport payload reaches stderr, and so how many bytes its line takes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransportLineFraming {
    /// `--error-format=human`: the raw `TRUST_JSON:{…}` line.
    RawStderr,
    /// `--error-format=json`: the payload is the `message` of a rustc JSON diagnostic,
    /// so every byte is JSON-string-escaped once more, and the diagnostic carries one
    /// span whose `file_name` takes `span_file_name_bytes` (its JSON-escaped body).
    /// Build it with [`Self::json_diagnostic`].
    JsonDiagnostic {
        /// [`json_string_body_bytes`] of the span's `file_name` as the emitter writes it.
        span_file_name_bytes: u64,
    },
}

impl TransportLineFraming {
    /// The JSON-diagnostic framing of a compile whose transport note's span renders
    /// `span_file_name` (Trust, TRANSPORT-LINE-BUDGET-1 review F4: a crate-root path, or a
    /// `--remap-path-prefix` target, can be longer than any fixed allowance).
    #[must_use]
    pub fn json_diagnostic(span_file_name: &str) -> Self {
        Self::JsonDiagnostic { span_file_name_bytes: json_string_body_bytes(span_file_name) }
    }

    /// Bytes of the whole stderr line (newline included) that carries `payload_json`,
    /// the serialized message without the `TRUST_JSON:` prefix. Exact for
    /// [`Self::RawStderr`]; for [`Self::JsonDiagnostic`] exact for the message and the
    /// span's file name, and an upper bound ([`JSON_DIAGNOSTIC_FRAMING_OVERHEAD_BYTES`])
    /// for the rest.
    #[must_use]
    pub fn line_bytes(self, payload_json: &str) -> u64 {
        let prefix = crate::TRANSPORT_PREFIX;
        match self {
            Self::RawStderr => (prefix.len() + payload_json.len() + 1) as u64,
            Self::JsonDiagnostic { span_file_name_bytes } => {
                json_string_body_bytes(prefix)
                    + json_string_body_bytes(payload_json)
                    + span_file_name_bytes
                    + JSON_DIAGNOSTIC_FRAMING_OVERHEAD_BYTES
            }
        }
    }

    /// Bytes `fragment` adds to the line when it is part of the payload. Additive over
    /// concatenation, which is what lets the ladder price one row at a time.
    #[must_use]
    pub fn fragment_bytes(self, fragment: &str) -> u64 {
        match self {
            Self::RawStderr => fragment.len() as u64,
            Self::JsonDiagnostic { .. } => json_string_body_bytes(fragment),
        }
    }
}

/// Bytes of `text` written as the body of a JSON string by `serde_json` (quotes not
/// counted): `"` and `\` take two bytes, the short-escaped control characters two, the
/// other control characters six (`\u00XX`), everything else its UTF-8 bytes.
#[must_use]
pub fn json_string_body_bytes(text: &str) -> u64 {
    json_string_body_slice_bytes(text.as_bytes())
}

fn json_string_body_slice_bytes(bytes: &[u8]) -> u64 {
    bytes
        .iter()
        .map(|&byte| match byte {
            b'"' | b'\\' | b'\n' | b'\r' | b'\t' | 0x08 | 0x0c => 2u64,
            0x00..=0x1f => 6,
            _ => 1,
        })
        .sum()
}

struct FragmentByteCounter {
    framing: TransportLineFraming,
    bytes: u64,
}

impl std::io::Write for FragmentByteCounter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.bytes += match self.framing {
            TransportLineFraming::RawStderr => buf.len() as u64,
            TransportLineFraming::JsonDiagnostic { .. } => json_string_body_slice_bytes(buf),
        };
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn serialized_fragment_bytes<T: Serialize>(
    framing: TransportLineFraming,
    value: &T,
) -> Result<u64, serde_json::Error> {
    let mut counter = FragmentByteCounter { framing, bytes: 0 };
    serde_json::to_writer(&mut counter, value)?;
    Ok(counter.bytes)
}

/// Which step of the ladder a function's report needed. Absent from the envelope when
/// the report fit whole.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TransportBudgetStep {
    /// Step 1: authority-free payloads withheld; no outcome changed.
    WithheldDiagnosticPayloads,
    /// Step 2: proof evidence withheld; the rows that claimed credit were demoted.
    WithheldProofEvidence,
    /// Step 3: the rows were replaced by one fail-closed row.
    ReportReplaced,
}

/// One row field the ladder can withhold.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TransportWithheldField {
    /// [`TransportObligationResult::original_vc_snapshot`] (step 1).
    OriginalVcSnapshot,
    /// The artifact payloads (`materialization`, `metadata`) of
    /// [`TransportObligationResult::proof_evidence`] (step 2, demotes).
    ProofEvidencePayloads,
    /// The artifact payloads (`materialization`, `metadata`) of
    /// [`TransportObligationResult::native_trust_ir`] (step 2, demotes).
    NativeTrustIrPayloads,
}

impl TransportWithheldField {
    /// The wire spelling (the row field's own name).
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::OriginalVcSnapshot => "original_vc_snapshot",
            Self::ProofEvidencePayloads => "proof_evidence_payloads",
            Self::NativeTrustIrPayloads => "native_trust_ir_payloads",
        }
    }

    /// Whether withholding this field can change what a consumer derives from the row,
    /// so that the row may keep no favorable outcome without it.
    #[must_use]
    pub const fn carries_authority(self) -> bool {
        matches!(self, Self::ProofEvidencePayloads | Self::NativeTrustIrPayloads)
    }

    fn present_in(self, row: &TransportObligationResult) -> bool {
        match self {
            Self::OriginalVcSnapshot => row.original_vc_snapshot.is_some(),
            Self::ProofEvidencePayloads => row
                .proof_evidence
                .as_ref()
                .is_some_and(|proof| proof.artifacts.iter().any(artifact_carries_payload)),
            Self::NativeTrustIrPayloads => row
                .native_trust_ir
                .as_ref()
                .is_some_and(|native| native.artifacts.iter().any(artifact_carries_payload)),
        }
    }

    fn withhold_from(self, row: &mut TransportObligationResult) {
        match self {
            Self::OriginalVcSnapshot => row.original_vc_snapshot = None,
            Self::ProofEvidencePayloads => {
                if let Some(proof) = &mut row.proof_evidence {
                    hollow(&mut proof.artifacts, &mut proof.diagnostics);
                }
            }
            Self::NativeTrustIrPayloads => {
                if let Some(native) = &mut row.native_trust_ir {
                    hollow(&mut native.artifacts, &mut native.diagnostics);
                }
            }
        }
    }
}

const STEP1_FIELDS: [TransportWithheldField; 1] = [TransportWithheldField::OriginalVcSnapshot];
const STEP2_FIELDS: [TransportWithheldField; 2] =
    [TransportWithheldField::ProofEvidencePayloads, TransportWithheldField::NativeTrustIrPayloads];

/// The code of the Error diagnostic step 2 adds to an evidence record whose artifact
/// payloads it withheld.
pub const TRANSPORT_LINE_BUDGET_EVIDENCE_DIAGNOSTIC: &str =
    "transport_line_budget_payload_withheld";

/// Whether an artifact still carries a payload step 2 withholds.
fn artifact_carries_payload(artifact: &crate::TransportEvidenceArtifact) -> bool {
    artifact.materialization.is_some() || artifact.metadata.is_some()
}

/// Withhold every artifact's payload and say so in the record's own diagnostics.
fn hollow(
    artifacts: &mut [crate::TransportEvidenceArtifact],
    diagnostics: &mut Vec<crate::TransportEvidenceDiagnostic>,
) {
    for artifact in artifacts.iter_mut() {
        artifact.materialization = None;
        artifact.metadata = None;
    }
    diagnostics.push(crate::TransportEvidenceDiagnostic {
        code: TRANSPORT_LINE_BUDGET_EVIDENCE_DIAGNOSTIC.to_string(),
        severity: crate::TransportEvidenceDiagnosticSeverity::Error,
        message: "the function's report did not fit the transport line budget, so this \
                  record's artifact payloads (materialization, metadata) were withheld; it \
                  grants no publication proof credit"
            .to_string(),
        detail: None,
    });
}

/// The rows (indices into `results`) one field was withheld from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportWithheldEvidence {
    pub field: TransportWithheldField,
    pub rows: Vec<usize>,
}

/// The per-function counts of the rows step 3 replaced, as the envelope would have
/// stated them.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportReplacedRows {
    pub total: usize,
    pub proved: usize,
    pub failed: usize,
    pub unknown: usize,
    pub timed_out: usize,
    pub skipped: usize,
    pub runtime_checked: usize,
}

/// The compiler's statement, on a function's envelope, that its report did not fit the
/// transport line budget whole, and what it withheld or replaced to make it fit.
/// Absent from the wire when the report fit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportBudgetDisclosure {
    /// The budget the line was fitted under (bytes of the whole line).
    pub line_budget_bytes: u64,
    /// What the line would have taken with nothing withheld.
    pub unbounded_line_bytes: u64,
    /// The last step the report needed.
    pub step: TransportBudgetStep,
    /// How many rows the compiler minted for the function. Equal to `results.len()`
    /// unless `step` is [`TransportBudgetStep::ReportReplaced`].
    pub minted_rows: usize,
    /// Per field, the rows it was withheld from, rows ascending, fields in
    /// [`TransportWithheldField`] order.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub withheld: Vec<TransportWithheldEvidence>,
    /// The rows whose favorable outcome step 2 demoted, ascending.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub demoted_rows: Vec<usize>,
    /// Step 3 only: the counts of the replaced rows.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub replaced: Option<TransportReplacedRows>,
}

impl TransportBudgetDisclosure {
    /// A defect in the disclosure against the rows it travels with, or `None`. A
    /// consumer treats a defect as a malformed function report. In particular, a row
    /// that lost proof evidence while still claiming a favorable outcome is a defect:
    /// the producer promises to demote every such row.
    #[must_use]
    pub fn defect(&self, results: &[TransportObligationResult]) -> Option<String> {
        if self.line_budget_bytes < MIN_TRANSPORT_LINE_BUDGET_BYTES
            || self.line_budget_bytes > TRANSPORT_LINE_BUDGET_BYTES
        {
            return Some(format!(
                "transport budget disclosure names a {}-byte budget, outside \
                 [{MIN_TRANSPORT_LINE_BUDGET_BYTES}, {TRANSPORT_LINE_BUDGET_BYTES}]",
                self.line_budget_bytes
            ));
        }
        if self.unbounded_line_bytes <= self.line_budget_bytes {
            return Some(
                "transport budget disclosure on a report that fit its budget whole".to_string(),
            );
        }
        let rows = results.len();
        let in_range = |indices: &[usize]| {
            indices.windows(2).all(|w| w[0] < w[1]) && indices.iter().all(|&i| i < rows)
        };
        if self.withheld.iter().any(|entry| entry.rows.is_empty() || !in_range(&entry.rows))
            || self.withheld.windows(2).any(|w| w[0].field >= w[1].field)
            || !in_range(&self.demoted_rows)
        {
            return Some(
                "transport budget disclosure lists a row out of range, out of order or twice"
                    .to_string(),
            );
        }
        match (self.step, self.replaced) {
            (TransportBudgetStep::ReportReplaced, Some(replaced)) => {
                let fallback_only = rows == 1
                    && results[0].kind == TRANSPORT_LINE_BUDGET_ROW_KIND
                    && results[0].solver == TRANSPORT_LINE_BUDGET_ROW_SOLVER
                    && matches!(results[0].outcome, Outcome::Failed | Outcome::Unknown)
                    && results[0].proof_evidence.is_none()
                    && results[0].native_trust_ir.is_none()
                    && results[0].grade.is_none()
                    && (replaced.failed == 0 || results[0].outcome == Outcome::Failed);
                if !fallback_only
                    || replaced.total != self.minted_rows
                    || self.minted_rows == 0
                    || !self.withheld.is_empty()
                    || !self.demoted_rows.is_empty()
                {
                    return Some(
                        "transport budget disclosure replaced the report but the rows are not \
                         its one fail-closed row"
                            .to_string(),
                    );
                }
            }
            (TransportBudgetStep::ReportReplaced, None) | (_, Some(_)) => {
                return Some(
                    "transport budget disclosure's step and replaced counts disagree".to_string(),
                );
            }
            (step, None) => {
                if self.minted_rows != rows {
                    return Some(format!(
                        "transport budget disclosure minted {} rows but the report carries {rows}",
                        self.minted_rows
                    ));
                }
                let authority_withheld: std::collections::BTreeSet<usize> = self
                    .withheld
                    .iter()
                    .filter(|entry| entry.field.carries_authority())
                    .flat_map(|entry| entry.rows.iter().copied())
                    .collect();
                for &row in &authority_withheld {
                    if outcome_is_favorable(results[row].outcome) || results[row].grade.is_some() {
                        return Some(format!(
                            "transport budget disclosure withheld row {row}'s proof evidence but \
                             the row still claims `{}`{}",
                            results[row].outcome.as_str(),
                            if results[row].grade.is_some() { " with a grade" } else { "" }
                        ));
                    }
                }
                if let Some(row) = self
                    .withheld
                    .iter()
                    .flat_map(|entry| entry.rows.iter().copied())
                    .find(|&row| is_envelope_shape_row(&results[row]))
                {
                    return Some(format!(
                        "transport budget disclosure withheld a payload of row {row}, a `{}` row \
                         the ladder never strips",
                        results[row].kind
                    ));
                }
                if !self.demoted_rows.iter().all(|row| authority_withheld.contains(row)) {
                    return Some(
                        "transport budget disclosure demoted a row whose proof evidence it did \
                         not withhold"
                            .to_string(),
                    );
                }
                let needed = if authority_withheld.is_empty() {
                    TransportBudgetStep::WithheldDiagnosticPayloads
                } else {
                    TransportBudgetStep::WithheldProofEvidence
                };
                if step != needed || self.withheld.is_empty() {
                    return Some(
                        "transport budget disclosure's step does not match what it withheld"
                            .to_string(),
                    );
                }
                for (field, row) in self
                    .withheld
                    .iter()
                    .flat_map(|entry| entry.rows.iter().map(move |&row| (entry.field, row)))
                {
                    if field.present_in(&results[row]) {
                        return Some(format!(
                            "transport budget disclosure says row {row}'s `{}` was withheld, but \
                             the row carries it",
                            field.as_str()
                        ));
                    }
                }
            }
        }
        None
    }
}

/// Whether an outcome is one a consumer could credit from the row's proof evidence: a
/// proof or a runtime-check disposition. Every other outcome grants nothing.
#[must_use]
pub const fn outcome_is_favorable(outcome: Outcome) -> bool {
    matches!(outcome, Outcome::Proved | Outcome::RuntimeChecked)
}

/// Whether targo-trust's exit-code gate (`partition_outcome_counts`) reads this row by
/// a conditional-evidence arm: one that counts the row's FAVORABLE label as a
/// transport defect (a genuine unknown) and its other labels as conditional evidence
/// (`assumed`, a declared contract panic, a test-harness exclusion). For such a row
/// `unknown` is not the bottom, so step 2 never touches a favorable one. The
/// predicates are the ones the gate calls, from this crate.
#[must_use]
pub fn is_conditional_evidence_row(row: &TransportObligationResult) -> bool {
    row.kind.starts_with("assumption:")
        || row.kind == crate::assumption::COROUTINE_RESUME_CONTRACT_ROW_KIND
        || row.kind == crate::assumption::GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_KIND
        || crate::assumption::is_coroutine_resume_conditional_row_kind(&row.kind)
        || crate::exclusion::is_test_harness_exclusion_row_kind(&row.kind)
        || crate::tolerance::classify_contract_panic(&crate::tolerance::ContractPanicView {
            text: &row.description,
            row_kind: Some(&row.kind),
        })
        .is_declared()
}

/// The kind of the compiler's zero-obligation inventory row
/// (`compiler/rustc_mir_transform/src/trust_verify.rs`), which targo-trust recognizes
/// by its exact shape (`is_exact_zero_obligation_inventory_row`) and elides.
pub const ZERO_OBLIGATION_INVENTORY_ROW_KIND: &str = "no_obligations";

/// Whether a consumer recognizes this row's kind by an EXACT shape that includes
/// "no claim field present" (targo-trust's `carries_only_envelope_facts`): the
/// zero-obligation inventory row and the test-harness exclusion row, both of which
/// targo-trust elides from the gate when they match exactly, while a lookalike stays
/// and fails closed. Withholding a field from a lookalike could complete that shape
/// and move it out of the fail-closed path, so the ladder withholds nothing from a
/// row of these kinds at any step (it is left whole, or replaced in step 3).
#[must_use]
pub fn is_envelope_shape_row(row: &TransportObligationResult) -> bool {
    row.kind == ZERO_OBLIGATION_INVENTORY_ROW_KIND
        || crate::exclusion::is_test_harness_exclusion_row_kind(&row.kind)
}

/// The outcome a row publishes once its proof evidence is withheld (step 2).
///
/// targo-trust reads verdicts off that evidence (`normalize_transport_outcome`): proof
/// evidence whose status is `failed` turns a `proved`, `runtime_checked` or `timeout`
/// label into a failure, and evidence that does not back a favorable label turns it
/// into `unknown`. Without the evidence it keeps the label as written. So the row is
/// `failed` when its evidence refutes a `proved`, `runtime_checked` or `timeout`
/// label; `unknown` when it is otherwise favorable; and keeps any other outcome, which
/// without its evidence targo reads no better than with it (`failed` stays `failed`
/// where evidence could only soften it to `timeout` or `unknown`; `unknown`,
/// `skipped`, `unsupported`, `canceled` and `rejected` are `unknown` either way; a
/// `timeout` stays `timeout` unless its evidence refuted it).
#[must_use]
pub fn demoted_outcome(row: &TransportObligationResult) -> Outcome {
    let evidence_refutes =
        matches!(row.outcome, Outcome::Proved | Outcome::RuntimeChecked | Outcome::Timeout)
            && row
                .proof_evidence
                .as_ref()
                .is_some_and(|proof| proof.status == crate::TransportProofStatus::Failed);
    if evidence_refutes {
        Outcome::Failed
    } else if outcome_is_favorable(row.outcome) {
        Outcome::Unknown
    } else {
        row.outcome
    }
}

/// Whether step 1 may withhold this row's diagnostic payloads: it carries one, and it
/// is not an envelope-shape row ([`is_envelope_shape_row`]).
fn step1_may_withhold(row: &TransportObligationResult) -> bool {
    STEP1_FIELDS.iter().any(|field| field.present_in(row)) && !is_envelope_shape_row(row)
}

/// Whether step 2 may withhold this row's proof evidence: it carries some, it is not
/// an envelope-shape row ([`is_envelope_shape_row`]), and it is not a favorable row of
/// a conditional-evidence kind ([`is_conditional_evidence_row`]).
fn step2_may_withhold(row: &TransportObligationResult) -> bool {
    STEP2_FIELDS.iter().any(|field| field.present_in(row))
        && !is_envelope_shape_row(row)
        && !(outcome_is_favorable(row.outcome) && is_conditional_evidence_row(row))
}

/// What [`fit_function_result`] did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FittedTransportLine {
    /// The serialized message (no `TRUST_JSON:` prefix) to emit.
    pub payload: String,
    /// The bytes its line takes under the framing it was fitted for.
    pub line_bytes: u64,
}

/// Serialize a function result exactly as `TransportMessage::FunctionResult` serializes
/// it (the internally tagged `type` first), from a borrow: the report can be tens of
/// megabytes, and the ladder measures it more than once.
///
/// # Errors
///
/// Only a `serde_json` serialization failure.
pub fn function_result_payload(
    result: &FunctionTransportResult,
) -> Result<String, serde_json::Error> {
    #[derive(Serialize)]
    #[serde(tag = "type")]
    enum FunctionResultMessage<'a> {
        #[serde(rename = "function_result")]
        FunctionResult(&'a FunctionTransportResult),
    }
    serde_json::to_string(&FunctionResultMessage::FunctionResult(result))
}

/// The ladder's bookkeeping: which fields left which rows, and which rows were demoted.
#[derive(Default)]
struct Withheld {
    rows: std::collections::BTreeMap<TransportWithheldField, std::collections::BTreeSet<usize>>,
    demoted: std::collections::BTreeSet<usize>,
}

impl Withheld {
    fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    fn disclosure(
        &self,
        budget: u64,
        unbounded: u64,
        minted_rows: usize,
    ) -> TransportBudgetDisclosure {
        let step = if self.rows.keys().any(|field| field.carries_authority()) {
            TransportBudgetStep::WithheldProofEvidence
        } else {
            TransportBudgetStep::WithheldDiagnosticPayloads
        };
        TransportBudgetDisclosure {
            line_budget_bytes: budget,
            unbounded_line_bytes: unbounded,
            step,
            minted_rows,
            withheld: self
                .rows
                .iter()
                .map(|(field, rows)| TransportWithheldEvidence {
                    field: *field,
                    rows: rows.iter().copied().collect(),
                })
                .collect(),
            demoted_rows: self.demoted.iter().copied().collect(),
            replaced: None,
        }
    }
}

/// Fit one function's `TransportMessage::FunctionResult` under `budget` bytes of
/// `framing`, by the ladder in the module docs, and return the payload to emit.
///
/// `restate` re-derives every envelope field that depends on the rows' outcomes or on
/// the rows themselves (the counts, the stable ids). It is called whenever step 2
/// demotes a row and when step 3 replaces the rows; step 1 changes neither.
/// `fallback_location` anchors the step-3 row.
///
/// The result's `line_bytes` is at most `budget` unless even the step-3 envelope
/// (the function's identity strings and one row) exceeds it, which no budget at or
/// above [`MIN_TRANSPORT_LINE_BUDGET_BYTES`] meets for any real function path.
///
/// # Errors
///
/// Only a `serde_json` serialization failure.
pub fn fit_function_result(
    result: &mut FunctionTransportResult,
    budget: u64,
    framing: TransportLineFraming,
    fallback_location: Option<SourceSpan>,
    restate: &mut dyn FnMut(&mut FunctionTransportResult),
) -> Result<FittedTransportLine, serde_json::Error> {
    result.transport_budget = None;
    let payload = function_result_payload(result)?;
    let unbounded = framing.line_bytes(&payload);
    if unbounded <= budget {
        return Ok(FittedTransportLine { payload, line_bytes: unbounded });
    }
    drop(payload);
    let minted_rows = result.results.len();
    // Read before any row changes: what step 3 would replace (the envelope's own
    // counts), and whether any of it is refuted, by its label or by its evidence.
    let replaced = TransportReplacedRows {
        total: result.total,
        proved: result.proved,
        failed: result.failed,
        unknown: result.unknown,
        timed_out: result.timed_out,
        skipped: result.skipped,
        runtime_checked: result.runtime_checked,
    };
    let refuted = result
        .results
        .iter()
        .any(|row| row.outcome == Outcome::Failed || demoted_outcome(row) == Outcome::Failed);
    let mut withheld = Withheld::default();

    for (fields, step2) in [(&STEP1_FIELDS[..], false), (&STEP2_FIELDS[..], true)] {
        // Each row's saving, priced once: what its fragment shrinks by when this step
        // strips it. Step 2 takes the rows that claim nothing favorable first.
        let mut candidates: Vec<(bool, u64, usize)> = Vec::new();
        for (index, row) in result.results.iter().enumerate() {
            let eligible = if step2 { step2_may_withhold(row) } else { step1_may_withhold(row) };
            if !eligible {
                continue;
            }
            let before = serialized_fragment_bytes(framing, row)?;
            let mut stripped = row.clone();
            strip_row(&mut stripped, fields, step2, budget);
            let after = serialized_fragment_bytes(framing, &stripped)?;
            if before > after {
                candidates.push((
                    step2 && outcome_is_favorable(row.outcome),
                    before - after,
                    index,
                ));
            }
        }
        // Cheapest loss first, then the largest saving; ties by row order, so the
        // choice is deterministic.
        candidates.sort_by(|a, b| a.0.cmp(&b.0).then(b.1.cmp(&a.1)).then(a.2.cmp(&b.2)));
        let mut next = 0;
        loop {
            result.transport_budget =
                (!withheld.is_empty()).then(|| withheld.disclosure(budget, unbounded, minted_rows));
            let payload = function_result_payload(result)?;
            let line_bytes = framing.line_bytes(&payload);
            if line_bytes <= budget {
                return Ok(FittedTransportLine { payload, line_bytes });
            }
            if next == candidates.len() {
                break;
            }
            // Take rows until their savings cover the excess, net of what listing a row
            // in the disclosure costs (an index and a comma in up to three lists: under
            // 48 bytes).
            let mut excess = line_bytes - budget;
            let mut demoted_any = false;
            while next < candidates.len() && excess > 0 {
                let (_, saving, index) = candidates[next];
                next += 1;
                let row = &mut result.results[index];
                for &field in fields {
                    if field.present_in(row) {
                        withheld.rows.entry(field).or_default().insert(index);
                    }
                }
                if step2 && demoted_outcome(row) != row.outcome {
                    withheld.demoted.insert(index);
                    demoted_any = true;
                }
                strip_row(row, fields, step2, budget);
                excess = excess.saturating_sub(saving.saturating_sub(48));
            }
            if demoted_any {
                restate(result);
            }
        }
    }

    // Step 3: even every row stripped of every withholdable payload does not fit.
    result.results = vec![fallback_row(
        &result.function,
        minted_rows,
        budget,
        replaced,
        refuted,
        fallback_location,
    )];
    result.cached = 0;
    restate(result);
    result.transport_budget = Some(TransportBudgetDisclosure {
        line_budget_bytes: budget,
        unbounded_line_bytes: unbounded,
        step: TransportBudgetStep::ReportReplaced,
        minted_rows,
        withheld: Vec::new(),
        demoted_rows: Vec::new(),
        replaced: Some(replaced),
    });
    let mut payload = function_result_payload(result)?;
    // The modeled facts qualify proved rows, and none remains; they are the one list of
    // the fallback envelope that is not the function's identity.
    if framing.line_bytes(&payload) > budget && !result.modeled_facts.is_empty() {
        result.modeled_facts.clear();
        payload = function_result_payload(result)?;
    }
    let line_bytes = framing.line_bytes(&payload);
    Ok(FittedTransportLine { payload, line_bytes })
}

/// Strip one row exactly as [`fit_function_result`] strips a row it selects for `step`
/// under `budget`, and say whether the step may select it at all (when it may not, the
/// row is left as it is). For consumers that pin the ladder's effect on their own
/// reading of a row; [`TransportBudgetStep::ReportReplaced`] strips no row.
pub fn strip_row_for_step(
    row: &mut TransportObligationResult,
    step: TransportBudgetStep,
    budget: u64,
) -> bool {
    let (fields, step2, eligible) = match step {
        TransportBudgetStep::WithheldDiagnosticPayloads => {
            (&STEP1_FIELDS[..], false, step1_may_withhold(row))
        }
        TransportBudgetStep::WithheldProofEvidence => {
            (&STEP2_FIELDS[..], true, step2_may_withhold(row))
        }
        TransportBudgetStep::ReportReplaced => return false,
    };
    if eligible {
        strip_row(row, fields, step2, budget);
    }
    eligible
}

/// Strip one row for a step: withhold `fields`, and in step 2 withdraw the row's grade
/// (the authority it states is no longer on the wire) and demote it.
fn strip_row(
    row: &mut TransportObligationResult,
    fields: &[TransportWithheldField],
    step2: bool,
    budget: u64,
) {
    if step2 {
        use std::fmt::Write as _;
        row.grade = None;
        let outcome = demoted_outcome(row);
        if outcome != row.outcome {
            let was = row.outcome;
            row.outcome = outcome;
            let prior = row.reason.take();
            let mut reason = String::with_capacity(
                160 + prior.as_ref().map_or(0, |p| p.len() + 20),
            );
            let _ = write!(
                reason,
                "{TRANSPORT_LINE_BUDGET_DEMOTION_PREFIX} the function's report did not fit the \
                 {budget}-byte transport line, so this row's proof-evidence payloads ("
            );
            let mut first = true;
            for &field in fields {
                if field.present_in(row) {
                    if !first {
                        reason.push_str(", ");
                    }
                    first = false;
                    reason.push_str(field.as_str());
                }
            }
            let _ = write!(
                reason,
                ") were withheld and its `{}` is published as `{}`",
                was.as_str(),
                outcome.as_str(),
            );
            if let Some(prior) = prior.as_deref() {
                let _ = write!(reason, " (its reason was: {prior})");
            }
            row.reason = Some(reason);
        }
    }
    for &field in fields {
        if field.present_in(row) {
            field.withhold_from(row);
        }
    }
}

fn fallback_row(
    function: &str,
    minted_rows: usize,
    budget: u64,
    replaced: TransportReplacedRows,
    refuted: bool,
    location: Option<SourceSpan>,
) -> TransportObligationResult {
    TransportObligationResult {
        obligation_id: None,
        claim_digest_sha256: None,
        kind: TRANSPORT_LINE_BUDGET_ROW_KIND.to_string(),
        original_vc_snapshot: None,
        typed_kind: None,
        description: format!(
            "the verification report of `{function}` ({minted_rows} rows) does not fit the \
             {budget}-byte transport line even with every optional evidence payload withheld; \
             its rows are not transported and the function is not verified"
        ),
        location,
        outcome: if refuted { Outcome::Failed } else { Outcome::Unknown },
        solver: TRANSPORT_LINE_BUDGET_ROW_SOLVER.to_string(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: Some(format!(
            "{TRANSPORT_LINE_BUDGET_DEMOTION_PREFIX} the report was replaced by this fail-closed \
             row; the replaced rows were {} proved, {} failed, {} runtime-checked and {} unknown \
             ({} timed out, {} skipped); a refuted replaced row makes this row `failed`",
            replaced.proved,
            replaced.failed,
            replaced.runtime_checked,
            replaced.unknown,
            replaced.timed_out,
            replaced.skipped,
        )),
        design_mandate: false,
        gap_class: None,
        native_trust_ir: None,
        proof_evidence: None,
        monitor: None,
        assumes: Vec::new(),
        grade: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::authority_grade::{GradeDischarge, GradeEncoding, ObligationGrade};
    use crate::{
        OriginalVcSnapshot, TransportEvidenceArtifact, TransportMessage,
        TransportNativeTrustIrEvidence, TransportProofEvidence, TransportProofStatus,
    };

    /// The JSON framing of a compile whose crate root is `src/lib.rs`.
    const JSON: TransportLineFraming =
        TransportLineFraming::JsonDiagnostic { span_file_name_bytes: "src/lib.rs".len() as u64 };

    const ALL_OUTCOMES: [Outcome; 9] = [
        Outcome::Proved,
        Outcome::Failed,
        Outcome::Unknown,
        Outcome::Timeout,
        Outcome::RuntimeChecked,
        Outcome::Skipped,
        Outcome::Unsupported,
        Outcome::Canceled,
        Outcome::Rejected,
    ];
    const ALL_STATUSES: [TransportProofStatus; 6] = [
        TransportProofStatus::Proved,
        TransportProofStatus::Failed,
        TransportProofStatus::Unknown,
        TransportProofStatus::Timeout,
        TransportProofStatus::Unsupported,
        TransportProofStatus::Rejected,
    ];

    fn row(kind: &str, outcome: Outcome) -> TransportObligationResult {
        serde_json::from_value(serde_json::json!({
            "kind": kind,
            "description": format!("the {kind} obligation"),
            "outcome": outcome.as_str(),
            "solver": "trust-full-verifier",
            "time_ms": 1,
        }))
        .expect("row fixture")
    }

    /// A snapshot whose payload is `bytes` long and full of quotes, so the JSON
    /// diagnostic framing escapes it twice over.
    fn snapshot(bytes: usize) -> Box<OriginalVcSnapshot> {
        let unit = r#"{"k":"v"},"#;
        Box::new(OriginalVcSnapshot {
            schema: "trust-original-vc/v1".into(),
            obligation_id: "vc:f:assert:0".into(),
            claim_digest_sha256: "0".repeat(64),
            typed_input_digest_sha256: None,
            expanded_function_identity: None,
            overflow_checks: true,
            target: "aarch64-apple-darwin".into(),
            payload_sha256: "1".repeat(64),
            original_vc_json: unit.repeat(bytes / unit.len() + 1),
        })
    }

    fn artifact(bytes: usize) -> TransportEvidenceArtifact {
        TransportEvidenceArtifact {
            kind: "certificate".into(),
            format: Some("clean-cic".into()),
            artifact_id: None,
            digest: None,
            uri: None,
            materialization: None,
            // A CIC term as the compiler carries it: a JSON byte array.
            metadata: Some(serde_json::Value::Array(
                (0..bytes / 4).map(|i| serde_json::Value::from(100 + (i % 150))).collect(),
            )),
        }
    }

    fn proof(status: TransportProofStatus, bytes: usize) -> TransportProofEvidence {
        TransportProofEvidence {
            suite: "trust-full-verifier".into(),
            backend: "clean".into(),
            request_id: None,
            proof_id: Some("proof:1".into()),
            native_id: None,
            status,
            strength: None,
            evidence: None,
            artifacts: vec![artifact(bytes)],
            diagnostics: Vec::new(),
        }
    }

    fn native(bytes: usize) -> TransportNativeTrustIrEvidence {
        TransportNativeTrustIrEvidence {
            suite: "trust-full-verifier".into(),
            backend: "trust-ir".into(),
            request_id: None,
            native_id: Some("native:1".into()),
            present: true,
            artifacts: vec![artifact(bytes)],
            diagnostics: Vec::new(),
        }
    }

    /// Whether a row's evidence records survive with every artifact payload withheld and
    /// the in-band diagnostic added (step 2's effect on a row it selects).
    fn hollowed(row: &TransportObligationResult) -> bool {
        let record_ok =
            |artifacts: &[TransportEvidenceArtifact],
             diagnostics: &[crate::TransportEvidenceDiagnostic]| {
                artifacts.iter().all(|a| a.materialization.is_none() && a.metadata.is_none())
                    && diagnostics
                        .iter()
                        .any(|d| d.code == TRANSPORT_LINE_BUDGET_EVIDENCE_DIAGNOSTIC)
            };
        row.proof_evidence.as_ref().is_none_or(|p| record_ok(&p.artifacts, &p.diagnostics))
            && row.native_trust_ir.as_ref().is_none_or(|n| record_ok(&n.artifacts, &n.diagnostics))
            && (row.proof_evidence.is_some() || row.native_trust_ir.is_some())
    }

    fn grade() -> ObligationGrade {
        ObligationGrade::new(
            GradeEncoding::ProvenCalculus,
            GradeDischarge::KernelReferenceChecked,
            &[],
        )
    }

    /// The counts exactly as trustc's `PublishedRowTally::json_counts` states them for
    /// rows without instance-discharge or entry-assumption kinds.
    fn restate_counts(result: &mut FunctionTransportResult) {
        let (mut proved, mut failed, mut unknown, mut timed_out, mut skipped, mut rc) =
            (0, 0, 0, 0, 0, 0);
        for row in &result.results {
            match row.outcome {
                Outcome::Proved => proved += 1,
                Outcome::Failed => failed += 1,
                Outcome::RuntimeChecked => rc += 1,
                Outcome::Timeout => {
                    timed_out += 1;
                    unknown += 1;
                }
                Outcome::Skipped => {
                    skipped += 1;
                    unknown += 1;
                }
                _ => unknown += 1,
            }
        }
        result.proved = proved;
        result.failed = failed;
        result.unknown = unknown;
        result.timed_out = timed_out;
        result.skipped = skipped;
        result.runtime_checked = rc;
        result.total = result.results.len();
        result.stable_ids = (0..result.results.len()).map(|i| format!("id:{i}")).collect();
    }

    fn envelope(function: &str, rows: Vec<TransportObligationResult>) -> FunctionTransportResult {
        let mut result: FunctionTransportResult = serde_json::from_value(serde_json::json!({
            "function": function,
            "results": [],
            "proved": 0, "failed": 0, "unknown": 0, "runtime_checked": 0, "total": 0,
        }))
        .expect("envelope fixture");
        result.crate_name = Some("budget_fixture".into());
        result.verification_session = "session".into();
        result.modeled_facts = vec!["modeled fact".into()];
        result.results = rows;
        restate_counts(&mut result);
        result
    }

    fn fit(
        result: &mut FunctionTransportResult,
        budget: u64,
        framing: TransportLineFraming,
    ) -> (FittedTransportLine, usize) {
        let mut restated = 0;
        let fitted = fit_function_result(result, budget, framing, None, &mut |r| {
            restated += 1;
            restate_counts(r);
        })
        .expect("fit");
        (fitted, restated)
    }

    /// The rank the gate gives a row's normalized outcome, best last. Used to state
    /// "never upgraded" over the whole outcome x evidence space.
    fn rank(outcome: Outcome) -> u8 {
        match outcome {
            Outcome::Failed => 0,
            Outcome::Proved => 3,
            Outcome::RuntimeChecked => 2,
            _ => 1,
        }
    }

    /// targo-trust's `normalize_transport_outcome` for a full-verifier row, restated
    /// over trust-types' outcomes (the targo-trust tests check the real one).
    fn targo_reading(row: &TransportObligationResult) -> Outcome {
        let parsed = match row.outcome {
            o
            @ (Outcome::Proved | Outcome::Failed | Outcome::RuntimeChecked | Outcome::Timeout) => o,
            _ => Outcome::Unknown,
        };
        let Some(proof) = &row.proof_evidence else { return parsed };
        match proof.status {
            TransportProofStatus::Proved if parsed == Outcome::Proved => Outcome::Proved,
            status if parsed == Outcome::Timeout && status != TransportProofStatus::Failed => {
                Outcome::Timeout
            }
            TransportProofStatus::Proved => Outcome::Unknown,
            TransportProofStatus::Failed if parsed == Outcome::Unknown => Outcome::Unknown,
            TransportProofStatus::Failed => Outcome::Failed,
            TransportProofStatus::Timeout => Outcome::Timeout,
            _ if parsed == Outcome::RuntimeChecked => Outcome::RuntimeChecked,
            _ => Outcome::Unknown,
        }
    }

    #[test]
    fn the_budget_is_half_targos_cap_and_a_request_only_lowers_it() {
        assert_eq!(TRANSPORT_LINE_BUDGET_BYTES * 2, 128 * 1024 * 1024);
        assert_eq!(lowered_line_budget(None), TRANSPORT_LINE_BUDGET_BYTES);
        assert_eq!(lowered_line_budget(Some(u64::MAX)), TRANSPORT_LINE_BUDGET_BYTES);
        assert_eq!(
            lowered_line_budget(Some(TRANSPORT_LINE_BUDGET_BYTES + 1)),
            TRANSPORT_LINE_BUDGET_BYTES
        );
        assert_eq!(lowered_line_budget(Some(0)), MIN_TRANSPORT_LINE_BUDGET_BYTES);
        assert_eq!(lowered_line_budget(Some(1)), MIN_TRANSPORT_LINE_BUDGET_BYTES);
        assert_eq!(lowered_line_budget(Some(100_000)), 100_000);
    }

    #[test]
    fn json_string_body_bytes_is_serde_jsons_escaping() {
        for text in [
            "",
            "plain",
            r#"{"a":"b\\c"}"#,
            "tab\tnew\nline\rcr",
            "\u{0}\u{1}\u{1f}\u{8}\u{c}\u{7f}",
            "unicode \u{e9} \u{1F600}",
            &"\"".repeat(1000),
        ] {
            let quoted = serde_json::to_string(text).unwrap();
            assert_eq!(json_string_body_bytes(text), (quoted.len() - 2) as u64, "{text:?}");
        }
    }

    #[test]
    fn line_bytes_is_exact_for_raw_stderr_and_bounds_a_json_diagnostic() {
        let payload = r#"{"type":"function_result","x":"\"q\""}"#;
        let raw = format!("{}{payload}\n", crate::TRANSPORT_PREFIX);
        assert_eq!(TransportLineFraming::RawStderr.line_bytes(payload), raw.len() as u64);
        // rustc's JSON emitter as `rustc_errors::json` writes a transport note (its own
        // test pins the line at most the message body plus the 4 KiB frame).
        let message = format!("{}{payload}", crate::TRANSPORT_PREFIX);
        let line = json_diagnostic_line(&message, "src/lib.rs");
        assert!(JSON.line_bytes(payload) >= line.len() as u64);
        let body = serde_json::to_string(&message).unwrap().len() as u64 - 2;
        assert_eq!(
            JSON.line_bytes(payload),
            body + "src/lib.rs".len() as u64 + JSON_DIAGNOSTIC_FRAMING_OVERHEAD_BYTES
        );
    }

    /// The line rustc's JSON emitter writes for a transport note (`rustc_errors::json`,
    /// `// Trust:`): one span, at the start of the file the compile names first.
    fn json_diagnostic_line(message: &str, file_name: &str) -> String {
        serde_json::json!({
            "$message_type": "diagnostic",
            "message": message,
            "code": {"code": crate::TRANSPORT_DIAGNOSTIC_CODE, "explanation": null},
            "level": "note",
            "spans": [{
                "file_name": file_name, "byte_start": 0, "byte_end": 0, "line_start": 1,
                "line_end": 1, "column_start": 1, "column_end": 1, "is_primary": true,
                "text": [], "label": null, "suggested_replacement": null,
                "suggestion_applicability": null, "expansion": null,
            }],
            "children": [],
            "rendered": concat!(
                "note: Trust verification transport ",
                "(its machine-readable payload is this diagnostic's `message`)\n\n",
            ),
        })
        .to_string()
            + "\n"
    }

    /// Review F4 (2026-11-02): the span's `file_name` is the crate root as the compile
    /// renders it, which a long checkout path or a `--remap-path-prefix` target can make
    /// longer than the fixed frame. It is counted exactly, so a line the ladder says fits
    /// does fit, whatever the name.
    #[test]
    fn a_long_span_file_name_is_counted_not_assumed_short() {
        let payload = r#"{"type":"function_result","x":"\"q\""}"#;
        let message = format!("{}{payload}", crate::TRANSPORT_PREFIX);
        for name in [
            String::new(),
            "src/lib.rs".to_string(),
            format!("/{}/src/lib.rs", "deep\"dir\\".repeat(2_000)),
            "/".repeat(3 * JSON_DIAGNOSTIC_FRAMING_OVERHEAD_BYTES as usize),
        ] {
            let framing = TransportLineFraming::json_diagnostic(&name);
            let line = json_diagnostic_line(&message, &name);
            assert!(
                framing.line_bytes(payload) >= line.len() as u64,
                "a {}-byte file name: {} < {}",
                name.len(),
                framing.line_bytes(payload),
                line.len()
            );
            // Exact in the name: a longer name costs exactly its escaped bytes.
            assert_eq!(
                framing.line_bytes(payload),
                TransportLineFraming::json_diagnostic("").line_bytes(payload)
                    + json_string_body_bytes(&name)
            );
        }
        // And the ladder fits a report under the budget the real line is judged by.
        let long = format!("/{}/src/lib.rs", "r".repeat(8 * 1024));
        let framing = TransportLineFraming::json_diagnostic(&long);
        let mut rows = Vec::new();
        for i in 0..6 {
            let mut r = row(&format!("overflow:add{i}"), Outcome::Proved);
            r.original_vc_snapshot = Some(snapshot(3_000));
            rows.push(r);
        }
        let mut result = envelope("m::f", rows);
        let budget = MIN_TRANSPORT_LINE_BUDGET_BYTES + 8 * 1024;
        let (fitted, _) = fit(&mut result, budget, framing);
        let message = format!("{}{}", crate::TRANSPORT_PREFIX, fitted.payload);
        let line = json_diagnostic_line(&message, &long);
        assert!(fitted.line_bytes >= line.len() as u64, "the ladder priced the real line");
        assert!(line.len() as u64 <= budget, "a {}-byte line over {budget}", line.len());
        assert!(result.transport_budget.is_some(), "the long name made the report not fit");
    }

    #[test]
    fn the_borrowed_payload_is_the_transport_messages_serialization() {
        let mut first = row("overflow:add", Outcome::Proved);
        first.original_vc_snapshot = Some(snapshot(300));
        first.proof_evidence = Some(proof(TransportProofStatus::Proved, 200));
        first.grade = Some(grade());
        let result = envelope("m::f", vec![first, row("divzero", Outcome::Failed)]);
        let owned =
            serde_json::to_string(&TransportMessage::FunctionResult(result.clone())).unwrap();
        assert_eq!(function_result_payload(&result).unwrap(), owned);
        let parsed = crate::parse_transport_payload(&owned).expect("payload parses");
        let TransportMessage::FunctionResult(parsed) = parsed else {
            panic!("not a function result")
        };
        assert_eq!(parsed, result);
    }

    #[test]
    fn a_report_that_fits_is_emitted_unchanged_and_undisclosed() {
        let mut first = row("overflow:add", Outcome::Proved);
        first.original_vc_snapshot = Some(snapshot(2_000));
        first.proof_evidence = Some(proof(TransportProofStatus::Proved, 2_000));
        let mut result = envelope("m::f", vec![first]);
        let before = result.clone();
        let (fitted, restated) = fit(&mut result, MIN_TRANSPORT_LINE_BUDGET_BYTES, JSON);
        assert_eq!(result, before);
        assert_eq!(restated, 0);
        assert!(!fitted.payload.contains("transport_budget"));
        assert_eq!(fitted.payload, function_result_payload(&before).unwrap());
    }

    #[test]
    fn step_one_withholds_snapshots_largest_first_and_changes_no_outcome() {
        let mut rows = Vec::new();
        for (i, bytes) in [2_000usize, 9_000, 4_000, 9_000].into_iter().enumerate() {
            let mut r = row(&format!("overflow:add{i}"), Outcome::Proved);
            r.original_vc_snapshot = Some(snapshot(bytes));
            r.proof_evidence = Some(proof(TransportProofStatus::Proved, 500));
            r.grade = Some(grade());
            rows.push(r);
        }
        let mut result = envelope("m::f", rows);
        let before = result.clone();
        let budget = 30_000;
        let unbounded = JSON.line_bytes(&function_result_payload(&before).unwrap());
        assert!(unbounded > budget, "the fixture must not fit: {unbounded}");
        let (fitted, restated) = fit(&mut result, budget, JSON);
        assert!(fitted.line_bytes <= budget);
        assert_eq!(JSON.line_bytes(&fitted.payload), fitted.line_bytes);
        assert_eq!(restated, 0, "step 1 changes no outcome, so nothing is restated");
        let disclosure = result.transport_budget.clone().expect("disclosed");
        assert_eq!(disclosure.step, TransportBudgetStep::WithheldDiagnosticPayloads);
        assert_eq!(disclosure.unbounded_line_bytes, unbounded);
        assert_eq!(disclosure.minted_rows, 4);
        // The two 9 000-byte snapshots first, ties in row order; the small ones kept.
        assert_eq!(
            disclosure.withheld,
            vec![TransportWithheldEvidence {
                field: TransportWithheldField::OriginalVcSnapshot,
                rows: vec![1, 3]
            }]
        );
        assert!(disclosure.demoted_rows.is_empty());
        assert_eq!(disclosure.defect(&result.results), None);
        for (after, before) in result.results.iter().zip(&before.results) {
            assert_eq!(after.outcome, before.outcome);
            assert_eq!(after.proof_evidence, before.proof_evidence);
            assert_eq!(after.grade, before.grade);
        }
        assert!(result.results[0].original_vc_snapshot.is_some());
        assert!(result.results[1].original_vc_snapshot.is_none());
        assert_eq!(
            (result.proved, result.total, result.stable_ids.clone()),
            (before.proved, before.total, before.stable_ids.clone())
        );
        // The payload on the wire is the fitted result, disclosure included.
        let wire = crate::parse_transport_payload(&fitted.payload).unwrap();
        let TransportMessage::FunctionResult(wire) = wire else { panic!("not a function result") };
        assert_eq!(wire, result);
    }

    #[test]
    fn step_two_takes_unfavorable_rows_first_and_demotes_favorable_ones() {
        let mut unknown = row("overflow:sub", Outcome::Unknown);
        unknown.proof_evidence = Some(proof(TransportProofStatus::Unknown, 6_000));
        let mut proved = row("overflow:add", Outcome::Proved);
        proved.proof_evidence = Some(proof(TransportProofStatus::Proved, 12_000));
        proved.native_trust_ir = Some(native(3_000));
        proved.grade = Some(grade());
        proved.reason = Some("prior reason".into());
        let mut kept = row("divzero", Outcome::Proved);
        kept.proof_evidence = Some(proof(TransportProofStatus::Proved, 400));
        kept.grade = Some(grade());
        let mut result = envelope("m::f", vec![unknown, proved, kept]);
        let before = result.clone();
        let budget = 20_000;
        let (fitted, restated) = fit(&mut result, budget, JSON);
        assert!(fitted.line_bytes <= budget, "{}", fitted.line_bytes);
        let disclosure = result.transport_budget.clone().expect("disclosed");
        assert_eq!(disclosure.step, TransportBudgetStep::WithheldProofEvidence);
        assert_eq!(disclosure.defect(&result.results), None);
        assert_eq!(disclosure.demoted_rows, vec![1]);
        assert!(restated >= 1, "a demotion restates the counts");
        // Row 0 claimed nothing: its evidence went first and its outcome stays.
        assert_eq!(result.results[0].outcome, Outcome::Unknown);
        assert!(hollowed(&result.results[0]));
        // Its record survives: the status and suite a consumer keys on are still there.
        assert_eq!(
            result.results[0].proof_evidence.as_ref().map(|p| (p.status, p.suite.as_str())),
            Some((TransportProofStatus::Unknown, "trust-full-verifier"))
        );
        // Row 1 lost its evidence payloads and grade, and says why.
        let demoted = &result.results[1];
        assert_eq!(demoted.outcome, Outcome::Unknown);
        assert!(hollowed(demoted));
        assert_eq!(demoted.grade, None);
        let reason = demoted.reason.as_deref().unwrap();
        assert!(reason.starts_with(TRANSPORT_LINE_BUDGET_DEMOTION_PREFIX), "{reason}");
        assert!(reason.contains("`proved` is published as `unknown`"), "{reason}");
        assert!(reason.contains("prior reason"), "{reason}");
        // Row 2 was not needed: it keeps its proof, its evidence and its grade.
        assert_eq!(result.results[2], before.results[2]);
        // The counts follow the rows.
        assert_eq!((result.proved, result.unknown, result.total), (1, 2, 3));
        assert_eq!(result.stable_ids, before.stable_ids);
    }

    #[test]
    fn step_two_keeps_every_record_and_withholds_only_its_payloads() {
        // Readers key on a record's presence (targo's envelope-only shape, its policy-B
        // relabel), its status (verdict normalization), its suite and backend (the
        // unsafe-memory coverage report) and its diagnostics (the hardened model
        // assumption inventory). Step 2 must leave all of those as they were.
        let mut proved = row("overflow:add", Outcome::Proved);
        let mut evidence = proof(TransportProofStatus::Proved, 30_000);
        evidence.suite = "trust-unsafe-memory".into();
        evidence.diagnostics.push(crate::TransportEvidenceDiagnostic {
            code: "model_assumption".into(),
            severity: crate::TransportEvidenceDiagnosticSeverity::Warning,
            message: "a model assumption".into(),
            detail: None,
        });
        evidence.artifacts[0].digest = None;
        evidence.artifacts[0].uri = Some("trust://artifact".into());
        proved.proof_evidence = Some(evidence);
        proved.native_trust_ir = Some(native(10_000));
        let before = proved.clone();
        assert!(strip_row_for_step(
            &mut proved,
            TransportBudgetStep::WithheldProofEvidence,
            TRANSPORT_LINE_BUDGET_BYTES
        ));
        assert!(hollowed(&proved));
        for (after, before) in
            [(proved.proof_evidence.as_ref().unwrap(), before.proof_evidence.as_ref().unwrap())]
        {
            assert_eq!(after.status, before.status);
            assert_eq!(after.suite, before.suite);
            assert_eq!(after.backend, before.backend);
            assert_eq!(after.proof_id, before.proof_id);
            assert_eq!(after.diagnostics[..before.diagnostics.len()], before.diagnostics[..]);
            assert_eq!(after.diagnostics.len(), before.diagnostics.len() + 1);
            assert_eq!(after.artifacts.len(), before.artifacts.len());
            for (a, b) in after.artifacts.iter().zip(&before.artifacts) {
                assert_eq!(
                    (&a.kind, &a.format, &a.artifact_id, &a.digest, &a.uri),
                    (&b.kind, &b.format, &b.artifact_id, &b.digest, &b.uri)
                );
            }
        }
        let (after, before) =
            (proved.native_trust_ir.as_ref().unwrap(), before.native_trust_ir.as_ref().unwrap());
        assert_eq!(
            (after.present, &after.suite, &after.backend),
            (before.present, &before.suite, &before.backend)
        );
        assert_eq!(after.artifacts.len(), before.artifacts.len());
    }

    #[test]
    fn step_two_keeps_a_refutation_the_evidence_carried() {
        for outcome in [Outcome::Proved, Outcome::RuntimeChecked, Outcome::Timeout] {
            let mut refuted = row("overflow:add", outcome);
            refuted.proof_evidence = Some(proof(TransportProofStatus::Failed, 30_000));
            let mut result = envelope("m::f", vec![refuted]);
            let (fitted, _) = fit(&mut result, 20_000, TransportLineFraming::RawStderr);
            assert!(fitted.line_bytes <= 20_000);
            assert_eq!(result.results[0].outcome, Outcome::Failed, "{outcome:?}");
            assert_eq!(result.failed, 1);
            assert_eq!(result.transport_budget.as_ref().unwrap().defect(&result.results), None);
        }
    }

    #[test]
    fn step_two_never_touches_a_favorable_conditional_evidence_row() {
        for kind in [
            "assumption:memory-safe-panic",
            crate::assumption::COROUTINE_RESUME_CONTRACT_ROW_KIND,
            crate::assumption::GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_KIND,
        ] {
            let mut defective = row(kind, Outcome::Proved);
            defective.proof_evidence = Some(proof(TransportProofStatus::Proved, 30_000));
            assert!(is_conditional_evidence_row(&defective), "{kind}");
            let mut result = envelope("m::f", vec![defective.clone()]);
            fit(&mut result, 20_000, TransportLineFraming::RawStderr);
            // Too big without step 2 on it: the function falls back, failing closed;
            // the row is never relabelled `unknown` (which the gate would count as
            // conditional evidence).
            assert_eq!(
                result.transport_budget.as_ref().unwrap().step,
                TransportBudgetStep::ReportReplaced,
                "{kind}"
            );
            // The same row in its non-favorable form may lose its evidence as usual.
            let mut skipped = defective.clone();
            skipped.outcome = Outcome::Skipped;
            let mut result = envelope("m::f", vec![skipped]);
            fit(&mut result, 20_000, TransportLineFraming::RawStderr);
            assert_eq!(
                result.transport_budget.as_ref().unwrap().step,
                TransportBudgetStep::WithheldProofEvidence,
                "{kind}"
            );
            assert_eq!(result.results[0].outcome, Outcome::Skipped, "{kind}");
        }
    }

    #[test]
    fn neither_step_touches_an_envelope_shape_row() {
        // targo-trust elides these kinds when they match an exact shape that includes
        // "no claim field present"; a lookalike that carries a snapshot or evidence
        // must stay a lookalike (and fail closed), so the ladder strips nothing from
        // it, in either step, whatever its outcome.
        for kind in [ZERO_OBLIGATION_INVENTORY_ROW_KIND, crate::exclusion::TEST_HARNESS_ROW_KIND] {
            for outcome in ALL_OUTCOMES {
                let mut lookalike = row(kind, outcome);
                lookalike.original_vc_snapshot = Some(snapshot(30_000));
                lookalike.proof_evidence = Some(proof(TransportProofStatus::Proved, 30_000));
                assert!(is_envelope_shape_row(&lookalike), "{kind}");
                for step in [
                    TransportBudgetStep::WithheldDiagnosticPayloads,
                    TransportBudgetStep::WithheldProofEvidence,
                ] {
                    let mut stripped = lookalike.clone();
                    assert!(!strip_row_for_step(&mut stripped, step, TRANSPORT_LINE_BUDGET_BYTES));
                    assert_eq!(
                        serde_json::to_value(&stripped).unwrap(),
                        serde_json::to_value(&lookalike).unwrap(),
                        "{kind} {outcome:?} {step:?}"
                    );
                }
                let mut result = envelope("m::f", vec![lookalike.clone()]);
                fit(&mut result, 20_000, TransportLineFraming::RawStderr);
                assert_eq!(
                    result.transport_budget.as_ref().unwrap().step,
                    TransportBudgetStep::ReportReplaced,
                    "{kind} {outcome:?}: left whole, so the report falls back"
                );
                // Beside an ordinary row that can carry the cut, the lookalike rides
                // whole and only the ordinary row loses its payload.
                let mut ordinary = row("overflow:add", Outcome::Failed);
                ordinary.original_vc_snapshot = Some(snapshot(60_000));
                let mut small = lookalike.clone();
                small.original_vc_snapshot = Some(snapshot(200));
                small.proof_evidence = Some(proof(TransportProofStatus::Proved, 200));
                let mut result = envelope("m::f", vec![small.clone(), ordinary]);
                fit(&mut result, 20_000, TransportLineFraming::RawStderr);
                let disclosure = result.transport_budget.clone().unwrap();
                assert_eq!(disclosure.step, TransportBudgetStep::WithheldDiagnosticPayloads);
                assert_eq!(
                    serde_json::to_value(&result.results[0]).unwrap(),
                    serde_json::to_value(&small).unwrap(),
                    "{kind} {outcome:?}"
                );
                assert_eq!(disclosure.defect(&result.results), None);
            }
        }
        // Control: an ordinary row of the same outcome and payloads is stripped.
        let mut ordinary = row("overflow:add", Outcome::Failed);
        ordinary.original_vc_snapshot = Some(snapshot(30_000));
        assert!(strip_row_for_step(
            &mut ordinary,
            TransportBudgetStep::WithheldDiagnosticPayloads,
            TRANSPORT_LINE_BUDGET_BYTES
        ));
        assert!(ordinary.original_vc_snapshot.is_none());
    }

    #[test]
    fn a_disclosure_naming_an_envelope_shape_row_is_a_defect() {
        let mut ordinary = row("overflow:add", Outcome::Failed);
        ordinary.original_vc_snapshot = Some(snapshot(30_000));
        let mut result = envelope(
            "m::f",
            vec![ordinary, row(ZERO_OBLIGATION_INVENTORY_ROW_KIND, Outcome::Proved)],
        );
        fit(&mut result, 20_000, TransportLineFraming::RawStderr);
        let good = result.transport_budget.clone().unwrap();
        assert_eq!(good.defect(&result.results), None, "positive control");
        let mut forged = good.clone();
        forged.withheld[0].rows = vec![0, 1];
        assert!(
            forged.defect(&result.results).is_some_and(|d| d.contains("never strips")),
            "{:?}",
            forged.defect(&result.results)
        );
    }

    #[test]
    fn step_three_replaces_the_rows_with_one_fail_closed_row() {
        for (refuted, expected) in [(false, Outcome::Unknown), (true, Outcome::Failed)] {
            let mut rows: Vec<_> = (0..120)
                .map(|i| {
                    let mut r = row(&format!("overflow:add:{i:04}"), Outcome::Proved);
                    r.description = format!("obligation {i} {}", "d".repeat(200));
                    r
                })
                .collect();
            if refuted {
                rows[7].outcome = Outcome::Failed;
            }
            let mut result = envelope("m::big", rows);
            let before = result.clone();
            let (fitted, restated) = fit(&mut result, MIN_TRANSPORT_LINE_BUDGET_BYTES, JSON);
            assert!(fitted.line_bytes <= MIN_TRANSPORT_LINE_BUDGET_BYTES);
            assert!(restated >= 1);
            assert_eq!(result.results.len(), 1);
            let fallback = &result.results[0];
            assert_eq!(fallback.kind, TRANSPORT_LINE_BUDGET_ROW_KIND);
            assert_eq!(fallback.outcome, expected);
            assert!(
                fallback.description.contains("m::big")
                    && fallback.description.contains("120 rows")
            );
            let disclosure = result.transport_budget.clone().unwrap();
            assert_eq!(disclosure.step, TransportBudgetStep::ReportReplaced);
            assert_eq!(disclosure.minted_rows, 120);
            let replaced = disclosure.replaced.unwrap();
            assert_eq!(
                (replaced.total, replaced.proved, replaced.failed),
                (before.total, before.proved, before.failed)
            );
            assert_eq!(disclosure.defect(&result.results), None);
            assert_eq!(result.total, 1);
            assert_eq!(result.proved, 0, "no proof survives the fallback");
            assert_eq!(result.cached, 0);
        }
    }

    #[test]
    fn demotion_never_upgrades_over_every_outcome_and_evidence_status() {
        for outcome in ALL_OUTCOMES {
            for status in ALL_STATUSES.map(Some).into_iter().chain([None]) {
                let mut r = row("overflow:add", outcome);
                r.proof_evidence = status.map(|status| proof(status, 10));
                r.grade = Some(grade());
                let read_with = targo_reading(&r);
                // The real step-2 strip where the row has payloads to give; a row with
                // none is never selected, so its reading cannot change.
                let mut stripped = r.clone();
                let selected = strip_row_for_step(
                    &mut stripped,
                    TransportBudgetStep::WithheldProofEvidence,
                    TRANSPORT_LINE_BUDGET_BYTES,
                );
                assert_eq!(selected, status.is_some(), "{outcome:?} {status:?}");
                if !selected {
                    continue;
                }
                assert!(hollowed(&stripped));
                assert_eq!(stripped.grade, None);
                let read_without = targo_reading(&stripped);
                assert!(
                    rank(read_without) <= rank(read_with),
                    "{outcome:?} with {status:?}: read {read_with:?} with its evidence, \
                     {read_without:?} without"
                );
                assert!(!outcome_is_favorable(stripped.outcome), "{outcome:?} {status:?}");
                if read_with == Outcome::Failed {
                    assert_eq!(read_without, Outcome::Failed, "{outcome:?} {status:?}");
                }
                // The stricter reading, where a consumer ignores even the record: the
                // demoted label alone is never better either.
                let mut bare = stripped.clone();
                bare.proof_evidence = None;
                assert!(rank(targo_reading(&bare)) <= rank(read_with), "{outcome:?} {status:?}");
            }
        }
    }

    #[test]
    fn a_disclosure_that_disagrees_with_its_rows_is_a_defect() {
        let mut proved = row("overflow:add", Outcome::Proved);
        proved.proof_evidence = Some(proof(TransportProofStatus::Proved, 30_000));
        proved.original_vc_snapshot = Some(snapshot(10_000));
        let mut result = envelope("m::f", vec![proved, row("divzero", Outcome::Proved)]);
        fit(&mut result, 20_000, TransportLineFraming::RawStderr);
        let good = result.transport_budget.clone().unwrap();
        assert_eq!(good.defect(&result.results), None, "positive control");

        let defective =
            |edit: &dyn Fn(&mut TransportBudgetDisclosure, &mut Vec<TransportObligationResult>)| {
                let mut disclosure = good.clone();
                let mut rows = result.results.clone();
                edit(&mut disclosure, &mut rows);
                disclosure.defect(&rows)
            };
        // A row that lost its evidence but kept its favorable label.
        assert!(defective(&|_, rows| rows[0].outcome = Outcome::Proved).is_some());
        // ... or its grade.
        assert!(defective(&|_, rows| rows[0].grade = Some(grade())).is_some());
        // A row index past the rows, or listed twice.
        assert!(defective(&|d, _| d.withheld[0].rows.push(9)).is_some());
        assert!(defective(&|d, _| d.demoted_rows.push(0)).is_some());
        // A demotion of a row whose evidence was kept.
        assert!(defective(&|d, _| d.demoted_rows = vec![1]).is_some());
        // A withheld field that is still on the row.
        assert!(defective(&|_, rows| rows[0].original_vc_snapshot = Some(snapshot(10))).is_some());
        // The wrong step, a budget out of range, a report that fit, a row count off.
        assert!(
            defective(&|d, _| d.step = TransportBudgetStep::WithheldDiagnosticPayloads).is_some()
        );
        assert!(defective(&|d, _| d.line_budget_bytes = TRANSPORT_LINE_BUDGET_BYTES + 1).is_some());
        assert!(defective(&|d, _| d.line_budget_bytes = 1).is_some());
        assert!(defective(&|d, _| d.unbounded_line_bytes = d.line_budget_bytes).is_some());
        assert!(defective(&|d, _| d.minted_rows = 3).is_some());
        // Replaced counts on a report that was not replaced.
        assert!(defective(&|d, _| d.replaced = Some(TransportReplacedRows::default())).is_some());
        // A "replacement" whose rows are not the one fail-closed row.
        assert!(
            defective(&|d, _| {
                d.step = TransportBudgetStep::ReportReplaced;
                d.withheld.clear();
                d.demoted_rows.clear();
                d.replaced = Some(TransportReplacedRows { total: 2, ..Default::default() });
            })
            .is_some()
        );
    }

    #[test]
    fn a_replacement_that_hides_a_refutation_is_a_defect() {
        let mut rows: Vec<_> = (0..120)
            .map(|i| {
                let mut r = row(&format!("k{i}"), Outcome::Proved);
                r.description = "d".repeat(300);
                r
            })
            .collect();
        rows[3].outcome = Outcome::Failed;
        let mut result = envelope("m::f", rows);
        fit(&mut result, MIN_TRANSPORT_LINE_BUDGET_BYTES, TransportLineFraming::RawStderr);
        let good = result.transport_budget.clone().unwrap();
        assert_eq!(good.defect(&result.results), None, "positive control");
        let mut rows = result.results.clone();
        rows[0].outcome = Outcome::Unknown;
        assert!(good.defect(&rows).is_some());
    }

    #[test]
    fn fitting_is_deterministic() {
        let build = || {
            let rows = (0..6)
                .map(|i| {
                    let mut r = row(&format!("k{i}"), Outcome::Proved);
                    r.original_vc_snapshot = Some(snapshot(5_000));
                    r.proof_evidence = Some(proof(TransportProofStatus::Proved, 5_000));
                    r
                })
                .collect();
            envelope("m::f", rows)
        };
        let (mut a, mut b) = (build(), build());
        let (fa, _) = fit(&mut a, 30_000, JSON);
        let (fb, _) = fit(&mut b, 30_000, JSON);
        assert_eq!(fa, fb);
        assert_eq!(a, b);
    }
}
