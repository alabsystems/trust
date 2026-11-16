//! Direct-formula PRODUCTION DUMP schema, writer and fail-closed parser
//! (Step 6, increment 2, item 1 — docs/design/DIRECT-LANE-PROOF-AUTHORITY.md).
//!
//! Closes the model-vs-real gap of increment 1: the installer
//! (`trust_thir_lower::direct_obligations::install_direct_obligations`) can be
//! asked — strictly opt-in, via the `TRUST_DIRECT_FORMULA_DUMP=<dir>`
//! environment variable — to write the REAL per-record
//! `DirectFormulaOutcome` disclosures beside the obligation rows it installs,
//! one JSONL file per crate, and `direct_record_grading::grade_real_records`
//! feeds those records to the SAME parity graders the in-situ model oracle
//! uses. The dump is DISCLOSURE, not authority: its absence changes nothing,
//! its presence changes no module byte, and an IO failure never fails
//! semantic finalization — fail-closed lives at the READER (the v6/D1
//! `spec_cli` precedent), which refuses an unknown version, a missing, short
//! or skewed seal, trailing rows, and any withheld reason outside the ONE
//! enumerated vocabulary below.
//!
//! SCHEMA (one JSON object per line; every line carries the version):
//!
//! ```text
//! record  {"v":"trust-thir-lower/direct-formula-dump@1","crate":..,"def_path":..,
//!          "def_index":N,"slug":..,"line":N,"col":N,"occ":N,"assertion_id":..,
//!          "block":N,"inst_index":N,
//!          "outcome":{"minted":{"formula":<RAW>,"smtlib":".."}}
//!                  | {"outcome":{"withheld":{"reason":".."}}}
//!                  | {"outcome":{"not_minted":true}}}
//! seal    {"v":..,"row":"seal","crate":..,"records":N}
//! ```
//!
//! THE MINTED-ONCE RULE, MECHANIZED: `outcome.minted.formula` is the
//! `MintedDirectFormula.formula_json` bytes embedded VERBATIM through
//! [`serde_json::value::RawValue`] — never `serde_json::to_string(&formula)`
//! at dump time, never a re-render at grade time. `occ` and `assertion_id`
//! are dumped AS COMPUTED at install, from the same mint the obligation row
//! shares. The writer goes through an `O_EXCL` temp file in the target
//! directory plus an atomic rename, so a concurrent double-build (lib+test
//! units sharing one crate name) yields ONE complete sealed file — never
//! interleaved bytes (last-writer-wins, disclosed here).
//!
//! WHY THIS LIVES IN trust-ir-bridge: `trust-thir-lower` already depends on
//! this crate (the Step-6 mint), so writer and grader share ONE schema and
//! ONE withheld-reason vocabulary — drift between producer and reader is
//! structurally impossible.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::Write as _;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use serde_json::value::RawValue;

/// Version stamped on EVERY line (the `trust_spec_emit` reader discipline: a
/// consumer keys on this before believing any other field).
pub const DIRECT_FORMULA_DUMP_VERSION: &str = "trust-thir-lower/direct-formula-dump@1";

/// The environment variable the installer reads — FRESH per call via
/// `std::env::var_os`, deliberately no `OnceLock` (the per-test-env
/// constraint), so unset costs one env read and nothing else.
pub const TRUST_DIRECT_FORMULA_DUMP_ENV: &str = "TRUST_DIRECT_FORMULA_DUMP";

/// THE enumerated withheld-reason vocabulary — the single shared const the
/// parser refuses outside of, which is what makes the new-class accounting
/// fail closed by construction: a producer minting a reason this slice does
/// not carry produces a dump the reader rejects, never a silently-new bucket.
///
/// Sources, kept in ONE place by design:
/// * `safety_formulas::FormulaDecline::code()` — the mint's own vocabulary;
/// * the capture's codes (`trust-thir-lower/src/direct_formula_capture.rs`);
/// * the increment-2 widening codes
///   (`trust-thir-lower/src/direct_operand_widening.rs` + the model mirror in
///   `safety_formulas::parity_oracle::convert_operand`).
pub const ENUMERATED_WITHHELD_REASONS: &[&str] = &[
    // FormulaDecline::code() vocabulary.
    "non-concrete-width",
    "unsupported-char-width",
    "opaque-operand",
    "mir-core-is-temp-cond-var",
    "fallback-shaped-var-would-guess-mir-index",
    "outside-builder-envelope",
    "wrong-operand-count",
    "render-failed",
    "synthetic-name-collision",
    // Capture-side wiring code (a site B binop outside Add/Sub/Mul).
    "unsupported-binop-shape",
    // Increment-2 named-value-resolution declines (both lanes).
    "unnamed-temp-operand",
    "ambiguous-operand-name",
    "shadowed-operand-name",
    // Increment-3 depth-2 (checked-trio) widening: the shared mint's nested
    // width guard. Unreachable from well-typed Rust (the only width-changing
    // step is a cast, outside the honest scope) — enumerated so a carrier
    // desync fails closed as a named decline, never a parser rejection.
    "nested-operand-width-mismatch",
];

/// One dumped record row. Field order is the serialized order.
#[derive(Debug, Serialize, Deserialize)]
pub struct DumpedDirectRecord {
    /// Always [`DIRECT_FORMULA_DUMP_VERSION`] on a well-formed line.
    pub v: String,
    #[serde(rename = "crate")]
    pub krate: String,
    /// `tcx.def_path_str` rendering (crate name NOT included — `krate` above
    /// carries it), exactly the spelling `DirectBodyObligations.def_path`
    /// holds; `{krate}::{def_path}` is the grader's pairing scope.
    pub def_path: String,
    pub def_index: u32,
    pub slug: String,
    /// Identity LO line/col — the node's own `#loc`, `L0C0` when absent,
    /// exactly as the installed row's identity renders them.
    pub line: u32,
    pub col: u32,
    /// The per-function occurrence ordinal AS COMPUTED at install; the grader
    /// uses it VERBATIM, never re-derives it.
    pub occ: u32,
    /// The minted identity, shared byte-for-byte with the obligation row.
    pub assertion_id: String,
    /// Positional (non-identity) context, for the human reading the dump.
    pub block: u32,
    pub inst_index: u32,
    pub outcome: DumpedOutcome,
}

/// The session-state `DirectFormulaOutcome`, serialized.
#[derive(Debug, Serialize, Deserialize)]
pub enum DumpedOutcome {
    /// `formula` is the once-rendered `formula_json` VERBATIM (RawValue —
    /// the bytes cross serialization untouched); `smtlib` the once-rendered
    /// SMT-LIB string.
    #[serde(rename = "minted")]
    Minted { formula: Box<RawValue>, smtlib: String },
    #[serde(rename = "withheld")]
    Withheld { reason: String },
    #[serde(rename = "not_minted")]
    NotMinted(bool),
}

impl DumpedOutcome {
    /// Build the minted arm from the ONCE-RENDERED derivatives, verbatim.
    /// This is the only constructor the producer hook uses — there is no
    /// path here that re-renders a `Formula` (kill-mutation W1's target).
    /// A `formula_json` that is not valid JSON cannot ride a `RawValue`;
    /// that is unreachable for a real mint (the bytes came from
    /// `serde_json::to_string`) and degrades, loudly, to the enumerated
    /// `render-failed` withhold rather than failing the caller.
    pub fn minted_verbatim(formula_json: &str, smtlib: &str) -> Self {
        match RawValue::from_string(formula_json.to_string()) {
            Ok(raw) => Self::Minted { formula: raw, smtlib: smtlib.to_string() },
            Err(err) => {
                eprintln!(
                    "warning: direct-formula dump: minted formula_json is not valid JSON \
                     ({err}); recording the row as withheld `render-failed` (diagnostic \
                     disclosure only)"
                );
                Self::Withheld { reason: "render-failed".to_string() }
            }
        }
    }
}

/// Seal row: written after the records, carrying their count. A file without
/// it (or with a skewed count) is TORN and the parser refuses it whole.
#[derive(Debug, Serialize, Deserialize)]
struct SealRow {
    v: String,
    row: String,
    #[serde(rename = "crate")]
    krate: String,
    records: usize,
}

/// Minimal per-line probe: version + optional row discriminator. Parsed
/// first so dispatch never guesses a line's kind.
#[derive(Debug, Deserialize)]
struct LineProbe {
    v: String,
    #[serde(default)]
    row: Option<String>,
}

/// Render the complete JSONL content (records then seal). Split from the
/// file write so byte-level pins and the parser tests need no filesystem.
///
/// Errors only when serde_json cannot render a row (theoretical — every
/// field is a plain scalar/string/RawValue).
pub fn render_direct_formula_dump(
    crate_name: &str,
    rows: &[DumpedDirectRecord],
) -> Result<String, String> {
    let mut out = String::new();
    for row in rows {
        let line = serde_json::to_string(row)
            .map_err(|err| format!("direct-formula dump: row failed to render: {err}"))?;
        out.push_str(&line);
        out.push('\n');
    }
    let seal = SealRow {
        v: DIRECT_FORMULA_DUMP_VERSION.to_string(),
        row: "seal".to_string(),
        krate: crate_name.to_string(),
        records: rows.len(),
    };
    let line = serde_json::to_string(&seal)
        .map_err(|err| format!("direct-formula dump: seal failed to render: {err}"))?;
    out.push_str(&line);
    out.push('\n');
    Ok(out)
}

/// Write `<dir>/<crate_name>.direct-formulas.jsonl` atomically: content goes
/// to an `O_EXCL` temp path in `<dir>` first, then one `rename` publishes it.
/// A reader never observes a torn file from THIS writer; concurrent writers
/// (lib+test units of one crate) are last-writer-wins with each writer
/// publishing a complete sealed file.
pub fn write_direct_formula_dump(
    dir: &Path,
    crate_name: &str,
    rows: &[DumpedDirectRecord],
) -> std::io::Result<PathBuf> {
    let content = render_direct_formula_dump(crate_name, rows)
        .map_err(|err| std::io::Error::new(std::io::ErrorKind::InvalidData, err))?;
    let final_path = dir.join(format!("{crate_name}.direct-formulas.jsonl"));
    let mut attempt = 0u32;
    let (temp_path, mut file) = loop {
        let candidate = dir.join(format!(
            ".{crate_name}.direct-formulas.jsonl.tmp.{}.{attempt}",
            std::process::id()
        ));
        match std::fs::OpenOptions::new().write(true).create_new(true).open(&candidate) {
            Ok(file) => break (candidate, file),
            Err(err) if err.kind() == std::io::ErrorKind::AlreadyExists && attempt < 1024 => {
                attempt += 1;
            }
            Err(err) => return Err(err),
        }
    };
    let write_result = file.write_all(content.as_bytes()).and_then(|()| file.flush());
    drop(file);
    if let Err(err) = write_result {
        let _ = std::fs::remove_file(&temp_path);
        return Err(err);
    }
    if let Err(err) = std::fs::rename(&temp_path, &final_path) {
        let _ = std::fs::remove_file(&temp_path);
        return Err(err);
    }
    Ok(final_path)
}

/// Parse a dump file's content, FAIL-CLOSED (the reader is the gate, v6/D1):
/// refuses an unknown version on any line, a missing seal, a seal whose count
/// disagrees with the records present, trailing rows after the seal, a seal
/// crate that disagrees with any record's, an unparseable or blank line, and
/// any withheld reason outside [`ENUMERATED_WITHHELD_REASONS`].
///
/// On success returns the records only (the seal is consumed by the check).
pub fn parse_direct_formula_dump(text: &str) -> Result<Vec<DumpedDirectRecord>, Vec<String>> {
    let mut errors: Vec<String> = Vec::new();
    let mut records: Vec<DumpedDirectRecord> = Vec::new();
    let mut seal: Option<SealRow> = None;

    for (index, line) in text.lines().enumerate() {
        let lineno = index + 1;
        if line.trim().is_empty() {
            errors.push(format!("line {lineno}: blank line inside a sealed dump"));
            continue;
        }
        let probe: LineProbe = match serde_json::from_str(line) {
            Ok(probe) => probe,
            Err(err) => {
                errors.push(format!("line {lineno}: unparseable: {err}"));
                continue;
            }
        };
        if probe.v != DIRECT_FORMULA_DUMP_VERSION {
            errors.push(format!(
                "line {lineno}: unknown version {:?} (this reader understands only \
                 {DIRECT_FORMULA_DUMP_VERSION:?}; do not guess at a foreign schema)",
                probe.v
            ));
            continue;
        }
        if seal.is_some() {
            errors.push(format!(
                "line {lineno}: row after the seal — the file is torn or was appended to; \
                 refuse it whole"
            ));
            continue;
        }
        match probe.row.as_deref() {
            Some("seal") => match serde_json::from_str::<SealRow>(line) {
                Ok(row) => seal = Some(row),
                Err(err) => errors.push(format!("line {lineno}: malformed seal: {err}")),
            },
            Some(other) => {
                errors.push(format!("line {lineno}: unknown row kind {other:?}"));
            }
            None => match serde_json::from_str::<DumpedDirectRecord>(line) {
                Ok(record) => {
                    if let DumpedOutcome::Withheld { reason } = &record.outcome {
                        if !ENUMERATED_WITHHELD_REASONS.contains(&reason.as_str()) {
                            errors.push(format!(
                                "line {lineno}: withheld reason {reason:?} is outside the \
                                 enumerated vocabulary; a new decline class must be added to \
                                 ENUMERATED_WITHHELD_REASONS in the same reviewed change that \
                                 introduces it (fail closed, never a silent new bucket)"
                            ));
                            continue;
                        }
                    }
                    records.push(record);
                }
                Err(err) => errors.push(format!("line {lineno}: malformed record: {err}")),
            },
        }
    }

    match &seal {
        None => errors.push(
            "missing seal row: the dump was torn before completion (or is empty); \
             re-run the compilation that produces it"
                .to_string(),
        ),
        Some(seal_row) => {
            if seal_row.records != records.len() {
                errors.push(format!(
                    "seal records count {} disagrees with the {} record row(s) present — \
                     torn or tampered file, refused whole",
                    seal_row.records,
                    records.len()
                ));
            }
            for record in &records {
                if record.krate != seal_row.krate {
                    errors.push(format!(
                        "record crate {:?} disagrees with seal crate {:?}",
                        record.krate, seal_row.krate
                    ));
                }
            }
        }
    }

    if errors.is_empty() { Ok(records) } else { Err(errors) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(slug: &str, occ: u32, outcome: DumpedOutcome) -> DumpedDirectRecord {
        DumpedDirectRecord {
            v: DIRECT_FORMULA_DUMP_VERSION.to_string(),
            krate: "fixture".to_string(),
            def_path: "arith::checked".to_string(),
            def_index: 7,
            slug: slug.to_string(),
            line: 15,
            col: 4,
            occ,
            assertion_id: format!("fixture::arith::checked#L15C4#{slug}#o{occ}"),
            block: 0,
            inst_index: 2 + occ,
            outcome,
        }
    }

    /// Round-trip preserves the RAW formula bytes untouched — including
    /// deliberately non-canonical whitespace a re-render would normalize
    /// away. This is the byte channel the whole grader rides on.
    #[test]
    fn round_trip_preserves_raw_formula_bytes_verbatim() {
        let noncanonical = r#"{"Var": ["x" , "Int"]}"#;
        let rows = vec![
            record(
                "overflow",
                0,
                DumpedOutcome::minted_verbatim(noncanonical, "(declare-const x Int)"),
            ),
            record("overflow", 1, DumpedOutcome::Withheld { reason: "opaque-operand".into() }),
            record("div_by_zero", 0, DumpedOutcome::NotMinted(true)),
        ];
        let text = render_direct_formula_dump("fixture", &rows).expect("render");
        assert_eq!(text.lines().count(), 4, "3 records + 1 seal");
        let parsed = parse_direct_formula_dump(&text).expect("parse");
        assert_eq!(parsed.len(), 3);
        let DumpedOutcome::Minted { formula, smtlib } = &parsed[0].outcome else {
            panic!("first row must be minted");
        };
        assert_eq!(formula.get(), noncanonical, "raw bytes must survive untouched");
        assert_eq!(smtlib, "(declare-const x Int)");
        assert_eq!(parsed[0].assertion_id, "fixture::arith::checked#L15C4#overflow#o0");
    }

    /// The four seal/version refusals, each named.
    #[test]
    fn parser_refuses_torn_or_foreign_files() {
        let rows = vec![record(
            "overflow",
            0,
            DumpedOutcome::Withheld { reason: "opaque-operand".into() },
        )];
        let good = render_direct_formula_dump("fixture", &rows).expect("render");

        // Missing seal.
        let torn: String = good.lines().next().map(|l| format!("{l}\n")).unwrap();
        let errs = parse_direct_formula_dump(&torn).expect_err("missing seal must refuse");
        assert!(errs.iter().any(|e| e.contains("missing seal")), "{errs:?}");

        // Skewed seal count.
        let skewed = good.replace("\"records\":1", "\"records\":2");
        let errs = parse_direct_formula_dump(&skewed).expect_err("skewed seal must refuse");
        assert!(errs.iter().any(|e| e.contains("disagrees with the 1 record")), "{errs:?}");

        // Trailing row after the seal.
        let trailing = format!("{good}{}", good.lines().next().unwrap());
        let errs = parse_direct_formula_dump(&trailing).expect_err("trailing row must refuse");
        assert!(errs.iter().any(|e| e.contains("row after the seal")), "{errs:?}");

        // Unknown version.
        let foreign = good.replace("direct-formula-dump@1", "direct-formula-dump@9");
        let errs = parse_direct_formula_dump(&foreign).expect_err("unknown version must refuse");
        assert!(errs.iter().any(|e| e.contains("unknown version")), "{errs:?}");

        // Empty file = missing seal.
        assert!(parse_direct_formula_dump("").is_err());
    }

    /// A withheld reason outside the enumerated vocabulary is refused — the
    /// fail-closed half of the new-class accounting.
    #[test]
    fn parser_refuses_a_reason_outside_the_enumerated_vocabulary() {
        let rows = vec![record(
            "overflow",
            0,
            DumpedOutcome::Withheld { reason: "novel-decline-nobody-reviewed".into() },
        )];
        let text = render_direct_formula_dump("fixture", &rows).expect("render");
        let errs = parse_direct_formula_dump(&text).expect_err("unknown reason must refuse");
        assert!(
            errs.iter().any(|e| e.contains("novel-decline-nobody-reviewed")
                && e.contains("enumerated vocabulary")),
            "{errs:?}"
        );
    }

    /// Every reason either lane can mint is in the enumerated slice — the
    /// producer-side half of the accounting (FormulaDecline's codes are
    /// checked one by one so a new variant cannot land without extending the
    /// vocabulary in the same change).
    #[test]
    fn enumerated_vocabulary_covers_every_formula_decline_code() {
        use crate::safety_formulas::FormulaDecline;
        let declines = [
            FormulaDecline::NonConcreteWidth,
            FormulaDecline::UnsupportedCharWidth,
            FormulaDecline::OpaqueOperand,
            FormulaDecline::MirCoreIsTempCondVar,
            FormulaDecline::FallbackShapedVarWouldGuessMirIndex,
            FormulaDecline::OutsideBuilderEnvelope { builder: "x" },
            FormulaDecline::WrongOperandCount { expected: 1, got: 2 },
            FormulaDecline::RenderFailed,
            FormulaDecline::SyntheticNameCollision,
            FormulaDecline::NestedOperandWidthMismatch { outer: (32, false), inner: (64, false) },
        ];
        for decline in declines {
            assert!(
                ENUMERATED_WITHHELD_REASONS.contains(&decline.code()),
                "{} missing from ENUMERATED_WITHHELD_REASONS",
                decline.code()
            );
        }
    }

    /// Seal-crate/record-crate disagreement is a refusal (belt for a file
    /// assembled from two crates' rows).
    #[test]
    fn parser_refuses_a_seal_crate_mismatch() {
        let rows = vec![record("overflow", 0, DumpedOutcome::NotMinted(true))];
        let text = render_direct_formula_dump("other_crate", &rows).expect("render");
        let errs = parse_direct_formula_dump(&text).expect_err("crate mismatch must refuse");
        assert!(errs.iter().any(|e| e.contains("disagrees with seal crate")), "{errs:?}");
    }
}
