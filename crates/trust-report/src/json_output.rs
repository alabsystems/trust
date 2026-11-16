//! JSON file and streaming output for proof reports.
//!
//! Writes `JsonProofReport` to JSON files and NDJSON streams.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::Write;
use std::path::Path;

use serde::Serialize;
use sha2::{Digest, Sha256};
use trust_types::*;

const NDJSON_SCHEMA: &str = "trust.report.ndjson.v2";

#[derive(Serialize)]
struct BorrowedNdjsonHeader<'a> {
    record_type: &'static str,
    schema: &'static str,
    authority: &'static str,
    metadata: &'a ReportMetadata,
    crate_name: &'a str,
    expected_functions: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    hardened: &'a Option<HardenedReportContext>,
    #[serde(skip_serializing_if = "<[AssumptionEntry]>::is_empty")]
    assumptions: &'a [AssumptionEntry],
    #[serde(skip_serializing_if = "Option::is_none")]
    verification_gate: &'a Option<VerificationGateReport>,
    #[serde(skip_serializing_if = "Option::is_none")]
    cargo_proof_inventory: &'a Option<CargoProofInventoryReport>,
}

#[derive(Serialize)]
struct BorrowedNdjsonFunctionRecord<'a> {
    record_type: &'static str,
    crate_name: &'a str,
    #[serde(flatten)]
    function: &'a FunctionProofReport,
}

#[derive(Serialize)]
struct BorrowedNdjsonFooter<'a> {
    record_type: &'static str,
    schema: &'static str,
    summary: &'a CrateSummary,
    functions_emitted: usize,
    function_records_sha256: String,
    canonical_report_sha256: String,
}

struct DigestWriter<'a>(&'a mut Sha256);

impl Write for DigestWriter<'_> {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.0.update(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn sha256_hex(digest: impl AsRef<[u8]>) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let bytes = digest.as_ref();
    let mut value = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        value.push(HEX[(byte >> 4) as usize] as char);
        value.push(HEX[(byte & 0x0f) as usize] as char);
    }
    value
}

/// Write an observational JSON proof-report projection to the output directory.
///
/// Creates `report.json` (pretty-printed) in the given directory. Serialized
/// bytes explicitly carry [`SERIALIZED_REPORT_AUTHORITY`] and never transfer a
/// verifier's live proof capability.
pub fn write_json_report(report: &JsonProofReport, output_dir: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(output_dir)?;
    let file = std::fs::File::create(output_dir.join("report.json"))?;
    let mut writer = std::io::BufWriter::new(file);
    serde_json::to_writer_pretty(&mut writer, report)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    writer.flush()
}

/// Write the proof report as newline-delimited JSON (NDJSON) to a writer.
///
/// NDJSON format for streaming large crate results:
/// - Line 1: versioned header record with metadata, policy, assumptions, and
///   the exact final verification gate
/// - Lines 2..N: one record per function
/// - Last line: footer record with crate summary and digests binding both the
///   ordered function records and the canonical JSON report
///
/// Each line is a self-contained JSON object. Consumers can process
/// function results incrementally without loading the entire report.
pub fn write_ndjson<W: Write>(report: &JsonProofReport, writer: &mut W) -> std::io::Result<()> {
    // Header
    let header = BorrowedNdjsonHeader {
        record_type: "header",
        schema: NDJSON_SCHEMA,
        authority: SERIALIZED_REPORT_AUTHORITY,
        metadata: &report.metadata,
        crate_name: &report.crate_name,
        expected_functions: report.functions.len(),
        hardened: &report.hardened,
        assumptions: &report.assumptions,
        verification_gate: &report.verification_gate,
        cargo_proof_inventory: &report.cargo_proof_inventory,
    };
    serde_json::to_writer(&mut *writer, &header)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    writer.write_all(b"\n")?;

    // Per-function records
    let mut function_records_digest = Sha256::new();
    function_records_digest.update(b"trust.report.ndjson.function-records.v2");
    function_records_digest.update((report.functions.len() as u64).to_be_bytes());
    let mut record_bytes = Vec::new();
    for func in &report.functions {
        record_bytes.clear();
        let record = BorrowedNdjsonFunctionRecord {
            record_type: "function",
            crate_name: &report.crate_name,
            function: func,
        };
        serde_json::to_writer(&mut record_bytes, &record)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        function_records_digest.update((record_bytes.len() as u64).to_be_bytes());
        function_records_digest.update(&record_bytes);
        writer.write_all(&record_bytes)?;
        writer.write_all(b"\n")?;
    }

    // Footer
    let mut canonical_report_digest = Sha256::new();
    canonical_report_digest.update(b"trust.report.ndjson.canonical-report.v2");
    serde_json::to_writer(DigestWriter(&mut canonical_report_digest), report)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    let footer = BorrowedNdjsonFooter {
        record_type: "footer",
        schema: NDJSON_SCHEMA,
        summary: &report.summary,
        functions_emitted: report.functions.len(),
        function_records_sha256: format!(
            "sha256:{}",
            sha256_hex(function_records_digest.finalize())
        ),
        canonical_report_sha256: format!(
            "sha256:{}",
            sha256_hex(canonical_report_digest.finalize())
        ),
    };
    serde_json::to_writer(&mut *writer, &footer)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    writer.write_all(b"\n")?;

    Ok(())
}

/// Write the proof report as NDJSON to a file.
pub fn write_ndjson_report(report: &JsonProofReport, output_dir: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(output_dir)?;
    let file = std::fs::File::create(output_dir.join("report.ndjson"))?;
    let mut writer = std::io::BufWriter::new(file);
    write_ndjson(report, &mut writer)?;
    writer.flush()?;
    Ok(())
}
