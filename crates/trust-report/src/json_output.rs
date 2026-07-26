//! JSON file and streaming output for proof reports.
//!
//! Writes `JsonProofReport` to JSON files and NDJSON streams.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::Write;
use std::path::Path;

use sha2::{Digest, Sha256};
use trust_types::*;

const NDJSON_SCHEMA: &str = "trust.report.ndjson.v2";

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
    let bytes = digest.as_ref();
    let mut value = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(&mut value, "{byte:02x}").expect("writing to String cannot fail");
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
    let header = NdjsonHeader {
        record_type: "header".to_string(),
        schema: NDJSON_SCHEMA.to_string(),
        authority: SERIALIZED_REPORT_AUTHORITY.to_string(),
        metadata: report.metadata.clone(),
        crate_name: report.crate_name.clone(),
        expected_functions: report.functions.len(),
        hardened: report.hardened.clone(),
        assumptions: report.assumptions.clone(),
        verification_gate: report.verification_gate.clone(),
        cargo_proof_inventory: report.cargo_proof_inventory.clone(),
    };
    serde_json::to_writer(&mut *writer, &header)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    writer.write_all(b"\n")?;

    // Per-function records
    let mut function_records_digest = Sha256::new();
    function_records_digest.update(b"trust.report.ndjson.function-records.v2");
    function_records_digest.update((report.functions.len() as u64).to_be_bytes());
    for func in &report.functions {
        let record = NdjsonFunctionRecord {
            record_type: "function".to_string(),
            crate_name: report.crate_name.clone(),
            function: func.clone(),
        };
        let record_bytes = serde_json::to_vec(&record)
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
    let footer = NdjsonFooter {
        record_type: "footer".to_string(),
        schema: NDJSON_SCHEMA.to_string(),
        summary: report.summary.clone(),
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
