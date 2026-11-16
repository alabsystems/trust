// targo-trust/saved_report.rs: the canonical saved proof report loader.
//
// `report.json` is the one saved report format, and this is its one reader
// (`targo trust report --query`, the report bundle tests). A serialized report
// is OBSERVATION, never authority: the decoder downgrades every serialized
// favorable claim and returns the receipt of that pass. No older format — the
// pre-canonical `{ results: [...] }` SavedReport — is read; such a file is
// refused, never converted (T9; the saved-report diff it served is replaced by
// the committed obligation baseline, `crate::baseline`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;

use trust_types::{JsonProofReport, SavedReportSanitization};

use crate::input_limits::{MAX_SAVED_PROOF_REPORT_BYTES, read_bounded_file};

/// A fail-closed saved report together with the receipt from its first and only
/// sanitization pass.
///
/// Observational consumers may inspect `report`, including the `Unknown` rows
/// produced by sanitization. Authority-consuming callers must inspect
/// `sanitization` and either replay the live operation or reject serialized
/// favorable claims; verifier and compiler/monitor authority is deliberately
/// not serializable.
#[derive(Debug)]
pub(crate) struct LoadedReport {
    pub(crate) report: JsonProofReport,
    pub(crate) sanitization: SavedReportSanitization,
}

impl LoadedReport {
    pub(crate) fn reject_unreplayed_proved_claims(&self, path: &Path) -> Result<(), String> {
        if self.sanitization.has_evidence_defects() {
            let path = crate::solver_detect::terminal_safe(&path.display().to_string());
            return Err(format!(
                "saved report authority gate failed for `{path}`: {} serialized proved obligation(s) lacked live verifier replay authority",
                self.sanitization.evidence_defects
            ));
        }
        Ok(())
    }
}

/// Load a saved canonical `JsonProofReport`. No older format is read: a
/// file that is not the canonical report is refused with the decoder's reason.
///
/// This is an observational boundary: serialized proof claims are downgraded,
/// not treated as a parse error. The returned sanitization receipt lets each
/// caller choose whether observing the fail-closed report is sufficient or a
/// live verifier replay is required.
pub(crate) fn load_report(path: &Path) -> Result<LoadedReport, String> {
    let canonical_path = path
        .canonicalize()
        .map_err(|e| format!("failed to canonicalize `{}`: {e}", path.display()))?;
    let report_root = canonical_path.parent().ok_or_else(|| {
        format!("saved report `{}` has no canonical parent directory", path.display())
    })?;
    let content = read_bounded_file(&canonical_path, MAX_SAVED_PROOF_REPORT_BYTES)
        .map_err(|e| format!("failed to read `{}`: {e}", path.display()))?;

    // The explicit decoder returns the receipt from the first and only
    // sanitization pass; re-sanitizing an already downgraded report would erase
    // whether the input attempted to assert `Proved`. Its error is kept: a
    // canonical report it refuses (a budget profile of a schema this toolchain
    // does not read, say) must say why.
    let (report, sanitization, _untrusted_claims) =
        JsonProofReport::decode_saved_json(&content, Some(report_root)).map_err(|error| {
            format!(
                "failed to parse `{}` as a canonical JsonProofReport ({error}); no older saved \
                 report format is read",
                path.display()
            )
        })?;
    Ok(LoadedReport { report, sanitization })
}

#[cfg(test)]
#[path = "saved_report_tests.rs"]
mod tests;
