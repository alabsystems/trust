// Evidence emission: trust.js262.adopted-execution-report.v1 — the scorecard
// embedded verbatim plus ledger identities and a computed (never hard-coded)
// gate claim. Strict-exit behavior is always on: any validation finding =>
// exit 1.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::path::Path;

use crate::model::{
    EvidenceClaims, EvidenceKernelReceipt, EvidenceLedgers, EvidenceReport, EvidenceValidation,
    EVIDENCE_SCHEMA, SCORECARD_SCHEMA,
};
use crate::util::{git_head, now_utc_iso, validation_date, Finding};
use crate::validate::validate_ledgers;

/// Mint and independently re-check the JS→Clean-kernel receipts.
///
/// This is the only path in the JS lane that ends in a kernel, so the evidence
/// report is where it belongs: a reader asking "what has TrustJS actually
/// proved?" should not have to know that a separate crate exists. Every builtin
/// is certified fresh here rather than read from the committed certificates —
/// a certificate on disk is a record of some past run, and the point of the row
/// is that the kernel accepted the term produced by THIS tree.
///
/// A failed re-check is a finding, which makes the whole evidence run fail
/// closed. It has to be: a minted receipt the kernel then rejects means either
/// the interpreter changed under the transcription or the bridge is broken, and
/// neither is a thing to publish a conformance claim next to.
fn kernel_receipts(findings: &mut Vec<Finding>) -> Vec<EvidenceKernelReceipt> {
    type Certifier = (&'static str, fn() -> Result<Option<trust_js_certify_bridge::CertifiedBuiltin>, String>);
    const CERTIFIERS: &[Certifier] = &[
        ("String.prototype.toLowerCase", trust_js_certify_bridge::certify_tolowercase_ascii),
        ("String.prototype.toUpperCase", trust_js_certify_bridge::certify_touppercase_ascii),
        ("String.prototype.trim (whitespace class)", trust_js_certify_bridge::certify_whitespace_ascii),
        ("URI-Decode hex value", trust_js_certify_bridge::certify_hexval_ascii),
        ("encodeURIComponent unreserved set", trust_js_certify_bridge::certify_encuri_unreserved_ascii),
    ];

    let mut receipts = Vec::new();
    for (name, certify) in CERTIFIERS {
        match certify() {
            Ok(Some(certified)) => {
                let certificate = certified.to_certificate();
                let passed = certificate.kernel_check.passed;
                if !passed {
                    findings.push(Finding::new(
                        "kernel-recheck-failed",
                        format!("{name}: the minted receipt does not re-check"),
                    ));
                }
                receipts.push(EvidenceKernelReceipt {
                    builtin: certificate.builtin,
                    assurance_tier: certificate.assurance_tier,
                    transcription_sha256: certificate.transcription_sha256,
                    kernel_recheck_passed: passed,
                    term_sha256: certificate.clean_cic.term_sha256,
                    lineage_sha256: certificate.clean_cic.lineage_sha256,
                });
            }
            // `Ok(None)` is the bridge declining to mint — the interpreter and
            // the transcription disagreed somewhere, or the lane refused. Either
            // way there is no receipt, and silently publishing a report with one
            // fewer row than yesterday is how that stops being noticed.
            Ok(None) => findings.push(Finding::new(
                "kernel-receipt-withheld",
                format!("{name}: no receipt was minted"),
            )),
            Err(reason) => findings.push(Finding::new(
                "kernel-receipt-error",
                format!("{name}: {reason}"),
            )),
        }
    }
    receipts
}

pub fn run_evidence(scorecard_path: &Path, ledgers_dir: &Path, out_path: &Path) -> anyhow::Result<i32> {
    let vdate = validation_date();
    let mut findings: Vec<Finding> = Vec::new();

    // --- scorecard (embedded verbatim) ---
    let scorecard: serde_json::Value = match std::fs::read_to_string(scorecard_path) {
        Ok(text) => match serde_json::from_str(&text) {
            Ok(v) => v,
            Err(e) => {
                findings.push(Finding::new(
                    "scorecard-parse-error",
                    format!("{}: {e}", scorecard_path.display()),
                ));
                serde_json::Value::Null
            }
        },
        Err(e) => {
            findings.push(Finding::new(
                "scorecard-unreadable",
                format!("{}: {e}", scorecard_path.display()),
            ));
            serde_json::Value::Null
        }
    };
    if !scorecard.is_null() {
        match scorecard.get("schema").and_then(|v| v.as_str()) {
            Some(SCORECARD_SCHEMA) => {}
            other => findings.push(Finding::new(
                "scorecard-schema-mismatch",
                format!("scorecard schema is {other:?}, want {SCORECARD_SCHEMA:?}"),
            )),
        }
        if scorecard.get("partial").and_then(|v| v.as_bool()) == Some(true) {
            findings.push(Finding::new(
                "scorecard-partial",
                "a partial (--limit) scorecard is not admissible evidence",
            ));
        }
    }

    // --- ledgers ---
    let (ledger_findings, summary) = validate_ledgers(ledgers_dir, &vdate);
    findings.extend(ledger_findings);

    // --- repo head (read-only) ---
    let repo_head = git_head(ledgers_dir)
        .or_else(|| git_head(Path::new(".")))
        .unwrap_or_else(|| {
            findings.push(Finding::new("repo-head-unavailable", "git rev-parse HEAD failed"));
            "unknown".to_string()
        });

    // --- kernel receipts (the one proved thing in the JS lane) ---
    let receipts = kernel_receipts(&mut findings);

    // --- computed claim ---
    let gate_pass = scorecard
        .pointer("/gate/pass")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);
    let claim = gate_pass && findings.is_empty();

    let report = EvidenceReport {
        schema: EVIDENCE_SCHEMA.to_string(),
        schema_version: "1".to_string(),
        generated_at: now_utc_iso(),
        validation_date: vdate,
        repo_head,
        scorecard,
        ledgers: EvidenceLedgers {
            active_test_exceptions: summary.active_test_exceptions,
            active_audit_entries: summary.active_audit_entries,
            expired_entries: summary.expired_entries,
        },
        kernel_receipts: receipts,
        claims: EvidenceClaims { calibration_gate_claimed: claim },
        validation: EvidenceValidation {
            status: if findings.is_empty() { "pass" } else { "fail" }.to_string(),
            findings: findings.iter().map(Finding::render).collect(),
        },
    };

    if let Some(parent) = out_path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent)?;
        }
    }
    std::fs::write(out_path, serde_json::to_string_pretty(&report)?)?;
    let rechecked =
        report.kernel_receipts.iter().filter(|r| r.kernel_recheck_passed).count();
    println!(
        "evidence: wrote {} (claimed: {}, validation: {}, kernel receipts: {}/{} re-checked)",
        out_path.display(),
        report.claims.calibration_gate_claimed,
        report.validation.status,
        rechecked,
        report.kernel_receipts.len()
    );
    for f in &findings {
        eprintln!("evidence finding: {}", f.render());
    }
    Ok(if findings.is_empty() { 0 } else { 1 })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::EvidenceReport;

    #[test]
    fn partial_scorecard_never_claims() {
        let dir = tempfile::tempdir().unwrap();
        let scorecard = serde_json::json!({
            "schema": SCORECARD_SCHEMA,
            "partial": true,
            "gate": { "pass": false }
        });
        let sc_path = dir.path().join("scorecard.json");
        std::fs::write(&sc_path, scorecard.to_string()).unwrap();
        let ledgers = dir.path().join("ledgers");
        std::fs::create_dir_all(&ledgers).unwrap();
        let out = dir.path().join("evidence.json");
        let code = run_evidence(&sc_path, &ledgers, &out).unwrap();
        assert_eq!(code, 1); // missing ledgers + partial are findings
        let report: EvidenceReport =
            serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
        assert!(!report.claims.calibration_gate_claimed);
        assert_eq!(report.validation.status, "fail");
        assert!(report
            .validation
            .findings
            .iter()
            .any(|f| f.contains("scorecard-partial")));

        // The kernel receipts ride along on every evidence run, and each one is
        // re-checked here rather than trusted from the committed certificate.
        assert_eq!(report.kernel_receipts.len(), 5, "one receipt per certified builtin");
        for receipt in &report.kernel_receipts {
            assert!(receipt.kernel_recheck_passed, "{} did not re-check", receipt.builtin);
            // The claim must stay the narrow one the bridge makes.
            assert!(
                receipt.assurance_tier.contains("OUR TRANSCRIPTION"),
                "the assurance tier must not be softened into refinement to ECMA-262: {}",
                receipt.assurance_tier
            );
        }
        // A failed re-check would have to show up as a finding, not a quiet row.
        assert!(!report.validation.findings.iter().any(|f| f.contains("kernel-recheck-failed")));
    }
}
