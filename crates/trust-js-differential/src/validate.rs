// js262 ledger validation, fail-closed: baseline.toml / test-exceptions.toml /
// divergence-audit.toml parse with deny_unknown_fields; every ACTIVE test
// exception and ACTIVE divergence-audit entry must carry a well-formed
// YYYY-MM-DD expiry that is after reviewed_on and AFTER the validation date
// (lexicographic compare on zero-padded ISO dates). Permanent-category audit
// entries (benign_host_defined / spec_bug with permanent=true) carry issue
// links instead of expiry. Active projection_too_strong entries are findings:
// they demand a trust-js-trace fix, never a waiver.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::path::Path;

use crate::model::{
    Js262AuditEntry, Js262AuditStatus, Js262Baseline, Js262Classification, Js262DivergenceAudit,
    Js262ExceptionStatus, Js262TestExceptionLedger,
};
use crate::util::{is_valid_date, Finding};

/// Ledger identities surfaced into evidence artifacts.
#[derive(Debug, Clone, Default)]
pub struct LedgerSummary {
    pub active_test_exceptions: Vec<String>,
    pub active_audit_entries: Vec<String>,
    /// Entries marked active whose expiry has lapsed (always findings too).
    pub expired_entries: Vec<String>,
}

/// Is an audit entry an acceptable ACTIVE waiver on `date`? (Classification
/// acceptability is the caller's concern; projection_too_strong is flagged by
/// validation and never accepted by calibration.)
pub fn audit_entry_is_active(entry: &Js262AuditEntry, date: &str) -> bool {
    if entry.status != Js262AuditStatus::Active {
        return false;
    }
    if entry.permanent {
        return true;
    }
    match &entry.expires_on {
        Some(e) => is_valid_date(e) && e.as_str() > date,
        None => false,
    }
}

/// Validate the three ledgers under `dir` against `validation_date`.
/// Missing or unparseable files are findings (fail-closed).
pub fn validate_ledgers(dir: &Path, validation_date: &str) -> (Vec<Finding>, LedgerSummary) {
    let mut findings = Vec::new();
    let mut summary = LedgerSummary::default();

    // --- baseline.toml ---
    match read(dir, "baseline.toml", &mut findings) {
        Some(text) => match toml::from_str::<Js262Baseline>(&text) {
            Ok(baseline) => {
                if baseline.upstream.channel != "test262" {
                    findings.push(Finding::new(
                        "baseline-channel",
                        format!("upstream.channel is {:?}, want \"test262\"", baseline.upstream.channel),
                    ));
                }
                if baseline.schema_version.trim().is_empty() {
                    findings.push(Finding::new("baseline-schema-version", "schema_version is blank"));
                }
                for entry in &baseline.entries {
                    if entry.surface.trim().is_empty() {
                        findings.push(Finding::new(
                            "baseline-blank-surface",
                            format!("entry {}: surface is blank", entry.id),
                        ));
                    }
                }
            }
            Err(e) => findings.push(Finding::new("baseline-parse-error", format!("baseline.toml: {e}"))),
        },
        None => {}
    }

    // --- test-exceptions.toml ---
    if let Some(text) = read(dir, "test-exceptions.toml", &mut findings) {
        match toml::from_str::<Js262TestExceptionLedger>(&text) {
            Ok(ledger) => {
                for exc in &ledger.exceptions {
                    if exc.status != Js262ExceptionStatus::Active {
                        continue;
                    }
                    let id = &exc.id;
                    let mut sound = true;
                    if !is_valid_date(&exc.reviewed_on) {
                        findings.push(Finding::new(
                            "exception-bad-reviewed-on",
                            format!("{id}: reviewed_on {:?} is not YYYY-MM-DD", exc.reviewed_on),
                        ));
                        sound = false;
                    }
                    if !is_valid_date(&exc.expires_on) {
                        findings.push(Finding::new(
                            "exception-bad-expires-on",
                            format!("{id}: expires_on {:?} is not YYYY-MM-DD", exc.expires_on),
                        ));
                        sound = false;
                    }
                    if sound && exc.expires_on <= exc.reviewed_on {
                        findings.push(Finding::new(
                            "exception-expiry-before-review",
                            format!("{id}: expires_on {} <= reviewed_on {}", exc.expires_on, exc.reviewed_on),
                        ));
                        sound = false;
                    }
                    if sound && exc.expires_on.as_str() <= validation_date {
                        findings.push(Finding::new(
                            "expired-active-exception",
                            format!("{id}: active but expires_on {} <= validation date {validation_date}", exc.expires_on),
                        ));
                        summary.expired_entries.push(id.clone());
                        sound = false;
                    }
                    if sound {
                        summary.active_test_exceptions.push(id.clone());
                    }
                }
            }
            Err(e) => findings
                .push(Finding::new("exceptions-parse-error", format!("test-exceptions.toml: {e}"))),
        }
    }

    // --- divergence-audit.toml ---
    if let Some(text) = read(dir, "divergence-audit.toml", &mut findings) {
        match toml::from_str::<Js262DivergenceAudit>(&text) {
            Ok(audit) => {
                for entry in &audit.entries {
                    if entry.status != Js262AuditStatus::Active {
                        continue;
                    }
                    let id = &entry.id;
                    if entry.classification == Js262Classification::ProjectionTooStrong {
                        findings.push(Finding::new(
                            "projection-too-strong-entry",
                            format!(
                                "{id}: projection_too_strong is never a waiver — fix trust-js-trace instead"
                            ),
                        ));
                        continue;
                    }
                    if !is_valid_date(&entry.reviewed_on) {
                        findings.push(Finding::new(
                            "audit-bad-reviewed-on",
                            format!("{id}: reviewed_on {:?} is not YYYY-MM-DD", entry.reviewed_on),
                        ));
                        continue;
                    }
                    if entry.permanent {
                        // Permanent-category entries: benign_host_defined /
                        // spec_bug only, accountable via issue link.
                        if !matches!(
                            entry.classification,
                            Js262Classification::BenignHostDefined | Js262Classification::SpecBug
                        ) {
                            findings.push(Finding::new(
                                "audit-invalid-permanent-classification",
                                format!(
                                    "{id}: permanent entries must be benign_host_defined or spec_bug, got {:?}",
                                    entry.classification
                                ),
                            ));
                            continue;
                        }
                        if entry.issue.trim().is_empty() {
                            findings.push(Finding::new(
                                "audit-permanent-missing-issue",
                                format!("{id}: permanent entry has no issue link"),
                            ));
                            continue;
                        }
                        summary.active_audit_entries.push(id.clone());
                        continue;
                    }
                    match &entry.expires_on {
                        None => {
                            findings.push(Finding::new(
                                "audit-missing-expiry",
                                format!("{id}: non-permanent active entry has no expires_on"),
                            ));
                        }
                        Some(e) if !is_valid_date(e) => {
                            findings.push(Finding::new(
                                "audit-bad-expires-on",
                                format!("{id}: expires_on {e:?} is not YYYY-MM-DD"),
                            ));
                        }
                        Some(e) if e.as_str() <= entry.reviewed_on.as_str() => {
                            findings.push(Finding::new(
                                "audit-expiry-before-review",
                                format!("{id}: expires_on {e} <= reviewed_on {}", entry.reviewed_on),
                            ));
                        }
                        Some(e) if e.as_str() <= validation_date => {
                            findings.push(Finding::new(
                                "expired-active-audit-entry",
                                format!("{id}: active but expires_on {e} <= validation date {validation_date}"),
                            ));
                            summary.expired_entries.push(id.clone());
                        }
                        Some(_) => summary.active_audit_entries.push(id.clone()),
                    }
                }
            }
            Err(e) => findings
                .push(Finding::new("audit-parse-error", format!("divergence-audit.toml: {e}"))),
        }
    }

    (findings, summary)
}

fn read(dir: &Path, name: &str, findings: &mut Vec<Finding>) -> Option<String> {
    let path = dir.join(name);
    match std::fs::read_to_string(&path) {
        Ok(t) => Some(t),
        Err(e) => {
            findings.push(Finding::new("missing-ledger", format!("{}: {e}", path.display())));
            None
        }
    }
}

/// Load the divergence audit for calibration classification. Missing file =>
/// empty audit (zero waivers) — validation findings still gate ledger_ok.
/// Load the test-exceptions ledger (empty on absence/parse failure — the
/// validate subcommand reports those as findings; consumers only need the
/// active rows).
pub fn load_test_exceptions(dir: &Path) -> crate::model::Js262TestExceptionLedger {
    let path = dir.join("test-exceptions.toml");
    match std::fs::read_to_string(&path) {
        Ok(text) => toml::from_str(&text).unwrap_or(crate::model::Js262TestExceptionLedger {
            schema_version: "1".to_string(),
            exceptions: vec![],
        }),
        Err(_) => crate::model::Js262TestExceptionLedger {
            schema_version: "1".to_string(),
            exceptions: vec![],
        },
    }
}

/// An exception waives only while active, well-formed, and unexpired.
pub fn test_exception_is_active(e: &crate::model::Js262TestException, date: &str) -> bool {
    e.status == crate::model::Js262ExceptionStatus::Active
        && crate::util::is_valid_date(&e.reviewed_on)
        && crate::util::is_valid_date(&e.expires_on)
        && e.expires_on.as_str() > e.reviewed_on.as_str()
        && e.expires_on.as_str() > date
}

pub fn load_audit(dir: &Path) -> Js262DivergenceAudit {
    let path = dir.join("divergence-audit.toml");
    match std::fs::read_to_string(&path) {
        Ok(text) => toml::from_str(&text).unwrap_or(Js262DivergenceAudit {
            schema_version: "1".to_string(),
            entries: vec![],
        }),
        Err(_) => Js262DivergenceAudit { schema_version: "1".to_string(), entries: vec![] },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    const DATE: &str = "2026-07-21";

    fn write_ledgers(dir: &Path, baseline: &str, exceptions: &str, audit: &str) {
        fs::write(dir.join("baseline.toml"), baseline).unwrap();
        fs::write(dir.join("test-exceptions.toml"), exceptions).unwrap();
        fs::write(dir.join("divergence-audit.toml"), audit).unwrap();
    }

    const GOOD_BASELINE: &str = r#"
schema_version = "1"
id = "js262-baseline-m0"
entries = []
[upstream]
channel = "test262"
revision = "tc39/test262:cafe"
[local]
revision = "beef"
"#;

    fn exception(status: &str, reviewed: &str, expires: &str) -> String {
        format!(
            r#"
schema_version = "1"
[[exceptions]]
id = "exc-1"
test_id = "t"
suite = "js262"
path = "test/language/x.js"
kind = "expected_fail"
status = "{status}"
owner = "ayates"
reason = "r"
issue = "https://example.invalid/1"
reviewed_on = "{reviewed}"
expires_on = "{expires}"
"#
        )
    }

    fn audit(status: &str, classification: &str, permanent: bool, expires: Option<&str>) -> String {
        let expiry = expires.map(|e| format!("expires_on = \"{e}\"\n")).unwrap_or_default();
        format!(
            r#"
schema_version = "1"
[[entries]]
id = "aud-1"
path = "test/built-ins/x.js"
mode = "bare"
fingerprint = "00112233aabbccdd"
classification = "{classification}"
status = "{status}"
owner = "ayates"
reason = "r"
issue = "https://example.invalid/2"
reviewed_on = "2026-07-01"
permanent = {permanent}
{expiry}"#
        )
    }

    #[test]
    fn clean_ledgers_pass() {
        let dir = tempfile::tempdir().unwrap();
        write_ledgers(
            dir.path(),
            GOOD_BASELINE,
            &exception("active", "2026-07-01", "2026-09-01"),
            &audit("active", "node_bug", false, Some("2026-09-01")),
        );
        let (findings, summary) = validate_ledgers(dir.path(), DATE);
        assert!(findings.is_empty(), "unexpected findings: {findings:?}");
        assert_eq!(summary.active_test_exceptions, ["exc-1"]);
        assert_eq!(summary.active_audit_entries, ["aud-1"]);
        assert!(summary.expired_entries.is_empty());
    }

    #[test]
    fn expired_active_entries_are_findings() {
        let dir = tempfile::tempdir().unwrap();
        write_ledgers(
            dir.path(),
            GOOD_BASELINE,
            &exception("active", "2026-05-01", "2026-07-21"), // == validation date => expired
            &audit("active", "bun_bug", false, Some("2026-07-10")), // after review, lapsed
        );
        let (findings, summary) = validate_ledgers(dir.path(), DATE);
        assert!(findings.iter().any(|f| f.code == "expired-active-exception"));
        assert!(findings.iter().any(|f| f.code == "expired-active-audit-entry"));
        assert_eq!(summary.expired_entries.len(), 2);
        assert!(summary.active_test_exceptions.is_empty());
    }

    #[test]
    fn resolved_entries_are_ignored() {
        let dir = tempfile::tempdir().unwrap();
        write_ledgers(
            dir.path(),
            GOOD_BASELINE,
            &exception("resolved", "2026-05-01", "2026-06-01"),
            &audit("resolved", "node_bug", false, Some("2026-06-01")),
        );
        let (findings, summary) = validate_ledgers(dir.path(), DATE);
        assert!(findings.is_empty(), "unexpected findings: {findings:?}");
        assert!(summary.active_test_exceptions.is_empty());
        assert!(summary.active_audit_entries.is_empty());
    }

    #[test]
    fn permanent_rules() {
        let dir = tempfile::tempdir().unwrap();
        // Permanent benign_host_defined with issue: OK, no expiry needed.
        write_ledgers(
            dir.path(),
            GOOD_BASELINE,
            &exception("active", "2026-07-01", "2026-09-01"),
            &audit("active", "benign_host_defined", true, None),
        );
        let (findings, summary) = validate_ledgers(dir.path(), DATE);
        assert!(findings.is_empty(), "unexpected findings: {findings:?}");
        assert_eq!(summary.active_audit_entries, ["aud-1"]);

        // Permanent node_bug: invalid classification for permanence.
        write_ledgers(
            dir.path(),
            GOOD_BASELINE,
            &exception("active", "2026-07-01", "2026-09-01"),
            &audit("active", "node_bug", true, None),
        );
        let (findings, _) = validate_ledgers(dir.path(), DATE);
        assert!(findings.iter().any(|f| f.code == "audit-invalid-permanent-classification"));

        // Non-permanent without expiry: missing expiry finding.
        write_ledgers(
            dir.path(),
            GOOD_BASELINE,
            &exception("active", "2026-07-01", "2026-09-01"),
            &audit("active", "spec_bug", false, None),
        );
        let (findings, _) = validate_ledgers(dir.path(), DATE);
        assert!(findings.iter().any(|f| f.code == "audit-missing-expiry"));
    }

    #[test]
    fn projection_too_strong_is_always_a_finding() {
        let dir = tempfile::tempdir().unwrap();
        write_ledgers(
            dir.path(),
            GOOD_BASELINE,
            &exception("active", "2026-07-01", "2026-09-01"),
            &audit("active", "projection_too_strong", false, Some("2026-09-01")),
        );
        let (findings, summary) = validate_ledgers(dir.path(), DATE);
        assert!(findings.iter().any(|f| f.code == "projection-too-strong-entry"));
        assert!(summary.active_audit_entries.is_empty());
    }

    #[test]
    fn missing_ledgers_are_findings() {
        let dir = tempfile::tempdir().unwrap();
        let (findings, _) = validate_ledgers(dir.path(), DATE);
        assert_eq!(findings.iter().filter(|f| f.code == "missing-ledger").count(), 3);
    }

    #[test]
    fn active_waiver_predicate() {
        let a: Js262DivergenceAudit =
            toml::from_str(&audit("active", "node_bug", false, Some("2026-09-01"))).unwrap();
        assert!(audit_entry_is_active(&a.entries[0], DATE));
        assert!(!audit_entry_is_active(&a.entries[0], "2026-09-01")); // == expiry => lapsed
        let p: Js262DivergenceAudit =
            toml::from_str(&audit("active", "benign_host_defined", true, None)).unwrap();
        assert!(audit_entry_is_active(&p.entries[0], "2099-01-01"));
        let r: Js262DivergenceAudit =
            toml::from_str(&audit("resolved", "node_bug", false, Some("2026-09-01"))).unwrap();
        assert!(!audit_entry_is_active(&r.entries[0], DATE));
    }
}
