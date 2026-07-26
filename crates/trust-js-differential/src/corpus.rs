// corpus-verify: fail-closed pin check of the local Test262 checkout against
// tests/js262/corpus-pin.json (trust.js262.corpus-pin.v1). Verifies the git
// HEAD, every pinned harness payload's sha256, exact payload coverage of
// harness/**.js (both directions), payload ordering, and the recomputed
// manifest_hash. Any drift is a named finding => exit 1.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::path::Path;

use crate::model::{CorpusPin, CORPUS_PIN_SCHEMA};
use crate::util::{git_head, sha256_file, Finding};

/// Recompute the pin manifest hash over the payload list as ordered.
pub fn manifest_hash(pin: &CorpusPin) -> String {
    let mut acc = String::new();
    for p in &pin.payloads {
        acc.push_str(&p.relative_path);
        acc.push('\n');
        acc.push_str(&p.sha256);
        acc.push('\n');
    }
    trust_js_trace::sha256_hex(acc.as_bytes())
}

fn walk_harness(root: &Path, rel_dir: &str, out: &mut Vec<String>) -> std::io::Result<()> {
    for entry in std::fs::read_dir(root.join(rel_dir))? {
        let entry = entry?;
        let name = entry.file_name();
        let name = name.to_string_lossy().into_owned();
        let rel = format!("{rel_dir}/{name}");
        let ft = entry.file_type()?;
        if ft.is_dir() {
            walk_harness(root, &rel, out)?;
        } else if ft.is_file() && rel.ends_with(".js") {
            out.push(rel);
        }
    }
    Ok(())
}

/// The fail-closed corpus-pin verification. Returns all findings.
pub fn corpus_verify(corpus: &Path, pin_path: &Path) -> Vec<Finding> {
    let mut findings = Vec::new();

    let pin_text = match std::fs::read_to_string(pin_path) {
        Ok(t) => t,
        Err(e) => {
            findings.push(Finding::new(
                "pin-unreadable",
                format!("cannot read {}: {e}", pin_path.display()),
            ));
            return findings;
        }
    };
    let pin: CorpusPin = match serde_json::from_str(&pin_text) {
        Ok(p) => p,
        Err(e) => {
            findings.push(Finding::new(
                "pin-parse-error",
                format!("{} does not parse as {CORPUS_PIN_SCHEMA}: {e}", pin_path.display()),
            ));
            return findings;
        }
    };

    if pin.schema != CORPUS_PIN_SCHEMA {
        findings.push(Finding::new(
            "pin-schema-mismatch",
            format!("schema is {:?}, want {CORPUS_PIN_SCHEMA:?}", pin.schema),
        ));
    }
    let expected_revision = format!("tc39/test262:{}", pin.git_commit_hash);
    if pin.upstream.revision != expected_revision {
        findings.push(Finding::new(
            "pin-internal-revision-mismatch",
            format!(
                "upstream.revision {:?} != \"tc39/test262:<git_commit_hash>\" ({expected_revision})",
                pin.upstream.revision
            ),
        ));
    }

    match git_head(corpus) {
        Some(head) if head == pin.git_commit_hash => {}
        Some(head) => findings.push(Finding::new(
            "corpus-head-drift",
            format!("git rev-parse HEAD is {head}, pin wants {}", pin.git_commit_hash),
        )),
        None => findings.push(Finding::new(
            "corpus-head-unreadable",
            format!("git rev-parse HEAD failed in {}", corpus.display()),
        )),
    }

    // Payload ordering (bytewise ascending by relative_path) and duplicates.
    for w in pin.payloads.windows(2) {
        if w[0].relative_path >= w[1].relative_path {
            findings.push(Finding::new(
                "pin-payload-order",
                format!(
                    "payloads not sorted bytewise ascending at {:?} >= {:?}",
                    w[0].relative_path, w[1].relative_path
                ),
            ));
            break;
        }
    }

    // Every pinned payload must exist with a matching sha256.
    for payload in &pin.payloads {
        let abs = corpus.join(&payload.relative_path);
        match sha256_file(&abs) {
            Ok(actual) if actual == payload.sha256 => {}
            Ok(actual) => findings.push(Finding::new(
                "payload-sha256-drift",
                format!("{}: pinned {} actual {actual}", payload.relative_path, payload.sha256),
            )),
            Err(e) => findings.push(Finding::new(
                "payload-missing",
                format!("{}: {e}", payload.relative_path),
            )),
        }
    }

    // Coverage: EVERY file under harness/ ending .js must be pinned.
    let mut on_disk = Vec::new();
    match walk_harness(corpus, "harness", &mut on_disk) {
        Ok(()) => {
            on_disk.sort();
            let pinned: std::collections::BTreeSet<&str> =
                pin.payloads.iter().map(|p| p.relative_path.as_str()).collect();
            for rel in &on_disk {
                if !pinned.contains(rel.as_str()) {
                    findings.push(Finding::new(
                        "unpinned-harness-payload",
                        format!("{rel} exists under harness/ but is not pinned"),
                    ));
                }
            }
        }
        Err(e) => findings.push(Finding::new(
            "harness-walk-failed",
            format!("cannot walk {}/harness: {e}", corpus.display()),
        )),
    }

    let recomputed = manifest_hash(&pin);
    if recomputed != pin.manifest_hash {
        findings.push(Finding::new(
            "manifest-hash-drift",
            format!("recomputed {recomputed} != pinned {}", pin.manifest_hash),
        ));
    }

    findings
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{PinPayload, PinUpstream};

    fn pin_for(root: &Path, files: &[(&str, &str)]) -> CorpusPin {
        let mut payloads = Vec::new();
        for (rel, content) in files {
            let abs = root.join(rel);
            std::fs::create_dir_all(abs.parent().unwrap()).unwrap();
            std::fs::write(&abs, content).unwrap();
            payloads
                .push(PinPayload {
                    relative_path: rel.to_string(),
                    sha256: trust_js_trace::sha256_hex(content.as_bytes()),
                });
        }
        payloads.sort_by(|a, b| a.relative_path.cmp(&b.relative_path));
        let mut pin = CorpusPin {
            schema: CORPUS_PIN_SCHEMA.to_string(),
            date: "2026-07-21".to_string(),
            upstream: PinUpstream {
                repo: "https://github.com/tc39/test262.git".to_string(),
                revision: "tc39/test262:cafe".to_string(),
                snapshot_date: "2026-07-21".to_string(),
            },
            git_commit_hash: "cafe".to_string(),
            payloads,
            manifest_hash: String::new(),
        };
        pin.manifest_hash = manifest_hash(&pin);
        pin
    }

    #[test]
    fn detects_payload_drift_and_coverage() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        let pin = pin_for(root, &[("harness/assert.js", "a();"), ("harness/sm/x.js", "b();")]);
        // No git repo in the tempdir: corpus-head-unreadable is expected; the
        // payload checks are what this test pins down.
        let pin_path = root.join("pin.json");
        std::fs::write(&pin_path, serde_json::to_string(&pin).unwrap()).unwrap();
        let findings = corpus_verify(root, &pin_path);
        assert!(findings.iter().any(|f| f.code == "corpus-head-unreadable"));
        assert!(!findings.iter().any(|f| f.code == "payload-sha256-drift"));
        assert!(!findings.iter().any(|f| f.code == "unpinned-harness-payload"));

        // Tamper with a pinned payload => sha drift.
        std::fs::write(root.join("harness/assert.js"), "tampered();").unwrap();
        let findings = corpus_verify(root, &pin_path);
        assert!(findings.iter().any(|f| f.code == "payload-sha256-drift"));

        // Add an unpinned harness file => coverage finding.
        std::fs::write(root.join("harness/new.js"), "n();").unwrap();
        let findings = corpus_verify(root, &pin_path);
        assert!(findings.iter().any(|f| f.code == "unpinned-harness-payload"));
    }

    #[test]
    fn detects_manifest_hash_drift() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        let mut pin = pin_for(root, &[("harness/assert.js", "a();")]);
        pin.manifest_hash = "0".repeat(64);
        let pin_path = root.join("pin.json");
        std::fs::write(&pin_path, serde_json::to_string(&pin).unwrap()).unwrap();
        let findings = corpus_verify(root, &pin_path);
        assert!(findings.iter().any(|f| f.code == "manifest-hash-drift"));
    }
}
