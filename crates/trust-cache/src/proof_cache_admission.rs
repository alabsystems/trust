// trust-cache/proof_cache_admission.rs: release proof/query cache admission.
//
// Release full-verify may only replay proof/query cache entries after an
// explicit admission report binds each entry to its spec, policy, verifier,
// proof mode, source revision, replay row, and admission decision.

use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

/// Schema name for release proof/query cache admission reports.
pub const PROOF_QUERY_CACHE_ADMISSION_SCHEMA: &str = "trust.proof-query-cache-admission.v1";

/// Current release proof/query cache admission schema version.
pub const PROOF_QUERY_CACHE_ADMISSION_VERSION: u64 = 1;

/// Metrics emitted by the proof/query cache admission validator.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[trust::skip]
pub struct ProofQueryCacheAdmissionMetrics {
    pub manifests: usize,
    pub entries: usize,
    pub admitted_entries: usize,
    pub rejected_entries: usize,
    pub legacy_entries: usize,
    pub spec_less_entries: usize,
    pub replay_rows: usize,
    pub admission_rows: usize,
    pub bounded_entries: usize,
    pub unbounded_entries: usize,
    pub verifier_hash_missing: usize,
    pub source_revision_mismatches: usize,
}

/// Result status for proof/query cache admission validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ProofQueryCacheAdmissionStatus {
    Passed,
    Failed,
}

/// Validation report for one proof/query cache admission manifest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[trust::skip]
pub struct ProofQueryCacheAdmissionReport {
    pub status: ProofQueryCacheAdmissionStatus,
    pub schema: Option<String>,
    pub version: Option<u64>,
    pub policy_key: Option<String>,
    pub source_revision: Option<String>,
    pub metrics: ProofQueryCacheAdmissionMetrics,
    pub errors: Vec<String>,
}

impl ProofQueryCacheAdmissionReport {
    #[must_use]
    pub fn ok(&self) -> bool {
        self.status == ProofQueryCacheAdmissionStatus::Passed
    }
}

/// Validate a parsed proof/query cache admission JSON value.
#[must_use]
pub fn validate_proof_query_cache_admission_json(value: &Value) -> ProofQueryCacheAdmissionReport {
    let mut validator = AdmissionValidator::default();
    validator.validate(value)
}

/// Validate a proof/query cache admission JSON string.
pub fn validate_proof_query_cache_admission_str(
    contents: &str,
) -> Result<ProofQueryCacheAdmissionReport, serde_json::Error> {
    let value: Value = serde_json::from_str(contents)?;
    Ok(validate_proof_query_cache_admission_json(&value))
}

#[derive(Default)]
struct AdmissionValidator {
    errors: Vec<String>,
    metrics: ProofQueryCacheAdmissionMetrics,
}

impl AdmissionValidator {
    fn validate(&mut self, value: &Value) -> ProofQueryCacheAdmissionReport {
        self.metrics.manifests = 1;
        let Some(object) = value.as_object() else {
            self.errors.push("proof-query cache admission manifest must be a JSON object".into());
            self.metrics.legacy_entries = 1;
            return self.report(None, None, None, None);
        };

        let schema = object.get("schema").and_then(Value::as_str).map(str::to_string);
        let version = object.get("version").and_then(Value::as_u64);
        let policy_key = object.get("policy_key").and_then(Value::as_str).map(str::to_string);
        let source_revision =
            object.get("source_revision").and_then(Value::as_str).map(str::to_string);

        if schema.as_deref() != Some(PROOF_QUERY_CACHE_ADMISSION_SCHEMA) {
            self.errors.push(format!(
                "proof-query cache admission has unexpected schema: {:?}",
                schema.as_deref()
            ));
        }
        if version != Some(PROOF_QUERY_CACHE_ADMISSION_VERSION) {
            self.errors
                .push(format!("proof-query cache admission has unexpected version: {:?}", version));
        }
        if schema.is_none() || version.is_none() {
            self.errors.push(
                "legacy proof-query cache admission is missing schema/version and is not release evidence"
                    .into(),
            );
        }

        self.require_non_empty_manifest_string(object, "policy_key");
        self.require_non_empty_manifest_string(object, "source_revision");

        let entries = self.required_array(object, "entries");
        let replay_rows = self.required_array(object, "replay_rows");
        let admission_rows = self.required_array(object, "admission_rows");

        self.metrics.entries = entries.len();
        self.metrics.replay_rows = replay_rows.len();
        self.metrics.admission_rows = admission_rows.len();
        if schema.is_none() || version.is_none() {
            self.metrics.legacy_entries = entries.len().max(1);
        }

        if entries.is_empty() {
            self.errors.push(
                "proof-query cache admission entries must be non-empty when configured".into(),
            );
        }
        if replay_rows.is_empty() {
            self.errors.push("proof-query cache admission replay_rows must be non-empty".into());
        }
        if admission_rows.is_empty() {
            self.errors.push("proof-query cache admission admission_rows must be non-empty".into());
        }

        let mut entry_keys = BTreeSet::new();
        for (index, entry) in entries.iter().enumerate() {
            if let Some(key) =
                self.validate_entry(index, entry, policy_key.as_deref(), source_revision.as_deref())
            {
                if entry_keys.contains(&key) {
                    self.errors.push(format!(
                        "entries[{index}].cache_key duplicates another entry: {key}"
                    ));
                } else {
                    entry_keys.insert(key);
                }
            }
        }

        let replay_by_key = self.validate_rows(
            "replay_rows",
            replay_rows,
            &entry_keys,
            &["entry_key", "status", "verdict"],
            &[("status", "replayed"), ("verdict", "proved")],
        );
        let admission_by_key = self.validate_rows(
            "admission_rows",
            admission_rows,
            &entry_keys,
            &["entry_key", "decision"],
            &[("decision", "admit")],
        );

        for key in &entry_keys {
            if !replay_by_key.contains_key(key) {
                self.errors.push(format!(
                    "entries cache_key {key} has no matching proof-query replay row"
                ));
            }
            if !admission_by_key.contains_key(key) {
                self.errors.push(format!(
                    "entries cache_key {key} has no matching proof-query admission row"
                ));
            }
        }

        self.report(schema, version, policy_key, source_revision)
    }

    fn report(
        &self,
        schema: Option<String>,
        version: Option<u64>,
        policy_key: Option<String>,
        source_revision: Option<String>,
    ) -> ProofQueryCacheAdmissionReport {
        ProofQueryCacheAdmissionReport {
            status: if self.errors.is_empty() {
                ProofQueryCacheAdmissionStatus::Passed
            } else {
                ProofQueryCacheAdmissionStatus::Failed
            },
            schema,
            version,
            policy_key,
            source_revision,
            metrics: self.metrics.clone(),
            errors: self.errors.clone(),
        }
    }

    fn require_non_empty_manifest_string(
        &mut self,
        object: &serde_json::Map<String, Value>,
        key: &str,
    ) {
        if non_empty_string(object.get(key)).is_none() {
            self.errors
                .push(format!("proof-query cache admission {key} must be a non-empty string"));
        }
    }

    fn required_array<'a>(
        &mut self,
        object: &'a serde_json::Map<String, Value>,
        key: &str,
    ) -> &'a [Value] {
        match object.get(key).and_then(Value::as_array) {
            Some(values) => values.as_slice(),
            None => {
                self.errors.push(format!("proof-query cache admission {key} must be an array"));
                &[]
            }
        }
    }

    fn validate_entry(
        &mut self,
        index: usize,
        value: &Value,
        manifest_policy_key: Option<&str>,
        manifest_source_revision: Option<&str>,
    ) -> Option<String> {
        let Some(object) = value.as_object() else {
            self.errors.push(format!("entries[{index}] must be a JSON object"));
            self.metrics.legacy_entries += 1;
            return None;
        };

        let cache_key = self.require_entry_string(index, object, "cache_key");
        self.require_digest_string(index, object, "content_hash");
        let spec_hash = self.require_digest_string(index, object, "spec_hash");
        if spec_hash.is_none() {
            self.metrics.spec_less_entries += 1;
        }

        let policy_key = self.require_entry_string(index, object, "policy_key");
        if let (Some(entry_policy), Some(manifest_policy)) =
            (policy_key.as_deref(), manifest_policy_key)
        {
            if entry_policy != manifest_policy {
                self.errors.push(format!(
                    "entries[{index}].policy_key does not match manifest policy_key"
                ));
            }
        }

        let source_revision = self.require_entry_string(index, object, "source_revision");
        if let (Some(entry_revision), Some(manifest_revision)) =
            (source_revision.as_deref(), manifest_source_revision)
        {
            if entry_revision != manifest_revision {
                self.metrics.source_revision_mismatches += 1;
                self.errors.push(format!(
                    "entries[{index}].source_revision does not match manifest source_revision"
                ));
            }
        }

        self.require_entry_string(index, object, "solver");
        self.require_entry_string(index, object, "proof_mode");
        self.validate_boundedness(index, object.get("boundedness"));
        self.validate_verifier(index, object.get("verifier"));

        match object.get("admitted").and_then(Value::as_bool) {
            Some(true) => self.metrics.admitted_entries += 1,
            Some(false) => {
                self.metrics.rejected_entries += 1;
                self.errors.push(format!(
                    "entries[{index}].admitted must be true for release proof-query cache replay"
                ));
            }
            None => {
                self.metrics.rejected_entries += 1;
                self.errors.push(format!("entries[{index}].admitted must be a boolean true"));
            }
        }

        cache_key
    }

    fn require_entry_string(
        &mut self,
        index: usize,
        object: &serde_json::Map<String, Value>,
        key: &str,
    ) -> Option<String> {
        let value = non_empty_string(object.get(key));
        if value.is_none() {
            self.errors.push(format!("entries[{index}].{key} must be a non-empty string"));
        }
        value.map(str::to_string)
    }

    fn require_digest_string(
        &mut self,
        index: usize,
        object: &serde_json::Map<String, Value>,
        key: &str,
    ) -> Option<String> {
        let value = self.require_entry_string(index, object, key)?;
        if !looks_like_sha256(&value) {
            self.errors.push(format!("entries[{index}].{key} must be a sha256 digest"));
        }
        Some(value)
    }

    fn validate_boundedness(&mut self, index: usize, value: Option<&Value>) {
        let Some(object) = value.and_then(Value::as_object) else {
            self.errors.push(format!("entries[{index}].boundedness must be a JSON object"));
            return;
        };
        let Some(kind) = non_empty_string(object.get("kind")) else {
            self.errors
                .push(format!("entries[{index}].boundedness.kind must be a non-empty string"));
            return;
        };
        match kind {
            "bounded" => {
                // Statistics counter (per-entry boundedness tally in the
                // report): saturating_add is exact for every reachable count
                // (at most one increment per element of a live JSON array)
                // and at the unreachable usize::MAX extreme pins instead of
                // wrapping to 0. Not checked_add: a diagnostic tally over an
                // untrusted manifest must not become an abort; pass/fail is
                // carried by `errors`, never by this count.
                self.metrics.bounded_entries = self.metrics.bounded_entries.saturating_add(1);
                if object.get("depth").and_then(Value::as_u64).is_none() {
                    self.errors.push(format!(
                        "entries[{index}].boundedness.depth must be present for bounded proof modes"
                    ));
                }
            }
            "unbounded" => {
                // Statistics counter: saturate, same rationale as
                // `bounded_entries` above.
                self.metrics.unbounded_entries =
                    self.metrics.unbounded_entries.saturating_add(1);
            }
            other => self.errors.push(format!(
                "entries[{index}].boundedness.kind must be bounded or unbounded, got {other:?}"
            )),
        }
    }

    fn validate_verifier(&mut self, index: usize, value: Option<&Value>) {
        let Some(object) = value.and_then(Value::as_object) else {
            self.errors.push(format!("entries[{index}].verifier must be a JSON object"));
            return;
        };
        for key in ["identity", "version"] {
            if non_empty_string(object.get(key)).is_none() {
                self.errors
                    .push(format!("entries[{index}].verifier.{key} must be a non-empty string"));
            }
        }
        match non_empty_string(object.get("hash")) {
            Some(hash) if looks_like_sha256(hash) => {}
            Some(_) => self.errors.push(format!(
                "entries[{index}].verifier.hash must be a sha256 digest when present"
            )),
            None => {
                // Statistics counter: saturate, same rationale as
                // `bounded_entries` in validate_boundedness. Saturation can
                // never take a nonzero count back to zero, so any external
                // "hash-missing must be zero" gate over the report stays
                // sound; the fail-closed error below is pushed independently
                // of this count.
                self.metrics.verifier_hash_missing =
                    self.metrics.verifier_hash_missing.saturating_add(1);
                if non_empty_string(object.get("hash_unavailable_reason")).is_none() {
                    self.errors.push(format!(
                        "entries[{index}].verifier.hash or verifier.hash_unavailable_reason is required"
                    ));
                }
            }
        }
    }

    fn validate_rows(
        &mut self,
        label: &str,
        rows: &[Value],
        entry_keys: &BTreeSet<String>,
        required_keys: &[&str],
        required_values: &[(&str, &str)],
    ) -> BTreeMap<String, usize> {
        let mut by_key = BTreeMap::new();
        for (index, value) in rows.iter().enumerate() {
            let Some(object) = value.as_object() else {
                self.errors.push(format!("{label}[{index}] must be a JSON object"));
                continue;
            };
            let mut has_required_values = true;
            for key in required_keys.iter().copied() {
                if non_empty_string(object.get(key)).is_none() {
                    self.errors.push(format!("{label}[{index}].{key} must be a non-empty string"));
                }
            }
            for (key, expected) in required_values.iter().copied() {
                match non_empty_string(object.get(key)) {
                    Some(actual) if actual == expected => {}
                    Some(actual) => {
                        has_required_values = false;
                        self.metrics.rejected_entries += 1;
                        self.errors.push(format!(
                            "{label}[{index}].{key} must be {expected:?}, got {actual:?}"
                        ));
                    }
                    None => {
                        has_required_values = false;
                    }
                }
            }
            let entry_key = non_empty_string(object.get("entry_key"));
            if let Some(key) = entry_key {
                let entry_key_matches = entry_keys.contains(key);
                if !entry_key_matches {
                    self.errors.push(format!(
                        "{label}[{index}].entry_key does not match any admitted entry: {key}"
                    ));
                }
                if entry_key_matches && has_required_values {
                    *by_key.entry(key.to_string()).or_insert(0) += 1;
                }
            }
        }
        by_key
    }
}

fn non_empty_string(value: Option<&Value>) -> Option<&str> {
    value.and_then(Value::as_str).map(str::trim).filter(|s| !s.is_empty())
}

fn looks_like_sha256(value: &str) -> bool {
    let digest = value.strip_prefix("sha256:").unwrap_or(value);
    digest.len() == 64 && digest.as_bytes().iter().all(u8::is_ascii_hexdigit)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn digest(ch: char) -> String {
        format!("sha256:{}", ch.to_string().repeat(64))
    }

    fn revision(ch: char) -> String {
        ch.to_string().repeat(40)
    }

    fn valid_manifest() -> Value {
        let source_revision = revision('a');
        json!({
            "schema": PROOF_QUERY_CACHE_ADMISSION_SCHEMA,
            "version": PROOF_QUERY_CACHE_ADMISSION_VERSION,
            "policy_key": "full-verify-release-proof-cache-v1",
            "source_revision": source_revision,
            "entries": [
                {
                    "cache_key": "vc:crate::checked_add:0",
                    "content_hash": digest('1'),
                    "spec_hash": digest('2'),
                    "policy_key": "full-verify-release-proof-cache-v1",
                    "verifier": {
                        "identity": "trustc",
                        "version": "1.96.0-trust",
                        "hash": digest('3')
                    },
                    "solver": "ay",
                    "proof_mode": "chc",
                    "boundedness": {"kind": "unbounded"},
                    "source_revision": source_revision,
                    "admitted": true
                }
            ],
            "replay_rows": [
                {
                    "entry_key": "vc:crate::checked_add:0",
                    "status": "replayed",
                    "verdict": "proved"
                }
            ],
            "admission_rows": [
                {
                    "entry_key": "vc:crate::checked_add:0",
                    "decision": "admit",
                    "reason": "schema, hashes, verifier, mode, and source revision matched"
                }
            ]
        })
    }

    #[test]
    fn valid_manifest_passes_with_inspectable_metrics() {
        let report = validate_proof_query_cache_admission_json(&valid_manifest());

        assert!(report.ok(), "{:?}", report.errors);
        assert_eq!(report.metrics.entries, 1);
        assert_eq!(report.metrics.admitted_entries, 1);
        assert_eq!(report.metrics.replay_rows, 1);
        assert_eq!(report.metrics.admission_rows, 1);
        assert_eq!(report.metrics.unbounded_entries, 1);
        assert_eq!(report.metrics.spec_less_entries, 0);
    }

    #[test]
    fn missing_schema_version_is_legacy_and_fails_closed() {
        let mut manifest = valid_manifest();
        let object = manifest.as_object_mut().unwrap();
        object.remove("schema");
        object.remove("version");

        let report = validate_proof_query_cache_admission_json(&manifest);

        assert!(!report.ok());
        assert_eq!(report.metrics.legacy_entries, 1);
        assert!(
            report.errors.iter().any(|error| error.contains("missing schema/version")),
            "{:?}",
            report.errors
        );
    }

    #[test]
    fn spec_less_entry_is_rejected() {
        let mut manifest = valid_manifest();
        manifest["entries"][0]["spec_hash"] = json!("");

        let report = validate_proof_query_cache_admission_json(&manifest);

        assert!(!report.ok());
        assert_eq!(report.metrics.spec_less_entries, 1);
        assert!(
            report.errors.iter().any(|error| error.contains("entries[0].spec_hash")),
            "{:?}",
            report.errors
        );
    }

    #[test]
    fn bounded_entry_requires_depth() {
        let mut manifest = valid_manifest();
        manifest["entries"][0]["proof_mode"] = json!("bmc");
        manifest["entries"][0]["boundedness"] = json!({"kind": "bounded"});

        let report = validate_proof_query_cache_admission_json(&manifest);

        assert!(!report.ok());
        assert_eq!(report.metrics.bounded_entries, 1);
        assert!(
            report.errors.iter().any(|error| error.contains("boundedness.depth")),
            "{:?}",
            report.errors
        );
    }

    #[test]
    fn missing_replay_or_admission_rows_fail() {
        let mut manifest = valid_manifest();
        manifest["replay_rows"] = json!([]);
        manifest["admission_rows"] = json!([]);

        let report = validate_proof_query_cache_admission_json(&manifest);

        assert!(!report.ok());
        assert!(report.errors.iter().any(|error| error.contains("replay_rows")));
        assert!(report.errors.iter().any(|error| error.contains("admission_rows")));
    }

    #[test]
    fn replay_row_status_failed_is_rejected() {
        let mut manifest = valid_manifest();
        manifest["replay_rows"][0]["status"] = json!("failed");

        let report = validate_proof_query_cache_admission_json(&manifest);

        assert!(!report.ok());
        assert!(
            report
                .errors
                .iter()
                .any(|error| error.contains("replay_rows[0].status must be \"replayed\"")),
            "{:?}",
            report.errors
        );
    }

    #[test]
    fn boundedness_and_verifier_hash_counters_are_exact_on_reachable_manifests() {
        let mut manifest = valid_manifest();

        // entries[1]: bounded with depth (counts bounded_entries).
        let mut bounded = manifest["entries"][0].clone();
        bounded["cache_key"] = json!("vc:crate::checked_add:1");
        bounded["proof_mode"] = json!("bmc");
        bounded["boundedness"] = json!({"kind": "bounded", "depth": 3});

        // entries[2]: unbounded, verifier hash absent with a documented
        // reason (counts unbounded_entries and verifier_hash_missing
        // without producing an error).
        let mut hashless = manifest["entries"][0].clone();
        hashless["cache_key"] = json!("vc:crate::checked_add:2");
        hashless["verifier"] = json!({
            "identity": "trustc",
            "version": "1.96.0-trust",
            "hash_unavailable_reason": "verifier built without self-hash support"
        });

        let entries = manifest["entries"].as_array_mut().unwrap();
        entries.push(bounded);
        entries.push(hashless);
        for key in ["vc:crate::checked_add:1", "vc:crate::checked_add:2"] {
            manifest["replay_rows"].as_array_mut().unwrap().push(json!({
                "entry_key": key,
                "status": "replayed",
                "verdict": "proved"
            }));
            manifest["admission_rows"].as_array_mut().unwrap().push(json!({
                "entry_key": key,
                "decision": "admit",
                "reason": "schema, hashes, verifier, mode, and source revision matched"
            }));
        }

        let report = validate_proof_query_cache_admission_json(&manifest);

        assert!(report.ok(), "{:?}", report.errors);
        assert_eq!(report.metrics.entries, 3);
        assert_eq!(report.metrics.admitted_entries, 3);
        assert_eq!(report.metrics.bounded_entries, 1);
        assert_eq!(report.metrics.unbounded_entries, 2);
        assert_eq!(report.metrics.verifier_hash_missing, 1);
    }

    #[test]
    fn bounded_entries_counter_pins_at_usize_max() {
        let mut validator = AdmissionValidator::default();
        validator.metrics.bounded_entries = usize::MAX;

        validator.validate_boundedness(0, Some(&json!({"kind": "bounded", "depth": 1})));

        assert_eq!(validator.metrics.bounded_entries, usize::MAX);
        assert!(validator.errors.is_empty(), "{:?}", validator.errors);
    }

    #[test]
    fn unbounded_entries_counter_pins_at_usize_max() {
        let mut validator = AdmissionValidator::default();
        validator.metrics.unbounded_entries = usize::MAX;

        validator.validate_boundedness(0, Some(&json!({"kind": "unbounded"})));

        assert_eq!(validator.metrics.unbounded_entries, usize::MAX);
        assert!(validator.errors.is_empty(), "{:?}", validator.errors);
    }

    #[test]
    fn verifier_hash_missing_counter_pins_at_usize_max_and_still_fails_closed() {
        let mut validator = AdmissionValidator::default();
        validator.metrics.verifier_hash_missing = usize::MAX;

        validator.validate_verifier(
            0,
            Some(&json!({"identity": "trustc", "version": "1.96.0-trust"})),
        );

        assert_eq!(validator.metrics.verifier_hash_missing, usize::MAX);
        // Saturating the counter must not mask the independent fail-closed
        // error: hash or hash_unavailable_reason is still required.
        assert!(
            validator.errors.iter().any(|error| error.contains("verifier.hash")),
            "{:?}",
            validator.errors
        );
    }

    #[test]
    fn replay_row_verdict_unknown_is_rejected() {
        let mut manifest = valid_manifest();
        manifest["replay_rows"][0]["verdict"] = json!("unknown");

        let report = validate_proof_query_cache_admission_json(&manifest);

        assert!(!report.ok());
        assert!(
            report
                .errors
                .iter()
                .any(|error| error.contains("replay_rows[0].verdict must be \"proved\"")),
            "{:?}",
            report.errors
        );
    }
}
