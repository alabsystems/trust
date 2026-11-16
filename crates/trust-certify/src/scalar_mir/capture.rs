//! Session-local diagnostic interchange, never a source/proof capability.
//! rustc's private borrowed-body wrapper creates pairs; the direct producer
//! consumes them by its exact DefIndex→FuncId assembly mapping. Public data
//! here is deliberately not accepted by any compiler authority constructor.

use std::collections::BTreeMap;
use std::sync::Arc;

use super::ScalarMirBody;

pub const MAX_SOURCE_PAYLOAD_BYTES: usize = 8 * 1024 * 1024;
pub const MAX_BODY_PAYLOAD_BYTES: usize = 8 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ScalarSourceIdentity {
    pub file_name: String,
    pub stable_source_id: String,
    pub original_source_hash: String,
    pub normalized_source_hash: String,
}

#[derive(Clone, PartialEq, Eq)]
pub struct ScalarSourceObservation {
    pub identity: ScalarSourceIdentity,
    pub normalized_source: Arc<str>,
    pub body_span: String,
}

impl std::fmt::Debug for ScalarSourceObservation {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // The complete bytes are retained ONCE in the registry's source table.
        // Per-body debug payloads refer to that exact identity, not another
        // copy of the same source file for every pass input and output.
        out.debug_struct("ScalarSourceObservation")
            .field("identity", &self.identity)
            .field("normalized_source_bytes", &self.normalized_source.len())
            .field("body_span", &self.body_span)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct ScalarBodyObservation {
    pub identity: String,
    pub full_debug_body: String,
    pub field_accounting: Vec<(&'static str, &'static str)>,
    pub source: Result<ScalarSourceObservation, String>,
    pub model: Result<ScalarMirBody, String>,
}

#[derive(Clone, Debug)]
pub struct ScalarPassObservation {
    pub sequence: u64,
    pub def_path_hash: String,
    pub before: ScalarBodyObservation,
    pub after: Option<ScalarBodyObservation>,
    pub pair_error: Option<String>,
}

#[derive(Default)]
pub struct ScalarCaptureRegistry {
    pub next_sequence: u64,
    pub records: BTreeMap<u32, Vec<ScalarPassObservation>>,
    pub sources: BTreeMap<ScalarSourceIdentity, Arc<str>>,
    pub retained_source_bytes: usize,
    pub retained_body_bytes: usize,
}

impl ScalarCaptureRegistry {
    pub fn intern_source(
        &mut self,
        identity: ScalarSourceIdentity,
        bytes: &str,
        body_span: String,
    ) -> Result<ScalarSourceObservation, String> {
        let retained = if let Some(existing) = self.sources.get(&identity) {
            if existing.as_ref() != bytes {
                return Err("same source identity has different exact bytes".into());
            }
            existing.clone()
        } else {
            let size = bytes
                .len()
                .saturating_add(identity.file_name.len())
                .saturating_add(identity.stable_source_id.len())
                .saturating_add(identity.original_source_hash.len())
                .saturating_add(identity.normalized_source_hash.len());
            if trust_types::audit_ledger::cap_hit_if(
                size > MAX_SOURCE_PAYLOAD_BYTES.saturating_sub(self.retained_source_bytes),
                "crates/trust-certify/src/scalar_mir/capture.rs:MAX_SOURCE_PAYLOAD_BYTES",
            ) {
                return Err("aggregate normalized-source payload budget exhausted".into());
            }
            let retained: Arc<str> = bytes.into();
            self.sources.insert(identity.clone(), retained.clone());
            self.retained_source_bytes += size;
            retained
        };
        Ok(ScalarSourceObservation { identity, normalized_source: retained, body_span })
    }

    /// Limit variable-size body payloads, not the identity census. On refusal
    /// the caller must still record this before/after occurrence and its reason.
    pub fn retain_body(&mut self, mut body: ScalarBodyObservation) -> ScalarBodyObservation {
        let mut size = body.identity.len().saturating_add(body.full_debug_body.len());
        if let Ok(source) = &body.source {
            for value in [
                &source.identity.file_name,
                &source.identity.stable_source_id,
                &source.identity.original_source_hash,
                &source.identity.normalized_source_hash,
                &source.body_span,
            ] {
                size = size.saturating_add(value.len());
            }
        }
        if trust_types::audit_ledger::cap_hit_if(
            size > MAX_BODY_PAYLOAD_BYTES.saturating_sub(self.retained_body_bytes),
            "crates/trust-certify/src/scalar_mir/capture.rs:MAX_BODY_PAYLOAD_BYTES",
        ) {
            let reason = "aggregate body payload budget exhausted; identity occurrence retained";
            // Drop the allocation too; clear() alone retains its capacity in
            // every refused row and would defeat the aggregate payload bound.
            body.full_debug_body = String::new();
            body.source = Err(reason.into());
            body.model = Err(reason.into());
        } else {
            self.retained_body_bytes += size;
        }
        body
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source_identity() -> ScalarSourceIdentity {
        ScalarSourceIdentity {
            file_name: "fixture.rs".into(),
            stable_source_id: "file".into(),
            original_source_hash: "original".into(),
            normalized_source_hash: "normalized".into(),
        }
    }

    #[test]
    fn source_pool_shares_exact_bytes_and_refuses_identity_or_budget_substitution() {
        let mut pool = ScalarCaptureRegistry::default();
        let first = pool.intern_source(source_identity(), "source", "span1".into()).unwrap();
        let bytes = pool.retained_source_bytes;
        let second = pool.intern_source(source_identity(), "source", "span2".into()).unwrap();
        assert!(Arc::ptr_eq(&first.normalized_source, &second.normalized_source));
        assert_eq!(pool.retained_source_bytes, bytes);
        assert_eq!(pool.sources.len(), 1);
        assert_ne!(first.body_span, second.body_span);
        assert!(pool.intern_source(source_identity(), "changed", "span".into()).is_err());
        assert_eq!(pool.retained_source_bytes, bytes);
        pool.retained_source_bytes = MAX_SOURCE_PAYLOAD_BYTES;
        assert!(pool.intern_source(source_identity(), "source", "span3".into()).is_ok());
        let mut different = source_identity();
        different.stable_source_id.push('x');
        assert!(pool.intern_source(different, "source", "span".into()).is_err());
        assert_eq!(pool.sources.len(), 1);
    }

    #[test]
    fn exhausted_body_payload_does_not_suppress_the_recordable_occurrence() {
        let mut pool = ScalarCaptureRegistry::default();
        pool.retained_body_bytes = MAX_BODY_PAYLOAD_BYTES;
        let body = ScalarBodyObservation {
            identity: "actual item/phase/pass".into(),
            full_debug_body: "actual body".into(),
            field_accounting: vec![],
            source: Err("not loaded".into()),
            model: Ok(super::super::successor_before()),
        };
        let refused = pool.retain_body(body);
        assert_eq!(refused.identity, "actual item/phase/pass");
        assert!(refused.full_debug_body.is_empty());
        assert_eq!(refused.full_debug_body.capacity(), 0);
        assert!(refused.source.is_err());
        assert!(refused.model.is_err());
        pool.records.entry(7).or_default().push(ScalarPassObservation {
            sequence: 1,
            def_path_hash: "exact def".into(),
            before: refused,
            after: None,
            pair_error: None,
        });
        assert_eq!(pool.records[&7].len(), 1);
        assert_eq!(pool.retained_body_bytes, MAX_BODY_PAYLOAD_BYTES);
    }
}
