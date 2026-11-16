//! Check native WP certificates against the exact current typed input.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, OnceLock};

use serde::Deserialize;
use trust_ir::{
    NativeVerificationBundle, NativeVerificationRequest, ProofDigest, TrustWpNativeRequest,
};
use trust_verifier_api::{
    EvidenceArtifactKind, ObligationEvidence, TrustContractBundle, TrustObligation,
};
use trust_wp_lib::trust_ir_body::{TRUST_IR_BODY_WP_SCHEMA, replay_trust_ir_body_contracts};

#[derive(Debug)]
pub(super) struct NativeWpReplay {
    bundle: Arc<NativeVerificationBundle>,
    checked: ReplayChecks,
}

type ReplayKey = (String, String, u32, u32);

#[derive(Debug, Default)]
struct ReplayChecks {
    entries: Mutex<BTreeMap<ReplayKey, Arc<OnceLock<bool>>>>,
}

impl ReplayChecks {
    fn check(&self, key: ReplayKey, replay: impl FnOnce() -> bool) -> bool {
        let result = {
            let Ok(mut entries) = self.entries.lock() else { return false };
            Arc::clone(entries.entry(key).or_default())
        };
        // A repeated exact question shares its completed check. Independent
        // questions can replay concurrently; no map lock covers a solver call.
        *result.get_or_init(|| {
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(replay)).unwrap_or(false)
        })
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Certificate {
    statement: Statement,
    replay: String,
    accepted: bool,
    authority: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Statement {
    schema: String,
    bundle_id: String,
    obligation_id: String,
    request: TrustWpNativeRequest,
    module_digest: ProofDigest,
    source_digest: Option<ProofDigest>,
    results: Vec<trust_wp_lib::VerifyBundleResult>,
}

impl NativeWpReplay {
    pub(super) fn new(bundle: &NativeVerificationBundle) -> Self {
        Self { bundle: Arc::new(bundle.clone()), checked: ReplayChecks::default() }
    }

    pub(super) fn checked_proof(
        &self,
        public: &TrustContractBundle,
        obligation: &TrustObligation,
        evidence: &ObligationEvidence,
        request_id: u32,
        proof_id: u32,
    ) -> Option<super::CheckedNativeWpProof> {
        if !self.accepts(public, obligation, evidence, request_id, proof_id) {
            return None;
        }
        let digest = public.canonical_obligation_semantic_digest_sha256(obligation).ok()?;
        super::CheckedNativeWpProof::new(
            Arc::clone(&self.bundle),
            digest,
            evidence,
            request_id,
            proof_id,
        )
    }

    pub(super) fn accepts(
        &self,
        public: &TrustContractBundle,
        obligation: &TrustObligation,
        evidence: &ObligationEvidence,
        request_id: u32,
        proof_id: u32,
    ) -> bool {
        let Some(proof) =
            self.bundle.module.proof_obligations.iter().find(|proof| proof.id.index() == proof_id)
        else {
            return false;
        };
        // Transport bindings are deliberately outside the logical claim
        // digest. Check them on every call, including a warm proof-cache hit.
        if trust_verifier_api::native_contract_claim::validate_native_public_module_binding(
            &self.bundle.module,
            proof,
            obligation,
        )
        .is_err()
        {
            return false;
        }
        let mut certificates = evidence
            .artifacts
            .iter()
            .filter(|artifact| artifact.kind == EvidenceArtifactKind::ProofCertificate);
        let Some(artifact) = certificates.next() else { return false };
        if certificates.next().is_some() {
            return false;
        }
        let Some(materialization) = artifact.materialization.as_ref() else { return false };
        if !materialization.matches_hash(&artifact.hash) {
            return false;
        }
        let Some(bytes) =
            materialization.bound_payload_bytes(artifact.kind, &obligation.obligation_id)
        else {
            return false;
        };
        let Ok(public_digest) = public.canonical_obligation_semantic_digest_sha256(obligation)
        else {
            return false;
        };
        // The enclosing index owns one immutable native input. Bind memoized
        // checks to both exact certificate bytes and the complete public claim.
        let key = (artifact.hash.value.clone(), public_digest, request_id, proof_id);
        self.checked.check(key, || self.check(bytes, public, obligation, request_id, proof_id))
    }

    fn check(
        &self,
        bytes: &[u8],
        public: &TrustContractBundle,
        obligation: &TrustObligation,
        request_id: u32,
        proof_id: u32,
    ) -> bool {
        let Ok(certificate) = serde_json::from_slice::<Certificate>(bytes) else { return false };
        let statement = certificate.statement;
        if !certificate.accepted
            || certificate.replay
                != "rederive WP from original typed body and contract; replay native pure evidence"
            || certificate.authority != "Trusted; not Clean-kernel certified"
            || statement.schema != TRUST_IR_BODY_WP_SCHEMA
            || statement.bundle_id != public.bundle_id
            || statement.obligation_id != obligation.obligation_id
            || statement.module_digest != self.bundle.trust_ir_module_digest
            || statement.source_digest != self.bundle.provenance.source_digest
            || statement.results.len() != 1
            || statement.results[0].status != trust_wp_lib::VerifyBundleStatus::Verified
            || statement.request.id.index() != request_id
            || statement.request.obligations != [trust_ir::ProofId::new(proof_id)]
        {
            return false;
        }
        let Some(proof) =
            self.bundle.module.proof_obligations.iter().find(|proof| proof.id.index() == proof_id)
        else {
            return false;
        };
        if super::validate_public_claim(&self.bundle.module, Some(proof), public, obligation)
            .is_err()
        {
            return false;
        }
        if !self.bundle.requests.iter().any(|request| {
            matches!(request, NativeVerificationRequest::TrustWp(native) if native == &statement.request)
        }) {
            return false;
        }
        let mut scoped = self.bundle.as_ref().clone();
        scoped.requests.retain(|request| {
            matches!(request, NativeVerificationRequest::TrustWp(native) if native == &statement.request)
        });
        replay_trust_ir_body_contracts(&scoped, &statement.results).is_ok()
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Barrier, mpsc};
    use std::time::Duration;

    use super::*;

    fn key() -> ReplayKey {
        ("certificate".into(), "public-claim".into(), 1, 2)
    }

    #[test]
    fn independent_native_wp_replays_do_not_wait_for_another_question() {
        let checks = Arc::new(ReplayChecks::default());
        let first = Arc::clone(&checks);
        let (started, start) = mpsc::channel();
        let (release, released) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            first.check(key(), || {
                started.send(()).unwrap();
                released.recv_timeout(Duration::from_secs(30)).unwrap();
                true
            })
        });
        start.recv_timeout(Duration::from_secs(30)).unwrap();
        let mut other = key();
        other.3 += 1;
        // This must complete while the first replay still waits for release.
        let second = checks.check(other, || true);
        let released = release.send(()).is_ok();
        let first = worker.join().unwrap();
        assert!(second && released && first);
    }

    #[test]
    fn concurrent_exact_native_wp_questions_replay_once() {
        let checks = Arc::new(ReplayChecks::default());
        let calls = AtomicUsize::new(0);
        let ready = Barrier::new(8);
        std::thread::scope(|scope| {
            for _ in 0..8 {
                let checks = &checks;
                let calls = &calls;
                let ready = &ready;
                scope.spawn(move || {
                    ready.wait();
                    assert!(checks.check(key(), || {
                        calls.fetch_add(1, Ordering::Relaxed);
                        true
                    }));
                });
            }
        });
        assert_eq!(calls.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn native_wp_replay_panics_remain_cached_refusals() {
        let checks = ReplayChecks::default();
        assert!(!checks.check(key(), || panic!("failed replay")));
        assert!(!checks.check(key(), || true));
        let mut other = key();
        other.0.push_str("-different");
        assert!(checks.check(other, || true));
    }
}
