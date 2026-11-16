//! Persisted proof terms are search hints, never persisted authority.
//!
//! Targo prepares a private run directory. The compiler imports only demanded
//! proof hints into a bounded, immutable session snapshot, supplies the freshly
//! generated VC, reconstructs its context, and checks an
//! imported term in the current kernel before minting a reference certificate.
//! The persisted key names the violation formula, not its old source location
//! or authority. Each consumer creates a fresh full-row lineage. Unsupported
//! families and every cache error fall back to ordinary search.

use std::collections::{BTreeSet, HashMap};
use std::path::Path;
#[cfg(test)]
use std::{
    fs::{self, OpenOptions},
    io::Write as _,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};
#[cfg(test)]
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_ir::{ProofDigest, ProofEvidence};
pub use trust_proof_session::ProofArtifactStore;
use trust_proof_session::storage::{
    DIRECTORY, MAX_SNAPSHOT_FILES, atomic_write, check_private_dir, private_dir, read_bounded,
};
#[cfg(test)]
use trust_proof_session::storage::{
    MAX_ARTIFACT_BYTES, MAX_SNAPSHOT_BYTES, atomic_write_new, proof_files,
};
use trust_types::VerificationCondition;
const MAX_SEARCH_WAIT: Duration = Duration::from_secs(120);

mod audit;
pub use audit::{AuditedProof, ReplayAudit, ReplayKind};

/// Exact full-VC data identity used while carrying a replayed proof. This is
/// neither a digest nor proof authority. Share the certifier's depth gate and
/// guarded stack before its existing full-VC serializer can recurse.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProofReplayVcIdentity(Vec<u8>);

impl ProofReplayVcIdentity {
    #[must_use]
    pub fn of(vc: &VerificationCondition) -> Option<Self> {
        let max_depth = super::vc_max_depth_within_gate(vc)?;
        if max_depth <= super::SHALLOW_CALLER_STACK_MAX_DEPTH
            || super::ON_CERTIFY_STACK.with(std::cell::Cell::get)
        {
            let out = super::ObligationIdentity::from_vc(vc).map(|id| Self(id.encoded));
            if let Some(cause) = trust_types::verify_budget::exhaustion_cause() {
                super::note_certify_stop(cause);
            }
            return out;
        }
        super::on_certify_stack(|| {
            super::ObligationIdentity::from_vc(vc).map(|id| Self(id.encoded))
        })
    }
}

struct CandidateProof {
    evidence: ProofEvidence,
    replay: Option<ReplayKind>,
}

impl CandidateProof {
    fn admit_audit(
        self,
        vc: &VerificationCondition,
        stopped: bool,
        deadline: Option<Instant>,
    ) -> AuditedProof {
        let mut audit = (!stopped && deadline.is_none_or(|at| Instant::now() < at))
            .then(|| self.replay.and_then(|kind| ReplayAudit::new(vc, &self.evidence, kind)))
            .flatten();
        if super::RUN_STOP.with(|stop| stop.get().is_some())
            || deadline.is_some_and(|at| Instant::now() >= at)
        {
            audit = None;
        }
        AuditedProof::new(self.evidence, audit)
    }
}

#[cfg(test)]
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SessionPool {
    schema: u32,
    directory: PathBuf,
}

#[cfg(test)]
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ImportBudget {
    schema: u32,
    files: usize,
    bytes: u64,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SavedProof {
    schema: u32,
    violation: Vec<u8>,
    term: Vec<u8>,
    context: Vec<u8>,
}

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

// This key selects mathematics only. It cannot grant authority for a row.
// Every hit below is rebound to the independently supplied full current VC.
fn violation_key(vc: &VerificationCondition) -> Option<Vec<u8>> {
    super::ObligationIdentity::from_violation(&vc.formula).map(|identity| identity.encoded)
}

fn filename(violation: &[u8]) -> String {
    format!("{}.json", digest(violation))
}

/// Certify a freshly generated VC, first attempting an imported proof term.
/// Cache failure is a search miss. All ordinary admission/depth/stop gates
/// still apply, and only unstopped, directly replayable proofs are exported.
#[must_use]
pub fn certify_vc_with_artifacts(vc: &VerificationCondition, root: &Path) -> Option<ProofEvidence> {
    certify_using(vc, root, |identity| super::certify_with_identity_on_stack(&vc.formula, identity))
}

/// Try only existing mathematics, before dispatching a solver. A miss never
/// starts proof search or waits for a producer. The current VC, kernel and
/// stop/deadline gates still decide whether the presented bytes are usable.
#[must_use]
pub fn replay_vc_with_artifacts_reporting_stop_until(
    vc: &VerificationCondition,
    root: &Path,
    deadline: Option<Instant>,
) -> (Option<ProofEvidence>, Option<trust_types::determinism::StopCause>) {
    let (proof, stop) = replay_candidate_reporting_stop_until(vc, root, deadline);
    (proof.map(|proof| proof.evidence), stop)
}

/// The same replay and admission gates, with a non-authority observation bound
/// to the exact returned proof. A receipt is not a final published-row result.
#[must_use]
pub fn replay_vc_with_artifacts_reporting_stop_and_audit_until(
    vc: &VerificationCondition,
    root: &Path,
    deadline: Option<Instant>,
) -> (Option<AuditedProof>, Option<trust_types::determinism::StopCause>) {
    let (proof, stop) = super::with_stop_scope(|| {
        let (proof, stop) = replay_candidate_reporting_stop_until(vc, root, deadline);
        proof.map(|proof| proof.admit_audit(vc, stop.is_some(), deadline))
    });
    (if stop.is_none() { proof } else { None }, stop)
}

fn replay_candidate_reporting_stop_until(
    vc: &VerificationCondition,
    root: &Path,
    deadline: Option<Instant>,
) -> (Option<CandidateProof>, Option<trust_types::determinism::StopCause>) {
    let (evidence, stop) = super::with_stop_scope(|| {
        if vc.kernel_authority_refusal().is_some()
            || !super::vc_within_depth_gate(vc)
            || !root.is_absolute()
            || check_private_dir(root).is_err()
        {
            return None;
        }
        super::on_certify_stack_if_needed(|| {
            super::injected_test_stop(vc);
            if deadline.is_some_and(|at| Instant::now() >= at) {
                super::note_certify_stop(trust_types::determinism::StopCause::WallBackstop);
                return None;
            }
            let identity = super::ObligationIdentity::from_vc(vc)?;
            let violation = violation_key(vc)?;
            let store = ProofArtifactStore::from_session(root);
            let evidence = replay_from_session(vc, root, &identity, &violation, store.as_ref());
            if deadline.is_some_and(|at| Instant::now() >= at) {
                super::note_certify_stop(trust_types::determinism::StopCause::WallBackstop);
                return None;
            }
            evidence
        })
    });
    (if stop.is_none() { evidence } else { None }, stop)
}

fn replay_from_session(
    vc: &VerificationCondition,
    root: &Path,
    identity: &super::ObligationIdentity,
    violation: &[u8],
    store: Option<&ProofArtifactStore>,
) -> Option<CandidateProof> {
    let directory = root.join(DIRECTORY);
    let name = filename(violation);
    if check_private_dir(&directory).is_ok()
        && check_private_dir(&directory.join("incoming")).is_ok()
    {
        if let Some(evidence) =
            replay(vc, identity, violation, &directory.join("incoming").join(&name))
        {
            return Some(evidence);
        }
    }
    store.and_then(|store| {
        let path = store.import(root, &name).ok()??;
        replay(vc, identity, violation, &path)
    })
}

fn certify_using(
    vc: &VerificationCondition,
    root: &Path,
    produce: impl FnOnce(&super::ObligationIdentity) -> Option<ProofEvidence> + Send,
) -> Option<ProofEvidence> {
    certify_using_until(vc, root, None, produce)
}

fn certify_using_until(
    vc: &VerificationCondition,
    root: &Path,
    deadline: Option<Instant>,
    produce: impl FnOnce(&super::ObligationIdentity) -> Option<ProofEvidence> + Send,
) -> Option<ProofEvidence> {
    certify_using_until_candidate(vc, root, deadline, produce).map(|proof| proof.evidence)
}

fn certify_using_until_candidate(
    vc: &VerificationCondition,
    root: &Path,
    deadline: Option<Instant>,
    produce: impl FnOnce(&super::ObligationIdentity) -> Option<ProofEvidence> + Send,
) -> Option<CandidateProof> {
    if vc.kernel_authority_refusal().is_some() || !super::vc_within_depth_gate(vc) {
        return None;
    }
    let usable_root = root.is_absolute() && check_private_dir(root).is_ok();
    super::on_certify_stack_if_needed(|| {
        super::injected_test_stop(vc);
        if deadline.is_some_and(|at| Instant::now() >= at) {
            super::note_certify_stop(trust_types::determinism::StopCause::WallBackstop);
            return None;
        }
        let identity = super::ObligationIdentity::from_vc(vc)?;
        let violation = violation_key(vc)?;
        let directory = root.join(DIRECTORY);
        let name = filename(&violation);
        let shared_store = usable_root.then(|| ProofArtifactStore::from_session(root)).flatten();
        if usable_root {
            if let Some(evidence) =
                replay_from_session(vc, root, &identity, &violation, shared_store.as_ref())
            {
                return Some(evidence);
            }
        }
        let mut shared_lease = None;
        if let Some(store) = &shared_store {
            // General/synthesized families keep their ordinary producer path.
            // Only directly supported Int conjunctions coordinate cold search.
            if eligible_shared_search(vc)
                && !super::IN_MEMO_PRODUCER.with(std::cell::Cell::get)
                && super::RUN_STOP.with(|stop| stop.get().is_none())
            {
                let now = Instant::now();
                let wait_end = now.checked_add(MAX_SEARCH_WAIT).unwrap_or(now);
                let mut backoff = Duration::from_millis(2);
                loop {
                    if deadline.is_some_and(|at| Instant::now() >= at) {
                        super::note_certify_stop(trust_types::determinism::StopCause::WallBackstop);
                        return None;
                    }
                    match store.try_search_lease(&violation) {
                        Ok(Some(lease)) => {
                            // The preceding owner may have published while we
                            // waited. A lease is ownership, never a proof.
                            if let Some(evidence) =
                                replay_from_session(vc, root, &identity, &violation, Some(store))
                            {
                                return Some(evidence);
                            }
                            shared_lease = Some(lease);
                            break;
                        }
                        Ok(None) => {
                            #[cfg(test)]
                            note_lease_wait();
                            if Instant::now() >= wait_end {
                                break;
                            }
                            let end = deadline.map_or(wait_end, |at| at.min(wait_end));
                            std::thread::sleep(
                                backoff.min(end.saturating_duration_since(Instant::now())),
                            );
                            backoff = (backoff * 2).min(Duration::from_millis(50));
                            if deadline.is_some_and(|at| Instant::now() >= at) {
                                super::note_certify_stop(
                                    trust_types::determinism::StopCause::WallBackstop,
                                );
                                return None;
                            }
                            // All waiters can check a newly published proof in
                            // parallel, without acquiring the producer lease.
                            if let Some(evidence) =
                                replay_from_session(vc, root, &identity, &violation, Some(store))
                            {
                                return Some(evidence);
                            }
                        }
                        Err(_) => break, // optional coordination unavailable
                    }
                }
            }
        }
        let (evidence, stop) = super::with_stop_scope(|| produce(&identity));
        // An earlier attempted replay (or an entry-point stop) also belongs to
        // this certification. A later successful producer cannot erase it.
        if usable_root && stop.is_none() && super::RUN_STOP.with(|stop| stop.get().is_none()) {
            if let Some(ProofEvidence::CleanCic { term, context, lineage, .. }) = &evidence {
                // Publishing a hint must not start another kernel search. The
                // producer already earned this token; this pure context check
                // only selects the family whose imported terms we can replay.
                if super::reference_mint::reference_certificate_for_parts(term, context, lineage)
                    .is_some()
                    && super::presented_artifact_context(
                        &vc.formula,
                        &identity,
                        term,
                        context,
                        lineage,
                    )
                    .is_some()
                {
                    let saved = SavedProof {
                        schema: 2,
                        violation,
                        term: term.clone(),
                        context: context.clone(),
                    };
                    if let Ok(bytes) = serde_json::to_vec(&saved) {
                        let owns_publication =
                            shared_lease.as_ref().is_none_or(|lease| lease.validate().is_ok());
                        if owns_publication {
                            if private_dir(&directory).is_ok() {
                                let _ = atomic_write(&directory.join("outgoing"), &name, &bytes);
                            }
                            if let (Some(store), Some(_lease)) = (&shared_store, &shared_lease) {
                                // This completed mathematical proof is useful
                                // even if another row later fails the program.
                                let _ = atomic_write(store.objects_directory(), &name, &bytes);
                            }
                        }
                    }
                }
            }
        }
        evidence.map(|evidence| CandidateProof { evidence, replay: None })
    })
}

/// The artifact-aware entry point with the same stop propagation as
/// `certify_vc_reporting_stop`; a hint never suppresses a recorded stop.
#[must_use]
pub fn certify_vc_with_artifacts_reporting_stop(
    vc: &VerificationCondition,
    root: &Path,
) -> (Option<ProofEvidence>, Option<trust_types::determinism::StopCause>) {
    certify_vc_with_artifacts_reporting_stop_until(vc, root, None)
}

/// As above, respecting the compiler's existing per-function deadline while
/// waiting for a shared proof-search owner.
#[must_use]
pub fn certify_vc_with_artifacts_reporting_stop_until(
    vc: &VerificationCondition,
    root: &Path,
    deadline: Option<Instant>,
) -> (Option<ProofEvidence>, Option<trust_types::determinism::StopCause>) {
    super::with_stop_scope(|| {
        certify_using_until(vc, root, deadline, |identity| {
            super::certify_with_identity_on_stack(&vc.formula, identity)
        })
    })
}

/// Preserve the certifier's evidence/stop result while carrying an observation
/// only for successful artifact replay before the original deadline. Fresh
/// production and unobserved/withdrawn replay never manufacture a hit.
#[must_use]
pub fn certify_vc_with_artifacts_reporting_stop_and_audit_until(
    vc: &VerificationCondition,
    root: &Path,
    deadline: Option<Instant>,
) -> (Option<AuditedProof>, Option<trust_types::determinism::StopCause>) {
    super::with_stop_scope(|| {
        let proof = certify_using_until_candidate(vc, root, deadline, |identity| {
            super::certify_with_identity_on_stack(&vc.formula, identity)
        });
        proof.map(|proof| {
            proof.admit_audit(vc, super::RUN_STOP.with(|stop| stop.get().is_some()), deadline)
        })
    })
}

fn eligible_shared_search(vc: &VerificationCondition) -> bool {
    if !super::branch_clamp::formula_is_well_sorted_bool(&vc.formula) {
        return false;
    }
    let mut conjuncts = Vec::new();
    super::collect_conjuncts(&vc.formula, &mut conjuncts);
    !conjuncts.is_empty()
        && conjuncts.into_iter().all(|formula| {
            let Some(atoms) = super::normalize_atom(formula) else { return false };
            let mut variables = BTreeSet::new();
            !atoms.is_empty()
                && atoms.iter().all(|atom| super::collect_int_vars(atom, &mut variables))
        })
}

#[cfg(test)]
fn note_lease_wait() {
    if let Some(path) = std::env::var_os("TRUST_TEST_PROOF_LEASE_WAITED") {
        let _ = fs::write(path, b"waiting");
    }
}

fn direct_replay(
    vc: &VerificationCondition,
    identity: &super::ObligationIdentity,
    term: &[u8],
    context: &[u8],
    lineage: &ProofDigest,
) -> bool {
    super::recheck_cleancic_with_identity_or(term, context, lineage, &vc.formula, identity, || None)
}

// Only live ReferenceAccepted-derived certificates enter this table. It is not
// serialized, and a hit never substitutes for the current row's context check.
fn checked_mathematics() -> &'static Mutex<HashMap<[u8; 32], super::ReferenceCertificate>> {
    static CHECKED: OnceLock<Mutex<HashMap<[u8; 32], super::ReferenceCertificate>>> =
        OnceLock::new();
    CHECKED.get_or_init(|| Mutex::new(HashMap::new()))
}

fn mathematics_key(term: &[u8], context: &[u8], variables: &BTreeSet<String>) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(b"trust.proof-artifact.live-mathematics.v1\0");
    for bytes in [term, context] {
        hash.update((bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
    }
    // Bind the current Int globals abstracted by the reference check as well
    // as the serialized hypotheses and proof term.
    hash.update((variables.len() as u64).to_le_bytes());
    for variable in variables {
        hash.update((variable.len() as u64).to_le_bytes());
        hash.update(variable.as_bytes());
    }
    hash.finalize().into()
}

fn replay(
    vc: &VerificationCondition,
    identity: &super::ObligationIdentity,
    violation: &[u8],
    path: &Path,
) -> Option<CandidateProof> {
    let saved: SavedProof = serde_json::from_slice(&read_bounded(path).ok()?).ok()?;
    if saved.schema != 2 || saved.violation != violation {
        return None;
    }
    // There is deliberately no saved row identity or acceptance token. The
    // current compiler supplies the row and earns its own lineage and current
    // reference-kernel certificate from the presented mathematics.
    let lineage = super::lineage_digest(&saved.term, &saved.context, identity);
    let variables = super::presented_artifact_context(
        &vc.formula,
        identity,
        &saved.term,
        &saved.context,
        &lineage,
    )?;
    let key = mathematics_key(&saved.term, &saved.context, &variables);
    let mut lock_key = b"proof-artifact-live:\0".to_vec();
    lock_key.extend_from_slice(&key);
    // Reuse the native per-key flight mechanism. Nested producers do not wait,
    // matching the certifier's existing protection against recursive cycles.
    let flight = (!super::IN_MEMO_PRODUCER.with(std::cell::Cell::get))
        .then(|| super::MemoFlight::acquire(&lock_key));
    let _ownership = flight
        .as_ref()
        .map(|flight| flight.serial.lock().unwrap_or_else(std::sync::PoisonError::into_inner));
    let evidence = ProofEvidence::CleanCic {
        term: saved.term,
        context: saved.context,
        lineage,
        kernel_recheck: None,
    };
    let cached = checked_mathematics().lock().ok().and_then(|cache| cache.get(&key).cloned());
    if let Some(certificate) = cached {
        super::reference_mint::register_evidence(&evidence, Some(&certificate));
        return super::reference_certificate_for(&evidence).map(|_| CandidateProof {
            evidence,
            replay: Some(ReplayKind::CurrentProcessReference),
        });
    }
    let ProofEvidence::CleanCic { term, context, .. } = &evidence else { return None };
    if !direct_replay(vc, identity, term, context, &lineage) {
        return None;
    }
    let certificate = super::reference_certificate_for(&evidence)?;
    if super::RUN_STOP.with(|stop| stop.get().is_none()) {
        if let Ok(mut cache) = checked_mathematics().lock() {
            if cache.len() < MAX_SNAPSHOT_FILES {
                cache.insert(key, certificate);
            }
        }
    }
    Some(CandidateProof { evidence, replay: Some(ReplayKind::CurrentKernelRecheck) })
}

#[cfg(test)]
mod tests;
