// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Untrusted VF5 annotation/certificate hints in the existing private proof
//! session. No certificate, environment, row, verdict or producer grade is
//! deserialized. Every hit is checked against the CURRENT artifact, function
//! and symbol through the original `RowProved` judgment and reference kernel.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::Expr;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_proof_session::ProofArtifactStore;
use trust_proof_session::storage::{
    DIRECTORY, MAX_ARTIFACT_BYTES, MAX_SNAPSHOT_BYTES, MAX_SNAPSHOT_FILES,
    check_private_dir, read_bounded,
};
use trust_types::determinism::StopCause;

use super::{CalculusRowCertificate, CalculusRowClaim, CalculusRowMiss, Vf5Reference};

const DOMAIN: &[u8] = b"trust.vf5.module-hints.v1\0";

/// A fresh reference-checked judgment for the late reporting lane. It cannot
/// be converted into the legacy globally registerable certificate, cloned or
/// deserialized. The ordinary compiler may consume it only for the current
/// artifact-bound final policy/report, leaving its eager caller/optimizer
/// facts and cached verdicts unchanged. Stopped replay returns no token.
#[derive(Debug)]
pub struct CheckedPresentation {
    certificate: CalculusRowCertificate,
    goal: Expr,
    proof: Expr,
    annotation: Expr,
    certificates: Expr,
}

impl CheckedPresentation {
    #[must_use]
    pub fn matches_claim(&self, claim: &CalculusRowClaim) -> bool {
        self.certificate.fid() == claim.fid
            && self.certificate.binds_symbol(&claim.symbol)
            && self.certificate.binds_artifact(&claim.artifact)
    }

    /// Data identifying the genuinely checked judgment, not a constructor or
    /// a serialized source of proof authority.
    #[must_use]
    pub fn artifact_sha256(&self) -> [u8; 32] { self.certificate.artifact_sha256() }

    #[must_use]
    pub fn fid(&self) -> u64 { self.certificate.fid() }

    #[must_use]
    pub fn symbol(&self) -> &[u8] { self.certificate.symbol() }

    #[must_use]
    pub fn environment_sha256(&self) -> [u8; 32] { self.certificate.reference().env_digest().0 }

    #[must_use]
    pub fn statement_sha256(&self) -> [u8; 32] { self.certificate.reference().decl_digest() }

    /// The exact mathematical data passed to the fenced checker, not a
    /// favorable precomputed report placeholder. Borrowing it cannot recover
    /// the legacy registerable certificate stored privately in this token.
    #[must_use]
    pub fn goal(&self) -> &Expr { &self.goal }

    #[must_use]
    pub fn proof(&self) -> &Expr { &self.proof }

    #[must_use]
    pub fn annotation(&self) -> &Expr { &self.annotation }

    #[must_use]
    pub fn certificates(&self) -> &Expr { &self.certificates }
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SavedHints {
    schema: u32,
    artifact_sha256: String,
    // Reuse Clean's bounded, canonical term codec. These are mathematical
    // proposals, not CertifiedPayloads or accepted reference certificates.
    annotation: Vec<u8>,
    certificates: Vec<u8>,
}

/// Intake/identity/codec failures stay distinct from a real row judgment's
/// typed kernel refusal. Neither is a counterexample or a favorable verdict.
#[derive(Debug)]
pub enum Vf5HintMiss {
    NoHint,
    Io(std::io::Error),
    Envelope(serde_json::Error),
    Invalid(&'static str),
    SnapshotRefused(String),
    Term(String),
    Stopped(StopCause),
    Row(CalculusRowMiss),
}

/// The existing proof store's exact-key shape, separated from formula proofs
/// and other protocols. This is a lookup key only, never row authority.
#[must_use]
pub fn filename(artifact: &[u8]) -> String {
    let mut digest = Sha256::new();
    digest.update(DOMAIN);
    digest.update(Sha256::digest(artifact));
    format!("{:x}.json", digest.finalize())
}

/// Encode ONLY an untrusted producer's mathematical proposal. Publishing
/// these bytes confers no row authority and cannot alter a base pin.
pub fn encode(
    artifact: &[u8],
    annotation: &Expr,
    certificates: &Expr,
) -> Result<Vec<u8>, Vf5HintMiss> {
    if artifact.is_empty() {
        return Err(Vf5HintMiss::Invalid("empty artifact"));
    }
    let hints = SavedHints {
        schema: 1,
        artifact_sha256: format!("{:x}", Sha256::digest(artifact)),
        annotation: serialize_term(annotation).map_err(|error| Vf5HintMiss::Term(format!("{error:?}")))?,
        certificates: serialize_term(certificates)
            .map_err(|error| Vf5HintMiss::Term(format!("{error:?}")))?,
    };
    let bytes = serde_json::to_vec(&hints).map_err(Vf5HintMiss::Envelope)?;
    if bytes.len() as u64 > MAX_ARTIFACT_BYTES {
        return Err(Vf5HintMiss::Invalid("oversized hint envelope"));
    }
    Ok(bytes)
}

pub(super) fn decode(artifact: &[u8], bytes: &[u8]) -> Result<(Expr, Expr), Vf5HintMiss> {
    if bytes.len() as u64 > MAX_ARTIFACT_BYTES {
        return Err(Vf5HintMiss::Invalid("oversized hint envelope"));
    }
    let hints: SavedHints = serde_json::from_slice(bytes).map_err(Vf5HintMiss::Envelope)?;
    if artifact.is_empty()
        || hints.schema != 1
        || hints.artifact_sha256 != format!("{:x}", Sha256::digest(artifact))
    {
        return Err(Vf5HintMiss::Invalid("unsupported schema or changed artifact identity"));
    }
    let annotation = deserialize_term(&hints.annotation)
        .map_err(|error| Vf5HintMiss::Term(format!("{error:?}")))?;
    let certificates = deserialize_term(&hints.certificates)
        .map_err(|error| Vf5HintMiss::Term(format!("{error:?}")))?;
    Ok((annotation, certificates))
}

fn read_snapshot(root: &Path, artifact: &[u8]) -> Result<Vec<u8>, Vf5HintMiss> {
    if !root.is_absolute() {
        return Err(Vf5HintMiss::Invalid("proof session root is not absolute"));
    }
    check_private_dir(root).map_err(Vf5HintMiss::Io)?;
    let directory = root.join(DIRECTORY);
    check_private_dir(&directory).map_err(Vf5HintMiss::Io)?;
    let incoming = directory.join("incoming");
    check_private_dir(&incoming).map_err(Vf5HintMiss::Io)?;
    let name = filename(artifact);
    let path = incoming.join(&name);
    match std::fs::symlink_metadata(&path) {
        Ok(_) => read_bounded(&path).map_err(Vf5HintMiss::Io),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            let store = ProofArtifactStore::from_session(root).ok_or(Vf5HintMiss::NoHint)?;
            let path = store.import(root, &name).map_err(Vf5HintMiss::Io)?
                .ok_or(Vf5HintMiss::NoHint)?;
            read_bounded(&path).map_err(Vf5HintMiss::Io)
        }
        Err(error) => Err(Vf5HintMiss::Io(error)),
    }
}

enum Snapshot {
    Bytes(Arc<[u8]>),
    Refused(String),
}

#[derive(Default)]
struct Snapshots {
    entries: HashMap<String, Snapshot>,
    bytes: u64,
}

/// One compiler/session owner retains one approved immutable base and the
/// first actual hint bytes (or refusal) per demanded artifact. Keeping a
/// private pathname alone would NOT freeze later writes to that file.
pub struct Vf5HintSession {
    reference: Vf5Reference,
    root: PathBuf,
    snapshots: Mutex<Snapshots>,
}

impl Vf5HintSession {
    /// `reference` already passed the production pin fence. This constructor
    /// neither imports a base nor creates native/session resource authority.
    pub fn new(reference: Vf5Reference, root: &Path) -> Result<Self, Vf5HintMiss> {
        if !root.is_absolute() {
            return Err(Vf5HintMiss::Invalid("proof session root is not absolute"));
        }
        check_private_dir(root).map_err(Vf5HintMiss::Io)?;
        Ok(Self { reference, root: root.to_owned(), snapshots: Mutex::default() })
    }

    fn snapshot(&self, artifact: &[u8]) -> Result<Arc<[u8]>, Vf5HintMiss> {
        let name = filename(artifact);
        let mut snapshots = self.snapshots.lock()
            .map_err(|_| Vf5HintMiss::Invalid("hint snapshot lock poisoned"))?;
        if let Some(snapshot) = snapshots.entries.get(&name) {
            return match snapshot {
                Snapshot::Bytes(bytes) => Ok(Arc::clone(bytes)),
                Snapshot::Refused(reason) => Err(Vf5HintMiss::SnapshotRefused(reason.clone())),
            };
        }
        if snapshots.entries.len() >= MAX_SNAPSHOT_FILES {
            return Err(Vf5HintMiss::Invalid("hint snapshot population exceeds session bound"));
        }
        let bytes = read_snapshot(&self.root, artifact).and_then(|bytes| {
            snapshots.bytes = snapshots.bytes.checked_add(bytes.len() as u64)
                .filter(|count| *count <= MAX_SNAPSHOT_BYTES)
                .ok_or(Vf5HintMiss::Invalid("hint bytes exceed session bound"))?;
            Ok(Arc::<[u8]>::from(bytes))
        });
        match bytes {
            Ok(bytes) => {
                snapshots.entries.insert(name, Snapshot::Bytes(Arc::clone(&bytes)));
                Ok(bytes)
            }
            Err(error) => {
                snapshots.entries.insert(name, Snapshot::Refused(format!("{error:?}")));
                Err(error)
            }
        }
    }

    /// Replay a demanded mathematical hint. `claim` is supplied from the
    /// caller's actual published module; the kernel checks fid/symbol against
    /// the artifact's OWN decoded function. Each row is genuinely checked,
    /// even when the immutable proposal bytes were already consumed.
    ///
    /// No search, producer wait, snapshot refresh, row registration, grade
    /// selection or deadline extension occurs. Misses leave ordinary checks
    /// and refusals in force.
    pub fn replay(
        &self,
        claim: &CalculusRowClaim,
        deadline: Option<Instant>,
    ) -> Result<CheckedPresentation, Vf5HintMiss> {
        check_deadline()?;
        let (result, stop) = crate::with_stop_scope(|| {
            let result = clean_kernel::tc::run_until(deadline, || {
                check_deadline()?;
                let bytes = self.snapshot(&claim.artifact)?;
                let (annotation, certificates) = decode(&claim.artifact, &bytes)?;
                let checked = super::certify_calculus_judgment(
                    &self.reference, claim, &annotation, &certificates,
                ).map_err(Vf5HintMiss::Row)?;
                check_deadline()?;
                Ok((checked, annotation, certificates))
            })
            .unwrap_or(Err(Vf5HintMiss::Stopped(StopCause::WallBackstop)));
            if let Err(Vf5HintMiss::Stopped(stop)) = &result {
                crate::note_certify_stop(*stop);
            }
            result
        });
        #[cfg(test)]
        tests::before_presentation(result.is_ok() && stop.is_none());
        match stop {
            Some(stop) => Err(Vf5HintMiss::Stopped(stop)),
            None => {
                // The Trust scope can expire after the inner kernel/scope
                // bookend. Recheck currentness before and after presentation
                // construction under the SAME explicit/earlier Clean deadline.
                let result = clean_kernel::tc::run_until(deadline, || {
                    check_deadline()?;
                    let presentation = result.map(|(checked, annotation, certificates)| CheckedPresentation {
                        certificate: checked.certificate, goal: checked.goal, proof: checked.proof,
                        annotation, certificates,
                    })?;
                    check_deadline()?;
                    Ok(presentation)
                }).unwrap_or(Err(Vf5HintMiss::Stopped(StopCause::WallBackstop)));
                if let Err(Vf5HintMiss::Stopped(stop)) = &result {
                    crate::note_certify_stop(*stop);
                }
                result
            }
        }
    }
}

fn check_deadline() -> Result<(), Vf5HintMiss> {
    // Reuse the base's non-charging Trust-step/clock and Clean checkpoint.
    // Its canonical read-only observation classifies an unpolled spent scope;
    // it neither charges a traversal step nor renews an inherited deadline.
    if let Some(stop) = super::base::preparation_stop() {
        Err(Vf5HintMiss::Stopped(stop))
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(unix)]
    use std::os::unix::fs::PermissionsExt;

    #[derive(Clone, Copy)]
    enum CompletionStop { Steps, Clock }

    thread_local! {
        static COMPLETION_STOP: std::cell::Cell<Option<CompletionStop>> = const { std::cell::Cell::new(None) };
        static COMPLETION_GUARD: std::cell::RefCell<Option<trust_types::verify_budget::VerifyBudgetGuard>> = const { std::cell::RefCell::new(None) };
    }

    // Test-only injection after the real private kernel judgment and normal
    // stop-scope exit, before any CheckedPresentation is returned. Install an
    // actual ambient Trust scope here; never synthesize a trip or pre-poll it.
    pub(super) fn before_presentation(completed: bool) {
        let Some(stop) = COMPLETION_STOP.with(std::cell::Cell::take) else { return; };
        assert!(completed, "completion control requires an actual accepted kernel judgment");
        assert_eq!(trust_types::verify_budget::exhaustion_cause(), None);
        let guard = match stop {
            CompletionStop::Steps => trust_types::verify_budget::VerifyBudgetGuard::install(None, 0),
            CompletionStop::Clock => trust_types::verify_budget::VerifyBudgetGuard::install(
                Some(Instant::now() - std::time::Duration::from_secs(1)), u64::MAX,
            ),
        };
        assert_eq!(trust_types::verify_budget::exhaustion_cause(), None);
        COMPLETION_GUARD.with(|held| {
            assert!(held.borrow().is_none());
            *held.borrow_mut() = Some(guard);
        });
    }

    struct CompletionHook;
    impl Drop for CompletionHook {
        fn drop(&mut self) {
            COMPLETION_STOP.with(|stop| stop.set(None));
            let guard = COMPLETION_GUARD.with(|held| held.borrow_mut().take());
            drop(guard);
        }
    }
    fn completion_stop(stop: CompletionStop) -> CompletionHook {
        COMPLETION_STOP.with(|pending| {
            assert!(pending.get().is_none());
            pending.set(Some(stop));
        });
        CompletionHook
    }

    #[test]
    fn proposal_roundtrip_is_bound_to_exact_artifact() {
        // Codec/identity test only: these expressions are not a VF5 proof.
        let annotation = Expr::nat_lit(3);
        let certificates = Expr::nat_lit(5);
        let bytes = encode(b"actual artifact", &annotation, &certificates).unwrap();
        assert_eq!(decode(b"actual artifact", &bytes).unwrap(), (annotation, certificates));
        assert!(matches!(decode(b"changed artifact", &bytes), Err(Vf5HintMiss::Invalid(_))));
        assert_ne!(filename(b"actual artifact"), filename(b"changed artifact"));
        assert_ne!(filename(b"actual artifact"), format!("{:x}.json", Sha256::digest(b"actual artifact")));
    }

    #[test]
    fn hints_cannot_deserialize_a_grade_or_noncanonical_term() {
        let bytes = encode(b"actual artifact", &Expr::nat_lit(3), &Expr::nat_lit(5)).unwrap();
        let mut hints: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        hints["grade"] = serde_json::json!("CalculusRowProved");
        assert!(matches!(decode(b"actual artifact", &serde_json::to_vec(&hints).unwrap()), Err(Vf5HintMiss::Envelope(_))));
        let mut hints: SavedHints = serde_json::from_slice(&bytes).unwrap();
        hints.annotation.push(0);
        assert!(matches!(decode(b"actual artifact", &serde_json::to_vec(&hints).unwrap()), Err(Vf5HintMiss::Term(_))));
    }

    fn fixture(bytes: Option<&[u8]>) -> (tempfile::TempDir, Vf5HintSession, CalculusRowClaim) {
        #[cfg(unix)]
        let directory = tempfile::Builder::new()
            .permissions(std::fs::Permissions::from_mode(0o700))
            .tempdir().unwrap();
        #[cfg(not(unix))]
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        #[cfg(unix)]
        assert_eq!(std::fs::metadata(root).unwrap().permissions().mode() & 0o777, 0o700,
            "owned hint fixture root must be private at creation");
        trust_proof_session::storage::private_dir(root).unwrap();
        trust_proof_session::storage::private_dir(&root.join(DIRECTORY)).unwrap();
        let incoming = root.join(DIRECTORY).join("incoming");
        trust_proof_session::storage::private_dir(&incoming).unwrap();
        let claim = CalculusRowClaim { artifact: vec![1], fid: 0, symbol: b"hint-control".to_vec() };
        let good = encode(&claim.artifact, &Expr::nat_lit(0), &Expr::nat_lit(0)).unwrap();
        std::fs::write(incoming.join(filename(&claim.artifact)), bytes.unwrap_or(&good)).unwrap();
        // Existing cfg(test)-only stand-in: these tests cover cache/deadline
        // mechanics, NOT the real VF5 calculus or production pin admission.
        let session = Vf5HintSession::new(super::super::test_support::pinned_toy(true), root).unwrap();
        (directory, session, claim)
    }

    #[test]
    fn actual_replay_respects_inherited_earlier_deadline_and_existing_stop() {
        let (_directory, session, claim) = fixture(None);
        assert!(session.replay(&claim, None).is_ok(), "unstopped paired control");
        let mut stopped = false;
        let _outer = clean_kernel::tc::run_until(Some(Instant::now()), || {
            stopped = matches!(
                session.replay(&claim, Some(Instant::now() + std::time::Duration::from_secs(60))),
                Err(Vf5HintMiss::Stopped(StopCause::WallBackstop))
            );
        });
        assert!(stopped, "later explicit deadline cannot renew expired outer");
        let (_, stop) = crate::with_stop_scope(|| {
            crate::note_certify_stop(StopCause::WallBackstop);
            assert!(matches!(session.replay(&claim, None), Err(Vf5HintMiss::Stopped(_))));
        });
        assert_eq!(stop, Some(StopCause::WallBackstop));
    }

    #[test]
    fn hint_replay_refuses_unpolled_spent_step_budget() {
        let (_directory, session, claim) = fixture(None);
        assert!(session.replay(&claim, None).is_ok(), "unstopped paired control");
        let _guard = trust_types::verify_budget::VerifyBudgetGuard::install(None, 0);
        assert_eq!(trust_types::verify_budget::exhaustion_cause(), None);
        assert!(matches!(session.replay(&claim, None),
            Err(Vf5HintMiss::Stopped(StopCause::Steps))));
    }

    #[test]
    fn hint_replay_refuses_unpolled_expired_trust_deadline() {
        let (_directory, session, claim) = fixture(None);
        assert!(session.replay(&claim, None).is_ok(), "unstopped paired control");
        let expired = Instant::now() - std::time::Duration::from_secs(1);
        let _guard = trust_types::verify_budget::VerifyBudgetGuard::install(Some(expired), u64::MAX);
        assert_eq!(trust_types::verify_budget::exhaustion_cause(), None);
        let later = Instant::now() + std::time::Duration::from_secs(60);
        assert!(matches!(session.replay(&claim, Some(later)),
            Err(Vf5HintMiss::Stopped(StopCause::WallBackstop))));
    }

    #[test]
    fn hint_replay_completion_refuses_unpolled_spent_step_budget() {
        let (_directory, session, claim) = fixture(None);
        assert!(session.replay(&claim, None).is_ok(), "unstopped paired control");
        assert_eq!(trust_types::verify_budget::exhaustion_cause(), None);
        let _hook = completion_stop(CompletionStop::Steps);
        assert!(matches!(session.replay(&claim, None),
            Err(Vf5HintMiss::Stopped(StopCause::Steps))));
        assert!(COMPLETION_GUARD.with(|held| held.borrow().is_some()), "actual completion hook ran");
    }

    #[test]
    fn hint_replay_completion_refuses_unpolled_expired_trust_deadline() {
        let (_directory, session, claim) = fixture(None);
        assert!(session.replay(&claim, None).is_ok(), "unstopped paired control");
        assert_eq!(trust_types::verify_budget::exhaustion_cause(), None);
        let _hook = completion_stop(CompletionStop::Clock);
        let later = Instant::now() + std::time::Duration::from_secs(60);
        assert!(matches!(session.replay(&claim, Some(later)),
            Err(Vf5HintMiss::Stopped(StopCause::WallBackstop))));
        assert!(COMPLETION_GUARD.with(|held| held.borrow().is_some()), "actual completion hook ran");
    }

    #[test]
    fn hint_replay_checkpoints_do_not_charge_trust_steps() {
        let (_directory, session, claim) = fixture(None);
        assert!(session.replay(&claim, None).is_ok(), "unstopped paired control");
        let _guard = trust_types::verify_budget::VerifyBudgetGuard::install(None, 1);
        for _ in 0..4 {
            assert!(session.replay(&claim, None).is_ok());
            assert_eq!(trust_types::verify_budget::exhaustion_cause(), None);
        }
        // The first actual traversal charge still owns the original step.
        // This poll occurs only AFTER every replay in this positive control.
        assert!(!trust_types::verify_budget::budget_exhausted());
        assert_eq!(trust_types::verify_budget::exhaustion_cause(), None);
    }

    #[test]
    fn checked_presentation_is_current_claim_only_and_never_enters_legacy_registry() {
        let (_directory, session, mut claim) = fixture(None);
        claim.symbol = b"isolated-hint-presentation-control".to_vec();
        assert!(super::super::calculus_row_certificate_for(&claim.symbol).is_none());
        let token = session.replay(&claim, None).unwrap();
        assert!(token.matches_claim(&claim));
        assert_eq!(token.fid(), claim.fid);
        assert_eq!(token.symbol(), claim.symbol);
        assert_eq!(token.annotation(), &Expr::nat_lit(0));
        assert_eq!(token.certificates(), &Expr::nat_lit(0));
        let (goal, proof) = super::super::judgment(&claim, token.annotation(), token.certificates());
        assert_eq!(token.goal(), &goal);
        assert_eq!(token.proof(), &proof);
        assert!(super::super::calculus_row_certificate_for(&claim.symbol).is_none(),
            "a completed reporting proof is not a legacy caller/optimizer certificate");
        for changed in [
            CalculusRowClaim { fid: claim.fid + 1, ..claim.clone() },
            CalculusRowClaim { symbol: b"other-function".to_vec(), ..claim.clone() },
            CalculusRowClaim { artifact: vec![2], ..claim.clone() },
        ] {
            assert!(!token.matches_claim(&changed));
        }
        let expired = Instant::now() - std::time::Duration::from_secs(1);
        assert!(matches!(session.replay(&claim, Some(expired)), Err(Vf5HintMiss::Stopped(_))));
        assert!(super::super::calculus_row_certificate_for(&claim.symbol).is_none(),
            "stopped replay cannot expose a registerable certificate");
    }

    #[test]
    fn consumed_malformed_or_valid_hint_cannot_refresh_from_private_file() {
        let (directory, session, claim) = fixture(Some(b"not JSON"));
        assert!(matches!(session.replay(&claim, None), Err(Vf5HintMiss::Envelope(_))));
        let good = encode(&claim.artifact, &Expr::nat_lit(0), &Expr::nat_lit(0)).unwrap();
        let path = directory.path().join(DIRECTORY).join("incoming").join(filename(&claim.artifact));
        std::fs::write(path, good).unwrap();
        assert!(matches!(session.replay(&claim, None), Err(Vf5HintMiss::Envelope(_))));

        let (directory, session, claim) = fixture(None);
        assert!(session.replay(&claim, None).is_ok());
        let changed = encode(&claim.artifact, &Expr::nat_lit(1), &Expr::nat_lit(0)).unwrap();
        let path = directory.path().join(DIRECTORY).join("incoming").join(filename(&claim.artifact));
        std::fs::write(path, &changed).unwrap();
        assert!(session.replay(&claim, None).is_ok(), "first captured bytes remain in memory");
        let (_other_directory, other, claim) = fixture(Some(&changed));
        assert!(matches!(other.replay(&claim, None), Err(Vf5HintMiss::Row(CalculusRowMiss::Refused(_)))),
            "the changed annotation itself is refused by the stand-in kernel");
    }
}
