//! Current-kernel proof replay before native search. Public rows stay pending;
//! the owned proof must still pass the compiler's exact final-row admission.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;

use trust_certify::proof_artifacts::{AuditedProof, ProofReplayVcIdentity, ReplayAudit};
use trust_types::VerificationCondition;
use trust_verifier_api::{TrustContractBundle, TrustObligation, VerifierExecutionContext};

#[derive(Debug)]
pub struct CurrentKernelProofReplay {
    bundle: Arc<TrustContractBundle>,
    obligation: TrustObligation,
    vc_bytes: ProofReplayVcIdentity,
    context: trust_verifier_api::VerifierExecutionSnapshot,
    deadline: Option<Instant>,
    proof: AuditedProof,
    reference: trust_certify::ReferenceCertificate,
    elapsed_ms: u64,
}

impl CurrentKernelProofReplay {
    /// These are proof facts about the supplied VC, not a public/native verdict
    /// or authority for its association with a program. The compiler must also
    /// check its independently frozen public-to-current-VC binding.
    #[must_use]
    pub fn matches(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        vc: &VerificationCondition,
        context: &VerifierExecutionContext,
    ) -> bool {
        obligation == &self.obligation
            && live(context)
            && context.deadline == self.deadline
            && context.snapshot() == self.context
            && bundle == self.bundle.as_ref()
            && ProofReplayVcIdentity::of(vc).as_ref() == Some(&self.vc_bytes)
            && self.proof.audit().is_some_and(|audit| audit.matches(vc, self.proof.evidence()))
            && trust_certify::reference_certificate_for(self.proof.evidence()).as_ref()
                == Some(&self.reference)
            && live(context)
    }

    /// Observed replay plus admission time, rounded down to milliseconds;
    /// never an inferred zero from absent native or AY solver work.
    #[must_use]
    pub fn elapsed_ms(&self) -> u64 {
        self.elapsed_ms
    }

    #[must_use]
    pub fn obligation(&self) -> &TrustObligation {
        &self.obligation
    }

    /// Consume only at the same current binding and live function boundary.
    /// No deserializer, clone or unchecked evidence-only extraction exists.
    #[must_use]
    pub fn into_parts_for(
        self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        vc: &VerificationCondition,
        context: &VerifierExecutionContext,
    ) -> Option<(trust_ir::ProofEvidence, ReplayAudit)> {
        if !self.matches(bundle, obligation, vc, context) {
            return None;
        }
        let (proof, audit) = self.proof.into_parts();
        if !live(context) {
            return None;
        }
        Some((proof, audit?))
    }
}

struct Candidate {
    obligation: TrustObligation,
    vc: VerificationCondition,
    vc_bytes: ProofReplayVcIdentity,
}

pub(super) struct KernelReplayInputs {
    bundle: Arc<TrustContractBundle>,
    root: PathBuf,
    context: trust_verifier_api::VerifierExecutionSnapshot,
    deadline: Option<Instant>,
    candidates: BTreeMap<String, Candidate>,
}

pub(super) struct KernelReplaySession {
    inputs: Arc<KernelReplayInputs>,
    checked: BTreeMap<String, CurrentKernelProofReplay>,
    native_admitted: Option<BTreeSet<String>>,
}

fn live(context: &VerifierExecutionContext) -> bool {
    !context.is_cancelled() && !context.budget_exceeded()
}

fn solve_live(context: &VerifierExecutionContext) -> bool {
    live(context) && context.solve_deadline().is_none_or(|at| Instant::now() < at)
}

impl KernelReplayInputs {
    pub(super) fn new(
        bundle: &TrustContractBundle,
        candidates: Vec<(TrustObligation, VerificationCondition)>,
        root: PathBuf,
        context: &VerifierExecutionContext,
    ) -> Option<Self> {
        if !root.is_absolute() || !live(context) {
            return None;
        }
        let requested =
            candidates.iter().map(|(obligation, _)| obligation.clone()).collect::<Vec<_>>();
        bundle.validate_requested_obligations(&requested).ok()?;
        let mut selected = BTreeMap::new();
        let mut unique_vcs = BTreeSet::new();
        for (obligation, vc) in candidates {
            let vc_bytes = ProofReplayVcIdentity::of(&vc)?;
            // Ambiguity is an ordinary miss for the complete candidate set.
            // A proof cannot donate one lineage to two current program rows.
            if !unique_vcs.insert(vc_bytes.clone())
                || selected.contains_key(&obligation.obligation_id)
            {
                return None;
            }
            selected
                .insert(obligation.obligation_id.clone(), Candidate { obligation, vc, vc_bytes });
        }
        Some(Self {
            bundle: Arc::new(bundle.clone()),
            root,
            context: context.snapshot(),
            deadline: context.deadline,
            candidates: selected,
        })
    }
}

impl KernelReplaySession {
    pub(super) fn start(inputs: Arc<KernelReplayInputs>) -> Self {
        Self { inputs, checked: BTreeMap::new(), native_admitted: None }
    }

    fn matches_context(
        &self,
        bundle: &TrustContractBundle,
        context: &VerifierExecutionContext,
    ) -> bool {
        live(context)
            && bundle == self.inputs.bundle.as_ref()
            && context.snapshot() == self.inputs.context
            && context.deadline == self.inputs.deadline
    }

    pub(super) fn replay(
        &mut self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        context: &VerifierExecutionContext,
        native_admission: impl FnOnce() -> BTreeSet<String>,
    ) -> bool {
        if !self.matches_context(bundle, context) || !solve_live(context) {
            return false;
        }
        let started = Instant::now();
        let Some(candidate) = self.inputs.candidates.get(&obligation.obligation_id) else {
            return false;
        };
        if candidate.obligation != *obligation
            || candidate.vc.kernel_authority_refusal().is_some()
            || !matches!(candidate.vc.type_invariant_tags(), trust_types::TinvTagScan::None)
        {
            return false;
        }
        let (proof, stop) =
            trust_certify::proof_artifacts::replay_vc_with_artifacts_reporting_stop_and_audit_until(
                &candidate.vc,
                &self.inputs.root,
                context.solve_deadline(),
            );
        let Some(proof) = proof.filter(|_| stop.is_none() && solve_live(context)) else {
            return false;
        };
        if !proof.audit().is_some_and(|audit| audit.matches(&candidate.vc, proof.evidence())) {
            return false;
        }
        let Some(reference) = trust_certify::reference_certificate_for(proof.evidence()) else {
            return false;
        };
        // Only a real replay hit pays for native preflight. Retain the exact
        // ordinary admission/public/source checks without translating a second
        // time on every ordinary artifact miss or every matched sibling.
        let admitted = self.native_admitted.get_or_insert_with(native_admission);
        if !admitted.contains(&obligation.obligation_id) || !solve_live(context) {
            return false;
        }
        let checked = CurrentKernelProofReplay {
            bundle: Arc::clone(&self.inputs.bundle),
            obligation: obligation.clone(),
            vc_bytes: candidate.vc_bytes.clone(),
            context: self.inputs.context.clone(),
            deadline: self.inputs.deadline,
            proof,
            reference,
            elapsed_ms: u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX),
        };
        if !checked.matches(bundle, obligation, &candidate.vc, context) || !solve_live(context) {
            return false;
        }
        self.checked.insert(obligation.obligation_id.clone(), checked);
        true
    }

    pub(super) fn take_checked(
        &mut self,
        bundle: &TrustContractBundle,
        context: &VerifierExecutionContext,
    ) -> Vec<CurrentKernelProofReplay> {
        let checked = std::mem::take(&mut self.checked);
        if !self.matches_context(bundle, context) {
            return Vec::new();
        }
        checked.into_values().collect()
    }
}
