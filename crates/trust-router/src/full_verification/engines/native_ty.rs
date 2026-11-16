//! Native ty temporal engine for the full verifier.
//!
//! Implements the TY primary with the real in-process temporal model checker
//! (trust-temporal CTL/liveness/fairness over tla-mc-core BFS, the same core
//! the legacy-lane `TyBackend` uses).
//!
//! Transport: the public `TrustObligation` carries no formula or state
//! machine, so the producer (`trust-mir-extract`) serializes the temporal
//! `VcKind` — property plus inline `StateMachineMetadata` — into obligation
//! metadata under [`trust_types::TY_TEMPORAL_MODEL_METADATA_KEY`]. This engine
//! rebuilds the machine from that entry and model-checks it.
//!
//! Evidence discipline (mirrors `NativeTrustMcTrustIrEngine` adapted to the
//! TyTemporal route):
//! * `Proved` carries `ProofStrength { ExplicitStateModel, Sound }` only when
//!   BFS provably completed; truncated exploration yields a bounded strength
//!   the full-lane policy rejects (fail-closed, never a spurious Sound).
//! * `Proved` evidence attaches a `SolverTranscript` artifact (the route
//!   requirement for `ProofFamily::TyTemporal`) plus a `ProofCheckReport`
//!   artifact recording an independent parse→rebuild→recheck replay, which a
//!   Sound (non-solver-backed) proof needs to satisfy
//!   `ObligationEvidence::satisfies_proof_artifact_policy`.
//! * Obligations without a transportable model are `Unsupported` with a
//!   diagnostic naming the missing metadata (never a silent Unknown), and
//!   refutations are `Failed` with a typed state/action trace.
//! * A REFUTATION-ONLY payload (`TY_TEMPORAL_MODEL_SCHEMA_REFUTATION_ONLY`: a
//!   derived model that may under-approximate the program) never yields
//!   `Proved`: a check that finds no counterexample is `Unknown` with a
//!   diagnostic saying so (D-10/D-11 plan SD-8). Its refutations stay
//!   `Failed`.
//! * The platform pass reads a refutation-only check TYPED, never through
//!   `EvidenceStatus` or diagnostic text ([`NativeTyEngine::check_refutation_only`],
//!   [`RefutationOnlyVerdict`]; Critique C-1, change 1): a counterexample
//!   trace, "no counterexample" with the exploration's completeness
//!   (exhaustive or truncated), or inconclusive. One pure mapping
//!   ([`classify`]) builds both that value and the wire `Unknown`.
//! * A refutation-only payload's formula is VETTED before any answer is
//!   read from it, typed or on the wire ([`vet_refutation_only`]): it must
//!   be CTL over the transported machine, the payload must declare its atom
//!   vocabulary, and every atom of the formula and every state label must be
//!   in it. Anything else is inconclusive (`Unknown`, never `Failed` and
//!   never "no counterexample"): an atom no state carries is false
//!   everywhere, so a misspelling would otherwise pass vacuously or refute
//!   spuriously (FC-7).

use trust_temporal::ctl::{CtlFormula, parse_ctl};
use trust_types::{
    CounterexampleValue, StateMachineMetadata, TY_TEMPORAL_MODEL_METADATA_KEY,
    TyTemporalModelPayload, VcKind, VerificationResult,
};
use trust_verifier_api::{
    API_VERSION, Counterexample, EngineCapability, EngineKind, EngineManifest, EvidenceArtifact,
    EvidenceArtifactKind, EvidenceArtifactMaterialization, EvidenceArtifactReference,
    EvidencePublicationMetadata, EvidenceStatus, ObligationEvidence, ObligationKind, ProofStrength,
    ReasoningKind, SupportLevel, TrustContractBundle, TrustObligation,
    ValidatedVerificationRequest, VerificationEngine,
};

use crate::ty_backend::{metadata_to_state_machine, verify_liveness, verify_temporal_property};

/// Schema marker stamped on this engine's transcript and check-report
/// artifacts and typed counterexamples.
const TY_EVIDENCE_SCHEMA: &str = "trust.ty.native-evidence.v1";

/// What a refutation-only check of a derived model gave, typed (Critique
/// C-1, change 1). The platform pass reads this, never `EvidenceStatus` or
/// diagnostic text.
///
/// There is no proof arm: a derived model may under-approximate the program,
/// so "no counterexample" is all ty can say about it (OD-8; it never becomes
/// `Proved`, `Certified` or a proof strength).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RefutationOnlyVerdict {
    /// ty refuted the formula. `trace` is the counterexample's machine-state
    /// sequence (one emitted-machine state id per step, from the initial
    /// state), the input of the derivation's replay.
    Counterexample { trace: Vec<usize> },
    /// No counterexample, over an exploration of this completeness.
    NoCounterexample { completeness: RefutationCompleteness },
    /// No answer: ty was inconclusive, or the payload, the formula or the
    /// counterexample did not parse. Never read as "no counterexample".
    Inconclusive { reason: String },
}

/// How much of the transported machine a "no counterexample" covered.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefutationCompleteness {
    /// The exploration provably completed (ty's `ExplicitStateModel`,
    /// `Sound` strength).
    Exhaustive,
    /// The exploration stopped after `states` states
    /// (`ProofStrength::bounded(states)`): an unexplored state may violate.
    Truncated { states: u64 },
}

/// The one mapping from ty's result to a [`RefutationOnlyVerdict`]. Pure.
///
/// * `Proved` at `ExplicitStateModel`/`Sound`: no counterexample, exhaustive;
///   at a bounded strength: no counterexample, truncated; at any other
///   strength: inconclusive (an unrecognised strength is never exhaustive).
/// * `Failed` whose counterexample steps are `step_{i}_…` machine-state ids
///   in order: the trace. Without a counterexample, empty, out of order, or
///   with a step that is not a state id: inconclusive.
/// * `Unknown`, `Timeout` and anything else: inconclusive.
///
/// `refutation_only` is whether the checked payload carried the
/// refutation-only schema. Only derived models are read this way: without
/// the marker the answer is the full lane's, so this is inconclusive.
#[must_use]
pub fn classify(result: &VerificationResult, refutation_only: bool) -> RefutationOnlyVerdict {
    if !refutation_only {
        return RefutationOnlyVerdict::Inconclusive {
            reason: "the payload is not refutation-only: a refutation-only check reads derived \
                     models only"
                .to_string(),
        };
    }
    match result {
        VerificationResult::Proved { strength, .. } => {
            match (&strength.reasoning, &strength.assurance, strength.bounded_depth()) {
                (
                    trust_types::ReasoningKind::ExplicitStateModel,
                    trust_types::AssuranceLevel::Sound,
                    _,
                ) => RefutationOnlyVerdict::NoCounterexample {
                    completeness: RefutationCompleteness::Exhaustive,
                },
                (_, _, Some(states)) => RefutationOnlyVerdict::NoCounterexample {
                    completeness: RefutationCompleteness::Truncated { states },
                },
                _ => RefutationOnlyVerdict::Inconclusive {
                    reason: format!(
                        "no counterexample, at a strength that is neither a complete explicit-state \
                         exploration nor a bounded one: {strength:?}"
                    ),
                },
            }
        }
        VerificationResult::Failed { counterexample: Some(ce), .. } => {
            match counterexample_trace(ce) {
                Ok(trace) => RefutationOnlyVerdict::Counterexample { trace },
                Err(reason) => RefutationOnlyVerdict::Inconclusive { reason },
            }
        }
        VerificationResult::Failed { counterexample: None, .. } => {
            RefutationOnlyVerdict::Inconclusive {
                reason: "ty refuted the formula but returned no counterexample to replay"
                    .to_string(),
            }
        }
        VerificationResult::Unknown { reason, .. } => {
            RefutationOnlyVerdict::Inconclusive { reason: reason.clone() }
        }
        other => RefutationOnlyVerdict::Inconclusive {
            reason: format!("unexpected ty verification result: {other:?}"),
        },
    }
}

/// The machine-state ids of a ty counterexample (`step_{i}_{state}` →
/// state id), or why they are not.
fn counterexample_trace(ce: &trust_types::Counterexample) -> Result<Vec<usize>, String> {
    if ce.assignments.is_empty() {
        return Err("ty's counterexample has no steps".to_string());
    }
    ce.assignments
        .iter()
        .enumerate()
        .map(|(i, (name, value))| {
            let prefix = format!("step_{i}_");
            if !name.starts_with(&prefix) {
                return Err(format!("counterexample step {i} is named `{name}`, not `{prefix}…`"));
            }
            let id = match value {
                CounterexampleValue::Int(v) => usize::try_from(*v).ok(),
                CounterexampleValue::Uint(v) => usize::try_from(*v).ok(),
                _ => None,
            };
            id.ok_or_else(|| {
                format!("counterexample step {i} carries {value:?}, not a machine state id")
            })
        })
        .collect()
}

/// Vet a REFUTATION-ONLY payload before any answer is read from it (FC-7):
/// the check must be a CTL formula over a transported machine, the payload
/// must declare its atom vocabulary, every atom the formula names must be
/// in that vocabulary, and so must every label a state carries (a
/// vocabulary that does not cover the machine's labels is not this
/// machine's). `Err` says why the payload is inconclusive.
///
/// The machine alone cannot tell a misspelt atom from a real one: a fixed
/// program legitimately labels no state with its violation atom, so only
/// the producer's declared vocabulary can.
pub(crate) fn vet_refutation_only(payload: &TyTemporalModelPayload) -> Result<(), String> {
    let VcKind::Temporal { property, machine: Some(md) } = &payload.vc_kind else {
        return Err(format!(
            "a refutation-only check reads a CTL formula over a transported machine, not `{}`",
            payload.vc_kind.description()
        ));
    };
    let formula = parse_ctl(property)
        .map_err(|e| format!("failed to parse temporal property `{property}` as CTL: {e}"))?;
    let mut atoms = Vec::new();
    ctl_atoms(&formula, &mut atoms)?;
    let Some(vocabulary) = &payload.vocabulary else {
        return Err(format!(
            "the refutation-only payload for `{property}` declares no atom vocabulary, so its \
             atoms cannot be vetted (an atom no state carries is false everywhere)"
        ));
    };
    if let Some(atom) = atoms.iter().find(|a| !vocabulary.contains(*a)) {
        return Err(format!(
            "`{property}` names atom `{atom}`, which is not in the payload's vocabulary \
             {vocabulary:?}"
        ));
    }
    // The order of the Fx map never escapes: the strays are sorted before
    // the first is named.
    #[allow(rustc::potential_query_instability)]
    let mut strays: Vec<&String> =
        md.labels.values().flatten().filter(|l| !vocabulary.contains(*l)).collect();
    strays.sort_unstable();
    if let Some(label) = strays.first() {
        return Err(format!(
            "a state of the machine carries `{label}`, which is not in the payload's vocabulary: \
             the vocabulary is not this machine's"
        ));
    }
    Ok(())
}

/// Every atom of `f`, or `Err` for a connective this vetting does not know
/// (its atoms could not be vetted).
fn ctl_atoms(f: &CtlFormula, out: &mut Vec<String>) -> Result<(), String> {
    match f {
        CtlFormula::Atom(a) => out.push(a.clone()),
        CtlFormula::True | CtlFormula::False => {}
        CtlFormula::Not(x)
        | CtlFormula::EX(x)
        | CtlFormula::EF(x)
        | CtlFormula::EG(x)
        | CtlFormula::AX(x)
        | CtlFormula::AF(x)
        | CtlFormula::AG(x) => ctl_atoms(x, out)?,
        CtlFormula::And(x, y)
        | CtlFormula::Or(x, y)
        | CtlFormula::EU(x, y)
        | CtlFormula::AU(x, y) => {
            ctl_atoms(x, out)?;
            ctl_atoms(y, out)?;
        }
        other => return Err(format!("unvetted CTL connective in `{other}`")),
    }
    Ok(())
}

/// Native ty adapter registered as the full verifier's temporal primary.
pub struct NativeTyEngine {
    manifest: EngineManifest,
}

impl NativeTyEngine {
    #[must_use]
    pub fn new() -> Self {
        // The manifest name must be exactly "ty": PrimaryEngine::matches_manifest
        // compares names, and require_all_required_engines fails every
        // obligation in the bundle when no engine named "ty" is registered.
        let mut manifest = EngineManifest::new(
            "ty",
            concat!(env!("CARGO_PKG_VERSION"), "+native-temporal"),
            EngineKind::Temporal,
        );
        manifest.api_version = API_VERSION.to_string();
        manifest.repository = Some("trust-router".to_string());
        manifest.capabilities = vec![
            EngineCapability {
                obligation_kind: ObligationKind::TemporalSafety,
                support: SupportLevel::Supported,
            },
            EngineCapability {
                obligation_kind: ObligationKind::Liveness,
                support: SupportLevel::Supported,
            },
        ];
        manifest.proof_modes =
            vec![ReasoningKind::ExplicitStateModel, ReasoningKind::TemporalModelCheck];
        Self { manifest }
    }

    fn owns(kind: &ObligationKind) -> bool {
        matches!(kind, ObligationKind::TemporalSafety | ObligationKind::Liveness)
    }

    /// Locate and parse the transported temporal model, if any.
    fn transported_model(obligation: &TrustObligation) -> Result<TyTemporalModelPayload, String> {
        let Some(entry) =
            obligation.metadata.iter().find(|entry| entry.key == TY_TEMPORAL_MODEL_METADATA_KEY)
        else {
            return Err(format!(
                "no temporal model transported: obligation metadata lacks `{TY_TEMPORAL_MODEL_METADATA_KEY}` \
                 (the producer must serialize the temporal VcKind — property + StateMachineMetadata — \
                 via trust_types::TyTemporalModelPayload; see trust-mir-extract::ty_temporal_model_metadata)"
            ));
        };
        TyTemporalModelPayload::from_metadata_value(&entry.value)
    }

    /// Run the model check for one transported temporal `VcKind`.
    ///
    /// Returns `Err(diagnostic)` for shapes with no checkable model (the
    /// evidence becomes `Unsupported`, fail-closed).
    fn check(vc_kind: &VcKind) -> Result<VerificationResult, String> {
        match vc_kind {
            VcKind::Temporal { property, machine: Some(md) } => {
                let machine = machine_from_metadata(md)?;
                Ok(verify_temporal_property(&machine, property))
            }
            VcKind::Temporal { property, machine: None } => Err(format!(
                "temporal VC `{property}` carries no StateMachineMetadata; \
                 the producer must attach the machine on VcKind::Temporal"
            )),
            VcKind::Liveness { property, machine: Some(md) } => {
                let machine = machine_from_metadata(md)?;
                Ok(verify_liveness(&machine, property))
            }
            VcKind::Liveness { property, machine: None } => Err(format!(
                "liveness VC `{}` carries no StateMachineMetadata; \
                 the producer must attach the machine on VcKind::Liveness",
                property.name
            )),
            VcKind::Fairness { .. } | VcKind::DeadState { .. } | VcKind::Deadlock => Err(format!(
                "temporal VC kind `{}` has no state-machine transport yet; \
                 attach StateMachineMetadata to the VcKind and extend NativeTyEngine::check",
                vc_kind.description()
            )),
            other => {
                Err(format!("VcKind `{}` is not a ty-owned temporal kind", other.description()))
            }
        }
    }

    /// Check a refutation-only obligation and say what ty found, typed
    /// (Critique C-1, change 1): the answer the platform pass reads.
    ///
    /// A missing, malformed or non-refutation-only payload, a formula ty
    /// cannot parse, a payload [`vet_refutation_only`] refuses (no declared
    /// vocabulary, or an atom outside it), an inconclusive check and a
    /// counterexample that names a state the machine does not have are all
    /// [`RefutationOnlyVerdict::Inconclusive`]. The wire evidence
    /// ([`VerificationEngine::verify`]) of the same obligation is built from
    /// the same [`classify`]: status `Unknown` (or `Failed` for a
    /// counterexample) and never a proof strength.
    #[must_use]
    pub fn check_refutation_only(&self, obligation: &TrustObligation) -> RefutationOnlyVerdict {
        let support = self.supports(obligation);
        if !support.is_supported() {
            return RefutationOnlyVerdict::Inconclusive {
                reason: format!("ty does not check this obligation: {support:?}"),
            };
        }
        let payload = match Self::transported_model(obligation) {
            Ok(payload) => payload,
            Err(reason) => return RefutationOnlyVerdict::Inconclusive { reason },
        };
        let result = match Self::check(&payload.vc_kind) {
            Ok(result) => result,
            Err(reason) => return RefutationOnlyVerdict::Inconclusive { reason },
        };
        if payload.is_refutation_only()
            && let Err(reason) = vet_refutation_only(&payload)
        {
            return RefutationOnlyVerdict::Inconclusive { reason };
        }
        match classify(&result, payload.is_refutation_only()) {
            RefutationOnlyVerdict::Counterexample { trace } => {
                let states = payload_machine(&payload).map_or(0, |md| md.states.len());
                match trace.iter().find(|s| **s >= states) {
                    Some(s) => RefutationOnlyVerdict::Inconclusive {
                        reason: format!(
                            "the counterexample names state {s}, but the machine has {states} states"
                        ),
                    },
                    None => RefutationOnlyVerdict::Counterexample { trace },
                }
            }
            other => other,
        }
    }

    /// Independent replay: re-parse the raw metadata value, rebuild the
    /// machine, re-run the check, and compare verdicts. This is the
    /// replay/check evidence a Sound (non-solver-backed) proof must carry.
    fn recheck_verdict(raw_metadata_value: &str) -> Result<&'static str, String> {
        let payload = TyTemporalModelPayload::from_metadata_value(raw_metadata_value)?;
        let result = Self::check(&payload.vc_kind)?;
        Ok(verdict_label(&result))
    }

    fn evidence_for(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
    ) -> ObligationEvidence {
        let raw_entry = obligation
            .metadata
            .iter()
            .find(|entry| entry.key == TY_TEMPORAL_MODEL_METADATA_KEY)
            .map(|entry| entry.value.clone());

        let payload = match Self::transported_model(obligation) {
            Ok(payload) => payload,
            Err(diagnostic) => return self.unsupported(obligation, diagnostic),
        };

        let result = match Self::check(&payload.vc_kind) {
            Ok(result) => result,
            Err(diagnostic) => return self.unsupported(obligation, diagnostic),
        };

        // A refutation-only payload whose formula cannot be vetted gives no
        // answer at all, not even a refutation: its counterexample may be
        // one of a misspelt atom (the same check the typed answer makes).
        if payload.is_refutation_only()
            && let Err(reason) = vet_refutation_only(&payload)
        {
            return self.refutation_only_unknown(
                obligation,
                &payload,
                &RefutationOnlyVerdict::Inconclusive { reason },
            );
        }

        match result {
            VerificationResult::Failed { counterexample, .. } => {
                self.failed(obligation, &payload, counterexample)
            }
            // A derived (refutation-only) model never proves (SD-8, OD-8):
            // anything but a refutation is `Unknown`, built from the typed
            // verdict `check_refutation_only` returns, so the wire and the
            // typed answer cannot disagree.
            result if payload.is_refutation_only() => {
                self.refutation_only_unknown(obligation, &payload, &classify(&result, true))
            }
            VerificationResult::Proved { strength, .. } => {
                self.proved(bundle, obligation, &payload, raw_entry.as_deref(), strength)
            }
            VerificationResult::Unknown { reason, .. } => ObligationEvidence {
                evidence_id: format!("ty:native:unknown:{}", obligation.obligation_id),
                obligation_id: obligation.obligation_id.clone(),
                engine: self.manifest.clone(),
                status: EvidenceStatus::Unknown,
                decline: None,
                proof_strength: None,
                artifacts: Vec::new(),
                counterexample: None,
                publication: EvidencePublicationMetadata::default(),
                diagnostics: vec![format!("ty model check inconclusive: {reason}")],
            },
            // Legacy VerificationResult is #[non_exhaustive]; treat anything
            // else (e.g. RuntimeChecked) as inconclusive, never Proved.
            other => ObligationEvidence {
                evidence_id: format!("ty:native:unknown:{}", obligation.obligation_id),
                obligation_id: obligation.obligation_id.clone(),
                engine: self.manifest.clone(),
                status: EvidenceStatus::Unknown,
                decline: None,
                proof_strength: None,
                artifacts: Vec::new(),
                counterexample: None,
                publication: EvidencePublicationMetadata::default(),
                diagnostics: vec![format!("unexpected ty verification result: {other:?}")],
            },
        }
    }

    /// The wire evidence of a refutation-only check that refuted nothing:
    /// `Unknown`, no proof strength, the typed verdict in words.
    fn refutation_only_unknown(
        &self,
        obligation: &TrustObligation,
        payload: &TyTemporalModelPayload,
        verdict: &RefutationOnlyVerdict,
    ) -> ObligationEvidence {
        let diagnostics = match verdict {
            RefutationOnlyVerdict::NoCounterexample { completeness } => {
                let mut diagnostics = vec![format!(
                    "no counterexample to `{}` in the transported machine; the payload is \
                     refutation-only (a derived model that may under-approximate the \
                     program), so this is not a proof",
                    property_description(&payload.vc_kind)
                )];
                if let RefutationCompleteness::Truncated { states } = completeness {
                    diagnostics.push(format!(
                        "the exploration was truncated after {states} states: an unexplored \
                         state may violate the property"
                    ));
                }
                diagnostics
            }
            RefutationOnlyVerdict::Inconclusive { reason } => {
                vec![format!("ty model check inconclusive: {reason}")]
            }
            RefutationOnlyVerdict::Counterexample { trace } => vec![format!(
                "ty model check inconclusive: a counterexample of {} steps reached the \
                 no-counterexample path",
                trace.len()
            )],
        };
        ObligationEvidence {
            evidence_id: format!("ty:native:unknown:{}", obligation.obligation_id),
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest.clone(),
            status: EvidenceStatus::Unknown,
            decline: None,
            proof_strength: None,
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics,
        }
    }

    fn proved(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        payload: &TyTemporalModelPayload,
        raw_metadata_value: Option<&str>,
        strength: trust_types::ProofStrength,
    ) -> ObligationEvidence {
        let strength = api_proof_strength(&strength);
        let evidence_id = format!("ty:native:proved:{}", obligation.obligation_id);
        let mut artifacts = Vec::new();
        let mut diagnostics = Vec::new();

        // Bind the exploration transcript to the exact typed temporal-model
        // statement that was checked. A transcript/check pair without this
        // producer-authored input edge is ambiguous and must fail closed.
        let normalized_obligation = normalized_obligation_json(bundle, obligation, payload);
        let normalized_obligation_artifact = inline_artifact(
            EvidenceArtifactKind::NormalizedObligation,
            format!("ty://full-verifier/{}/normalized-obligation", obligation.obligation_id),
            &normalized_obligation,
            &evidence_id,
            &obligation.obligation_id,
            Vec::new(),
        );
        let normalized_obligation_hash = normalized_obligation_artifact.hash.clone();
        artifacts.push(normalized_obligation_artifact);

        // Route artifact requirement (ProofFamily::TyTemporal): an explicit
        // exploration transcript.
        let transcript = transcript_json(bundle, obligation, payload, &strength);
        let transcript_artifact = inline_artifact(
            EvidenceArtifactKind::SolverTranscript,
            format!("ty://full-verifier/{}/exploration-transcript", obligation.obligation_id),
            &transcript,
            &evidence_id,
            &obligation.obligation_id,
            vec![EvidenceArtifactReference {
                kind: EvidenceArtifactKind::NormalizedObligation,
                hash: normalized_obligation_hash,
            }],
        );
        let transcript_hash = transcript_artifact.hash.clone();
        artifacts.push(transcript_artifact);

        // Aggregation artifact requirement for non-solver-backed Sound proofs:
        // an independent replay. Re-parse the raw metadata, rebuild, re-check,
        // and record verdict agreement. A disagreeing or failing replay keeps
        // the proof but is recorded loudly; the check report is only attached
        // when the replay confirms, so a broken replay fails closed at the
        // artifact policy instead of shipping vacuous check metadata.
        match raw_metadata_value.map(Self::recheck_verdict) {
            Some(Ok(recheck)) if recheck == "proved" => {
                let report = check_report_json(obligation, payload, recheck);
                artifacts.push(inline_artifact(
                    EvidenceArtifactKind::ProofCheckReport,
                    format!("ty://full-verifier/{}/replay-check-report", obligation.obligation_id),
                    &report,
                    &evidence_id,
                    &obligation.obligation_id,
                    vec![EvidenceArtifactReference {
                        kind: EvidenceArtifactKind::SolverTranscript,
                        hash: transcript_hash,
                    }],
                ));
                diagnostics.push(
                    "independent replay (re-parse + rebuild + re-check) confirmed the verdict"
                        .to_string(),
                );
            }
            Some(Ok(recheck)) => diagnostics.push(format!(
                "replay verdict `{recheck}` disagrees with `proved`; check report withheld \
                 (evidence will be rejected by the proof-artifact policy)"
            )),
            Some(Err(error)) => diagnostics.push(format!(
                "replay failed: {error}; check report withheld \
                 (evidence will be rejected by the proof-artifact policy)"
            )),
            None => diagnostics.push(
                "raw temporal-model metadata unavailable for replay; check report withheld"
                    .to_string(),
            ),
        }

        if strength.is_bounded() {
            diagnostics.push(
                "state-space exploration did not provably complete; strength is bounded and \
                 the full-verification policy will reject it (fail-closed)"
                    .to_string(),
            );
        }

        ObligationEvidence {
            evidence_id,
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest.clone(),
            status: EvidenceStatus::Proved,
            decline: None,
            proof_strength: Some(strength),
            artifacts,
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics,
        }
    }

    fn failed(
        &self,
        obligation: &TrustObligation,
        payload: &TyTemporalModelPayload,
        counterexample: Option<trust_types::Counterexample>,
    ) -> ObligationEvidence {
        let machine = payload_machine(payload);
        let trace = counterexample.as_ref().map(|ce| {
            ce.assignments
                .iter()
                .map(
                    |(name, value)| serde_json::json!({ "step": name, "value": value.to_string() }),
                )
                .collect::<Vec<_>>()
        });
        let data = serde_json::json!({
            "schema": TY_EVIDENCE_SCHEMA,
            "obligation_id": obligation.obligation_id,
            "property": property_description(&payload.vc_kind),
            "states": machine.map(|md| md.states.clone()),
            "trace": trace,
        });
        ObligationEvidence {
            evidence_id: format!("ty:native:failed:{}", obligation.obligation_id),
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest.clone(),
            status: EvidenceStatus::Failed,
            decline: None,
            proof_strength: None,
            artifacts: Vec::new(),
            counterexample: Some(Counterexample { format: TY_EVIDENCE_SCHEMA.to_string(), data }),
            publication: EvidencePublicationMetadata::default(),
            diagnostics: vec![format!(
                "temporal property refuted over the transported state machine: {}",
                property_description(&payload.vc_kind)
            )],
        }
    }

    fn unsupported(&self, obligation: &TrustObligation, diagnostic: String) -> ObligationEvidence {
        ObligationEvidence {
            evidence_id: format!("ty:native:unsupported:{}", obligation.obligation_id),
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest.clone(),
            status: EvidenceStatus::Unsupported,
            decline: None,
            proof_strength: None,
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: vec![diagnostic],
        }
    }
}

impl Default for NativeTyEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationEngine for NativeTyEngine {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if Self::owns(&obligation.kind) {
            SupportLevel::Supported
        } else {
            SupportLevel::Unsupported {
                reason: format!("ty does not own obligation kind {:?}", obligation.kind),
            }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        let (bundle, obligations) = request.into_parts();
        obligations
            .iter()
            .filter(|obligation| self.supports(obligation).is_supported())
            .map(|obligation| self.evidence_for(bundle, obligation))
            .collect()
    }
}

/// Rebuild the trust-temporal machine from serialized metadata (the same
/// conversion the legacy `TyBackend` applies).
fn machine_from_metadata(
    md: &StateMachineMetadata,
) -> Result<trust_temporal::StateMachine, String> {
    metadata_to_state_machine(md)
}

fn payload_machine(payload: &TyTemporalModelPayload) -> Option<&StateMachineMetadata> {
    match &payload.vc_kind {
        VcKind::Temporal { machine, .. } | VcKind::Liveness { machine, .. } => machine.as_ref(),
        _ => None,
    }
}

fn property_description(vc_kind: &VcKind) -> String {
    match vc_kind {
        VcKind::Temporal { property, .. } => property.clone(),
        VcKind::Liveness { property, .. } => {
            format!("liveness {}: {}", property.name, property.predicate)
        }
        other => other.description(),
    }
}

fn verdict_label(result: &VerificationResult) -> &'static str {
    match result {
        VerificationResult::Proved { .. } => "proved",
        VerificationResult::Failed { .. } => "failed",
        VerificationResult::Unknown { .. } => "unknown",
        _ => "other",
    }
}

/// Exploration transcript recorded as the route's `SolverTranscript` artifact.
fn transcript_json(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    payload: &TyTemporalModelPayload,
    strength: &ProofStrength,
) -> String {
    let exploration = payload_machine(payload).map(|md| match machine_from_metadata(md) {
        Ok(machine) => {
            let adapter = trust_temporal::ty_bridge::StateMachineAdapter::new(machine);
            let mut observer = tla_mc_core::NoopObserver::<
                trust_temporal::ty_bridge::StateMachineAdapter,
            >::default();
            match tla_mc_core::explore_bfs(&adapter, &mut observer) {
                Ok(outcome) => serde_json::json!({
                    "states_discovered": outcome.states_discovered,
                    "completed": outcome.completed,
                }),
                Err(error) => serde_json::json!({ "error": error.to_string() }),
            }
        }
        Err(error) => serde_json::json!({ "error": error }),
    });
    serde_json::json!({
        "schema": TY_EVIDENCE_SCHEMA,
        "bundle_id": bundle.bundle_id,
        "obligation_id": obligation.obligation_id,
        "property": property_description(&payload.vc_kind),
        "machine": payload_machine(payload),
        "exploration": exploration,
        "verdict": "proved",
        "proof_strength": strength,
    })
    .to_string()
}

/// Canonical typed statement consumed by the temporal model checker. Keeping
/// this separate from the exploration transcript makes the proof DAG bind the
/// verdict to an exact obligation/model pair instead of to an unscoped log.
fn normalized_obligation_json(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    payload: &TyTemporalModelPayload,
) -> String {
    serde_json::json!({
        "schema": TY_EVIDENCE_SCHEMA,
        "role": "normalized_obligation",
        "bundle_id": bundle.bundle_id,
        "obligation_id": obligation.obligation_id,
        "obligation_kind": obligation.kind,
        "required_strength": obligation.required_strength,
        "temporal_model": payload,
    })
    .to_string()
}

/// Replay check report recorded as the `ProofCheckReport` artifact.
fn check_report_json(
    obligation: &TrustObligation,
    payload: &TyTemporalModelPayload,
    recheck_verdict: &str,
) -> String {
    serde_json::json!({
        "schema": TY_EVIDENCE_SCHEMA,
        "obligation_id": obligation.obligation_id,
        "property": property_description(&payload.vc_kind),
        "replay": "re-parse metadata + rebuild machine + re-run model check",
        "original_verdict": "proved",
        "recheck_verdict": recheck_verdict,
        "consistent": true,
    })
    .to_string()
}

/// Map the legacy (trust-types) proof strength onto the public verifier-api
/// type. `ty_proof_strength` emits exactly two shapes — Sound/ExplicitStateModel
/// for provably complete exploration and bounded(n) otherwise; anything
/// unrecognized maps fail-closed to bounded(0), which the full-lane policy
/// rejects (never a spurious Sound).
fn api_proof_strength(strength: &trust_types::ProofStrength) -> ProofStrength {
    match (&strength.reasoning, &strength.assurance) {
        (trust_types::ReasoningKind::ExplicitStateModel, trust_types::AssuranceLevel::Sound) => {
            ProofStrength {
                reasoning: ReasoningKind::ExplicitStateModel,
                assurance: trust_verifier_api::AssuranceLevel::Sound,
            }
        }
        (_, trust_types::AssuranceLevel::BoundedSound { depth }) => ProofStrength::bounded(*depth),
        (trust_types::ReasoningKind::BoundedModelCheck { depth }, _) => {
            ProofStrength::bounded(*depth)
        }
        _ => ProofStrength::bounded(0),
    }
}

/// Hash-address an inline JSON artifact.
fn inline_artifact(
    kind: EvidenceArtifactKind,
    uri: String,
    content: &str,
    proof_binding_id: &str,
    obligation_id: &str,
    referenced_artifacts: Vec<EvidenceArtifactReference>,
) -> EvidenceArtifact {
    let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
        kind,
        content.as_bytes(),
        proof_binding_id,
        obligation_id,
        referenced_artifacts,
    )
    .expect("native ty inline proof artifact is non-empty and bounded");
    EvidenceArtifact {
        kind,
        uri: format!("{uri}/sha256/{}", hash.value),
        hash,
        materialization: Some(materialization),
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{StateMachineMetadata, TY_TEMPORAL_MODEL_SCHEMA_VERSION};
    use trust_verifier_api::{BundleSubject, MetadataEntry, SourceLocation};

    use super::*;

    fn temporal_obligation(metadata: Vec<MetadataEntry>) -> TrustObligation {
        TrustObligation {
            obligation_id: "vc:demo::f:temporal_safety:0".to_string(),
            kind: ObligationKind::TemporalSafety,
            contract_id: None,
            proof_item_id: None,
            source: SourceLocation::default(),
            description: "temporal: AG !bad".to_string(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata,
        }
    }

    fn mmap_model_metadata(single_writer: trust_types::SingleWriterEvidence) -> MetadataEntry {
        temporal_model_metadata("AG !bad", StateMachineMetadata::mmap_temporal_model(single_writer))
    }

    fn temporal_model_metadata(property: &str, machine: StateMachineMetadata) -> MetadataEntry {
        let payload = TyTemporalModelPayload::from_vc_kind(&VcKind::Temporal {
            property: property.to_string(),
            machine: Some(machine),
        })
        .expect("Temporal is a ty-owned kind");
        MetadataEntry {
            key: TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: payload.to_metadata_value().expect("payload serializes"),
        }
    }

    fn bundle(obligation: &TrustObligation) -> TrustContractBundle {
        let mut bundle = TrustContractBundle::empty(
            "bundle-ty",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.obligations.push(obligation.clone());
        bundle
    }

    #[test]
    fn manifest_is_the_required_ty_primary() {
        let engine = NativeTyEngine::new();
        assert_eq!(engine.manifest().name, "ty");
        assert!(engine.manifest().version.ends_with("+native-temporal"));
        assert_eq!(engine.manifest().kind, EngineKind::Temporal);
        assert!(engine.manifest().proof_modes.contains(&ReasoningKind::ExplicitStateModel));
    }

    #[test]
    fn proves_single_writer_mmap_model_sound_with_artifacts() {
        let engine = NativeTyEngine::new();
        let obligation = temporal_obligation(vec![mmap_model_metadata(
            trust_types::SingleWriterEvidence::Verified,
        )]);
        let evidence = engine.verify(&bundle(&obligation), &[obligation]);
        assert_eq!(evidence.len(), 1);
        let evidence = &evidence[0];
        assert_eq!(evidence.status, EvidenceStatus::Proved, "{evidence:#?}");
        let strength = evidence.proof_strength.as_ref().expect("proved evidence has strength");
        assert_eq!(strength.reasoning, ReasoningKind::ExplicitStateModel);
        assert_eq!(strength.assurance, trust_verifier_api::AssuranceLevel::Sound);
        assert!(evidence.has_solver_transcript_artifacts(), "TyTemporal route needs a transcript");
        assert!(
            evidence.has_replay_or_check_artifact_metadata(),
            "Sound (non-solver-backed) proof needs a replay/check artifact"
        );
        assert!(evidence.satisfies_proof_artifact_policy());
        assert!(evidence.is_unbounded_proof());
        let normalized = evidence
            .artifacts
            .iter()
            .find(|artifact| artifact.kind == EvidenceArtifactKind::NormalizedObligation)
            .expect("Ty proof carries its exact normalized statement");
        let transcript = evidence
            .artifacts
            .iter()
            .find(|artifact| artifact.kind == EvidenceArtifactKind::SolverTranscript)
            .expect("Ty proof carries its exploration transcript");
        assert_eq!(
            transcript
                .materialization
                .as_ref()
                .expect("transcript is materialized")
                .referenced_artifacts(),
            [EvidenceArtifactReference {
                kind: EvidenceArtifactKind::NormalizedObligation,
                hash: normalized.hash.clone(),
            }]
        );
        assert!(evidence.artifacts.iter().all(|artifact| {
            artifact.materialization.as_ref().is_some_and(|materialization| {
                materialization.proof_binding_id() == evidence.evidence_id
            })
        }));
        for artifact in &evidence.artifacts {
            assert!(artifact.hash.is_hash_addressed(), "artifact {artifact:?} lacks a digest");
        }
    }

    #[test]
    fn ty_proof_artifacts_cannot_be_transplanted_to_another_obligation() {
        let engine = NativeTyEngine::new();
        let obligation = temporal_obligation(vec![mmap_model_metadata(
            trust_types::SingleWriterEvidence::Verified,
        )]);
        let mut evidence = engine.verify(&bundle(&obligation), &[obligation]).remove(0);
        assert!(evidence.satisfies_proof_artifact_policy());

        evidence.obligation_id = "vc:demo::other:temporal_safety:0".to_string();
        assert!(
            !evidence.satisfies_proof_artifact_policy(),
            "owner-bound statement/transcript/check bytes must reject cross-obligation transplant"
        );
    }

    #[test]
    fn ty_transcript_check_pair_without_statement_lineage_is_rejected() {
        let engine = NativeTyEngine::new();
        let obligation = temporal_obligation(vec![mmap_model_metadata(
            trust_types::SingleWriterEvidence::Verified,
        )]);
        let mut evidence =
            engine.verify(&bundle(&obligation), std::slice::from_ref(&obligation)).remove(0);
        let transcript = inline_artifact(
            EvidenceArtifactKind::SolverTranscript,
            "ty://unit/lineage-free-transcript".to_string(),
            "lineage-free transcript",
            &evidence.evidence_id,
            &obligation.obligation_id,
            Vec::new(),
        );
        let check = inline_artifact(
            EvidenceArtifactKind::ProofCheckReport,
            "ty://unit/lineage-free-check".to_string(),
            "lineage-free check",
            &evidence.evidence_id,
            &obligation.obligation_id,
            vec![EvidenceArtifactReference {
                kind: EvidenceArtifactKind::SolverTranscript,
                hash: transcript.hash.clone(),
            }],
        );
        evidence.artifacts = vec![transcript, check];

        assert!(
            !evidence.satisfies_proof_artifact_policy(),
            "a mutually bound transcript/check pair still needs an exact structural input"
        );
    }

    #[test]
    fn refutes_multi_writer_mmap_model_with_trace() {
        let engine = NativeTyEngine::new();
        let obligation =
            temporal_obligation(vec![mmap_model_metadata(trust_types::SingleWriterEvidence::None)]);
        let evidence = engine.verify(&bundle(&obligation), &[obligation]);
        assert_eq!(evidence.len(), 1);
        let evidence = &evidence[0];
        assert_eq!(evidence.status, EvidenceStatus::Failed, "{evidence:#?}");
        assert!(evidence.proof_strength.is_none());
        let counterexample =
            evidence.counterexample.as_ref().expect("refutation carries a counterexample");
        assert_eq!(counterexample.format, TY_EVIDENCE_SCHEMA);
        assert!(counterexample.data["trace"].is_array(), "{:#?}", counterexample.data);
    }

    #[test]
    fn unsupported_without_transported_model() {
        let engine = NativeTyEngine::new();
        let obligation = temporal_obligation(Vec::new());
        let evidence = engine.verify(&bundle(&obligation), &[obligation]);
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(
            evidence[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains(TY_TEMPORAL_MODEL_METADATA_KEY)),
            "diagnostic must name the missing metadata key: {:#?}",
            evidence[0].diagnostics
        );
    }

    #[test]
    fn unsupported_on_malformed_payload() {
        let engine = NativeTyEngine::new();
        let obligation = temporal_obligation(vec![MetadataEntry {
            key: TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: "{not json".to_string(),
        }]);
        let evidence = engine.verify(&bundle(&obligation), &[obligation]);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(evidence[0].diagnostics.iter().any(|d| d.contains("malformed")));
    }

    #[test]
    fn unsupported_on_wrong_schema_version() {
        let engine = NativeTyEngine::new();
        let payload = serde_json::json!({
            "schema_version": "trust.ty.temporal-model.v999",
            "vc_kind": { "Deadlock": null },
        });
        let obligation = temporal_obligation(vec![MetadataEntry {
            key: TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: payload.to_string(),
        }]);
        let evidence = engine.verify(&bundle(&obligation), &[obligation]);
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        assert!(
            evidence[0].diagnostics.iter().any(|d| d.contains(TY_TEMPORAL_MODEL_SCHEMA_VERSION)),
            "{:#?}",
            evidence[0].diagnostics
        );
    }

    #[test]
    fn unsupported_on_unrepresentable_initial_state_sets() {
        let mut safe_first_labels = trust_types::fx::FxHashMap::default();
        safe_first_labels.insert(0, vec!["safe".to_string()]);
        let machine = |init_states| StateMachineMetadata {
            states: vec!["safe-initial".to_string(), "unsafe-initial".to_string()],
            init_states,
            transitions: vec![(0, "stay-safe".to_string(), 0), (1, "stay-unsafe".to_string(), 1)],
            labels: safe_first_labels.clone(),
        };
        let cases = [
            ("missing", machine(Vec::new()), "exactly one initial state"),
            ("out-of-range", machine(vec![2]), "out of range"),
            // With first-only conversion, this particular model falsely proved
            // `AG safe` by ignoring the unsafe second initial state.
            ("multiple", machine(vec![0, 1]), "exactly one initial state"),
        ];

        let engine = NativeTyEngine::new();
        for (label, machine, expected) in cases {
            let obligation = temporal_obligation(vec![temporal_model_metadata("AG safe", machine)]);
            let evidence = engine.verify(&bundle(&obligation), &[obligation]);
            assert_eq!(
                evidence[0].status,
                EvidenceStatus::Unsupported,
                "{label} initial-state metadata must fail closed: {:#?}",
                evidence[0]
            );
            assert!(
                evidence[0].diagnostics.iter().any(|diagnostic| diagnostic.contains(expected)),
                "{label} diagnostic must explain the rejection: {:#?}",
                evidence[0].diagnostics
            );
        }
    }

    /// SD-8: a derived (refutation-only) machine never proves; its
    /// refutations still fail with a trace.
    #[test]
    fn refutation_only_payload_never_proves_and_still_refutes() {
        let engine = NativeTyEngine::new();
        for (single_writer, want) in [
            (trust_types::SingleWriterEvidence::Verified, EvidenceStatus::Unknown),
            (trust_types::SingleWriterEvidence::None, EvidenceStatus::Failed),
        ] {
            let payload = TyTemporalModelPayload::refutation_only(&VcKind::Temporal {
                property: "AG !bad".to_string(),
                machine: Some(StateMachineMetadata::mmap_temporal_model(single_writer)),
            })
            .expect("Temporal is a ty-owned kind")
            .with_vocabulary(["bad".to_string()]);
            assert!(payload.is_refutation_only());
            let obligation = temporal_obligation(vec![MetadataEntry {
                key: TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
                value: payload.to_metadata_value().expect("payload serializes"),
            }]);
            let evidence = engine.verify(&bundle(&obligation), &[obligation]).remove(0);
            assert_eq!(evidence.status, want, "{evidence:#?}");
            assert!(evidence.proof_strength.is_none());
            if want == EvidenceStatus::Unknown {
                assert!(
                    evidence.diagnostics.iter().any(|d| d.contains("refutation-only")),
                    "{:#?}",
                    evidence.diagnostics
                );
            } else {
                assert!(evidence.counterexample.is_some());
            }
        }
    }

    #[test]
    fn non_ty_kinds_are_not_supported() {
        let engine = NativeTyEngine::new();
        let mut obligation = temporal_obligation(Vec::new());
        obligation.kind = ObligationKind::Assertion;
        assert!(!engine.supports(&obligation).is_supported());
        assert!(engine.verify(&bundle(&obligation), &[obligation]).is_empty());
    }

    // ---- L1b (Critique C-1, change 1): typed completeness for refutation-only checks ----

    fn proved(strength: trust_types::ProofStrength) -> VerificationResult {
        VerificationResult::Proved {
            solver: "ty".into(),
            time_ms: 0,
            strength,
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn failed(
        assignments: Option<Vec<(String, trust_types::CounterexampleValue)>>,
    ) -> VerificationResult {
        VerificationResult::Failed {
            solver: "ty".into(),
            time_ms: 0,
            counterexample: assignments.map(trust_types::Counterexample::new),
        }
    }

    /// A refutation-only obligation over `machine` whose vocabulary is
    /// `{bad}` (the mmap model's one atom).
    fn refutation_only_obligation(
        property: &str,
        machine: StateMachineMetadata,
    ) -> TrustObligation {
        refutation_only_obligation_with(property, machine, Some(&["bad"]))
    }

    fn refutation_only_obligation_with(
        property: &str,
        machine: StateMachineMetadata,
        vocabulary: Option<&[&str]>,
    ) -> TrustObligation {
        let mut payload = TyTemporalModelPayload::refutation_only(&VcKind::Temporal {
            property: property.to_string(),
            machine: Some(machine),
        })
        .expect("Temporal is a ty-owned kind");
        if let Some(atoms) = vocabulary {
            payload = payload.with_vocabulary(atoms.iter().map(|a| (*a).to_string()));
        }
        assert!(payload.is_refutation_only());
        temporal_obligation(vec![MetadataEntry {
            key: TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: payload.to_metadata_value().expect("payload serializes"),
        }])
    }

    fn multi_writer() -> StateMachineMetadata {
        StateMachineMetadata::mmap_temporal_model(trust_types::SingleWriterEvidence::None)
    }

    fn single_writer() -> StateMachineMetadata {
        StateMachineMetadata::mmap_temporal_model(trust_types::SingleWriterEvidence::Verified)
    }

    fn wire(obligation: &TrustObligation) -> ObligationEvidence {
        NativeTyEngine::new()
            .verify(&bundle(obligation), std::slice::from_ref(obligation))
            .remove(0)
    }

    fn is_inconclusive(v: &RefutationOnlyVerdict) -> bool {
        matches!(v, RefutationOnlyVerdict::Inconclusive { .. })
    }

    #[test]
    fn classify_complete_exploration_is_exhaustive() {
        let sound = trust_types::ProofStrength {
            reasoning: trust_types::ReasoningKind::ExplicitStateModel,
            assurance: trust_types::AssuranceLevel::Sound,
        };
        assert_eq!(
            classify(&proved(sound), true),
            RefutationOnlyVerdict::NoCounterexample {
                completeness: RefutationCompleteness::Exhaustive
            }
        );
    }

    #[test]
    fn classify_bounded_strength_is_truncated() {
        assert_eq!(
            classify(&proved(trust_types::ProofStrength::bounded(4096)), true),
            RefutationOnlyVerdict::NoCounterexample {
                completeness: RefutationCompleteness::Truncated { states: 4096 }
            }
        );
    }

    #[test]
    fn classify_unrecognised_strength_is_inconclusive_never_exhaustive() {
        // Sound, but not the explicit-state exploration ty reports: the
        // mapping does not guess.
        let other = trust_types::ProofStrength {
            reasoning: trust_types::ReasoningKind::Pdr,
            assurance: trust_types::AssuranceLevel::Sound,
        };
        assert!(matches!(
            classify(&proved(other), true),
            RefutationOnlyVerdict::Inconclusive { .. }
        ));
    }

    #[test]
    fn classify_unknown_is_inconclusive_never_no_counterexample() {
        let unknown = VerificationResult::Unknown {
            solver: "ty".into(),
            time_ms: 0,
            reason: "state budget".to_string(),
        };
        match classify(&unknown, true) {
            RefutationOnlyVerdict::Inconclusive { reason } => {
                assert!(reason.contains("state budget"), "{reason}");
            }
            v => panic!("an Unknown read {v:?}"),
        }
        let timeout = VerificationResult::Timeout { solver: "ty".into(), timeout_ms: 10 };
        assert!(matches!(classify(&timeout, true), RefutationOnlyVerdict::Inconclusive { .. }));
    }

    #[test]
    fn classify_failed_trace_is_a_counterexample_and_a_malformed_one_is_inconclusive() {
        use trust_types::CounterexampleValue as V;
        let step = |i: usize, v: V| (format!("step_{i}_q{i}"), v);
        assert_eq!(
            classify(&failed(Some(vec![step(0, V::Int(0)), step(1, V::Uint(3))])), true),
            RefutationOnlyVerdict::Counterexample { trace: vec![0, 3] }
        );
        for (what, bad) in [
            ("no counterexample", None),
            ("an empty trace", Some(Vec::new())),
            ("a negative state id", Some(vec![step(0, V::Int(-1))])),
            ("a non-integer value", Some(vec![step(0, V::Term("q0".to_string()))])),
            ("a boolean value", Some(vec![step(0, V::Bool(true))])),
            ("steps out of order", Some(vec![step(1, V::Int(0)), step(0, V::Int(1))])),
        ] {
            assert!(
                matches!(classify(&failed(bad), true), RefutationOnlyVerdict::Inconclusive { .. }),
                "{what} must be inconclusive"
            );
        }
    }

    #[test]
    fn classify_answers_only_for_a_refutation_only_payload() {
        let sound = trust_types::ProofStrength {
            reasoning: trust_types::ReasoningKind::ExplicitStateModel,
            assurance: trust_types::AssuranceLevel::Sound,
        };
        for result in [
            proved(sound),
            failed(Some(vec![("step_0_q0".to_string(), trust_types::CounterexampleValue::Int(0))])),
        ] {
            assert!(matches!(classify(&result, false), RefutationOnlyVerdict::Inconclusive { .. }));
        }
    }

    #[test]
    fn check_refutation_only_types_the_derived_model_answer() {
        let engine = NativeTyEngine::new();
        let ok = refutation_only_obligation(
            "AG !bad",
            StateMachineMetadata::mmap_temporal_model(trust_types::SingleWriterEvidence::Verified),
        );
        assert_eq!(
            engine.check_refutation_only(&ok),
            RefutationOnlyVerdict::NoCounterexample {
                completeness: RefutationCompleteness::Exhaustive
            }
        );
        let bad = refutation_only_obligation(
            "AG !bad",
            StateMachineMetadata::mmap_temporal_model(trust_types::SingleWriterEvidence::None),
        );
        match engine.check_refutation_only(&bad) {
            RefutationOnlyVerdict::Counterexample { trace } => {
                assert_eq!(trace.first(), Some(&0), "the trace starts at the initial state");
                assert!(trace.len() > 1, "{trace:?}");
            }
            v => panic!("the multi-writer model must be refuted: {v:?}"),
        }
    }

    #[test]
    fn check_refutation_only_malformed_atom_is_inconclusive() {
        let engine = NativeTyEngine::new();
        let obligation = refutation_only_obligation(
            "AG !fd-inherit violation",
            StateMachineMetadata::mmap_temporal_model(trust_types::SingleWriterEvidence::Verified),
        );
        match engine.check_refutation_only(&obligation) {
            RefutationOnlyVerdict::Inconclusive { reason } => {
                assert!(reason.contains("parse"), "{reason}");
            }
            v => panic!("a formula ty cannot parse is never answered: {v:?}"),
        }
    }

    #[test]
    fn check_refutation_only_payload_errors_are_inconclusive() {
        let engine = NativeTyEngine::new();
        let missing = temporal_obligation(Vec::new());
        let malformed = temporal_obligation(vec![MetadataEntry {
            key: TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: "{not json".to_string(),
        }]);
        // A full (proof-capable) payload is not a derived model.
        let full = temporal_obligation(vec![mmap_model_metadata(
            trust_types::SingleWriterEvidence::Verified,
        )]);
        for (what, o) in [("missing", missing), ("malformed", malformed), ("full", full)] {
            assert!(
                matches!(
                    engine.check_refutation_only(&o),
                    RefutationOnlyVerdict::Inconclusive { .. }
                ),
                "{what} payload must be inconclusive"
            );
        }
    }

    /// FC-2: no refutation-only path carries a proof strength, and the wire
    /// stays `Unknown` (no counterexample, truncated, inconclusive) or
    /// `Failed` (refuted).
    #[test]
    fn refutation_only_paths_never_carry_proof_strength() {
        let engine = NativeTyEngine::new();
        for (property, single_writer, want) in [
            ("AG !bad", trust_types::SingleWriterEvidence::Verified, EvidenceStatus::Unknown),
            ("AG !bad", trust_types::SingleWriterEvidence::None, EvidenceStatus::Failed),
            (
                "AG !fd-inherit violation",
                trust_types::SingleWriterEvidence::Verified,
                EvidenceStatus::Unknown,
            ),
        ] {
            let obligation = refutation_only_obligation(
                property,
                StateMachineMetadata::mmap_temporal_model(single_writer),
            );
            let evidence = engine.verify(&bundle(&obligation), &[obligation]).remove(0);
            assert_eq!(evidence.status, want, "{evidence:#?}");
            assert!(evidence.proof_strength.is_none(), "{evidence:#?}");
        }
        // The truncated arm, which no small machine reaches: built from the
        // typed value, it is Unknown, carries no strength and says so.
        let obligation = refutation_only_obligation(
            "AG !bad",
            StateMachineMetadata::mmap_temporal_model(trust_types::SingleWriterEvidence::Verified),
        );
        let payload = NativeTyEngine::transported_model(&obligation).expect("transported");
        let evidence = engine.refutation_only_unknown(
            &obligation,
            &payload,
            &RefutationOnlyVerdict::NoCounterexample {
                completeness: RefutationCompleteness::Truncated { states: 7 },
            },
        );
        assert_eq!(evidence.status, EvidenceStatus::Unknown);
        assert!(evidence.proof_strength.is_none());
        assert!(evidence.diagnostics.iter().any(|d| d.contains("refutation-only")));
        assert!(evidence.diagnostics.iter().any(|d| d.contains("truncated") && d.contains('7')));
    }

    // ---- Red-team holes H1 and H2 (L1b): what an "Exhaustive" answer is about ----

    /// H1. An atom that names no label still got a clean answer: `AG !bda`
    /// (a misspelt `bad`) over the REFUTABLE multi-writer machine answered
    /// `NoCounterexample { Exhaustive }`, and `AG bda` would refute
    /// spuriously. Now the payload declares its vocabulary and the engine
    /// refuses an atom outside it, typed and on the wire.
    #[test]
    fn refutation_only_atom_outside_the_vocabulary_is_inconclusive() {
        let engine = NativeTyEngine::new();
        let real = refutation_only_obligation("AG !bad", multi_writer());
        assert!(matches!(
            engine.check_refutation_only(&real),
            RefutationOnlyVerdict::Counterexample { .. }
        ));
        for formula in ["AG !bda", "AG bda", "AG (!bad && !bda)", "EF bda", "A[!bad U bda]"] {
            for machine in [multi_writer(), single_writer()] {
                let o = refutation_only_obligation(formula, machine);
                match engine.check_refutation_only(&o) {
                    RefutationOnlyVerdict::Inconclusive { reason } => {
                        assert!(reason.contains("`bda`"), "{formula}: {reason}");
                    }
                    v => panic!("`{formula}` names an atom outside the vocabulary: {v:?}"),
                }
                let evidence = wire(&o);
                assert_eq!(evidence.status, EvidenceStatus::Unknown, "{formula}: {evidence:#?}");
                assert!(evidence.proof_strength.is_none() && evidence.counterexample.is_none());
            }
        }
        // A declared atom no state carries is the fixed program's case: a
        // clean answer, because the producer said the atom is real.
        let fixed = refutation_only_obligation("AG !bad", single_writer());
        assert_eq!(
            engine.check_refutation_only(&fixed),
            RefutationOnlyVerdict::NoCounterexample {
                completeness: RefutationCompleteness::Exhaustive
            }
        );
    }

    /// H1. Without a declared vocabulary nothing is answered: not "no
    /// counterexample" and not a refutation (typed Inconclusive, wire
    /// Unknown, never Failed).
    #[test]
    fn refutation_only_payload_without_a_vocabulary_is_inconclusive() {
        let engine = NativeTyEngine::new();
        for (formula, machine) in
            [("AG !bad", multi_writer()), ("AG !bad", single_writer()), ("AG !bda", multi_writer())]
        {
            let o = refutation_only_obligation_with(formula, machine, None);
            match engine.check_refutation_only(&o) {
                RefutationOnlyVerdict::Inconclusive { reason } => {
                    assert!(reason.contains("vocabulary"), "{formula}: {reason}");
                }
                v => panic!("`{formula}` without a vocabulary answered {v:?}"),
            }
            let evidence = wire(&o);
            assert_eq!(evidence.status, EvidenceStatus::Unknown, "{formula}: {evidence:#?}");
            assert!(evidence.proof_strength.is_none() && evidence.counterexample.is_none());
        }
    }

    /// H1. A vocabulary that does not cover the machine's labels is not this
    /// machine's: inconclusive even for a formula over declared atoms.
    #[test]
    fn refutation_only_label_outside_the_vocabulary_is_inconclusive() {
        let engine = NativeTyEngine::new();
        let o = refutation_only_obligation_with("AG !good", multi_writer(), Some(&["good"]));
        match engine.check_refutation_only(&o) {
            RefutationOnlyVerdict::Inconclusive { reason } => {
                assert!(reason.contains("`bad`"), "{reason}");
            }
            v => panic!("a machine labelled outside its vocabulary answered {v:?}"),
        }
        assert_eq!(wire(&o).status, EvidenceStatus::Unknown);
    }

    /// H1. A refutation-only payload is vetted only as CTL over a machine:
    /// a liveness payload (whose predicate no vocabulary vets) is
    /// inconclusive, and so on the wire.
    #[test]
    fn refutation_only_non_ctl_payload_is_inconclusive() {
        let payload = TyTemporalModelPayload::refutation_only(&VcKind::Liveness {
            property: trust_types::LivenessProperty {
                name: "eventually_bad".to_string(),
                operator: trust_types::TemporalOperator::Eventually,
                predicate: "bad".to_string(),
                consequent: None,
                fairness: Vec::new(),
            },
            machine: Some(multi_writer()),
        })
        .expect("Liveness is a ty-owned kind")
        .with_vocabulary(["bad".to_string()]);
        let o = temporal_obligation(vec![MetadataEntry {
            key: TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: payload.to_metadata_value().expect("payload serializes"),
        }]);
        assert!(is_inconclusive(&NativeTyEngine::new().check_refutation_only(&o)));
        let evidence = wire(&o);
        assert_ne!(evidence.status, EvidenceStatus::Proved);
        assert_ne!(evidence.status, EvidenceStatus::Failed);
        assert!(evidence.proof_strength.is_none());
    }

    /// H2. A duplicate key in the payload's `labels` map was accepted (last
    /// wins), so `"3":["bad"],"3":[]` erased the refutable machine's bad
    /// state and the answer was `NoCounterexample { Exhaustive }`. Now any
    /// duplicate key is a payload error: inconclusive typed, unsupported on
    /// the wire, for the refutation-only and the full lane alike (the full
    /// lane PROVED the erased machine).
    #[test]
    fn duplicate_label_keys_in_a_payload_are_refused() {
        let engine = NativeTyEngine::new();
        let ro = refutation_only_obligation("AG !bad", multi_writer());
        let full =
            temporal_obligation(vec![mmap_model_metadata(trust_types::SingleWriterEvidence::None)]);
        for (lane, o) in [("refutation-only", ro), ("full", full)] {
            let value = o.metadata[0].value.clone();
            assert!(value.contains("\"3\":[\"bad\"]"), "{value}");
            for (what, dup) in [
                ("bad erased", "\"3\":[\"bad\"],\"3\":[]"),
                ("bad erased, other order", "\"3\":[],\"3\":[\"bad\"],\"3\":[]"),
                ("bad kept twice", "\"3\":[\"bad\"],\"3\":[\"bad\"]"),
                ("an escaped twin key", "\"3\":[\"bad\"],\"\\u0033\":[]"),
            ] {
                let mut t = o.clone();
                t.metadata[0].value = value.replacen("\"3\":[\"bad\"]", dup, 1);
                let v = engine.check_refutation_only(&t);
                assert!(is_inconclusive(&v), "{lane}, {what}: {v:?}");
                let evidence = wire(&t);
                assert_eq!(evidence.status, EvidenceStatus::Unsupported, "{lane}, {what}");
                assert!(
                    evidence.diagnostics.iter().any(|d| d.contains("twice")),
                    "{lane}, {what}: {:#?}",
                    evidence.diagnostics
                );
            }
        }
    }

    /// H2. The same state under two spellings of its index is one state
    /// keyed twice, whatever the JSON text looks like.
    #[test]
    fn a_state_labelled_under_two_spellings_is_refused() {
        let value = refutation_only_obligation("AG !bad", multi_writer()).metadata[0].value.clone();
        // A leading-zero spelling either does not parse as an index or
        // names state 3 again: never a silent override.
        let aliased = value.replacen("\"3\":[\"bad\"]", "\"3\":[\"bad\"],\"03\":[]", 1);
        let err = TyTemporalModelPayload::from_metadata_value(&aliased)
            .expect_err("an aliased state key must not parse");
        assert!(err.contains("twice") || err.contains("invalid"), "{err}");
        let mut o = temporal_obligation(Vec::new());
        o.metadata.push(MetadataEntry {
            key: TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: aliased,
        });
        assert!(is_inconclusive(&NativeTyEngine::new().check_refutation_only(&o)));
    }
}
