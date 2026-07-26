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

use trust_types::{
    StateMachineMetadata, TY_TEMPORAL_MODEL_METADATA_KEY, TyTemporalModelPayload, VcKind,
    VerificationResult,
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

        match result {
            VerificationResult::Proved { strength, .. } => {
                self.proved(bundle, obligation, &payload, raw_entry.as_deref(), strength)
            }
            VerificationResult::Failed { counterexample, .. } => {
                self.failed(obligation, &payload, counterexample)
            }
            VerificationResult::Unknown { reason, .. } => ObligationEvidence {
                evidence_id: format!("ty:native:unknown:{}", obligation.obligation_id),
                obligation_id: obligation.obligation_id.clone(),
                engine: self.manifest.clone(),
                status: EvidenceStatus::Unknown,
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
                proof_strength: None,
                artifacts: Vec::new(),
                counterexample: None,
                publication: EvidencePublicationMetadata::default(),
                diagnostics: vec![format!("unexpected ty verification result: {other:?}")],
            },
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

    fn mmap_model_metadata(single_writer: bool) -> MetadataEntry {
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
        let obligation = temporal_obligation(vec![mmap_model_metadata(true)]);
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
        let obligation = temporal_obligation(vec![mmap_model_metadata(true)]);
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
        let obligation = temporal_obligation(vec![mmap_model_metadata(true)]);
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
        let obligation = temporal_obligation(vec![mmap_model_metadata(false)]);
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

    #[test]
    fn non_ty_kinds_are_not_supported() {
        let engine = NativeTyEngine::new();
        let mut obligation = temporal_obligation(Vec::new());
        obligation.kind = ObligationKind::Assertion;
        assert!(!engine.supports(&obligation).is_supported());
        assert!(engine.verify(&bundle(&obligation), &[obligation]).is_empty());
    }
}
