//! Default verifier-api facade for builds that do not enable trust-mc-core.
//!
//! The proof-grade native adapter lives behind `trust-mc-core-types`. Keeping
//! this default facade metadata-only prevents ordinary trust-bmc consumers from
//! linking the AY/trust-mc solver stack while still failing closed through the
//! public verifier-api surface.

use trust_verifier_api::{
    EngineCapability, EngineKind, EngineManifest, EvidencePublicationMetadata, EvidenceStatus,
    ObligationEvidence, ObligationKind, ReasoningKind, SupportLevel, TrustObligation,
    ValidatedVerificationRequest, VerificationEngine,
};

use crate::{TrustMcConfig, TrustMcProofMode};

const ENGINE_NAME: &str = "trust-mc";
const TRUST_VC_HARDENED_NAMESPACE: &str = "trust.vc.hardened";
const TRUST_VC_HARDENED_WILDCARD: &str = "*";
const TRUST_VC_FORMULA_SCHEMA_METADATA_KEY: &str = "trust.vc.formula.schema";
const TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY: &str = "trust.vc.formula.payload";

pub const TRUST_MC_FULL_VERIFICATION_VERDICT_METADATA_KEY: &str =
    "trust-mc.full-verification-verdict.v1";
pub const TRUST_MC_TYPED_CHC_OBLIGATION_SCHEMA: &str = "trust-mc.typed-chc-obligation.v1";
pub const TRUST_MC_TYPED_CHC_BINDING_SCHEMA: &str = "trust-mc.typed-chc-binding.v1";
pub const TRUST_MC_TYPED_CHC_BINDING_METADATA_KEY: &str =
    "trust-mc.typed-chc-obligation.binding.v1";
pub const TRUST_MC_TYPED_CHC_SOURCE_DIGEST_METADATA_KEY: &str =
    "trust-mc.typed-chc-obligation.source_digest.sha256";
pub const TRUST_MC_TYPED_CHC_VC_DIGEST_METADATA_KEY: &str =
    "trust-mc.typed-chc-obligation.vc_digest.sha256";
pub const TRUST_MC_TYPED_CHC_SYNTHETIC_DIGEST_METADATA_KEY: &str =
    "trust-mc.typed-chc-obligation.synthetic_digest.sha256";

#[derive(Debug, Clone)]
pub struct TrustMcVerifierApiAdapter {
    manifest: EngineManifest,
    config: TrustMcConfig,
}

impl TrustMcVerifierApiAdapter {
    #[must_use]
    pub fn new(config: TrustMcConfig) -> Self {
        Self { manifest: trust_mc_manifest(), config }
    }

    #[must_use]
    pub fn config(&self) -> &TrustMcConfig {
        &self.config
    }

    fn unsupported_evidence(&self, obligation: &TrustObligation) -> ObligationEvidence {
        ObligationEvidence {
            evidence_id: format!("{}:{}:unsupported", ENGINE_NAME, obligation.obligation_id),
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest.clone(),
            status: EvidenceStatus::Unsupported,
            proof_strength: None,
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: vec![
                "trust-mc native verifier-api adapter is disabled in the default trust-bmc build; enable trust-bmc/trust-mc-core-types or trust-bmc/trust-build for proof-grade native evidence".to_string(),
            ],
        }
    }
}

impl Default for TrustMcVerifierApiAdapter {
    fn default() -> Self {
        Self::new(TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3))
    }
}

impl VerificationEngine for TrustMcVerifierApiAdapter {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if is_trust_mc_owned_obligation_kind(&obligation.kind)
            || is_typed_body_aware_e4_e5_obligation(obligation)
        {
            SupportLevel::Experimental {
                reason: "trust-mc lane is present but native proof adapter is feature-gated"
                    .to_string(),
            }
        } else {
            SupportLevel::Unsupported {
                reason: format!(
                    "trust-mc verifier-api adapter does not own {:?} obligations",
                    obligation.kind
                ),
            }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        let obligations = request.obligations();
        obligations.iter().map(|obligation| self.unsupported_evidence(obligation)).collect()
    }
}

fn is_typed_body_aware_e4_e5_obligation(obligation: &TrustObligation) -> bool {
    if !matches!(obligation.kind, ObligationKind::LoopInvariant | ObligationKind::Termination) {
        return false;
    }
    let Some(schema) = metadata_value(&obligation.metadata, TRUST_VC_FORMULA_SCHEMA_METADATA_KEY)
    else {
        return false;
    };
    if schema != trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION {
        return false;
    }
    let Some(payload) = metadata_value(&obligation.metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
    else {
        return false;
    };
    let Ok(predicate) =
        trust_types::json_depth::from_str_deep::<trust_verifier_api::TrustSpecPredicate>(payload)
    else {
        return false;
    };
    predicate.has_current_schema()
        && predicate.root_sort == trust_verifier_api::TrustSpecSort::Bool
        && predicate.root.sort == trust_verifier_api::TrustSpecSort::Bool
        && predicate.validate().is_ok()
        && has_current_compiler_vc_origin(obligation)
}

fn has_current_compiler_vc_origin(obligation: &TrustObligation) -> bool {
    let Some(encoded) =
        metadata_value(&obligation.metadata, trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
    else {
        return false;
    };
    let Ok(context) =
        trust_types::json_depth::from_str_deep::<trust_verifier_api::ObligationContext>(encoded)
    else {
        return false;
    };
    context.has_current_schema()
        && matches!(&context.producer, trust_verifier_api::ObligationProducer::CompilerMirExtract)
        && matches!(
            &context.origin,
            trust_verifier_api::ObligationOrigin::VerificationCondition {
                formula_schema: Some(schema),
                ..
            } if schema == trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION
        )
}

fn metadata_value<'a>(
    metadata: &'a [trust_verifier_api::MetadataEntry],
    key: &str,
) -> Option<&'a str> {
    let mut matches = metadata.iter().filter(|entry| entry.key == key);
    let value = matches.next()?.value.as_str();
    matches.next().is_none().then_some(value)
}

#[must_use]
pub fn trust_mc_owned_obligation_kinds() -> Vec<ObligationKind> {
    let mut kinds = vec![
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::Assertion,
        ObligationKind::ArithmeticSafety,
        ObligationKind::Invariant,
        ObligationKind::Protocol,
    ];
    kinds.extend(hardened_custom_obligation_kinds());
    kinds
}

#[must_use]
pub fn is_trust_mc_owned_obligation_kind(kind: &ObligationKind) -> bool {
    matches!(
        kind,
        ObligationKind::Assertion
            | ObligationKind::ArithmeticSafety
            | ObligationKind::Invariant
            | ObligationKind::Protocol
            // Trust (P1.2): body-aware `#[ensures]` VCs reach trust-mc as typed-CHC
            // Postcondition obligations; keep the stub's ownership set in step with
            // the native adapter's.
            | ObligationKind::Postcondition
            // Trust (P1.2 precedent, extended): call-site `#[requires]` VCs reach
            // trust-mc as typed-CHC Precondition obligations; kept in step.
            | ObligationKind::Precondition
    ) || is_hardened_custom_obligation_kind(kind)
}

fn is_hardened_custom_obligation_kind(kind: &ObligationKind) -> bool {
    matches!(
        kind,
        ObligationKind::Custom { namespace, .. } if namespace == TRUST_VC_HARDENED_NAMESPACE
    )
}

fn hardened_custom_obligation_kinds() -> Vec<ObligationKind> {
    [
        "raw_path_api",
        "path_identity",
        "permission_change",
        "permission_create",
        "permission_window",
        "utf8_reject",
        "byte_loss",
        "error_discard",
        "panic_boundary",
        "compat_observable",
        "process_semantics",
        "trust_domain",
        "trust_domain_order",
        "unsafe_operation",
        "ffi_boundary",
        "unknown",
        TRUST_VC_HARDENED_WILDCARD,
    ]
    .into_iter()
    .map(|name| ObligationKind::Custom {
        namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
        name: name.to_string(),
    })
    .collect()
}

fn trust_mc_manifest() -> EngineManifest {
    let mut manifest =
        EngineManifest::new(ENGINE_NAME, env!("CARGO_PKG_VERSION"), EngineKind::Reachability);
    manifest.capabilities = trust_mc_owned_obligation_kinds()
        .into_iter()
        .map(|obligation_kind| EngineCapability {
            obligation_kind,
            support: SupportLevel::Experimental {
                reason: "native trust-mc adapter is feature-gated".to_string(),
            },
        })
        .collect();
    manifest.proof_modes = vec![ReasoningKind::Chc, ReasoningKind::Pdr];
    manifest
}

#[cfg(test)]
mod tests {
    use trust_verifier_api::{
        MetadataEntry, ObligationContext, ObligationOrigin, ObligationProducer, SourceLocation,
        TrustSpecExpr, TrustSpecPredicate,
    };

    use super::*;

    fn obligation(kind: ObligationKind) -> TrustObligation {
        TrustObligation {
            obligation_id: "dynamic-loop-vc".to_string(),
            kind,
            contract_id: None,
            proof_item_id: None,
            source: SourceLocation::default(),
            description: "test dynamic loop VC ownership".to_string(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: Vec::new(),
        }
    }

    fn add_valid_compiler_vc_metadata(obligation: &mut TrustObligation) {
        let predicate = TrustSpecPredicate::new(TrustSpecExpr::bool_literal(false), Vec::new());
        obligation.metadata.extend([
            ObligationContext::new(
                ObligationProducer::CompilerMirExtract,
                ObligationOrigin::VerificationCondition {
                    vc_kind: "loop_contract".to_string(),
                    vc_index: 0,
                    formula_schema: Some(
                        trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
                    ),
                },
            )
            .to_metadata_entry()
            .expect("context serializes"),
            MetadataEntry {
                key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
                value: trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: serde_json::to_string(&predicate).expect("predicate serializes"),
            },
        ]);
    }

    #[test]
    fn dynamic_e4_e5_ownership_requires_unique_compiler_vc_origin() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let mut valid = obligation(ObligationKind::LoopInvariant);
        add_valid_compiler_vc_metadata(&mut valid);
        assert!(adapter.supports(&valid).is_supported());

        let mut root = TrustSpecExpr::bool_literal(false);
        // Each typed expression node contributes multiple JSON object levels,
        // so 96 semantic nodes exceed serde_json's default recursion bound
        // while remaining below the public predicate validator's explicit
        // semantic-depth limit.
        for _ in 0..96 {
            root = TrustSpecExpr::unary(trust_verifier_api::TrustSpecUnaryOp::Not, root);
        }
        let encoded = serde_json::to_string(&TrustSpecPredicate::new(root, Vec::new()))
            .expect("deep predicate should serialize");
        assert!(
            serde_json::from_str::<TrustSpecPredicate>(&encoded).is_err(),
            "fixture must exceed serde_json's default recursion limit"
        );
        let mut deep = obligation(ObligationKind::Termination);
        add_valid_compiler_vc_metadata(&mut deep);
        deep.metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .expect("payload metadata")
            .value = encoded;
        assert!(adapter.supports(&deep).is_supported());

        let mut over_limit = TrustSpecExpr::bool_literal(false);
        for _ in 0..=trust_verifier_api::MAX_CONTRACT_PREDICATE_JSON_DEPTH {
            over_limit =
                TrustSpecExpr::unary(trust_verifier_api::TrustSpecUnaryOp::Not, over_limit);
        }
        let mut over_limit_obligation = obligation(ObligationKind::LoopInvariant);
        add_valid_compiler_vc_metadata(&mut over_limit_obligation);
        over_limit_obligation
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .expect("payload metadata")
            .value = serde_json::to_string(&TrustSpecPredicate::new(over_limit, Vec::new()))
            .expect("over-limit fixture serializes");
        assert!(
            !adapter.supports(&over_limit_obligation).is_supported(),
            "deep parsing must not widen the public semantic-depth limit"
        );

        let mut wrong_origin = obligation(ObligationKind::Termination);
        add_valid_compiler_vc_metadata(&mut wrong_origin);
        let context = wrong_origin
            .metadata
            .iter_mut()
            .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
            .expect("context metadata");
        *context = ObligationContext::new(
            ObligationProducer::CompilerMirExtract,
            ObligationOrigin::UnsupportedContract {
                contract_index: 0,
                compiler_contract_kind: "decreases".to_string(),
                reason: "raw marker".to_string(),
            },
        )
        .to_metadata_entry()
        .expect("wrong-origin context serializes");
        assert!(!adapter.supports(&wrong_origin).is_supported());

        let mut invalid_predicate = obligation(ObligationKind::LoopInvariant);
        add_valid_compiler_vc_metadata(&mut invalid_predicate);
        let undeclared = TrustSpecPredicate::new(
            TrustSpecExpr::variable("missing", trust_verifier_api::TrustSpecSort::Bool),
            Vec::new(),
        );
        invalid_predicate
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
            .expect("payload metadata")
            .value = serde_json::to_string(&undeclared).expect("invalid fixture serializes");
        assert!(
            !adapter.supports(&invalid_predicate).is_supported(),
            "feature-off ownership must apply the same complete typed-predicate validator"
        );

        let mut duplicate_context = valid.clone();
        let duplicate = duplicate_context
            .metadata
            .iter()
            .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
            .expect("context metadata")
            .clone();
        duplicate_context.metadata.push(duplicate);
        assert!(!adapter.supports(&duplicate_context).is_supported());

        let mut malformed_context = valid;
        malformed_context
            .metadata
            .iter_mut()
            .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
            .expect("context metadata")
            .value = "{}".to_string();
        assert!(!adapter.supports(&malformed_context).is_supported());
    }

    #[test]
    fn manifest_advertises_every_unconditional_owned_lane() {
        let adapter = TrustMcVerifierApiAdapter::default();
        let owned = trust_mc_owned_obligation_kinds();

        for kind in [
            ObligationKind::Precondition,
            ObligationKind::Postcondition,
            ObligationKind::Assertion,
            ObligationKind::ArithmeticSafety,
            ObligationKind::Invariant,
            ObligationKind::Protocol,
        ] {
            assert!(owned.contains(&kind), "owned-kind inventory omitted the actual {kind:?} lane");
            assert!(
                adapter
                    .manifest()
                    .capabilities
                    .iter()
                    .any(|capability| capability.obligation_kind == kind),
                "manifest omitted the actual {kind:?} lane"
            );
        }

        assert_eq!(adapter.manifest().capabilities.len(), owned.len());

        let future = ObligationKind::Custom {
            namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
            name: "future_kernel_object_identity".to_string(),
        };
        let wildcard = ObligationKind::Custom {
            namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
            name: TRUST_VC_HARDENED_WILDCARD.to_string(),
        };
        assert!(
            adapter.supports(&obligation(future)).is_supported(),
            "feature-off ownership must preserve future hardened categories"
        );
        assert!(adapter.manifest().capabilities.iter().any(|capability| {
            capability.obligation_kind == wildcard && capability.support.is_supported()
        }));
    }
}
