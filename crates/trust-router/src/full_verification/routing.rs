//! Obligation → primary-engine routing tables for the full verifier.

use trust_verifier_api::{
    DeclineClass, EngineManifest, EvidenceStatus, ObligationKind, ProofStrength, ReasoningKind,
    TrustObligation,
};

use super::policy::{TRUST_VC_HARDENED_NAMESPACE, TRUST_VC_UNBOUNDED_ALLOCATION_NAMESPACE};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PrimaryEngine {
    TrustWp,
    TrustVc,
    TrustMc,
    Ty,
}

// TrustWP remains a recognized historical wire/provenance identity, but is not
// a required engine while it owns no dischargeable obligation kind.
pub(super) const REQUIRED_PRIMARY_ENGINES: [PrimaryEngine; 3] =
    [PrimaryEngine::TrustVc, PrimaryEngine::TrustMc, PrimaryEngine::Ty];

impl PrimaryEngine {
    pub(super) fn name(self) -> &'static str {
        match self {
            Self::TrustWp => "trust-wp",
            Self::TrustVc => "trust-vc",
            Self::TrustMc => "trust-mc",
            Self::Ty => "ty",
        }
    }

    pub(super) fn matches_manifest(self, manifest: &EngineManifest) -> bool {
        manifest.name == self.name()
    }

    pub(super) fn from_trust_ir_suite_name(name: &str) -> Option<Self> {
        // Trust: accept both hyphen and underscore variants. TrustIr's
        // `NativeVerifierSuite` Display/code emits underscore (`trust_wp`)
        // while the engine manifest name uses hyphen (`trust-wp`).
        match name.to_ascii_lowercase().as_str() {
            "trust-wp" | "trust_wp" => Some(Self::TrustWp),
            "trust-vc" | "trust_vc" => Some(Self::TrustVc),
            "trust-mc" | "trust_mc" => Some(Self::TrustMc),
            _ => None,
        }
    }

    pub(super) fn requires_trust_ir_native_bundle(self) -> bool {
        matches!(self, Self::TrustWp | Self::TrustVc | Self::TrustMc)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ProofFamily {
    TrustWpDeductive,
    TrustVcOwnership,
    TrustMcReachability,
    TyTemporal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RequiredAssurance {
    SmtBacked,
    Sound,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ObligationRoute {
    pub(super) obligation_kind: &'static str,
    pub(super) primary: PrimaryEngine,
    pub(super) proof_family: ProofFamily,
    pub(super) minimum_assurance: RequiredAssurance,
}

impl ObligationRoute {
    pub(super) fn accepts_strength(&self, strength: &ProofStrength) -> bool {
        if self.proof_family == ProofFamily::TrustWpDeductive {
            // Native replay establishes this Trusted derivation only. A
            // caller cannot promote it to a Clean-certified translation.
            return strength == &ProofStrength::deductive();
        }
        strength.is_publication_grade()
            && assurance_satisfies(strength, self.minimum_assurance)
            && self.accepts_reasoning(&strength.reasoning)
    }

    pub(super) fn accepts_reasoning(&self, reasoning: &ReasoningKind) -> bool {
        match self.proof_family {
            ProofFamily::TrustWpDeductive => matches!(reasoning, ReasoningKind::Deductive),
            ProofFamily::TrustVcOwnership => {
                matches!(reasoning, ReasoningKind::OwnershipAnalysis | ReasoningKind::Deductive)
            }
            ProofFamily::TrustMcReachability => {
                matches!(reasoning, ReasoningKind::Chc | ReasoningKind::Pdr)
            }
            ProofFamily::TyTemporal => matches!(
                reasoning,
                ReasoningKind::TemporalModelCheck | ReasoningKind::ExplicitStateModel
            ),
        }
    }

    pub(super) fn required_strength_description(&self) -> &'static str {
        match self.proof_family {
            ProofFamily::TrustWpDeductive => "trust-wp body-aware deductive Sound proof (Trusted)",
            ProofFamily::TrustVcOwnership => {
                "trust-vc ownership-analysis or deductive Sound+ proof"
            }
            ProofFamily::TrustMcReachability => "trust-mc CHC/PDR SmtBacked+ proof",
            ProofFamily::TyTemporal => "ty temporal or explicit-state Sound+ proof",
        }
    }
}

/// Route one typed obligation under the v6/D3 ownership split.
///
/// Precondition, postcondition, loop-invariant, and termination obligations are
/// TrustMC-owned whether or not a producer attached a body formula. A missing
/// formula fails closed in TrustMC; it never changes ownership or falls back to
/// the retired TrustWP contract lane. Producer-supplied suite metadata cannot
/// change this ownership table; it is checked later as a binding invariant.
pub(super) fn obligation_route(obligation: &TrustObligation) -> Option<ObligationRoute> {
    let body_aware_vc_kind = match &obligation.kind {
        ObligationKind::Postcondition => Some("Postcondition"),
        ObligationKind::Precondition => Some("Precondition"),
        ObligationKind::LoopInvariant => Some("LoopInvariant"),
        ObligationKind::Termination => Some("Termination"),
        _ => None,
    };
    if let Some(obligation_kind) = body_aware_vc_kind {
        return Some(ObligationRoute {
            obligation_kind,
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        });
    }
    obligation_route_for_kind(&obligation.kind)
}

/// A designated deductive-fallback route.
///
/// Newtyped so a PRIMARY route can never be handed to the fallback path by
/// mistake. A fallback is adjudicated AS ITSELF — its own engine, its own proof
/// family, its own assurance floor — because `route` is the sole anchor for the
/// artifact policy, the accepted reasoning family, and the native suite
/// identity. Reusing the primary's family would let a foreign proof satisfy a
/// requirement written to forbid it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct FallbackRoute(pub(super) ObligationRoute);

/// The deductive-fallback table.
///
/// Body-aware WP is an alternative deductive strategy for postconditions.
/// It carries its own Sound assurance floor and must replay against the same
/// typed body and original contract. Preconditions need call-site semantics
/// and remain outside this route.
pub(super) fn fallback_route(obligation: &TrustObligation) -> Option<FallbackRoute> {
    matches!(obligation.kind, ObligationKind::Postcondition).then_some(FallbackRoute(
        ObligationRoute {
            obligation_kind: "Postcondition",
            primary: PrimaryEngine::TrustWp,
            proof_family: ProofFamily::TrustWpDeductive,
            minimum_assurance: RequiredAssurance::Sound,
        },
    ))
}

/// Why a declined obligation is, or is not, eligible for a second engine.
///
/// Pure and total so the rules are testable without standing up a dispatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FallbackEligibility {
    /// Every rule held. The obligation may be re-attempted by the fallback.
    Eligible,
    /// The decline is terminal. The reason is kept for the audit trail.
    Terminal(FallbackRefusal),
}

/// The specific rule that made a decline terminal.
///
/// Enumerated so a refusal can be explained in a diagnostic rather than
/// silently doing nothing — "engine A declined, and here is why nobody else was
/// allowed to try" is the audit trail this mechanism owes a reader.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FallbackRefusal {
    /// The primary produced a definitive verdict, or a sibling row did.
    /// A refutation is settled; re-litigating it is laundering.
    Definitive,
    /// The primary's evidence was accepted. Nothing to retry.
    Accepted,
    /// Neither an inconclusive result nor an explicitly classified capability
    /// gap. Timeouts and cancellations are never retried here.
    NotADecline,
    /// No decline class, or a class that is not retryable. This is the default
    /// for every router-minted decline, every engine that has not been taught
    /// the distinction, and every older wire payload — terminal by construction.
    Unclassified,
    /// No fallback route is designated for this obligation.
    NoRoute,
    /// The designated fallback is the engine that already declined.
    SameEngine,
    /// The verification budget is exhausted; a retry would be unbounded work.
    BudgetExceeded,
}

/// Adjudicate whether a declined obligation may be re-attempted.
///
/// SOUNDNESS: this is written so that EVERY path not explicitly proven safe
/// returns `Terminal`. The rules are conjunctive and each is a positive test.
///
/// The caller must additionally establish, structurally, that the row came from
/// a real engine batch rather than one of the pre-dispatch declines — those are
/// router-minted and carry `decline: None`, so they are already caught by the
/// `Unclassified` arm, but relying on that alone would be relying on an
/// accident.
pub(super) fn fallback_eligibility(
    accepted: bool,
    status: EvidenceStatus,
    decline: Option<DeclineClass>,
    sibling_rows_are_definitive: bool,
    route: Option<FallbackRoute>,
    primary_engine_index: usize,
    fallback_engine_index: Option<usize>,
    budget_exceeded: bool,
) -> FallbackEligibility {
    use FallbackEligibility::{Eligible, Terminal};
    use FallbackRefusal as R;

    // A definitive verdict anywhere for this obligation ends the matter. This is
    // checked FIRST and covers the ladder hole: `rejected_primary_evidence` ranks
    // `Unsupported` above `Proved`, so an engine that returned BOTH a capability
    // decline and a Proved row the router rejected would present the decline as
    // the final row. Retrying there would erase the rejected proof that poisons
    // strict acceptance downstream.
    if sibling_rows_are_definitive {
        return Terminal(R::Definitive);
    }
    if matches!(status, EvidenceStatus::Proved | EvidenceStatus::Failed) {
        return Terminal(R::Definitive);
    }
    if accepted {
        return Terminal(R::Accepted);
    }
    if !matches!(status, EvidenceStatus::Unsupported | EvidenceStatus::Unknown) {
        return Terminal(R::NotADecline);
    }
    if status == EvidenceStatus::Unsupported && !DeclineClass::is_retryable(decline) {
        return Terminal(R::Unclassified);
    }
    if budget_exceeded {
        return Terminal(R::BudgetExceeded);
    }
    let Some(_route) = route else {
        return Terminal(R::NoRoute);
    };
    match fallback_engine_index {
        None => Terminal(R::NoRoute),
        Some(index) if index == primary_engine_index => Terminal(R::SameEngine),
        Some(_) => Eligible,
    }
}

pub(super) fn obligation_route_for_kind(kind: &ObligationKind) -> Option<ObligationRoute> {
    let route = match kind {
        ObligationKind::Precondition => ObligationRoute {
            obligation_kind: "Precondition",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        },
        ObligationKind::Postcondition => ObligationRoute {
            obligation_kind: "Postcondition",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        },
        ObligationKind::Assertion => ObligationRoute {
            obligation_kind: "Assertion",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        },
        ObligationKind::Invariant => ObligationRoute {
            obligation_kind: "Invariant",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        },
        ObligationKind::LoopInvariant => ObligationRoute {
            obligation_kind: "LoopInvariant",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        },
        ObligationKind::ArithmeticSafety => ObligationRoute {
            obligation_kind: "ArithmeticSafety",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        },
        ObligationKind::MemorySafety => ObligationRoute {
            obligation_kind: "MemorySafety",
            primary: PrimaryEngine::TrustVc,
            proof_family: ProofFamily::TrustVcOwnership,
            minimum_assurance: RequiredAssurance::Sound,
        },
        // BoundsCheck is trust-vc-owned end-to-end: the compiler constructs a
        // MIR-memory proof unit whose predicate is the negated guard-conjoined
        // bounds VC, and TrustVcTrustEngine discharges it with a replayable
        // certificate at import time. Without this route the full verifier
        // rejected the KIND before any engine saw the discharged evidence.
        ObligationKind::BoundsCheck => ObligationRoute {
            obligation_kind: "BoundsCheck",
            primary: PrimaryEngine::TrustVc,
            proof_family: ProofFamily::TrustVcOwnership,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::Ownership => ObligationRoute {
            obligation_kind: "Ownership",
            primary: PrimaryEngine::TrustVc,
            proof_family: ProofFamily::TrustVcOwnership,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::Refinement => ObligationRoute {
            obligation_kind: "Refinement",
            primary: PrimaryEngine::TrustVc,
            proof_family: ProofFamily::TrustVcOwnership,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::Termination => ObligationRoute {
            obligation_kind: "Termination",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        },
        ObligationKind::TemporalSafety => ObligationRoute {
            obligation_kind: "TemporalSafety",
            primary: PrimaryEngine::Ty,
            proof_family: ProofFamily::TyTemporal,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::Liveness => ObligationRoute {
            obligation_kind: "Liveness",
            primary: PrimaryEngine::Ty,
            proof_family: ProofFamily::TyTemporal,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::Protocol => ObligationRoute {
            obligation_kind: "Protocol",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        },
        ObligationKind::Custom { namespace, .. } if namespace == TRUST_VC_HARDENED_NAMESPACE => {
            ObligationRoute {
                obligation_kind: "HardenedBoundary",
                primary: PrimaryEngine::TrustMc,
                proof_family: ProofFamily::TrustMcReachability,
                minimum_assurance: RequiredAssurance::SmtBacked,
            }
        }
        // `trust.vc.unbounded_allocation` (#nia-oom) is trust-vc-owned
        // end-to-end on the BoundsCheck precedent above: the compiler
        // constructs a MIR-memory proof unit whose predicate is the negated
        // guard-conjoined `count >= CEILING` VC, and TrustVcTrustEngine
        // discharges it with a replayable certificate at import time. Routing
        // is DISPATCH, never proof: acceptance still requires the validated
        // proof unit plus the replayed certificate, and a payload-less or
        // unprovable obligation falls closed per-obligation.
        //
        // NEVER re-route this namespace to trust-mc / the whole-function CHC:
        // that proof does not encode the capacity budget and exactly that
        // mapping false-proved unbounded allocations (the recorded P0 at
        // trust-verifier-api's `TRUST_VC_UNBOUNDED_ALLOCATION_OBLIGATION_
        // NAMESPACE` doc).
        ObligationKind::Custom { namespace, .. }
            if namespace == TRUST_VC_UNBOUNDED_ALLOCATION_NAMESPACE =>
        {
            ObligationRoute {
                obligation_kind: "UnboundedAllocation",
                primary: PrimaryEngine::TrustVc,
                proof_family: ProofFamily::TrustVcOwnership,
                minimum_assurance: RequiredAssurance::Sound,
            }
        }
        ObligationKind::Custom { .. } => return None,
        _ => return None,
    };

    Some(route)
}

pub(super) fn assurance_satisfies(strength: &ProofStrength, minimum: RequiredAssurance) -> bool {
    match minimum {
        RequiredAssurance::SmtBacked => matches!(
            strength.assurance,
            trust_verifier_api::AssuranceLevel::SmtBacked
                | trust_verifier_api::AssuranceLevel::Sound
                | trust_verifier_api::AssuranceLevel::Certified
        ),
        RequiredAssurance::Sound => matches!(
            strength.assurance,
            trust_verifier_api::AssuranceLevel::Sound
                | trust_verifier_api::AssuranceLevel::Certified
        ),
    }
}
