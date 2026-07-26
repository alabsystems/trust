//! Capability and obligation-kind enumeration helpers for the full verifier.

use trust_verifier_api::{EngineCapability, ObligationKind, SupportLevel};

use super::policy::{TRUST_VC_HARDENED_NAMESPACE, TRUST_VC_HARDENED_WILDCARD};
use super::routing::{PrimaryEngine, obligation_route_for_kind};

pub(super) fn all_full_verification_capabilities() -> Vec<EngineCapability> {
    all_full_verification_obligation_kinds()
        .into_iter()
        .map(|obligation_kind| EngineCapability {
            obligation_kind,
            support: SupportLevel::Preferred,
        })
        .collect()
}

pub(super) fn all_full_verification_obligation_kinds() -> Vec<ObligationKind> {
    let mut kinds = vec![
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::Assertion,
        ObligationKind::Invariant,
        ObligationKind::LoopInvariant,
        ObligationKind::ArithmeticSafety,
        ObligationKind::BoundsCheck,
        ObligationKind::MemorySafety,
        ObligationKind::Ownership,
        ObligationKind::Refinement,
        ObligationKind::Termination,
        ObligationKind::TemporalSafety,
        ObligationKind::Liveness,
        ObligationKind::Protocol,
    ];
    kinds.extend(hardened_custom_obligation_kinds());
    kinds
}

pub(super) fn obligation_kinds_owned_by(primary: PrimaryEngine) -> Vec<ObligationKind> {
    all_full_verification_obligation_kinds()
        .into_iter()
        .filter(|kind| {
            obligation_route_for_kind(kind).is_some_and(|route| route.primary == primary)
        })
        .collect()
}

pub(super) fn hardened_custom_obligation_kinds() -> Vec<ObligationKind> {
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
