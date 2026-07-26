//! Backend selection and preference ranking for VC dispatch.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;

use trust_types::*;

use crate::{
    BackendRole, BackendSelection, VerificationBackend, ownership_encoding, termination_dispatch,
};

pub(crate) fn backend_plan(
    backends: &[Arc<dyn VerificationBackend>],
    vc: &VerificationCondition,
) -> Vec<BackendSelection> {
    let mut plan: Vec<BackendSelection> = ranked_backends(backends, vc)
        .into_iter()
        .map(|entry| {
            let backend = &backends[entry.index];
            BackendSelection {
                index: entry.index,
                name: backend.name().to_string().into(),
                role: backend.role(),
                can_handle: entry.can_handle,
            }
        })
        .collect();

    // Keep the already-ranked plan stable for any tie groups.
    // The ordering is determined entirely by the index list above.
    plan.shrink_to_fit();
    plan
}

pub(crate) fn eligible_backends<'a>(
    backends: &'a [Arc<dyn VerificationBackend>],
    vc: &VerificationCondition,
) -> Vec<&'a Arc<dyn VerificationBackend>> {
    // Classify the VC's property kind once, then validate each
    // candidate backend against it. This prevents unsound dispatch (e.g.,
    // routing termination VCs to PDR/k-induction which only prove safety).
    let property = termination_dispatch::classify_property(vc);
    let mut eligible = Vec::new();

    for entry in ranked_backends(backends, vc) {
        if !entry.can_handle {
            continue;
        }
        let backend = &backends[entry.index];
        // Skip backends that are invalid for this property kind.
        let validity = termination_dispatch::validate_dispatch(property, backend.name());
        if validity.is_invalid() {
            continue;
        }
        eligible.push(backend);
    }
    eligible
}

#[derive(Clone, Copy)]
struct RankedBackend {
    index: usize,
    can_handle: bool,
    rank: u8,
}

fn ranked_backends(
    backends: &[Arc<dyn VerificationBackend>],
    vc: &VerificationCondition,
) -> Vec<RankedBackend> {
    let level = vc.kind.proof_level();
    // Trust: #178 Detect ownership VCs for trust_vc priority routing.
    let is_ownership = ownership_encoding::is_ownership_vc(vc);
    let mut ranked: Vec<RankedBackend> = backends
        .iter()
        .enumerate()
        .map(|(index, backend)| {
            let can_handle = backend.can_handle(vc);
            RankedBackend {
                index,
                can_handle,
                rank: backend_preference_rank(backend.role(), level, is_ownership),
            }
        })
        .collect();

    ranked.sort_by_key(|entry| (u8::from(!entry.can_handle), entry.rank, entry.index));
    ranked
}

fn backend_preference_rank(role: BackendRole, level: ProofLevel, is_ownership: bool) -> u8 {
    // Trust: #178 Ownership VCs rank the Ownership backend first.
    if is_ownership {
        return match role {
            BackendRole::Ownership => 0,
            BackendRole::SmtSolver => 1,
            BackendRole::Deductive => 2,
            BackendRole::BoundedModelChecker => 3,
            BackendRole::HigherOrder => 4,
            BackendRole::Temporal => 5,
            BackendRole::AbstractInterpretation => 6,
            BackendRole::General => 7,
        };
    }

    match level {
        ProofLevel::L0Safety => match role {
            // Trust: cheap interval/range front-line, tried before the SMT
            // solver so bounded overflow VCs prove in µs instead of timing out.
            BackendRole::AbstractInterpretation => 0,
            BackendRole::SmtSolver => 1,
            BackendRole::BoundedModelChecker => 2,
            BackendRole::Deductive => 3,
            BackendRole::Ownership => 4,
            BackendRole::HigherOrder => 5,
            BackendRole::Temporal => 6,
            BackendRole::General => 7,
        },
        ProofLevel::L1Functional => match role {
            BackendRole::Deductive => 0,
            BackendRole::HigherOrder => 1,
            BackendRole::SmtSolver => 2,
            BackendRole::BoundedModelChecker => 3,
            BackendRole::Ownership => 4,
            BackendRole::Temporal => 5,
            BackendRole::AbstractInterpretation => 6,
            BackendRole::General => 7,
        },
        // HigherOrder (clean) ranked 1 for L2Domain — clean handles
        // induction proofs needed for domain-level properties (universal
        // quantification, recursive structures). Temporal (ty) stays first
        // for liveness/fairness; clean is preferred over deductive (trust-wp)
        // for higher-order reasoning.
        ProofLevel::L2Domain => match role {
            BackendRole::Temporal => 0,
            BackendRole::HigherOrder => 1,
            BackendRole::Deductive => 2,
            BackendRole::Ownership => 3,
            BackendRole::SmtSolver => 4,
            BackendRole::BoundedModelChecker => 5,
            BackendRole::AbstractInterpretation => 6,
            BackendRole::General => 7,
        },
        // Default rank for any future ProofLevel variants.
        _ => 8,
    }
}
