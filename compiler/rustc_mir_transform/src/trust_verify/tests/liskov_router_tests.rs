//! Trust (plan P4 / T4.1): the Liskov router `all_trait_impls_verified` builds
//! decides on the ay linked into trustc. These tests drive the deployed
//! inventory, `discover_router_backends` at the option defaults, on the exact
//! VCs `trust_vcgen::verify_liskov` emits for a one-clause trait postcondition,
//! so a lane that stops answering (a zero clock, a backend that only says
//! Unknown, a dropped slot) fails here rather than quietly refusing every
//! refinement. The UI pair `sealed_dyn_liskov_router_{proves,refutes}` drives
//! the same check through the compiler.

use super::super::*;

/// `result >= floor`, the shape the extractor gives `*result >= floor` on an
/// `i32` return (`Sort::Int`, the canonical return-place name).
fn result_at_least(floor: i128) -> Formula {
    Formula::Ge(Box::new(Formula::Var("result".into(), Sort::Int)), Box::new(Formula::Int(floor)))
}

/// The Liskov VCs for a trait promising `result >= 0` and an override
/// promising `result >= impl_floor`, with no preconditions on either side.
fn liskov_vcs(impl_floor: i128) -> Vec<VerificationCondition> {
    let trait_contract = trust_vcgen::TraitContract {
        trait_name: "c::sealed::Widget".into(),
        method: "rank".into(),
        parameter_names: vec!["self".into()],
        preconditions: Vec::new(),
        postconditions: vec![result_at_least(0)],
    };
    let impl_contract = trust_vcgen::ImplContract {
        impl_type: "c::Button".into(),
        method: "rank".into(),
        parameter_names: vec!["self".into()],
        preconditions: Vec::new(),
        postconditions: vec![result_at_least(impl_floor)],
    };
    assert!(
        !trust_vcgen::liskov_contracts_have_exact_identity(&trait_contract, &impl_contract),
        "an identical pair never reaches the router"
    );
    let vcs = trust_vcgen::verify_liskov(&trait_contract, &impl_contract);
    assert_eq!(vcs.len(), 1, "one covariance VC for one trait postcondition");
    vcs
}

/// The router `build_router` builds, at the option defaults.
fn deployed_router() -> trust_router::Router {
    let opts = rustc_session::config::Options::default();
    trust_router::Router::with_backends(discover_router_backends(
        opts.unstable_opts.trust_verify_timeout_ms,
        trust_types::determinism::EffortScale {
            conflicts_per_node: opts.unstable_opts.trust_verify_effort,
        },
    ))
}

#[test]
fn a_stronger_override_postcondition_is_proved_by_the_linked_ay() {
    let results = deployed_router().verify_all(&liskov_vcs(5));
    match &results[0].1 {
        VerificationResult::Proved { solver, strength, .. } => {
            assert_eq!(solver.as_str(), "ay-in-process", "the Liskov VC left the linked ay");
            assert_eq!(
                strength.assurance,
                trust_types::AssuranceLevel::SmtBacked,
                "the in-process lane mints a strict-checked unsat, never a bare one"
            );
        }
        other => panic!("`result >= 5 => result >= 0` must be proved in process, got {other:?}"),
    }
}

#[test]
fn a_weaker_override_postcondition_is_refuted_with_a_witness() {
    let results = deployed_router().verify_all(&liskov_vcs(-5));
    match &results[0].1 {
        VerificationResult::Failed { solver, counterexample: Some(_), .. } => {
            assert_eq!(solver.as_str(), "ay-in-process");
        }
        other => {
            panic!("`result >= -5 => result >= 0` must be refuted with a witness, got {other:?}")
        }
    }
}
