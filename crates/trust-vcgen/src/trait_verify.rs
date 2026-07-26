// trust_vcgen/trait_verify.rs: Trait contract inheritance verification
//
// Verifies that trait implementations satisfy the Liskov Substitution Principle:
// - Impl preconditions must be at least as weak as trait preconditions (contravariance)
// - Impl postconditions must be at least as strong as trait postconditions (covariance)
//
// This ensures any code written against the trait contract remains correct when
// a concrete impl is substituted.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

/// Trust: A trait method's contract (preconditions and postconditions).
#[derive(Debug, Clone)]
pub struct TraitContract {
    /// Fully qualified trait name (e.g., "std::iter::Iterator").
    pub trait_name: String,
    /// Method name within the trait.
    pub method: String,
    /// Source-level formal parameter names in declaration order.
    ///
    /// These names are part of the predicate binding environment. Two
    /// syntactically equal formulas are not comparable when (for example) `x`
    /// denotes argument 1 in the trait but argument 2 in the impl.
    pub parameter_names: Vec<String>,
    /// Preconditions the trait promises callers can rely on being accepted.
    pub preconditions: Vec<Formula>,
    /// Postconditions the trait promises callers can rely on being guaranteed.
    pub postconditions: Vec<Formula>,
}

/// Trust: An impl's contract for a trait method.
#[derive(Debug, Clone)]
pub struct ImplContract {
    /// The concrete type implementing the trait (e.g., "MyVec").
    pub impl_type: String,
    /// Method name (must match a trait method).
    pub method: String,
    /// Source-level formal parameter names in declaration order.
    ///
    /// Liskov verification fails closed unless this is exactly aligned with
    /// [`TraitContract::parameter_names`].
    pub parameter_names: Vec<String>,
    /// Preconditions the impl requires.
    pub preconditions: Vec<Formula>,
    /// Postconditions the impl guarantees.
    pub postconditions: Vec<Formula>,
}

/// Trust: Verify that an impl's contract satisfies its trait's contract (Liskov).
///
/// Generates verification conditions checking two properties:
///
/// 1. **Precondition contravariance**: We check that
///    (conjunction(P_trait) => conjunction(P_impl)) — i.e., anything accepted
///    by the complete trait precondition is also accepted by the impl. In
///    practice, the impl should have *weaker* (or equal) preconditions.
///    The VC is the negation of that implication; if SAT, the impl rejects
///    something the trait accepts.
///
/// 2. **Postcondition covariance**: For each trait postcondition Q_trait,
///    we check that (Q_impl_conj => Q_trait) — i.e., everything the impl
///    guarantees implies what the trait promises. The impl should have
///    *stronger* (or equal) postconditions.
///    VC formula: NOT(Q_impl_conj => Q_trait) — if SAT, the impl fails to
///    guarantee something the trait promises.
///
/// The two predicate environments must bind identical source parameter names
/// at every argument position. A mismatch is represented by a satisfiable
/// fail-closed VC; formula spellings alone cannot establish which call
/// argument a free variable denotes.
#[must_use]
pub fn verify_liskov(trait_c: &TraitContract, impl_c: &ImplContract) -> Vec<VerificationCondition> {
    // A free variable in a source contract is bound by the declaring method's
    // parameter environment, not by its spelling alone. Until the formulas
    // are capture-avoidably canonicalized to positional binders, accepting
    // differently named/reordered environments would conflate distinct call
    // arguments. Represent that unsupported comparison as a satisfiable
    // violation VC so every proof consumer fails closed.
    if trait_c.method != impl_c.method
        || trait_c.parameter_names != impl_c.parameter_names
        || !contract_binding_environment_is_well_formed(
            &trait_c.parameter_names,
            trait_c.preconditions.iter().chain(&trait_c.postconditions),
        )
        || !contract_binding_environment_is_well_formed(
            &impl_c.parameter_names,
            impl_c.preconditions.iter().chain(&impl_c.postconditions),
        )
    {
        return if trait_c.preconditions.is_empty()
            && trait_c.postconditions.is_empty()
            && impl_c.preconditions.is_empty()
            && impl_c.postconditions.is_empty()
        {
            Vec::new()
        } else {
            vec![VerificationCondition {
                kind: VcKind::Postcondition,
                function: format!(
                    "<{} as {}>::{} [unaligned contract binders]",
                    impl_c.impl_type, trait_c.trait_name, impl_c.method
                )
                .into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            }]
        };
    }

    let mut vcs = Vec::new();
    let location = SourceSpan::default();

    // Build conjunctions of both precondition sets. Liskov contravariance is
    // one implication over the complete predicates:
    //
    //     conjunction(trait_pre) => conjunction(impl_pre)
    //
    // Iterating individual trait clauses is too strong when there are several
    // clauses, and emits no check at all for the unsound case where the trait
    // has no requirement but the impl adds one.
    let trait_pre_conj = conjunction(&trait_c.preconditions);
    let impl_pre_conj = conjunction(&impl_c.preconditions);

    if !trait_c.preconditions.is_empty() || !impl_c.preconditions.is_empty() {
        let implication = Formula::Implies(Box::new(trait_pre_conj), Box::new(impl_pre_conj));
        vcs.push(VerificationCondition {
            kind: VcKind::Precondition {
                callee: format!(
                    "<{} as {}>::{}",
                    impl_c.impl_type, trait_c.trait_name, trait_c.method
                ),
            },
            function: format!(
                "<{} as {}>::{}",
                impl_c.impl_type, trait_c.trait_name, impl_c.method
            )
            .into(),
            location: location.clone(),
            formula: Formula::Not(Box::new(implication)),
            contract_metadata: None,
        });
    }

    // Build conjunction of all impl postconditions.
    let impl_post_conj = conjunction(&impl_c.postconditions);

    // Postcondition covariance: impl_post_conj => trait_post
    // The impl must guarantee at least everything the trait promises.
    // We negate the implication to find violations: NOT(impl_post => trait_post)
    for trait_post in &trait_c.postconditions {
        let implication =
            Formula::Implies(Box::new(impl_post_conj.clone()), Box::new(trait_post.clone()));
        vcs.push(VerificationCondition {
            kind: VcKind::Postcondition,
            function: format!(
                "<{} as {}>::{}",
                impl_c.impl_type, trait_c.trait_name, impl_c.method
            )
            .into(),
            location: location.clone(),
            formula: Formula::Not(Box::new(implication)),
            contract_metadata: None,
        });
    }

    vcs
}

/// Whether two compiler/source contract carriers have exact structural
/// identity under one unambiguous positional binder environment.
///
/// This is a proof by syntactic identity, so it deliberately rejects malformed
/// public carriers and differently named formals instead of trying to rename
/// free variables. Sequential syntactic renaming is not capture-safe for
/// swaps; non-identical contracts must use [`verify_liskov`] and discharge the
/// resulting VCs.
#[must_use]
pub fn liskov_contracts_have_exact_identity(
    trait_c: &TraitContract,
    impl_c: &ImplContract,
) -> bool {
    trait_c.method == impl_c.method
        && trait_c.parameter_names == impl_c.parameter_names
        && contract_binding_environment_is_well_formed(
            &trait_c.parameter_names,
            trait_c.preconditions.iter().chain(&trait_c.postconditions),
        )
        && contract_binding_environment_is_well_formed(
            &impl_c.parameter_names,
            impl_c.preconditions.iter().chain(&impl_c.postconditions),
        )
        && trait_c.preconditions == impl_c.preconditions
        && trait_c.postconditions == impl_c.postconditions
}

/// Check the public binder carrier before any formulas from it are compared.
///
/// The compiler supplies this carrier from an authenticated Rust signature,
/// but `trust-vcgen` is also a public library. Reject duplicate/reserved names
/// and free variables that cannot be traced to a formal or the canonical
/// return place, so two equally malformed caller-constructed carriers cannot
/// manufacture a tautological refinement.
fn contract_binding_environment_is_well_formed<'a>(
    parameter_names: &[String],
    formulas: impl Iterator<Item = &'a Formula>,
) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    for name in parameter_names {
        if !source_parameter_name_is_well_formed(name) || !seen.insert(name.as_str()) {
            return false;
        }
        match trust_types::source_contract_synthetic_name_collision(name) {
            None | Some(SourceContractSyntheticNameCollision::PositionalPlace) => {}
            Some(_) => return false,
        }
    }

    formulas
        .flat_map(Formula::free_variables)
        .all(|name| contract_free_variable_is_bound(&name, &seen))
}

fn source_parameter_name_is_well_formed(name: &str) -> bool {
    // The extractor's anonymous-pattern fallback is exactly `_N`, with N
    // one-based and no leading zeroes.
    if let Some(index) = name.strip_prefix('_')
        && !index.is_empty()
        && index.bytes().all(|byte| byte.is_ascii_digit())
    {
        return index.as_bytes()[0] != b'0';
    }

    let mut bytes = name.bytes();
    let Some(first) = bytes.next() else { return false };
    (first == b'_' || first.is_ascii_alphabetic())
        && bytes.all(|byte| byte == b'_' || byte.is_ascii_alphanumeric())
        && !matches!(name, "true" | "false" | "result" | "forall" | "exists")
        && trust_types::source_contract_synthetic_name_collision(name).is_none()
}

fn contract_free_variable_is_bound(
    name: &str,
    parameters: &std::collections::BTreeSet<&str>,
) -> bool {
    if return_place_derived_leaf(name) || parameter_derived_leaf(name, parameters) {
        return true;
    }
    name.strip_prefix("old_")
        .is_some_and(|entry_name| parameter_derived_leaf(entry_name, parameters))
}

fn return_place_derived_leaf(name: &str) -> bool {
    if matches!(name, "result" | "_0") {
        return true;
    }
    if let Some(base) = name.strip_suffix("__slice_len") {
        return return_place_derived_leaf(base);
    }
    if let Some((base, _)) = name.split_once('.') {
        return return_place_derived_leaf(base);
    }
    ["_len", "_discr", "_value", "_sign"]
        .into_iter()
        .any(|suffix| name.strip_suffix(suffix).is_some_and(return_place_derived_leaf))
}

fn parameter_derived_leaf(
    name: &str,
    parameters: &std::collections::BTreeSet<&str>,
) -> bool {
    if parameters.contains(name) {
        return true;
    }
    if let Some(base) = name.strip_suffix('*') {
        return parameter_derived_leaf(base, parameters);
    }
    if let Some(base) = name.strip_suffix("__slice_len") {
        return parameter_derived_leaf(base, parameters);
    }
    if let Some((base, _)) = name.split_once('.') {
        return parameter_derived_leaf(base, parameters);
    }
    ["_len", "_discr", "_value", "_sign"]
        .into_iter()
        .any(|suffix| name.strip_suffix(suffix).is_some_and(|base| {
            parameter_derived_leaf(base, parameters)
        }))
}

/// Build a conjunction of formulas. Returns `true` for empty input.
fn conjunction(formulas: &[Formula]) -> Formula {
    match formulas.len() {
        0 => Formula::Bool(true),
        1 => formulas[0].clone(),
        _ => Formula::And(formulas.to_vec()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: x > 0
    fn x_gt_0() -> Formula {
        Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)))
    }

    /// Helper: x >= 0
    fn x_ge_0() -> Formula {
        Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)))
    }

    /// Helper: result > 0
    fn result_gt_0() -> Formula {
        Formula::Gt(Box::new(Formula::Var("result".into(), Sort::Int)), Box::new(Formula::Int(0)))
    }

    /// Helper: result >= 0
    fn result_ge_0() -> Formula {
        Formula::Ge(Box::new(Formula::Var("result".into(), Sort::Int)), Box::new(Formula::Int(0)))
    }

    fn sample_trait_contract() -> TraitContract {
        TraitContract {
            trait_name: "Compute".to_string(),
            method: "compute".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        }
    }

    #[test]
    fn test_verify_liskov_identical_contracts_generates_vcs() {
        let trait_c = sample_trait_contract();
        let impl_c = ImplContract {
            impl_type: "MyComputer".to_string(),
            method: "compute".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);

        // 1 precondition check + 1 postcondition check
        assert_eq!(vcs.len(), 2);
        assert!(
            matches!(&vcs[0].kind, VcKind::Precondition { callee } if callee.contains("Compute"))
        );
        assert!(matches!(vcs[1].kind, VcKind::Postcondition));
    }

    #[test]
    fn test_verify_liskov_weaker_precondition_valid() {
        // Trait requires x > 0, impl accepts x >= 0 (weaker = accepts more = valid)
        let trait_c = sample_trait_contract();
        let impl_c = ImplContract {
            impl_type: "RelaxedComputer".to_string(),
            method: "compute".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_ge_0()],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        assert_eq!(vcs.len(), 2);

        // The precondition VC is NOT(x>0 => x>=0), which should be UNSAT
        // (meaning the impl validly weakens the precondition)
        let pre_vc = &vcs[0];
        assert!(
            matches!(&pre_vc.formula, Formula::Not(inner) if matches!(inner.as_ref(), Formula::Implies(_, _)))
        );
    }

    #[test]
    fn test_verify_liskov_stronger_postcondition_valid() {
        // Trait ensures result >= 0, impl ensures result > 0 (stronger = guarantees more = valid)
        let trait_c = sample_trait_contract();
        let impl_c = ImplContract {
            impl_type: "StrictComputer".to_string(),
            method: "compute".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_gt_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        assert_eq!(vcs.len(), 2);

        // The postcondition VC is NOT(result>0 => result>=0), which should be UNSAT
        // (meaning the stronger postcondition satisfies the weaker trait postcondition)
        let post_vc = &vcs[1];
        assert!(
            matches!(&post_vc.formula, Formula::Not(inner) if matches!(inner.as_ref(), Formula::Implies(_, _)))
        );
    }

    #[test]
    fn test_verify_liskov_stronger_precondition_generates_violation_vc() {
        // Trait requires x >= 0, but impl requires x > 0 (stronger = rejects more = INVALID)
        let trait_c = TraitContract {
            trait_name: "Compute".to_string(),
            method: "compute".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_ge_0()],
            postconditions: vec![result_ge_0()],
        };
        let impl_c = ImplContract {
            impl_type: "StricterComputer".to_string(),
            method: "compute".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        assert_eq!(vcs.len(), 2);

        // Precondition VC: NOT(x>=0 => x>0), which IS SAT (x=0 satisfies x>=0 but not x>0)
        // The solver would find this counterexample, proving the impl violates the trait contract.
        let pre_vc = &vcs[0];
        assert!(matches!(&pre_vc.kind, VcKind::Precondition { .. }));
        assert!(pre_vc.function.contains("StricterComputer"));
    }

    #[test]
    fn test_verify_liskov_weaker_postcondition_generates_violation_vc() {
        // Trait ensures result > 0, but impl only ensures result >= 0 (weaker = INVALID)
        let trait_c = TraitContract {
            trait_name: "Compute".to_string(),
            method: "compute".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_gt_0()],
        };
        let impl_c = ImplContract {
            impl_type: "WeakComputer".to_string(),
            method: "compute".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        assert_eq!(vcs.len(), 2);

        // Postcondition VC: NOT(result>=0 => result>0), which IS SAT (result=0)
        let post_vc = &vcs[1];
        assert!(matches!(post_vc.kind, VcKind::Postcondition));
        assert!(post_vc.function.contains("WeakComputer"));
    }

    #[test]
    fn test_verify_liskov_empty_contracts() {
        let trait_c = TraitContract {
            trait_name: "Empty".to_string(),
            method: "noop".to_string(),
            parameter_names: vec![],
            preconditions: vec![],
            postconditions: vec![],
        };
        let impl_c = ImplContract {
            impl_type: "MyEmpty".to_string(),
            method: "noop".to_string(),
            parameter_names: vec![],
            preconditions: vec![],
            postconditions: vec![],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        assert!(vcs.is_empty(), "empty contracts produce no VCs");
    }

    #[test]
    fn test_verify_liskov_multiple_preconditions() {
        // Trait has 2 preconditions
        let trait_c = TraitContract {
            trait_name: "Multi".to_string(),
            method: "process".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_gt_0(), x_ge_0()],
            postconditions: vec![result_ge_0()],
        };
        let impl_c = ImplContract {
            impl_type: "MultiImpl".to_string(),
            method: "process".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_ge_0()],
            postconditions: vec![result_gt_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        // One implication over the full precondition conjunction, plus one
        // postcondition VC.
        assert_eq!(vcs.len(), 2);
        assert_eq!(vcs.iter().filter(|v| matches!(v.kind, VcKind::Precondition { .. })).count(), 1);
        assert_eq!(vcs.iter().filter(|v| matches!(v.kind, VcKind::Postcondition)).count(), 1);
    }

    #[test]
    fn test_verify_liskov_multiple_postconditions() {
        let trait_c = TraitContract {
            trait_name: "Multi".to_string(),
            method: "process".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0(), result_gt_0()],
        };
        let impl_c = ImplContract {
            impl_type: "MultiImpl".to_string(),
            method: "process".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_gt_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        // 1 precondition + 2 postconditions = 3 VCs
        assert_eq!(vcs.len(), 3);
    }

    #[test]
    fn test_verify_liskov_vc_function_names_include_impl_and_trait() {
        let trait_c = sample_trait_contract();
        let impl_c = ImplContract {
            impl_type: "Foo".to_string(),
            method: "compute".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        for vc in &vcs {
            assert!(
                vc.function.contains("Foo") && vc.function.contains("Compute"),
                "function name should reference both impl type and trait: got {}",
                vc.function
            );
        }
    }

    #[test]
    fn test_conjunction_empty() {
        assert_eq!(conjunction(&[]), Formula::Bool(true));
    }

    #[test]
    fn test_conjunction_single() {
        let f = x_gt_0();
        assert_eq!(conjunction(std::slice::from_ref(&f)), f);
    }

    #[test]
    fn test_conjunction_multiple() {
        let formulas = vec![x_gt_0(), x_ge_0()];
        let result = conjunction(&formulas);
        assert!(matches!(result, Formula::And(ref v) if v.len() == 2));
    }

    #[test]
    fn test_verify_liskov_impl_with_no_preconditions_is_valid() {
        // An impl with no preconditions (accepts everything) is always valid
        let trait_c = sample_trait_contract();
        let impl_c = ImplContract {
            impl_type: "Permissive".to_string(),
            method: "compute".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        // 1 precondition VC (trait_pre => true, which is trivially valid) + 1 postcondition VC
        assert_eq!(vcs.len(), 2);

        // The precondition VC formula is NOT(x>0 => true) which is UNSAT — correct
        let pre_vc = &vcs[0];
        if let Formula::Not(inner) = &pre_vc.formula
            && let Formula::Implies(_, rhs) = inner.as_ref()
        {
            assert_eq!(**rhs, Formula::Bool(true), "empty impl preconditions should be true");
        }
    }

    #[test]
    fn test_verify_liskov_proof_levels() {
        let trait_c = sample_trait_contract();
        let impl_c = ImplContract {
            impl_type: "T".to_string(),
            method: "compute".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        for vc in &vcs {
            assert_eq!(
                vc.kind.proof_level(),
                ProofLevel::L1Functional,
                "trait contract VCs should be L1 functional"
            );
        }
    }

    #[test]
    fn test_verify_liskov_swapped_parameter_bindings_fail_closed() {
        let trait_c = TraitContract {
            trait_name: "Choose".to_string(),
            method: "choose".to_string(),
            parameter_names: vec!["self".to_string(), "x".to_string(), "y".to_string()],
            preconditions: vec![],
            postconditions: vec![Formula::Eq(
                Box::new(Formula::Var("result".to_string(), Sort::Int)),
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
            )],
        };
        let impl_c = ImplContract {
            impl_type: "Chooser".to_string(),
            method: "choose".to_string(),
            parameter_names: vec!["self".to_string(), "y".to_string(), "x".to_string()],
            preconditions: vec![],
            // The spelling is identical, but `x` is argument 2 for the trait
            // and argument 3 for the impl.
            postconditions: trait_c.postconditions.clone(),
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].formula, Formula::Bool(true));
        assert!(vcs[0].function.contains("unaligned contract binders"));
    }

    #[test]
    fn test_verify_liskov_impl_cannot_add_first_precondition() {
        let mut trait_c = sample_trait_contract();
        trait_c.preconditions.clear();
        let impl_c = ImplContract {
            impl_type: "Restrictive".to_string(),
            method: "compute".to_string(),
            parameter_names: vec!["x".to_string()],
            preconditions: vec![x_gt_0()],
            postconditions: vec![result_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        assert_eq!(vcs.len(), 2);
        assert!(matches!(
            &vcs[0].formula,
            Formula::Not(inner)
                if matches!(inner.as_ref(), Formula::Implies(lhs, _) if **lhs == Formula::Bool(true))
        ));
    }

    #[test]
    fn test_verify_liskov_equal_malformed_binders_fail_closed() {
        let trait_c = TraitContract {
            trait_name: "Malformed".to_string(),
            method: "run".to_string(),
            parameter_names: vec![],
            preconditions: vec![],
            postconditions: vec![x_ge_0()],
        };
        let impl_c = ImplContract {
            impl_type: "MalformedImpl".to_string(),
            method: "run".to_string(),
            parameter_names: vec![],
            preconditions: vec![],
            postconditions: vec![x_ge_0()],
        };

        let vcs = verify_liskov(&trait_c, &impl_c);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    #[test]
    fn test_verify_liskov_projection_like_formal_names_fail_closed() {
        let trait_c = TraitContract {
            trait_name: "Ambiguous".to_string(),
            method: "run".to_string(),
            parameter_names: vec!["x".to_string(), "x*".to_string()],
            preconditions: vec![],
            postconditions: vec![x_ge_0()],
        };
        let impl_c = ImplContract {
            impl_type: "AmbiguousImpl".to_string(),
            method: "run".to_string(),
            parameter_names: trait_c.parameter_names.clone(),
            preconditions: vec![],
            postconditions: trait_c.postconditions.clone(),
        };

        assert!(!liskov_contracts_have_exact_identity(&trait_c, &impl_c));
        let vcs = verify_liskov(&trait_c, &impl_c);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    #[test]
    fn test_source_parameter_name_grammar_distinguishes_fallbacks() {
        for accepted in ["x", "_name", "_1foo", "_0value", "_1", "_27"] {
            assert!(source_parameter_name_is_well_formed(accepted), "{accepted}");
        }
        for rejected in ["", "result", "x*", "x.y", "_0", "_01", "old_x", "x__slice_len"] {
            assert!(!source_parameter_name_is_well_formed(rejected), "{rejected}");
        }
    }
}
