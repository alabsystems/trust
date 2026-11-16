use clean_kernel::expr::BinderInfo;
use clean_kernel::level::Level;

use super::*;

fn identity() -> (Expr, Expr) {
    (
        Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        ),
        Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        ),
    )
}

fn false_type() -> Expr {
    Expr::pi(BinderInfo::Default, Expr::sort(Level::zero()), Expr::bvar(0))
}

fn theorem(name: Name, type_: Expr, value: Expr) -> ReplayInput {
    ReplayInput::Ordinary {
        declaration: Declaration::Theorem { name, level_params: vec![], type_, value },
        safety: DeclarationSafety::Safe,
    }
}

fn named(name: &str, type_: Expr, value: Expr) -> ReplayInput {
    theorem(Name::from_string(name), type_, value)
}

fn reference(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn replay(inputs: &[ReplayInput]) -> FreshReplay {
    let names: Vec<_> = inputs.iter().map(|input| input.name().clone()).collect();
    replay_closed_declarations(inputs, &names, ReplayLimits::default())
}

#[test]
fn valid_identity_really_passes_fresh_add_decl() {
    let (ty, value) = identity();
    let result = replay(&[named("Valid", ty.clone(), value.clone())]);
    let env = result.checked_environment().expect("valid fresh replay");
    let name = Name::from_string("Valid");
    assert_eq!(env.declaration_verification(&name), Some(DeclarationVerification::FullKernelCheck));
    let ci = env.get_const(&name).unwrap();
    assert_eq!(ci.type_, ty);
    assert_eq!(ci.value.as_ref(), Some(&value));
    assert_eq!(env.constants().count(), 1, "no assumed prelude was imported");
}

#[test]
fn actual_dependencies_are_checked_before_out_of_order_users() {
    let (ty, value) = identity();
    let result = replay(&[named("User", ty.clone(), reference("Leaf")), named("Leaf", ty, value)]);
    assert!(result.checked_environment().is_some(), "{:?}", result.report());
    assert_eq!(result.report().rows[0].dependencies, BTreeSet::from([Name::from_string("Leaf")]));
    assert!(result.report().rows.iter().all(|row| row.kernel_checked));
}

#[test]
fn self_reference_does_not_supply_its_own_proof() {
    let result = replay(&[named("Self", false_type(), reference("Self"))]);
    assert!(result.checked_environment().is_none());
    assert_eq!(result.report().rows[0].failures, [ReplayFailure::UnresolvedDependencyCycle]);
}

#[test]
fn mutual_reference_and_its_user_cannot_enter_the_checked_environment() {
    let result = replay(&[
        named("Left", false_type(), reference("Right")),
        named("Right", false_type(), reference("Left")),
        named("User", false_type(), reference("Left")),
    ]);
    assert!(result.checked_environment().is_none());
    assert_eq!(result.report().rows.len(), 3);
    assert!(result.report().rows.iter().all(|row| !row.kernel_checked
        && row.failures.contains(&ReplayFailure::UnresolvedDependencyCycle)));
}

#[test]
fn failed_leaf_taints_every_dependent_not_an_independent_valid_row() {
    let (ty, value) = identity();
    let result = replay(&[
        named("Bad", false_type(), value.clone()),
        named("User", false_type(), reference("Bad")),
        named("Transitive", false_type(), reference("User")),
        named("Valid", ty, value),
    ]);
    assert!(result.checked_environment().is_none(), "no accepted prefix of incomplete batch");
    assert!(matches!(result.report().rows[0].failures[0], ReplayFailure::KernelRejected(_)));
    assert!(
        result.report().rows[1]
            .failures
            .contains(&ReplayFailure::FailedDependency(Name::from_string("Bad")))
    );
    assert!(
        result.report().rows[2]
            .failures
            .contains(&ReplayFailure::FailedDependency(Name::from_string("User")))
    );
    assert!(result.report().rows[3].kernel_checked);
}

#[test]
fn absent_requested_identity_is_not_a_zero_error_success() {
    let result =
        replay_closed_declarations(&[], &[Name::from_string("Absent")], ReplayLimits::default());
    assert!(result.checked_environment().is_none());
    assert!(!result.report().inventory_errors.is_empty());
    assert_eq!(result.report().supplied_expected_identities, 1);
}

#[test]
fn omitted_and_extra_expected_rows_both_refuse() {
    let (ty, value) = identity();
    let inputs = [named("One", ty, value)];
    for expected in [
        vec![],
        vec![Name::from_string("Two")],
        vec![Name::from_string("One"), Name::from_string("Extra")],
    ] {
        let result = replay_closed_declarations(&inputs, &expected, ReplayLimits::default());
        assert!(result.checked_environment().is_none());
        assert!(!result.report().inventory_errors.is_empty());
    }
}

#[test]
fn duplicate_input_rows_are_retained_not_name_deduplicated() {
    let (ty, value) = identity();
    let one = named("One", ty, value);
    let result = replay(&[one.clone(), one]);
    assert!(result.checked_environment().is_none());
    assert_eq!(result.report().rows.len(), 2);
    assert!(
        result
            .report()
            .rows
            .iter()
            .all(|row| row.failures.contains(&ReplayFailure::DuplicateIdentity))
    );
}

#[test]
fn duplicate_expected_identity_is_refused_even_for_a_valid_input() {
    let (ty, value) = identity();
    let one = Name::from_string("One");
    let result = replay_closed_declarations(
        &[named("One", ty, value)],
        &[one.clone(), one],
        ReplayLimits::default(),
    );
    assert!(result.checked_environment().is_none());
    assert!(result.report().inventory_errors.iter().any(|error| error.contains("duplicate")));
}

#[test]
fn typed_quoted_and_numeric_names_are_not_display_string_identities() {
    let (ty, value) = identity();
    let names = [
        Name::anon().str("A.B"),
        Name::anon().str("A").str("B"),
        Name::anon().str("N").str("1"),
        Name::anon().str("N").num(1),
        Name::anon().str("fidèle"),
    ];
    assert_eq!(names.iter().cloned().collect::<BTreeSet<_>>().len(), names.len());
    let inputs: Vec<_> =
        names.iter().map(|name| theorem(name.clone(), ty.clone(), value.clone())).collect();
    let result = replay(&inputs);
    assert!(result.checked_environment().is_some(), "{:?}", result.report());
    assert_eq!(result.report().rows.len(), names.len());
}

#[test]
fn axioms_and_their_dependents_cannot_be_promoted_as_checked_proofs() {
    let axiom = ReplayInput::Ordinary {
        declaration: Declaration::Axiom {
            name: Name::from_string("Assumed"),
            level_params: vec![],
            type_: false_type(),
        },
        safety: DeclarationSafety::Safe,
    };
    let result = replay(&[axiom, named("User", false_type(), reference("Assumed"))]);
    assert!(result.checked_environment().is_none());
    assert!(result.report().rows[0].failures.contains(&ReplayFailure::UnauthorizedAxiom));
    assert!(
        result.report().rows[1]
            .failures
            .contains(&ReplayFailure::FailedDependency(Name::from_string("Assumed")))
    );
}

#[test]
fn unsafe_partial_unknown_and_unsupported_inputs_stay_in_the_population() {
    let (ty, value) = identity();
    for safety in
        [DeclarationSafety::Unsafe, DeclarationSafety::Partial, DeclarationSafety::Unmeasured]
    {
        let mut input = named("One", ty.clone(), value.clone());
        if let ReplayInput::Ordinary { safety: field, .. } = &mut input {
            *field = safety;
        }
        let result = replay(&[input]);
        assert!(result.checked_environment().is_none());
        assert!(
            result.report().rows[0].failures.contains(&ReplayFailure::UnsafeOrUnmeasured(safety))
        );
    }
    let result = replay(&[ReplayInput::Unsupported {
        name: Name::from_string("Family"),
        kind: "inductive family".into(),
    }]);
    assert!(result.checked_environment().is_none());
    assert_eq!(result.report().rows.len(), 1);
    assert!(matches!(result.report().rows[0].failures[0], ReplayFailure::UnsupportedKind(_)));
}

#[test]
fn missing_dependency_and_type_only_dependency_are_both_observed() {
    let result = replay(&[named("User", false_type(), reference("Missing"))]);
    assert!(
        result.report().rows[0]
            .failures
            .contains(&ReplayFailure::MissingDependency(Name::from_string("Missing")))
    );
    let result = replay(&[named("User", reference("TypeMissing"), Expr::sort(Level::zero()))]);
    assert!(
        result.report().rows[0]
            .failures
            .contains(&ReplayFailure::MissingDependency(Name::from_string("TypeMissing")))
    );
    assert!(result.checked_environment().is_none());
}

#[test]
fn resource_exhaustion_is_explicit_and_never_an_empty_success() {
    let (ty, value) = identity();
    let inputs = [named("One", ty, value)];
    let names = [Name::from_string("One")];
    let result = replay_closed_declarations(
        &inputs,
        &names,
        ReplayLimits { expression_nodes: 0, ..ReplayLimits::default() },
    );
    assert!(result.report().rows[0].failures.contains(&ReplayFailure::ExpressionBudget));
    assert!(result.checked_environment().is_none());
    let result = replay_closed_declarations(
        &inputs,
        &names,
        ReplayLimits { declarations: 0, ..ReplayLimits::default() },
    );
    assert!(!result.report().inventory_errors.is_empty());
    assert!(result.checked_environment().is_none());
}

#[test]
fn definitions_and_opaque_values_also_reenter_through_the_checked_kernel() {
    let (type_, value) = identity();
    let inputs = [
        ReplayInput::Ordinary {
            declaration: Declaration::Definition {
                name: Name::from_string("Definition"),
                level_params: vec![],
                type_: type_.clone(),
                value: value.clone(),
                is_reducible: false,
            },
            safety: DeclarationSafety::Safe,
        },
        ReplayInput::Ordinary {
            declaration: Declaration::Opaque {
                name: Name::from_string("Opaque"),
                level_params: vec![],
                type_,
                value,
            },
            safety: DeclarationSafety::Safe,
        },
    ];
    assert!(replay(&inputs).checked_environment().is_some());
}

#[test]
fn zero_kernel_budget_cannot_disable_the_resource_limit() {
    let (ty, value) = identity();
    let result = replay_closed_declarations(
        &[named("One", ty, value)],
        &[Name::from_string("One")],
        ReplayLimits { kernel_heartbeats_per_declaration: 0, ..ReplayLimits::default() },
    );
    assert!(
        result.checked_environment().is_none(),
        "zero means unlimited in the underlying kernel"
    );
    assert!(!result.report().inventory_errors.is_empty());
}

#[test]
fn tiny_kernel_budget_is_applied_to_real_add_decl() {
    let (ty, value) = identity();
    let result = replay_closed_declarations(
        &[named("One", ty, value)],
        &[Name::from_string("One")],
        ReplayLimits { kernel_heartbeats_per_declaration: 1, ..ReplayLimits::default() },
    );
    assert!(result.checked_environment().is_none());
    assert!(result.report().rows[0].failures.iter().any(|failure|
        matches!(failure, ReplayFailure::KernelRejected(error) if error.contains("Heartbeat"))));
}

#[test]
fn projection_and_unused_let_type_dependencies_cannot_be_hidden() {
    let (ty, value) = identity();
    let projected = replay(&[named(
        "Projection",
        ty.clone(),
        Expr::proj(Name::from_string("MissingFamily"), 0, value.clone()),
    )]);
    assert!(
        projected.report().rows[0]
            .failures
            .contains(&ReplayFailure::MissingDependency(Name::from_string("MissingFamily")))
    );
    let let_bound =
        replay(&[named("Let", ty, Expr::let_(reference("MissingType"), value.clone(), value))]);
    assert!(
        let_bound.report().rows[0]
            .failures
            .contains(&ReplayFailure::MissingDependency(Name::from_string("MissingType")))
    );
    assert!(projected.checked_environment().is_none());
    assert!(let_bound.checked_environment().is_none());
}

#[test]
fn ambient_axiom_only_mode_cannot_supply_a_checked_environment() {
    use clean_kernel::env::{MmAxiomOnlyGuard, set_mm_axiom_only};
    let (ty, value) = identity();
    let guard = MmAxiomOnlyGuard::enter();
    set_mm_axiom_only(true);
    let result = replay(&[named("One", ty.clone(), value), named("User", ty, reference("One"))]);
    drop(guard);
    assert!(result.checked_environment().is_none());
    assert!(
        result.report().rows[0]
            .failures
            .contains(&ReplayFailure::KernelDidNotRetainCheckedDeclaration)
    );
    assert!(
        result.report().rows[1]
            .failures
            .contains(&ReplayFailure::FailedDependency(Name::from_string("One")))
    );
}

#[test]
fn literals_with_implicit_dependencies_are_explicitly_unsupported() {
    let (ty, value) = identity();
    for literal in [Expr::nat_lit(0), Expr::str_lit("retained")] {
        let result = replay(&[
            named("Nat", ty.clone(), value.clone()),
            named("String", ty.clone(), value.clone()),
            named("Literal", ty.clone(), literal),
        ]);
        assert!(result.checked_environment().is_none());
        assert_eq!(result.report().rows.len(), 3);
        assert!(result.report().rows[2].failures.contains(&ReplayFailure::UnsupportedExpression));
    }
}

#[test]
fn undeclared_universe_parameters_are_rejected_by_the_kernel() {
    let u = Level::param(Name::from_string("u"));
    let result = replay(&[ReplayInput::Ordinary {
        declaration: Declaration::Definition {
            name: Name::from_string("Universe"),
            level_params: vec![],
            type_: Expr::sort(Level::succ(u.clone())),
            value: Expr::sort(u),
            is_reducible: false,
        },
        safety: DeclarationSafety::Safe,
    }]);
    assert!(result.checked_environment().is_none());
    assert!(result.report().rows[0].failures.iter().any(|failure|
        matches!(failure, ReplayFailure::KernelRejected(error) if error.contains("UndefinedLevelParam"))));
}
