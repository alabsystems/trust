// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use clean_kernel::{Constructor, InductiveDecl, InductiveType, TypeChecker};

use super::*;

fn fixture() -> (Environment, Domain) {
    let mut env = Environment::with_prelude();
    let name = Name::from_string("ClauseChoice");
    let ty = Expr::const_(name.clone(), vec![]);
    let constructors = vec![
        ConstructorSchema { name: name.clone().str("left"), type_: ty.clone() },
        ConstructorSchema { name: name.clone().str("right"), type_: ty },
    ];
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: constructors
                .iter()
                .map(|c| Constructor { name: c.name.clone(), type_: c.type_.clone() })
                .collect(),
        }],
    })
    .unwrap();
    let handle = RegisteredAdt::validate(
        &env,
        &AdtSchema { name, type_: Expr::type_(), num_params: 0, constructors },
        &[],
    )
    .unwrap();
    (env, Domain::RegisteredAdt(handle))
}

fn refl(domain: &Domain) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        domain.ty(),
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [domain.ty(), Expr::bvar(0)],
        ),
    )
}

#[test]
fn registered_clauses_keep_exact_bindings_and_refuse_unencoded_operations() {
    let (env, domain) = fixture();
    let facets = FacetTable::new();
    let bindings = [("x", domain.clone())];
    let goal = elaborate_goal_with_domains(&env, "x == x", &bindings, &facets).unwrap();
    TypeChecker::new(&env).check_type(&refl(&domain), &goal).unwrap();
    for clause in [
        "x < x",
        "x <= x",
        "x > x",
        "x >= x",
        "x == 0",
        "x == 42",
        "x + x == x",
        "x / 1 == x",
        "x & x == x",
        "x << 1 == x",
        "(x as nat) == 0",
        "x == true",
        "x",
    ] {
        assert!(elaborate_goal_with_domains(&env, clause, &bindings, &facets).is_err(), "{clause}");
    }
    assert!(domain.runtime_domain().is_err());
    assert!(elaborate_goal_in("x == x", &domain).is_err());
    assert!(elaborate_contract_in("x == x", "x == x", &domain).is_err());
    assert!(elaborate_goal_typed("x == x", &[("x", "ClauseChoice")]).is_err());
    assert!(elaborate_goal_with_domains(&env, "x == x", &[], &facets).is_err());
    assert!(
        elaborate_goal_with_domains(
            &env,
            "x == x",
            &[("x", domain.clone()), ("x", domain.clone())],
            &facets
        )
        .is_err()
    );
    assert!(
        elaborate_goal_with_domains(
            &env,
            "x == x",
            &[("x", domain.clone()), ("unused", domain.clone())],
            &facets
        )
        .is_err()
    );
    assert!(
        elaborate_goal_with_domains(&env, "x == n", &[("x", domain), ("n", Domain::Nat)], &facets)
            .is_err()
    );
}

#[test]
fn registered_ensures_uses_actual_self_call_and_retains_reflected_status() {
    let (mut env, domain) = fixture();
    let admission = admit_field_projection_function(
        &mut env,
        "import_choice_first",
        &[domain.clone(), domain.clone()],
        &["x".into(), "y".into()],
        0,
    )
    .unwrap();
    assert!(admission.require_kernel_check().is_err());
    let mut facets = FacetTable::new();
    facets
        .insert("first", FnFacets::from_structural_certificates(true, true, true, true, "fixture"));
    facets.admit("first", admission);
    let params = [("x", domain.clone()), ("y", domain.clone())];
    let goal =
        elaborate_ensures_with_domains(&env, "result == x", &params, "first", &facets).unwrap();
    let proof = Expr::lam(
        BinderInfo::Default,
        domain.ty(),
        Expr::lam(
            BinderInfo::Default,
            domain.ty(),
            Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
                [domain.ty(), Expr::bvar(1)],
            ),
        ),
    );
    TypeChecker::new(&env).check_type(&proof, &goal).unwrap();
    let false_goal =
        elaborate_ensures_with_domains(&env, "result == y", &params, "first", &facets).unwrap();
    assert!(TypeChecker::new(&env).check_type(&proof, &false_goal).is_err());
    let reordered = [("y", domain.clone()), ("x", domain.clone())];
    assert!(
        elaborate_ensures_with_domains(&env, "result == x", &reordered, "first", &facets).is_err()
    );
    assert!(
        elaborate_ensures_with_domains(&env, "result == x", &params, "missing", &facets).is_err()
    );
    assert!(facets.admitted("first").unwrap().require_kernel_check().is_err());
}

#[test]
fn registered_call_result_is_not_retyped_from_its_arguments() {
    let (mut env, domain) = fixture();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("import_choice_from_nat"),
        level_params: vec![],
        type_: Expr::arrow(nat(), domain.ty()),
        value: Expr::lam(BinderInfo::Default, nat(), Expr::const_str("ClauseChoice.left")),
        is_reducible: true,
    })
    .unwrap();
    let admission = Admission::reflected("import_choice_from_nat", 1).with_declared_signature(
        Some(domain.clone()),
        Some(DeclaredCarriers::of_domains(&[Domain::Nat], &domain)),
    );
    let mut facets = FacetTable::new();
    facets.insert(
        "choose",
        FnFacets::from_structural_certificates(true, true, true, true, "fixture"),
    );
    facets.admit("choose", admission);
    for (clause, bindings) in [
        ("choose(n) == choose(n)", vec![("n", Domain::Nat)]),
        ("choose(0) == choose(1)", vec![]),
        ("choose(n) == x", vec![("n", Domain::Nat), ("x", domain.clone())]),
    ] {
        let _ = elaborate_goal_with_domains(&env, clause, &bindings, &facets).expect(clause);
    }
    assert!(
        elaborate_goal_with_domains(&env, "choose(n) == n", &[("n", Domain::Nat)], &facets)
            .is_err()
    );
    assert!(elaborate_goal_with_domains(&env, "choose(0u8) == choose(0)", &[], &facets).is_err());
    // No bindings carry the stale handle here: it occurs only in the callee.
    assert!(
        elaborate_goal_with_domains(
            &Environment::with_prelude(),
            "choose(0) == choose(0)",
            &[],
            &facets
        )
        .is_err()
    );
}

#[test]
fn registered_arguments_do_not_erase_ambient_literal_suffixes() {
    let (mut env, domain) = fixture();
    let machine = Domain::Machine(MachineUIntWidth::U64);
    let mut facets = FacetTable::new();
    for (function, params) in [("a64", vec![]), ("from_choice", vec![domain.clone()])] {
        env.add_decl(Declaration::Definition {
            name: Name::from_string(function),
            level_params: vec![],
            type_: params.iter().rev().fold(machine.ty(), |tail, d| Expr::arrow(d.ty(), tail)),
            value: params.iter().rev().fold(machine.numeral(42).unwrap(), |tail, d| {
                Expr::lam(BinderInfo::Default, d.ty(), tail)
            }),
            is_reducible: true,
        })
        .unwrap();
        facets.insert(
            function,
            FnFacets::from_structural_certificates(true, true, true, true, "fixture"),
        );
        facets.admit(
            function,
            Admission::reflected(function, params.len()).with_declared_signature(
                Some(machine.clone()),
                Some(DeclaredCarriers::of_domains(&params, &machine)),
            ),
        );
    }
    let bindings = [("x", domain)];
    for source in ["x == x && a64() == 42u32", "from_choice(x) == 42u32"] {
        assert!(elaborate_goal_with_domains(&env, source, &bindings, &facets).is_err(), "{source}");
    }
    for source in ["x == x && a64() == 42u64", "from_choice(x) == 42u64"] {
        let _ = elaborate_goal_with_domains(&env, source, &bindings, &facets).expect(source);
    }
}

#[test]
fn registered_result_does_not_erase_negative_argument_suffixes() {
    let (mut env, domain) = fixture();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("choice_from_int"),
        level_params: vec![],
        type_: Expr::arrow(Domain::Int.ty(), domain.ty()),
        value: Expr::lam(
            BinderInfo::Default,
            Domain::Int.ty(),
            Expr::const_str("ClauseChoice.left"),
        ),
        is_reducible: true,
    })
    .unwrap();
    let mut facets = FacetTable::new();
    facets.insert(
        "choose",
        FnFacets::from_structural_certificates(true, true, true, true, "fixture"),
    );
    facets.admit(
        "choose",
        Admission::reflected("choice_from_int", 1).with_declared_signature(
            Some(domain.clone()),
            Some(DeclaredCarriers::of_domains(&[Domain::Int], &domain)),
        ),
    );
    let _ = elaborate_goal_with_domains(&env, "choose(-1) == choose(0)", &[], &facets).unwrap();
    for source in
        ["choose(-1i64) == choose(0)", "choose(-(1i64)) == choose(0)", "choose(1i64) == choose(0)"]
    {
        assert!(elaborate_goal_with_domains(&env, source, &[], &facets).is_err(), "{source}");
    }
}

#[test]
fn registered_bindings_work_under_quantifiers_without_changing_scalar_goals() {
    let (env, domain) = fixture();
    let facets = FacetTable::new();
    let _ = elaborate_goal_with_domains(&env, "forall n: nat, x == x", &[("x", domain)], &facets)
        .unwrap();
    for source in ["n == n", "forall k: nat, n == n", "n == n ==> n == n"] {
        let old = elaborate_goal_typed(source, &[("n", "nat")]).unwrap();
        let typed =
            elaborate_goal_with_domains(&env, source, &[("n", Domain::Nat)], &facets).unwrap();
        assert_eq!(old, typed, "scalar compatibility: {source}");
    }
}
