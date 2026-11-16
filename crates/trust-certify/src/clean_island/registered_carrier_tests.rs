// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual island admission and typed-goal consumption of checked Clean ADTs.
//! These fixtures do not claim a Rust representation or Rust-body refinement.

use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, TypeChecker};
use trust_spec_elab::{Admission, Carrier, Domain, FacetTable, RegisteredAdt};

use super::*;

const SOURCE: &str = r#"
inductive ContractChoice : Type where
  | later : Nat -> ContractChoice
  | earlier : Bool -> ContractChoice

structure ContractRecord : Type where
  count : Nat
  flag : Bool

inductive ContractPair (A : Type) (B : Type) : Type where
  | mk : A -> B -> ContractPair A B

def choice_id (x : ContractChoice) : ContractChoice := x
def record_id (x : ContractRecord) : ContractRecord := x
def pair_id (x : ContractPair Bool Nat) : ContractPair Bool Nat := x
def choice_constant (x : ContractChoice) : ContractChoice := ContractChoice.earlier Bool.false
def dependent_id (A : Type) (x : ContractPair A Nat) : ContractPair A Nat := x
"#;

fn checked_environment(source: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let outcome = check_clean_island_into(source, &mut env);
    assert!(!outcome.is_rejected(), "actual island registration: {:?}", outcome.errors);
    assert!(outcome.standin_imports.is_empty());
    env
}

fn registered(carrier: &Carrier) -> &RegisteredAdt {
    let Carrier::RegisteredAdt(adt) = carrier else {
        panic!("expected a checked registered carrier, got {carrier:?}");
    };
    adt
}

fn pair_type(first: Expr, second: Expr) -> Expr {
    Expr::apps(Expr::const_str("ContractPair"), [first, second])
}

#[test]
fn checked_island_admission_records_enum_record_and_applied_telescope() {
    let env = checked_environment(SOURCE);
    let mut facets = FacetTable::new();
    for name in ["choice_id", "record_id", "pair_id"] {
        let admission = admit_certified_island_definition(&env, name, &mut facets)
            .expect("the existing production admitter must audit the definition");
        assert!(admission.require_kernel_check().is_ok());
        assert_eq!(admission.arity, 1);
        let carriers = admission.carriers.as_ref().expect("full recorded telescope");
        assert_eq!(carriers.params.len(), 1);
        assert_eq!(carriers.params[0], carriers.ret);
        let adt = registered(&carriers.ret);
        adt.validate_in(&env).expect("readback remains valid in the admitting environment");
        let info = env.get_const(&Name::from_string(name)).expect("real definition");
        let ExprKind::Pi(_, domain, codomain) = info.type_.kind() else {
            panic!("identity must have one value binder");
        };
        assert_eq!(&adt.ty(), domain.as_ref());
        assert_eq!(&adt.ty(), codomain.as_ref());
        assert_eq!(admission.return_domain().cloned(), Some(Domain::RegisteredAdt(adt.clone())));
    }
    let enum_info = env.get_inductive(&Name::from_string("ContractChoice")).unwrap();
    assert_eq!(
        enum_info.constructor_names,
        vec![
            Name::from_string("ContractChoice.later"),
            Name::from_string("ContractChoice.earlier")
        ],
        "declaration order is intentionally not lexical order"
    );
    let pair = island_definition_carriers(&env, "pair_id").unwrap();
    let adt = registered(&pair.ret);
    assert_eq!(adt.name(), &Name::from_string("ContractPair"));
    assert_eq!(adt.arguments(), &[Expr::const_str("Bool"), Expr::const_str("Nat")]);
    assert_eq!(adt.ty(), pair_type(Expr::const_str("Bool"), Expr::const_str("Nat")));
}

#[test]
fn admitted_registered_identity_flows_through_the_typed_goal_and_kernel() {
    let env = checked_environment(SOURCE);
    let mut facets = FacetTable::new();
    let admission = admit_certified_island_definition(&env, "pair_id", &mut facets).unwrap();
    let adt = registered(&admission.carriers.as_ref().unwrap().ret).clone();
    let goal = trust_spec_elab::elaborate_goal_with_domains(
        &env,
        "pair_id(x) == x",
        &[("x", Domain::RegisteredAdt(adt.clone()))],
        &facets,
    )
    .expect("typed arguments must reach the actual admitted island call");
    let proof = Expr::lam(
        BinderInfo::Default,
        adt.ty(),
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [adt.ty(), Expr::bvar(0)],
        ),
    );
    TypeChecker::new(&env)
        .check_type(&proof, &goal)
        .expect("identity must reduce at the exact carrier");
    assert!(matches!(cert_meter::grade(&env, &goal, &proof), cert_meter::Grade::Certified));

    let swapped = registered_carrier_of_clean_type(
        &env,
        &pair_type(Expr::const_str("Nat"), Expr::const_str("Bool")),
    )
    .expect("the swapped application is itself a well-formed but different type");
    assert_ne!(adt, swapped);
    assert!(
        trust_spec_elab::elaborate_goal_with_domains(
            &env,
            "pair_id(x) == x",
            &[("x", Domain::RegisteredAdt(swapped))],
            &facets,
        )
        .is_err(),
        "same family name cannot erase the ordered type arguments"
    );
    assert!(
        trust_spec_elab::elaborate_goal_with_domains(
            &env,
            "x + x == x",
            &[("x", Domain::RegisteredAdt(adt))],
            &facets,
        )
        .is_err(),
        "registered carrier admission does not invent arithmetic"
    );

    let constant = admit_certified_island_definition(&env, "choice_constant", &mut facets).unwrap();
    let choice = registered(&constant.carriers.as_ref().unwrap().ret).clone();
    let false_goal = trust_spec_elab::elaborate_goal_with_domains(
        &env,
        "choice_constant(x) == x",
        &[("x", Domain::RegisteredAdt(choice.clone()))],
        &facets,
    )
    .expect("the false contract is well typed and must retain the actual call");
    let false_proof = Expr::lam(
        BinderInfo::Default,
        choice.ty(),
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [choice.ty(), Expr::bvar(0)],
        ),
    );
    assert!(TypeChecker::new(&env).infer_type(&false_proof).is_ok(), "the candidate body is valid");
    assert!(TypeChecker::new(&env).check_type(&false_proof, &false_goal).is_err());
    assert!(matches!(
        cert_meter::grade(&env, &false_goal, &false_proof),
        cert_meter::Grade::Rejected { .. }
    ));
}

#[test]
fn carrier_readback_preserves_constructor_order_and_field_types() {
    let original = checked_environment(SOURCE);
    let old_choice = island_definition_carriers(&original, "choice_id").unwrap();
    let old_record = island_definition_carriers(&original, "record_id").unwrap();
    let reordered_source = SOURCE.replace(
        "  | later : Nat -> ContractChoice\n  | earlier : Bool -> ContractChoice",
        "  | earlier : Bool -> ContractChoice\n  | later : Nat -> ContractChoice",
    );
    assert_ne!(reordered_source, SOURCE);
    let reordered = checked_environment(&reordered_source);
    let new_choice = island_definition_carriers(&reordered, "choice_id").unwrap();
    assert_ne!(old_choice, new_choice);
    assert!(registered(&old_choice.ret).validate_in(&reordered).is_err());

    let changed_source = SOURCE.replace("  count : Nat", "  count : Bool");
    assert_ne!(changed_source, SOURCE);
    let changed_field = checked_environment(&changed_source);
    let new_record = island_definition_carriers(&changed_field, "record_id").unwrap();
    assert_ne!(old_record, new_record);
    assert!(registered(&old_record.ret).validate_in(&changed_field).is_err());
}

#[test]
fn unsupported_carriers_and_reflected_admissions_do_not_gain_authority() {
    let env = checked_environment(SOURCE);
    for ty in [
        Expr::const_str("MissingCarrier"),
        Expr::app(Expr::const_str("ContractPair"), Expr::const_str("Bool")),
        pair_type(Expr::const_str("Bool"), Expr::bvar(0)),
        Expr::const_(Name::from_string("ContractChoice"), vec![Level::zero()]),
    ] {
        assert!(carrier_of_clean_type(&env, &ty).is_none(), "must refuse {ty:?}");
    }
    assert!(island_definition_carriers(&env, "dependent_id").is_none());

    let mut reflected = FacetTable::new();
    reflected.insert(
        "choice_id",
        trust_spec_elab::FnFacets::from_structural_certificates(
            true,
            true,
            true,
            true,
            "reflected fixture",
        ),
    );
    reflected.admit("choice_id", Admission::reflected("trust_import_choice_id", 1));
    let before = reflected.admitted("choice_id").unwrap().clone();
    assert!(admit_certified_island_definition(&env, "choice_id", &mut reflected).is_err());
    assert_eq!(reflected.admitted("choice_id"), Some(&before));
    assert!(before.require_kernel_check().is_err());
}
