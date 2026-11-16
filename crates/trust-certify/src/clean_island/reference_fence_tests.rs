// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual island-policy wiring controls. No process-global native-fold bypass:
//! an unrelated structurally registered record makes the reference base
//! ineligible while leaving the ordinary proof's own strict audit green.
use clean_kernel::{Declaration, Expr, Level, Name};

use super::*;

fn proof() -> (Expr, Expr) {
    let bool_ = Expr::const_str("Bool");
    let true_ = Expr::const_str("Bool.true");
    let one = vec![Level::succ(Level::zero())];
    let ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), one.clone()),
        [bool_.clone(), true_.clone(), true_.clone()],
    );
    let value = Expr::apps(Expr::const_(Name::from_string("Eq.refl"), one), [bool_, true_]);
    (ty, value)
}

fn add_structural_record(env: &mut Environment) {
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("tg8_unchecked_unrelated"),
        level_params: vec![],
        type_: Expr::const_str("Nat"),
        value: Expr::nat_lit(0),
        is_reducible: false,
    })
    .expect("test-only structurally valid record, without a kernel-check stamp");
}

#[test]
fn reference_fence_reaches_both_named_policies_and_definition_proofs() {
    let (ty, value) = proof();
    for definition in [false, true] {
        let mut env = Environment::with_prelude();
        let name = Name::from_string("tg8_wiring_proof");
        let (decl, leaf) = if definition {
            (
                Declaration::Definition {
                    name: name.clone(),
                    level_params: vec![],
                    type_: ty.clone(),
                    value: value.clone(),
                    is_reducible: false,
                },
                ElabResult::Definition {
                    name: name.clone(),
                    universe_params: vec![],
                    ty: ty.clone(),
                    val: value.clone(),
                    modifiers: Default::default(),
                },
            )
        } else {
            (
                Declaration::Theorem {
                    name: name.clone(),
                    level_params: vec![],
                    type_: ty.clone(),
                    value: value.clone(),
                },
                ElabResult::Theorem {
                    name: name.clone(),
                    universe_params: vec![],
                    ty: ty.clone(),
                    proof: value.clone(),
                    modifiers: Default::default(),
                },
            )
        };
        env.add_decl(decl).expect("ordinary checked proof");
        assert!(strict_leaf_policy_error(&env, &leaf).is_none());
        assert!(strict_registered_policy_error(&env, &name).is_none());
        add_structural_record(&mut env);
        assert!(
            matches!(cert_meter::grade(&env, &ty, &value), cert_meter::Grade::Certified),
            "control: the original audit accepts this proof's own closure"
        );
        let leaf_error = strict_leaf_policy_error(&env, &leaf)
            .expect("the sequential declaration fence must screen its reference base");
        assert!(leaf_error.contains("reference"), "{leaf_error}");
        let named_error = strict_registered_policy_error(&env, &name)
            .expect("the batch declaration fence must screen its reference base");
        assert!(named_error.contains("reference"), "{named_error}");
    }
}

#[test]
fn reference_fence_reaches_anonymous_leaf_judgments() {
    let (ty, value) = proof();
    let mut env = Environment::with_prelude();
    let leaf = ElabResult::Example { ty, val: value };
    assert!(strict_leaf_policy_error(&env, &leaf).is_none());
    add_structural_record(&mut env);
    let error = strict_leaf_policy_error(&env, &leaf)
        .expect("an anonymous proof must not bypass the reference base screen");
    assert!(error.contains("reference"), "{error}");
}

#[test]
fn actual_sequential_and_batch_acceptance_refuse_ineligible_bases() {
    for source in [
        "theorem tg8_actual : (1 : Nat) = 1 := rfl\n",
        "def tg8_actual : (1 : Nat) = 1 := rfl\n",
        "example : (1 : Nat) = 1 := rfl\n",
        "#guard (1 : Nat) = 1\n",
    ] {
        for batch in [false, true] {
            let mut env = Environment::with_prelude();
            let good = if batch {
                let mut ctx = FileContext::new();
                crate::clean_island_batch::check_islands_batched(&mut env, &mut ctx, &[source])
                    .outcomes
                    .remove(0)
            } else {
                check_clean_island_into(source, &mut env)
            };
            assert!(!good.is_rejected(), "positive batch={batch} {source}: {good:?}");
            assert_eq!(
                good.anonymous_judgments,
                usize::from(source.starts_with("example") || source.starts_with("#guard"))
            );
            let mut env = Environment::with_prelude();
            add_structural_record(&mut env);
            let bad = if batch {
                let mut ctx = FileContext::new();
                crate::clean_island_batch::check_islands_batched(&mut env, &mut ctx, &[source])
                    .outcomes
                    .remove(0)
            } else {
                check_clean_island_into(source, &mut env)
            };
            assert!(bad.is_rejected(), "negative batch={batch} {source}: {bad:?}");
            assert!(bad.errors.iter().any(|error| error.message.contains("reference")), "{bad:?}");
        }
    }
}

#[test]
fn a_registered_name_without_a_constant_is_refused() {
    let env = Environment::with_prelude();
    let error = strict_registered_policy_error(&env, &Name::from_string("tg8_missing"))
        .expect("absence cannot exempt a registered name from reference checking");
    assert!(error.contains("reference"), "{error}");
}

#[test]
fn a_structural_mathlib_standin_is_refused_while_a_lean_standin_is_disclosed() {
    let mut good = CleanIslandSession::new();
    let outcome = good.check("import Lean\ndef tg8_standin : Nat := 0\n");
    assert!(!outcome.is_rejected(), "{outcome:?}");
    assert_eq!(outcome.standin_imports[0].module, "Lean");
    let mut bad = CleanIslandSession::new();
    let outcome = bad.check("import Mathlib\ndef tg8_standin : Nat := 0\n");
    assert!(outcome.is_rejected(), "a stand-in's structural records are not a reference base");
    assert!(
        outcome.errors.iter().any(|e| e.message.contains("StructuralProvenance")),
        "{outcome:?}"
    );
    assert!(outcome.standin_imports.is_empty(), "no accepted substitution is reported");
}

#[test]
fn transactional_recovery_must_reference_check_its_final_survivors() {
    for structural in [false, true] {
        let mut session = CleanIslandSession::new();
        if structural {
            session.keyed.admit(add_structural_record);
        }
        let before = crate::reference_mint::island_entries();
        let batch = session.check_import_islands(&[
            "theorem tg8_survivor : (1 : Nat) = 1 := rfl",
            "theorem tg8_failure : (0 : Nat) = 1 := rfl",
        ]);
        assert!(batch.is_rejected());
        assert!(
            crate::reference_mint::island_entries() > before,
            "the restored survivor batch must reach the mandatory reference gate"
        );
        let survivor = session.env().get_const(&Name::from_string("tg8_survivor"));
        if structural {
            assert!(batch.refused_islands.contains(&1));
            assert!(session.is_tainted(), "a whole-base refusal must prohibit partial recovery");
            assert!(
                matches!(
                    session.check_citation("tg8_survivor", "1 == 1"),
                    CitationVerdict::SessionTainted
                ),
                "diagnostic declarations must confer no positive citation evidence"
            );
            assert!(
                batch.outcomes[0].errors.iter().any(|e| e.message.contains("reference")),
                "{batch:?}"
            );
        } else {
            assert_eq!(batch.refused_islands, [1]);
            assert!(survivor.is_some(), "independent checked proofs survive source failure");
        }
    }
}

#[test]
fn an_import_only_island_cannot_accept_an_ineligible_reference_base() {
    for batch in [false, true] {
        let mut session = CleanIslandSession::new();
        let outcome = if batch {
            session.check_all(&["import Mathlib"]).outcomes.remove(0)
        } else {
            session.check("import Mathlib")
        };
        assert!(outcome.is_rejected(), "batch={batch}: {outcome:?}");
        assert!(outcome.errors.iter().any(|e| e.message.contains("reference base")), "{outcome:?}");
        assert!(outcome.standin_imports.is_empty());
    }
}
