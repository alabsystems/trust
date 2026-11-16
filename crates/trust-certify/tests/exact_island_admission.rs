// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact declaration binding and re-admission cache controls. Ordinary fixtures
//! use full kernel admission; the structural-only negative is labeled as such.

use clean_kernel::{Declaration, Environment, Expr, Name};
use trust_certify::clean_island::{
    admit_certified_island_definition, admit_certified_island_definition_for_name,
    island_source_name,
};
use trust_spec_elab::FacetTable;
use trust_symbols::TermDigest;

fn definition(env: &mut Environment, name: Name, value: Expr, structural: bool) {
    let declaration = Declaration::Definition {
        name,
        level_params: vec![],
        type_: Expr::const_str("Bool"),
        value,
        is_reducible: true,
    };
    if structural {
        env.add_decl_structural(declaration).unwrap();
    } else {
        env.add_decl(declaration).expect("full kernel admission");
    }
}

fn environment(value: bool, structural: bool) -> Environment {
    let mut env = Environment::with_prelude();
    definition(
        &mut env,
        Name::from_string("subject"),
        Expr::const_str(if value { "Bool.true" } else { "Bool.false" }),
        structural,
    );
    env
}

fn admit(env: &Environment, facets: &mut FacetTable) -> TermDigest {
    admit_certified_island_definition(env, "subject", facets)
        .expect("fresh fully checked definition must admit")
        .require_kernel_check()
        .unwrap()
        .digest()
        .clone()
}

#[test]
fn repeated_identical_checked_admission_remains_idempotent() {
    let env = environment(true, false);
    let mut facets = FacetTable::new();
    let first = admit(&env, &mut facets);
    assert_eq!(first, admit(&env, &mut facets));
}

#[test]
fn cached_admission_cannot_hide_missing_current_declaration() {
    let mut facets = FacetTable::new();
    admit(&environment(true, false), &mut facets);
    let before = facets.admitted("subject").unwrap().clone();
    assert!(
        admit_certified_island_definition(&Environment::with_prelude(), "subject", &mut facets)
            .is_err()
    );
    assert_eq!(facets.admitted("subject").unwrap(), &before);
}

#[test]
fn cached_admission_cannot_upgrade_structural_only_context() {
    let mut facets = FacetTable::new();
    admit(&environment(true, false), &mut facets);
    let current = environment(true, true);
    assert!(
        admit_certified_island_definition(&current, "subject", &mut FacetTable::new()).is_err()
    );
    let before = facets.admitted("subject").unwrap().clone();
    assert!(admit_certified_island_definition(&current, "subject", &mut facets).is_err());
    assert_eq!(facets.admitted("subject").unwrap(), &before);
}

#[test]
fn cached_admission_cannot_rebind_changed_definition() {
    let mut facets = FacetTable::new();
    let first = admit(&environment(true, false), &mut facets);
    let current = environment(false, false);
    assert_ne!(first, admit(&current, &mut FacetTable::new()));
    let before = facets.admitted("subject").unwrap().clone();
    assert!(admit_certified_island_definition(&current, "subject", &mut facets).is_err());
    assert_eq!(facets.admitted("subject").unwrap(), &before);
}

#[test]
fn cached_admission_cannot_hide_new_transitive_axiom_debt() {
    let make = |axiomatic| {
        let mut env = Environment::with_prelude();
        if axiomatic {
            env.add_decl(Declaration::Axiom {
                name: Name::from_string("dependency"),
                level_params: vec![],
                type_: Expr::const_str("Bool"),
            })
            .unwrap();
        } else {
            definition(
                &mut env,
                Name::from_string("dependency"),
                Expr::const_str("Bool.true"),
                false,
            );
        }
        definition(&mut env, Name::from_string("subject"), Expr::const_str("dependency"), false);
        env
    };
    let original = make(false);
    let current = make(true);
    assert_eq!(
        original.get_const(&Name::from_string("subject")).unwrap().value,
        current.get_const(&Name::from_string("subject")).unwrap().value,
    );
    assert!(
        admit_certified_island_definition(&current, "subject", &mut FacetTable::new()).is_err()
    );
    let mut facets = FacetTable::new();
    admit(&original, &mut facets);
    let before = facets.admitted("subject").unwrap().clone();
    assert!(admit_certified_island_definition(&current, "subject", &mut facets).is_err());
    assert_eq!(facets.admitted("subject").unwrap(), &before);
}

fn twin_environment(numeric: bool, selected: usize) -> Environment {
    let names = if numeric {
        [Name::anon().str("Twin").num(7), Name::anon().str("Twin").str("7")]
    } else {
        [Name::from_string("Twin.leaf"), Name::anon().str("Twin.leaf")]
    };
    assert_ne!(names[0], names[1]);
    assert_eq!(names[0].to_string(), names[1].to_string());
    let mut env = Environment::with_prelude();
    for (i, name) in names.iter().enumerate() {
        definition(
            &mut env,
            name.clone(),
            Expr::const_str(if i == 0 { "Bool.true" } else { "Bool.false" }),
            false,
        );
    }
    definition(
        &mut env,
        Name::from_string("subject"),
        Expr::const_(names[selected].clone(), vec![]),
        false,
    );
    env
}

#[test]
fn quoted_reference_terms_have_distinct_admission_digests() {
    assert_ne!(
        admit(&twin_environment(false, 0), &mut FacetTable::new()),
        admit(&twin_environment(false, 1), &mut FacetTable::new()),
    );
}

#[test]
fn numeric_reference_terms_have_distinct_admission_digests() {
    assert_ne!(
        admit(&twin_environment(true, 0), &mut FacetTable::new()),
        admit(&twin_environment(true, 1), &mut FacetTable::new()),
    );
}

#[test]
fn metadata_erased_by_display_still_binds_exact_checked_term() {
    let make = |flag| {
        let mut env = Environment::with_prelude();
        definition(
            &mut env,
            Name::from_string("subject"),
            Expr::mdata(
                vec![(Name::from_string("annotation"), clean_kernel::MDataValue::Bool(flag))],
                Expr::const_str("Bool.true"),
            ),
            false,
        );
        env
    };
    assert_ne!(
        admit(&make(false), &mut FacetTable::new()),
        admit(&make(true), &mut FacetTable::new())
    );
}
#[test]
fn unrelated_checked_definition_does_not_invalidate_identical_admission() {
    let mut env = environment(true, false);
    let mut facets = FacetTable::new();
    let first = admit(&env, &mut facets);
    definition(&mut env, Name::from_string("unrelated"), Expr::const_str("Bool.false"), false);
    assert_eq!(first, admit(&env, &mut facets));
}

#[test]
fn allocation_sharing_does_not_change_checked_declaration_digest() {
    use clean_kernel::{BinderInfo, Level};
    let make = |shared| {
        let mut env = Environment::with_prelude();
        let leaf = Expr::const_str("Bool.true");
        let other = if shared { leaf.clone() } else { Expr::const_str("Bool.true") };
        let body = Expr::apps(
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]),
            [
                Expr::lam(BinderInfo::Default, Expr::const_str("Bool"), Expr::const_str("Bool")),
                leaf,
                other,
                Expr::const_str("Bool.true"),
            ],
        );
        definition(&mut env, Name::from_string("subject"), body, false);
        env
    };
    assert_eq!(
        admit(&make(false), &mut FacetTable::new()),
        admit(&make(true), &mut FacetTable::new())
    );
}

#[test]
fn encoding_limit_leaves_no_positive_facets_or_admission() {
    use std::sync::Arc;
    let mut env = Environment::with_prelude();
    definition(
        &mut env,
        Name::from_string("subject"),
        Expr::mdata(
            vec![(
                Name::from_string("large"),
                clean_kernel::MDataValue::String(Arc::from("x".repeat(16 * 1024 * 1024))),
            )],
            Expr::const_str("Bool.true"),
        ),
        false,
    );
    let mut facets = FacetTable::new();
    let error = admit_certified_island_definition(&env, "subject", &mut facets)
        .expect_err("incomplete binding must not mint or mutate admission");
    assert!(error.contains("16 MiB"), "{error}");
    assert!(facets.get("subject").is_none());
    assert!(facets.admitted("subject").is_none());
    admit(&environment(true, false), &mut facets);
}

#[test]
fn matching_term_digest_does_not_authorize_mutated_cached_arity() {
    let env = environment(true, false);
    let mut facets = FacetTable::new();
    admit(&env, &mut facets);
    let mut changed = facets.admitted("subject").unwrap().clone();
    changed.arity += 1;
    facets.admit("subject", changed.clone());
    assert!(admit_certified_island_definition(&env, "subject", &mut facets).is_err());
    assert_eq!(facets.admitted("subject").unwrap(), &changed);
}

#[test]
fn native_source_name_reader_preserves_components_and_rejects_expressions() {
    assert_eq!(island_source_name("A.b").unwrap(), Name::anon().str("A").str("b"));
    assert_eq!(island_source_name("«A.b»").unwrap(), Name::anon().str("A.b"));
    assert_eq!(island_source_name("A.«7»").unwrap(), Name::anon().str("A").str("7"));
    assert_ne!(island_source_name("A.«7»").unwrap(), Name::anon().str("A").num(7));
    assert_eq!(island_source_name("«plain»").unwrap(), island_source_name("plain").unwrap());
    for invalid in ["", "A.b + 1", "A.b := 0", "«unclosed"] {
        assert!(island_source_name(invalid).is_err(), "{invalid}");
    }
}

#[test]
fn typed_admissions_do_not_share_display_alias_facets_or_digests() {
    let mut env = Environment::with_prelude();
    let qualified = Name::anon().str("A").str("b");
    let quoted = Name::anon().str("A.b");
    // Identical types and values leave declaration identity as the distinguishing input.
    for name in [&qualified, &quoted] {
        definition(&mut env, name.clone(), Expr::const_str("Bool.true"), false);
    }
    let mut facets = FacetTable::new();
    let a = admit_certified_island_definition_for_name(&env, &qualified, &mut facets).unwrap();
    let b = admit_certified_island_definition_for_name(&env, &quoted, &mut facets).unwrap();
    assert_ne!(
        a.require_kernel_check().unwrap().digest(),
        b.require_kernel_check().unwrap().digest()
    );
    assert_eq!(facets.admitted("A.b"), Some(&a));
    assert_eq!(facets.admitted("«A.b»"), Some(&b));
    assert_eq!(admit_certified_island_definition_for_name(&env, &quoted, &mut facets).unwrap(), b);
}

#[test]
fn typed_admission_cannot_borrow_a_missing_or_unchecked_display_alias() {
    let qualified = Name::anon().str("A").str("b");
    let quoted = Name::anon().str("A.b");
    let mut env = Environment::with_prelude();
    definition(&mut env, qualified, Expr::const_str("Bool.true"), false);
    let mut facets = FacetTable::new();
    assert!(admit_certified_island_definition_for_name(&env, &quoted, &mut facets).is_err());
    definition(&mut env, quoted.clone(), Expr::const_str("Bool.true"), true);
    assert!(admit_certified_island_definition_for_name(&env, &quoted, &mut facets).is_err());
    assert!(facets.admitted("«A.b»").is_none());
}

#[test]
fn typed_admission_rechecks_changed_quoted_declaration_without_overwriting_cache() {
    let name = Name::anon().str("A.b");
    let make = |value| {
        let mut env = Environment::with_prelude();
        definition(&mut env, name.clone(), Expr::const_str(value), false);
        env
    };
    let mut facets = FacetTable::new();
    let first =
        admit_certified_island_definition_for_name(&make("Bool.true"), &name, &mut facets).unwrap();
    assert!(
        admit_certified_island_definition_for_name(&make("Bool.false"), &name, &mut facets,)
            .is_err()
    );
    assert_eq!(facets.admitted("«A.b»"), Some(&first));
}

#[test]
fn quoted_spelling_cannot_escape_the_reflected_namespace_backstop() {
    let name = island_source_name("«trust_import_spoof.part»").unwrap();
    let mut env = Environment::with_prelude();
    definition(&mut env, name.clone(), Expr::const_str("Bool.true"), false);
    let mut facets = FacetTable::new();
    let error = admit_certified_island_definition_for_name(&env, &name, &mut facets).unwrap_err();
    assert!(error.contains("Reflected") || error.contains("reflected"), "{error}");
    assert!(facets.admitted("«trust_import_spoof.part»").is_none());
}

#[test]
fn generated_numeric_identity_cannot_enter_the_source_facet_transport() {
    let numeric = Name::anon().str("N").num(7);
    let string = Name::anon().str("N").str("7");
    let mut env = Environment::with_prelude();
    for name in [&numeric, &string] {
        definition(&mut env, name.clone(), Expr::const_str("Bool.true"), false);
    }
    let mut facets = FacetTable::new();
    let error =
        admit_certified_island_definition_for_name(&env, &numeric, &mut facets).unwrap_err();
    assert!(error.contains("cannot encode"), "{error}");
    assert!(facets.admitted("N.7").is_none());
    assert!(facets.admitted("N.«7»").is_none());
    assert!(admit_certified_island_definition_for_name(&env, &string, &mut facets).is_ok());
}
