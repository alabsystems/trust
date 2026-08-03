//! `parsed_clause_matches_typed`: matching a re-parsed spec clause against the
//! compiler's own TYPED lowering of the same clause.
//!
//! THE DEFECT. `trust_types::parse_spec_expr` takes a bare `&str`, so it has no
//! type environment and stamps every unbound leaf with the default `Sort::Int`
//! (`trust-types/src/spec_parse.rs:793-802`). The compiler's contract lowering
//! knows the real type. `Formula` derives structural `PartialEq` and `Var`
//! compares its `Sort`, so a `bool` clause could never equal the re-parse of its
//! own source text — while an integer clause matched by coincidence. That split
//! the `bool` lane two ways: a duplicate ill-sorted postcondition VC (no
//! `trust.vc.formula.payload`, so a fail-closed Unknown) and a missing
//! `source_contract_index` (so the source-clause marker never discharged).
//!
//! These tests pin BOTH halves of the contract: the sentinel is forgiven, and
//! nothing else is.

use trust_types::{Formula, Sort};

use super::parsed_clause_matches_typed;

fn v(name: &str, sort: Sort) -> Formula {
    Formula::Var(name.into(), sort)
}
fn not(f: Formula) -> Formula {
    Formula::Not(Box::new(f))
}
fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}

// ─────────────────────────── the bug, end to end ───────────────────────────

/// THE REGRESSION TEST. The exact text the compiler lowers a nested `bool`
/// field clause to, re-parsed, must match the typed formula it came from.
/// This is `ensures !self.storage.f` — aterm's blocker.
#[test]
fn reparsed_nested_bool_clause_matches_its_typed_lowering() {
    let parsed = trust_types::parse_spec_expr("!((*self).0.0)")
        .expect("the compiler's own lowered contract text must parse");
    // What the parser can produce with no types: the Int sentinel.
    assert_eq!(parsed, not(v("self*.0.0", Sort::Int)), "parser sentinel changed");
    // What the compiler's typed lowering carries.
    let typed = not(v("self*.0.0", Sort::Bool));
    assert_ne!(parsed, typed, "if these are equal the sort bug is gone and this test is stale");
    assert!(parsed_clause_matches_typed(&parsed, &typed));
}

/// Depth 1 is the same defect: the axis is the SORT, not the nesting depth.
#[test]
fn reparsed_depth_one_bool_clause_matches_its_typed_lowering() {
    let parsed = trust_types::parse_spec_expr("!((*self).0)").expect("must parse");
    assert!(parsed_clause_matches_typed(&parsed, &not(v("self*.0", Sort::Bool))));
}

/// The integer lane matched by coincidence before the fix and must keep working.
#[test]
fn reparsed_integer_clause_still_matches() {
    let parsed = trust_types::parse_spec_expr("((*self).0.0) == (0)").expect("must parse");
    let typed = eq(v("self*.0.0", Sort::Int), Formula::Int(0));
    assert_eq!(parsed, typed, "the integer lane matched exactly before the fix");
    assert!(parsed_clause_matches_typed(&parsed, &typed));
}

/// A clause mixing an integer and a bool leaf: one `Bool` leaf used to poison
/// the whole clause.
#[test]
fn mixed_int_and_bool_clause_matches() {
    let parsed = trust_types::parse_spec_expr("((*self).0) == (0) && !((*self).1)")
        .expect("must parse");
    let typed = Formula::And(vec![
        eq(v("self*.0", Sort::Int), Formula::Int(0)),
        not(v("self*.1", Sort::Bool)),
    ]);
    assert!(parsed_clause_matches_typed(&parsed, &typed));
}

// ──────────────── everything the relaxation must still refuse ───────────────

/// A DIFFERENT PLACE spells a different name. This is the property that keeps
/// the relaxation from ever binding a clause to somebody else's field.
#[test]
fn different_place_name_is_refused() {
    let parsed = not(v("self*.0.0", Sort::Int));
    assert!(!parsed_clause_matches_typed(&parsed, &not(v("self*.0.1", Sort::Bool))));
    assert!(!parsed_clause_matches_typed(&parsed, &not(v("self*.1.0", Sort::Bool))));
    assert!(!parsed_clause_matches_typed(&parsed, &not(v("other*.0.0", Sort::Bool))));
}

/// The forgiveness is ONE-DIRECTIONAL: only the PARSED side's `Int` sentinel is
/// forgiven. A parsed non-`Int` sort must still match exactly, so a genuine
/// sort disagreement cannot be laundered by argument order.
#[test]
fn forgiveness_is_only_for_the_parsed_int_sentinel() {
    // parsed Bool vs typed Int -> refused (nothing to forgive on the parsed side)
    assert!(!parsed_clause_matches_typed(
        &not(v("self*.0", Sort::Bool)),
        &not(v("self*.0", Sort::Int)),
    ));
    // parsed Float vs typed Bool -> refused
    let f64s = Sort::Float { eb: 11, sb: 53 };
    assert!(!parsed_clause_matches_typed(
        &not(v("self*.0", f64s)),
        &not(v("self*.0", Sort::Bool)),
    ));
}

/// Constants are compared exactly: a true clause must never match a false one.
#[test]
fn differing_constants_are_refused() {
    let parsed = eq(v("self*.0", Sort::Int), Formula::Int(0));
    assert!(!parsed_clause_matches_typed(&parsed, &eq(v("self*.0", Sort::Int), Formula::Int(1))));
}

/// Different operators of the same arity must not be confused.
#[test]
fn differing_operators_are_refused() {
    let a = v("x", Sort::Int);
    let b = Formula::Int(3);
    let parsed = Formula::Lt(Box::new(a.clone()), Box::new(b.clone()));
    assert!(!parsed_clause_matches_typed(&parsed, &Formula::Le(Box::new(a), Box::new(b))));
}

/// Arity is part of the shape.
#[test]
fn differing_arity_is_refused() {
    let x = v("x", Sort::Int);
    let y = v("y", Sort::Int);
    let parsed = Formula::And(vec![x.clone(), y.clone()]);
    assert!(!parsed_clause_matches_typed(&parsed, &Formula::And(vec![x.clone(), y, x])));
}

/// A variable must not match a non-variable of any kind.
#[test]
fn variable_does_not_match_non_variable() {
    let parsed = v("x", Sort::Int);
    assert!(!parsed_clause_matches_typed(&parsed, &Formula::Bool(true)));
    assert!(!parsed_clause_matches_typed(&parsed, &Formula::Int(0)));
    assert!(!parsed_clause_matches_typed(&parsed, &not(v("x", Sort::Bool))));
}

/// Non-formula payload carried beside the children (here a bitvector width) is
/// compared exactly — the sentinel relaxation must not leak into it.
#[test]
fn differing_bitvector_width_is_refused() {
    let x = v("x", Sort::Int);
    let y = v("y", Sort::Int);
    let parsed = Formula::BvAdd(Box::new(x.clone()), Box::new(y.clone()), 32);
    assert!(!parsed_clause_matches_typed(
        &parsed,
        &Formula::BvAdd(Box::new(x), Box::new(y), 64),
    ));
}

/// Quantifier binder lists are non-child payload and are compared exactly, so a
/// bound leaf can never be mis-forgiven through a differing binder sort.
#[test]
fn differing_quantifier_binders_are_refused() {
    let body = Formula::Le(Box::new(v("i", Sort::Int)), Box::new(Formula::Int(1)));
    let parsed =
        Formula::Forall(vec![(trust_types::Symbol::intern("i"), Sort::Int)], Box::new(body.clone()));
    let other =
        Formula::Forall(vec![(trust_types::Symbol::intern("i"), Sort::Bool)], Box::new(body.clone()));
    assert!(!parsed_clause_matches_typed(&parsed, &other));
    // Same binders, same body: matches.
    assert!(parsed_clause_matches_typed(&parsed, &parsed.clone()));
    // A quantifier must not match its own body.
    assert!(!parsed_clause_matches_typed(&parsed, &body));
}

/// `Forall` and `Exists` share a shape but must never be interchanged.
#[test]
fn forall_does_not_match_exists() {
    let binder = vec![(trust_types::Symbol::intern("i"), Sort::Int)];
    let body = Formula::Le(Box::new(v("i", Sort::Int)), Box::new(Formula::Int(1)));
    let all = Formula::Forall(binder.clone(), Box::new(body.clone()));
    let ex = Formula::Exists(binder, Box::new(body));
    assert!(!parsed_clause_matches_typed(&all, &ex));
}

/// The sentinel relaxation reaches leaves nested arbitrarily deep, but only
/// when every enclosing node matches exactly.
#[test]
fn relaxation_reaches_deeply_nested_leaves() {
    let parsed = Formula::Implies(
        Box::new(v("a*.0", Sort::Int)),
        Box::new(Formula::Or(vec![not(v("b*.1.2", Sort::Int)), v("c*.3", Sort::Int)])),
    );
    let typed = Formula::Implies(
        Box::new(v("a*.0", Sort::Bool)),
        Box::new(Formula::Or(vec![not(v("b*.1.2", Sort::Bool)), v("c*.3", Sort::Bool)])),
    );
    assert!(parsed_clause_matches_typed(&parsed, &typed));

    // ...and one wrong name anywhere inside still refuses the whole clause.
    let typed_wrong = Formula::Implies(
        Box::new(v("a*.0", Sort::Bool)),
        Box::new(Formula::Or(vec![not(v("b*.1.9", Sort::Bool)), v("c*.3", Sort::Bool)])),
    );
    assert!(!parsed_clause_matches_typed(&parsed, &typed_wrong));
}

/// `Var` and `SymVar` are documented as the same variable in two spellings, so
/// they match — subject to the same name and sentinel rules.
#[test]
fn var_matches_symvar_spelling() {
    let parsed = v("self*.0", Sort::Int);
    let typed = Formula::SymVar(trust_types::Symbol::intern("self*.0"), Sort::Bool);
    assert!(parsed_clause_matches_typed(&parsed, &typed));

    let typed_other = Formula::SymVar(trust_types::Symbol::intern("self*.1"), Sort::Bool);
    assert!(!parsed_clause_matches_typed(&parsed, &typed_other));
}

/// Reflexivity: any formula matches itself, sentinel or not.
#[test]
fn identical_formulas_always_match() {
    for f in [
        Formula::Bool(true),
        Formula::Int(7),
        v("x", Sort::Int),
        v("y", Sort::Bool),
        not(v("z", Sort::Bool)),
        Formula::And(vec![v("a", Sort::Int), v("b", Sort::Bool)]),
    ] {
        assert!(parsed_clause_matches_typed(&f, &f), "{f:?} must match itself");
    }
}
