//! The AGGREGATE-FIELD twin of `return_slot_join_version_tests` and
//! `early_return_postcondition_tests`: an `ensures` over a FIELD of the
//! returned struct, on a body whose select writes the field's source local in
//! TWO predecessor blocks.
//!
//! THE DEFECT (measured 2026-08-27 against veripb-alab's SATURATE per-term
//! step). This is a TRUE clause:
//!
//! ```ignore
//! #[trust::ensures(move |ret: &Term| ret.coeff <= degree)]
//! fn sat_term(degree: i64, coeff: i64, v: u32) -> Term {
//!     let c = if coeff <= degree { coeff } else { degree };
//!     Term { coeff: c, lit: Lit { var: v, negated: false } }
//! }
//! ```
//!
//! `c` is one of `coeff` (taken only when `coeff <= degree`) or `degree`, so
//! `ret.coeff <= degree` holds on both branches. The native lane reported
//! `0 proved, 3 failed, counterexample: verified_counterexample = true`.
//!
//! `TRUST_DUMP_V2_VC` shows why. The then-branch VC carries
//!
//! ```text
//! Eq(Var("_0.0"), Var("c"))                        <- the field pin
//! Eq(Var("_0.0#s3_3"), Var("c#e_s2_0"))            <- the merge pin
//! Not(Le(Var("_0.0#s3_3"), Var("degree")))         <- the negated clause
//! ```
//!
//! The clause is negated at `_0.0#s3_3`, which the merge pin equates to
//! `c#e_s2_0` — the JOIN token of `c` across the two select arms. Nothing
//! defines that name: the arms define `c` and `c#s2_0`. So the negated clause
//! is a refutable query over a FREE value and the "counterexample" is a model
//! of a formula about nothing — the same failure mode as the two sibling
//! files, one level down, on a return-slot FIELD rather than on `_0` itself.
//!
//! WHY THE SIBLING FIXES DO NOT REACH IT. `unify_return_slot_versions` is
//! scoped by `is_return_slot_name`, which is `name == "_0" || name
//! .starts_with("_0#")` — it does not match `_0.0` or `_0.0#s3_3`. The
//! early-return MERGE PIN covers `&mut`-parameter places, not an ordinary
//! local feeding an aggregate field.
//!
//! REPRODUCED AT CRATE LEVEL by the fixture below, which needs no compiler
//! build. Its then-branch Postcondition VC is
//!
//! ```text
//! Eq(Var("_0.0"),      Var("c#s1_0"))        <- the field pin
//! Eq(Var("_0.0#s3_0"), Var("c#s1_0_s2_0"))   <- the merge pin, to the JOIN name
//! Not(Le(Var("_0.0#s3_0"), Var("degree")))   <- the negated clause
//! ```
//!
//! `c#s1_0_s2_0` is the reaching-def join of `c` over bb1 and bb2 and is
//! constrained by nothing, so the clause never reaches the solver as a
//! statement about the returned value.
//!
//! WHERE THE FIX BELONGS. `return_edge_merge_pins` already emits exactly the
//! needed shape — `subject#<join token> == subject#<this predecessor's exit
//! token>` — but only for subjects in `out_param_store_sorts`, i.e. places
//! stored through a `&mut` parameter, AND only for subjects the CLAUSE names.
//! Here the subject is an ordinary temp the clause never mentions; it is
//! reached only through the field pin. Widening that population is a change to
//! a lane with four deliberate soundness gates (in particular GATE 4, "never
//! trade a visible gap for an invisible one"), so it is left unmade rather
//! than guessed: turning a fail-safe false REFUTATION into a possible false
//! PROOF would be a far worse defect than the one this file records.
//!
//! DISCRIMINATION. The measured evidence that this is a defect and not a
//! missing feature is the pairing: the bare-select twin (`fn d(..) -> i64 {
//! if coeff <= degree { coeff } else { degree } }` with `ensures result <=
//! degree`) PROVES, and a plain-parameter field (`Term { coeff, .. }` with
//! `ensures ret.coeff <= degree`) PROVES. Only the two together fail.

use trust_types::{
    AggregateKind, BasicBlock, BinOp, BlockId, Formula, LocalDecl, Operand, Place,
    Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, VariantDef, VerifiableBody,
    VerifiableFunction,
};

use super::generate_v2_contract_vcs_impl;

fn span() -> SourceSpan {
    SourceSpan::default()
}

fn i64_ty() -> Ty {
    Ty::Int { width: 64, signed: true }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: span() }
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

/// `Term { coeff: i64, lit: i64 }` — `lit` stands in for the literal payload;
/// only the `coeff` field carries the clause.
fn term_ty() -> Ty {
    Ty::Adt {
        adt_kind: None,
        layout: None,
        name: "veripb::Term".into(),
        fields: vec![("coeff".into(), i64_ty()), ("lit".into(), i64_ty())],
        variants: vec![VariantDef {
            name: "Term".into(),
            discriminant: 0,
            fields: vec![("coeff".into(), i64_ty()), ("lit".into(), i64_ty())],
        }],
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
    }
}

/// The measured body at `-O`: a select writing `_3` in two blocks, then one
/// aggregate store into the return slot.
///
/// ```text
/// bb0: _5 = Le(_2, _1); switchInt(_5) [0 -> bb2, otherwise -> bb1]
/// bb1: _4 = _2;         goto bb3          // c = coeff   (_4 is a TEMP)
/// bb2: _4 = _1;         goto bb3          // c = degree
/// bb3: _0 = Term { coeff: _4, lit: _3 }; return
/// ```
fn select_into_field(clause: Formula) -> VerifiableFunction {
    VerifiableFunction {
        name: "sat_term".into(),
        def_path: "sat_term".into(),
        span: span(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: term_ty(), name: None },
                LocalDecl { index: 1, ty: i64_ty(), name: Some("degree".into()) },
                LocalDecl { index: 2, ty: i64_ty(), name: Some("coeff".into()) },
                LocalDecl { index: 3, ty: i64_ty(), name: Some("lit".into()) },
                LocalDecl { index: 4, ty: i64_ty(), name: Some("c".into()) },
                LocalDecl { index: 5, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                block(
                    0,
                    vec![assign(
                        Place::local(5),
                        Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(1)),
                        ),
                    )],
                    Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(5)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: span(),
                    },
                ),
                block(
                    1,
                    vec![assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(2))))],
                    Terminator::Goto(BlockId(3)),
                ),
                block(
                    2,
                    vec![assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(1))))],
                    Terminator::Goto(BlockId(3)),
                ),
                block(
                    3,
                    vec![assign(
                        Place::local(0),
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "veripb::Term".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![
                                Operand::Move(Place::local(4)),
                                Operand::Move(Place::local(3)),
                            ],
                        ),
                    )],
                    Terminator::Return,
                ),
            ],
            arg_count: 3,
            return_ty: term_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![clause],
        spec: Default::default(),
    }
}

fn postcondition_formulas(f: &VerifiableFunction) -> Vec<Formula> {
    generate_v2_contract_vcs_impl(f, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, trust_types::VcKind::Postcondition))
        .map(|vc| vc.formula)
        .collect()
}

/// Union-find over the formula's equalities: the set of names transitively
/// connected to `start` by `Eq` conjuncts anywhere in the VC.
///
/// Name IDENTITY is the wrong criterion here. The clause legitimately sits on
/// the join spelling `_0.0#s3_0`; what makes it a statement about the RETURNED
/// value rather than about nothing is that a chain of equalities leads from it
/// down to a parameter — `_0.0#s3_0 = c#s1_0_s2_0 = c#s1_0 = coeff`. This walks
/// that chain.
fn connected_names(formula: &Formula, start: &str) -> std::collections::BTreeSet<String> {
    fn edges(f: &Formula, out: &mut Vec<(Vec<String>, Vec<String>)>) {
        match f {
            Formula::And(cs) => cs.iter().for_each(|c| edges(c, out)),
            Formula::Eq(l, r) => {
                out.push((l.free_variables().into_iter().collect(), r.free_variables().into_iter().collect()));
                edges(l, out);
                edges(r, out);
            }
            _ => {}
        }
    }
    let mut pairs = Vec::new();
    edges(formula, &mut pairs);
    let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    seen.insert(start.to_string());
    loop {
        let before = seen.len();
        for (l, r) in &pairs {
            if l.iter().any(|n| seen.contains(n)) || r.iter().any(|n| seen.contains(n)) {
                seen.extend(l.iter().cloned());
                seen.extend(r.iter().cloned());
            }
        }
        if seen.len() == before {
            return seen;
        }
    }
}

/// The spelling the negated clause is versioned at, if any.
fn clause_field_name(formula: &Formula) -> Option<String> {
    formula
        .free_variables()
        .into_iter()
        .filter(|n| n == "_0.0" || n.starts_with("_0.0#"))
        .max_by_key(|n| n.len())
}

/// `ret.coeff <= degree` — TRUE for the select body.
fn clause_true() -> Formula {
    Formula::Le(
        Box::new(Formula::Var("_0.0".into(), Sort::Int)),
        Box::new(Formula::Var("degree".into(), Sort::Int)),
    )
}

/// `ret.coeff > degree` — the FALSE twin, which must still CONNECT.
fn clause_false() -> Formula {
    Formula::Gt(
        Box::new(Formula::Var("_0.0".into(), Sort::Int)),
        Box::new(Formula::Var("degree".into(), Sort::Int)),
    )
}

/// The clause's field name must be CONNECTED to the pin — one spelling per VC.
///
/// Both directions, as the sibling files do: a true clause that connects is
/// worthless as evidence unless its false twin connects the same way, since
/// discrimination is the solver's job and a twin that reaches a genuine
/// pinned value stays refutable from it.
#[test]
fn a_clause_on_an_aggregate_field_connects_to_its_pin() {
    for (label, clause) in [("true", clause_true()), ("false", clause_false())] {
        let f = select_into_field(clause);
        let formulas = postcondition_formulas(&f);
        assert!(!formulas.is_empty(), "{label}: no Postcondition VC was generated");
        for (i, formula) in formulas.iter().enumerate() {
            let field = clause_field_name(formula)
                .unwrap_or_else(|| panic!("{label}: VC {i} names no return-slot field"));
            let reach = connected_names(formula, &field);
            assert!(
                reach.contains("coeff") || reach.contains("degree"),
                "{label} clause, VC {i}: the clause is versioned at `{field}`, which no chain \
                 of equalities connects to a parameter — it reaches only {reach:?}. The clause \
                 is therefore a query over a FREE value and the row refutes whatever the body \
                 does.\n\nfull formula:\n{formula:?}",
            );
        }
    }
}
