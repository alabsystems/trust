//! VGAPS-G1 (the verifier-gaps design §2.3): the element-read congruence at the fact
//! level. Until G1 this was `immutable_read_value_tie_tests`, and three of its pins
//! encoded the retired gates (`mut_ref_base_declines`, `reseated_param_base_declines`,
//! `mut_borrowed_root_declines`). Each is REPLACED, not deleted: here by a pin that the
//! fact is emitted with the canonical key, and in `tests/element_read_congruence_realmir.rs`
//! by a verdict twin on real MIR with the named write placed between the two reads, which
//! must REFUTE (`must_refute_store_between_temps`, `must_refute_reseat_temps` and
//! `must_refute_two_reborrows_across_reseat`, `must_refute_reborrow_store_temps` and
//! `must_refute_elem_ref_store_temps`).

use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::{RowGlobalFacts, build_element_read_congruence_facts};

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}
fn usize_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}
fn shared_arr() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(Ty::Array { elem: Box::new(u32_ty()), len: 3 }) }
}
fn elem_read(base: usize, idx: usize) -> Operand {
    Operand::Copy(Place {
        local: base,
        projections: vec![Projection::Deref, Projection::Index(idx)],
    })
}
fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

/// `fn f(ps: &[u32;3], i: usize)` with two element reads through distinct
/// single-write index temps (`_5 = i; _3 = (*ps)[_5]; _6 = i; _4 = (*ps)[_6]`)
/// — the exact MIR shape of the guard-read / use-read pair.
fn two_read_func() -> VerifiableFunction {
    VerifiableFunction {
        name: "two_reads".to_string(),
        def_path: "test::two_reads".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: shared_arr(), name: Some("ps".into()) },
                LocalDecl { index: 2, ty: usize_ty(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: u32_ty(), name: None },
                LocalDecl { index: 4, ty: u32_ty(), name: None },
                LocalDecl { index: 5, ty: usize_ty(), name: None },
                LocalDecl { index: 6, ty: usize_ty(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(5, Rvalue::Use(Operand::Copy(Place::local(2)))),
                    assign(3, Rvalue::Use(elem_read(1, 5))),
                    assign(6, Rvalue::Use(Operand::Copy(Place::local(2)))),
                    assign(4, Rvalue::Use(elem_read(1, 6))),
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The one fact of `facts`, which must be `Or([Not(Eq(_5, _6)), Eq(read_a, read_b)])`.
fn the_one_congruence(facts: &[Formula]) -> (&Formula, &Formula) {
    assert_eq!(facts.len(), 1, "expected exactly one pair fact; got {facts:?}");
    match &facts[0] {
        Formula::Or(djs) => {
            assert_eq!(djs.len(), 2, "hypothesis + tie; got {djs:?}");
            let Formula::Not(inner) = &djs[0] else {
                panic!("first disjunct must be the index-disequality hypothesis; got {:?}", djs[0])
            };
            assert!(matches!(&**inner, Formula::Eq(..)), "`Not(Eq(..))`; got {inner:?}");
            assert!(
                matches!(&djs[1], Formula::Eq(..)),
                "second disjunct must be the read-value tie; got {:?}",
                djs[1]
            );
            (&djs[0], &djs[1])
        }
        other => panic!("expected Or(..); got {other:?}"),
    }
}

/// Base case: a shared-ref array base emits exactly ONE congruence fact
/// `Or(idx_a != idx_b, read_a == read_b)` — the index tie is a HYPOTHESIS.
#[test]
fn shared_ref_two_reads_emit_congruence() {
    let func = two_read_func();
    the_one_congruence(&build_element_read_congruence_facts(&func));
}

/// Replaces `mut_ref_base_declines`: a `&mut` base emits the SAME fact. The congruence
/// is a theorem at one point (I1/I2), not an immutability claim; a store between the
/// reads re-versions the element names or kills the guard read's definition, which
/// `element_read_congruence_realmir::every_write_between_the_reads_still_refutes` pins on
/// real MIR (`must_refute_store_between_temps`).
#[test]
fn a_mut_ref_base_emits_the_congruence() {
    let shared = build_element_read_congruence_facts(&two_read_func());
    let mut func = two_read_func();
    func.body.locals[1].ty =
        Ty::Ref { mutable: true, inner: Box::new(Ty::Array { elem: Box::new(u32_ty()), len: 3 }) };
    let facts = build_element_read_congruence_facts(&func);
    the_one_congruence(&facts);
    assert_eq!(facts, shared, "the base's mutability does not change the fact's spelling");
}

/// Replaces `reseated_param_base_declines`: `ps = other;` between the reads still groups
/// the two reads under `ps`'s one canonical key (both name `ps*[..]`, so at any one point
/// both denote elements of the one array `ps` holds there). The reseat is a write of
/// `ps`, which re-versions every `ps*[..]` name, so the guard read's definition does not
/// meet the use read: `must_refute_reseat_temps` and
/// `must_refute_two_reborrows_across_reseat` are its real-MIR twins.
#[test]
fn a_reseated_param_base_emits_one_congruence_under_its_one_name() {
    let mut func = two_read_func();
    func.body.locals.push(LocalDecl { index: 7, ty: shared_arr(), name: None });
    // Insert `ps = copy _7` BETWEEN the two reads.
    func.body.blocks[0].stmts.insert(2, assign(1, Rvalue::Use(Operand::Copy(Place::local(7)))));
    the_one_congruence(&build_element_read_congruence_facts(&func));
}

/// Replaces `mut_borrowed_root_declines`: a `&mut` borrow of the root emits the fact too;
/// a store through the borrow is a write channel the names carry
/// (`must_refute_reborrow_store_temps`, `must_refute_elem_ref_store_temps`).
#[test]
fn a_mut_borrowed_root_emits_the_congruence() {
    let mut func = two_read_func();
    func.body.locals.push(LocalDecl {
        index: 7,
        ty: Ty::Ref { mutable: true, inner: Box::new(shared_arr()) },
        name: None,
    });
    func.body.blocks[0]
        .stmts
        .insert(2, assign(7, Rvalue::Ref { mutable: true, place: Place::local(1) }));
    the_one_congruence(&build_element_read_congruence_facts(&func));
}

/// (I1): the group key is the CANONICAL place. A read through a single-assignment
/// reborrow `_7 = &(*ps)` names `ps*[..]` (`crate::canonical_place` folds it), so it
/// groups with a direct read of `ps`, while a read of ANOTHER base `qs` does not group
/// with either: different canonical roots are different arrays.
#[test]
fn the_group_key_is_the_canonical_place() {
    let mut func = two_read_func();
    func.body.locals.push(LocalDecl { index: 7, ty: shared_arr(), name: None });
    func.body.blocks[0].stmts.insert(
        2,
        assign(
            7,
            Rvalue::Ref {
                mutable: false,
                place: Place { local: 1, projections: vec![Projection::Deref] },
            },
        ),
    );
    // `_4 = (*_7)[_6]`, the reborrow's spelling of the second read.
    func.body.blocks[0].stmts[4] = assign(4, Rvalue::Use(elem_read(7, 6)));
    assert_eq!(
        crate::canonical_place(
            &func,
            &Place { local: 7, projections: vec![Projection::Deref, Projection::Index(6)] }
        )
        .local,
        1,
        "the reborrow folds to `ps`"
    );
    the_one_congruence(&build_element_read_congruence_facts(&func));

    // Another base: `qs` (a second parameter), read once each with `ps`.
    let mut other = two_read_func();
    other.body.locals.push(LocalDecl { index: 7, ty: shared_arr(), name: Some("qs".into()) });
    other.body.blocks[0].stmts[3] = assign(4, Rvalue::Use(elem_read(7, 6)));
    assert!(
        build_element_read_congruence_facts(&other).is_empty(),
        "reads of two bases never group: {:?}",
        build_element_read_congruence_facts(&other)
    );
}

/// Reads of DIFFERENT fields (`(*ps)[_5].0` vs `(*ps)[_6].1`) must NOT group:
/// different shapes are different elements-projections — no tie.
#[test]
fn different_field_shapes_do_not_group() {
    let mut func = two_read_func();
    // Retype the array element to a 2-tuple and re-project the reads.
    func.body.locals[1].ty = Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Array { elem: Box::new(Ty::Tuple(vec![u32_ty(), u32_ty()])), len: 3 }),
    };
    let read_a = Operand::Copy(Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Index(5), Projection::Field(0)],
    });
    let read_b = Operand::Copy(Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Index(6), Projection::Field(1)],
    });
    func.body.blocks[0].stmts[1] = assign(3, Rvalue::Use(read_a));
    func.body.blocks[0].stmts[3] = assign(4, Rvalue::Use(read_b));
    assert!(
        build_element_read_congruence_facts(&func).is_empty(),
        "different field projections must not tie"
    );
}

/// A `Downcast` projection (variant-relative read) bails the whole operand.
#[test]
fn downcast_projection_declines() {
    let mut func = two_read_func();
    let read_a = Operand::Copy(Place {
        local: 1,
        projections: vec![
            Projection::Deref,
            Projection::Index(5),
            Projection::Downcast(0),
            Projection::Field(0),
        ],
    });
    func.body.blocks[0].stmts[1] = assign(3, Rvalue::Use(read_a.clone()));
    func.body.blocks[0].stmts[3] = assign(4, Rvalue::Use(read_a));
    assert!(build_element_read_congruence_facts(&func).is_empty());
}

/// A `Move` operand is not a read the body can repeat: no fact.
#[test]
fn a_move_operand_is_not_considered() {
    let mut func = two_read_func();
    let moved = |idx| {
        Operand::Move(Place {
            local: 1,
            projections: vec![Projection::Deref, Projection::Index(idx)],
        })
    };
    func.body.blocks[0].stmts[1] = assign(3, Rvalue::Use(moved(5)));
    func.body.blocks[0].stmts[3] = assign(4, Rvalue::Use(moved(6)));
    assert!(build_element_read_congruence_facts(&func).is_empty());
}

/// A variable `name` of `like`'s sort: a read under another SSA version when `name` is
/// `like`'s name with a `#` token.
fn renamed(like: &Formula, name: &str) -> Formula {
    match like {
        Formula::Var(_, sort) => Formula::Var(name.to_owned(), sort.clone()),
        other => panic!("a read is a variable; got {other:?}"),
    }
}
fn var_name(read: &Formula) -> String {
    match read {
        Formula::Var(name, _) => name.clone(),
        other => panic!("a read is a variable; got {other:?}"),
    }
}

/// VGAPS-G2-FOLLOWUP (2) (2026-10-22, `docs/DECISION_QUEUE.md`): a row carries an
/// element-read congruence only when both of its reads are named, by the row itself in
/// any SSA version or by another global fact; it carries every other fact whole. The
/// real-MIR twin is `element_read_congruence_realmir::
/// a_congruence_reaches_only_the_rows_that_read_both_its_elements`.
#[test]
fn a_row_carries_a_congruence_only_when_both_reads_are_named() {
    let func = two_read_func();
    let congruences = build_element_read_congruence_facts(&func);
    let (_, tie) = the_one_congruence(&congruences);
    let Formula::Eq(read_a, read_b) = tie else { unreachable!("the tie is an `Eq`") };
    let (read_a, read_b) = (read_a.as_ref().clone(), read_b.as_ref().clone());
    let congruence = congruences[0].clone();
    let other_fact = Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Int(1)));
    let facts = RowGlobalFacts::new(&func, vec![other_fact.clone(), congruence.clone()]);
    let eq = |a: &Formula, b: &Formula| Formula::Eq(Box::new(a.clone()), Box::new(b.clone()));

    let both = eq(&read_a, &read_b);
    assert_eq!(facts.for_row(&both), vec![other_fact.clone(), congruence.clone()]);
    let versioned = eq(&renamed(&read_a, &format!("{}#s1_0", var_name(&read_a))), &read_b);
    assert_eq!(
        facts.for_row(&versioned),
        vec![other_fact.clone(), congruence.clone()],
        "a read is named in any SSA version"
    );
    for row in [eq(&read_a, &read_a), eq(&read_b, &read_b), Formula::Bool(true)] {
        assert_eq!(facts.for_row(&row), vec![other_fact.clone()], "row {row:?}");
    }

    // A read another global fact names counts as named for every row.
    let names_b = Formula::Le(Box::new(Formula::Int(0)), Box::new(read_b.clone()));
    let facts = RowGlobalFacts::new(&func, vec![names_b.clone(), congruence.clone()]);
    assert_eq!(facts.for_row(&eq(&read_a, &read_a)), vec![names_b.clone(), congruence]);
    assert_eq!(facts.for_row(&Formula::Bool(true)), vec![names_b]);
}

/// The filter's argument that dropping a congruence changes no verdict rests on a base's
/// congruences being PAIRWISE (`value_facts::RowGlobalFacts`): three reads of one base
/// emit one congruence for each of their three pairs, not a chain of two.
#[test]
fn three_reads_of_one_base_emit_every_pair() {
    let mut func = two_read_func();
    func.body.locals.push(LocalDecl { index: 7, ty: u32_ty(), name: None });
    func.body.locals.push(LocalDecl { index: 8, ty: usize_ty(), name: None });
    func.body.blocks[0].stmts.push(assign(8, Rvalue::Use(Operand::Copy(Place::local(2)))));
    func.body.blocks[0].stmts.push(assign(7, Rvalue::Use(elem_read(1, 8))));
    let facts = build_element_read_congruence_facts(&func);
    let mut pairs: Vec<(String, String)> = facts
        .iter()
        .map(|fact| {
            let Formula::Or(disjuncts) = fact else { panic!("a congruence; got {fact:?}") };
            let Some(Formula::Eq(a, b)) = disjuncts.last() else {
                panic!("a congruence ends in its tie; got {fact:?}")
            };
            let (a, b) = (var_name(a), var_name(b));
            if a <= b { (a, b) } else { (b, a) }
        })
        .collect();
    pairs.sort();
    pairs.dedup();
    assert_eq!(pairs.len(), 3, "every pair of the three reads: {facts:?}");
}

/// Review of `95449037cd` (2026-10-22, `docs/DECISION_QUEUE.md` VGAPS-G2-FOLLOWUP): a read
/// that a conjunct the row receives AFTER its global facts can name counts as named. A
/// `SwitchInt` on the element itself (`match a[i]`) puts the read in a path guard alone,
/// and a precondition can name it; with either, a row naming only the other read keeps
/// the congruence. Without both, it drops it (the control).
#[test]
fn a_read_a_later_conjunct_can_name_counts_as_named() {
    let congruence = build_element_read_congruence_facts(&two_read_func())[0].clone();
    let (_, tie) = the_one_congruence(std::slice::from_ref(&congruence));
    let Formula::Eq(read_a, read_b) = tie else { unreachable!("the tie is an `Eq`") };
    let (guarded, used) = if var_name(read_a).contains("[_5]") {
        (read_a.as_ref().clone(), read_b.as_ref().clone())
    } else {
        (read_b.as_ref().clone(), read_a.as_ref().clone())
    };
    assert!(var_name(&guarded).contains("[_5]"), "one read is `(*ps)[_5]`: {guarded:?}");
    let row = Formula::Eq(Box::new(used.clone()), Box::new(used));

    let control = RowGlobalFacts::new(&two_read_func(), vec![congruence.clone()]);
    assert!(control.for_row(&row).is_empty(), "nothing else names `(*ps)[_5]`");

    let mut switched = two_read_func();
    switched.body.blocks[0].terminator = Terminator::SwitchInt {
        discr: elem_read(1, 5),
        targets: vec![(0, BlockId(0))],
        otherwise: BlockId(0),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    let facts = RowGlobalFacts::new(&switched, vec![congruence.clone()]);
    assert_eq!(facts.for_row(&row), vec![congruence.clone()], "the path guard names it");

    let mut required = two_read_func();
    required.preconditions = vec![Formula::Le(Box::new(Formula::Int(0)), Box::new(guarded))];
    let facts = RowGlobalFacts::new(&required, vec![congruence.clone()]);
    assert_eq!(facts.for_row(&row), vec![congruence], "the precondition names it");
}
