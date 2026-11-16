use trust_types::{
    AtomicOperation, BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Projection, Rvalue,
    Sort, SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::{ParameterRebind, postcondition_references_mutated_param, rebound_parameter_places};

// ensures `*r == a` — references the parameter named "a".
fn ensures_eq_ret_a() -> Formula {
    Formula::Eq(
        Box::new(Formula::Var("__ret".into(), Sort::Int)),
        Box::new(Formula::Var("a".into(), Sort::Int)),
    )
}

fn func_with(stmts: Vec<Statement>) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: None },
            ],
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 1,
            return_ty: Ty::usize(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

#[test]
fn mut_borrow_of_param_in_ensures_is_flagged() {
    // f(mut a) { let p = &mut a; ...; a } — the &mut staleness vector. The whole-local
    // reassign scan misses `*p = ..` (place is `*p`), but the `_2 = &mut _1` borrow flags it.
    let func = func_with(vec![
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::default(),
        },
    ]);
    assert!(
        postcondition_references_mutated_param(&func, &ensures_eq_ret_a()),
        "an ensures over a param mutably borrowed (&mut a) must be flagged (fail-closed)"
    );
}

#[test]
fn unborrowed_param_in_ensures_is_not_flagged() {
    // identity f(a) { a } — no mutation, `*r == a` is genuinely true and must still prove.
    let func = func_with(vec![Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: SourceSpan::default(),
    }]);
    assert!(
        !postcondition_references_mutated_param(&func, &ensures_eq_ret_a()),
        "an identity ensures with no param mutation must NOT be flagged (still proves)"
    );
}

// ── Trust (2026-10-03, KNOWN_HAZARDS R-c): writes BELOW a parameter ──────────────
//
// `fn z(mut s: S) -> u8 ensures s.a == 0 { s.a = 0; 1 }` was proved and
// kernel-certified under `-Ztrust-policy=certify`: the predicate saw only whole-local
// writes, so the field store slipped past it and the VC read `s.0` at its exit
// version. Each row below is one write channel of a by-value parameter `s: S { a, b }`
// (local 1), checked against a clause that names `s.a` (`s.0`), and the control that
// must stay unflagged: a store through a `&mut` parameter (PD-15 reads that pointee at
// exit on purpose).
//
// The predicate is the UNION of a channel walk and the `local_defs` seam's non-SSA test
// (`7f118dfc1f` closed the same hole with the seam alone). The seam names a non-SSA
// parameter WHOLE, so the rows marked "seam union" pin capabilities the walk alone kept
// and the union gives up (DECISION_QUEUE R-c): a write to the OTHER field, an `assume`,
// a store through a reference a by-value parameter holds in a field, a `Drop`.

fn span() -> SourceSpan {
    SourceSpan::default()
}

fn struct_s() -> Ty {
    Ty::adt("S", vec![("a".into(), Ty::u8()), ("b".into(), Ty::u8())])
}

/// `fn f(s: <param_ty>) -> u8` with one scratch local `_2: <scratch_ty>`, the given
/// statements in bb0, and `terminator` ending bb0 (a `Return` unless a test needs a call).
fn func_with_param(
    param_ty: Ty,
    scratch_ty: Ty,
    stmts: Vec<Statement>,
    terminator: Terminator,
) -> VerifiableFunction {
    let mut blocks = vec![BasicBlock { id: BlockId(0), stmts, terminator }];
    if !matches!(blocks[0].terminator, Terminator::Return) {
        blocks.push(BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return });
    }
    VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: span(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u8(), name: None },
                LocalDecl { index: 1, ty: param_ty, name: Some("s".into()) },
                LocalDecl { index: 2, ty: scratch_ty, name: None },
            ],
            blocks,
            arg_count: 1,
            return_ty: Ty::u8(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn by_value(stmts: Vec<Statement>) -> VerifiableFunction {
    func_with_param(struct_s(), Ty::u8(), stmts, Terminator::Return)
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: span() }
}

fn const_u8(value: u8) -> Rvalue {
    Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(u128::from(value), 8)))
}

/// `ensures <name> == 0`, with `<name>` the formula name the generator gives `place`.
fn ensures_place_is_zero(func: &VerifiableFunction, place: &Place) -> Formula {
    Formula::Eq(
        Box::new(Formula::Var(crate::place_to_var_name(func, place), Sort::Int)),
        Box::new(Formula::Int(0)),
    )
}

fn field_a() -> Place {
    Place::field(1, 0)
}

fn field_b() -> Place {
    Place::field(1, 1)
}

#[test]
fn field_names_are_the_projection_spelling() {
    // The rows below match a clause against a written place BY NAME; pin the two
    // names so a renaming cannot make every row vacuous.
    let func = by_value(vec![]);
    assert_eq!(crate::place_to_var_name(&func, &field_a()), "s.0");
    assert_eq!(crate::place_to_var_name(&func, &field_b()), "s.1");
}

#[test]
fn field_assign_of_by_value_param_is_flagged() {
    // `z`: `s.a = 0` under `ensures s.a == 0`.
    let func = by_value(vec![assign(field_a(), const_u8(0))]);
    assert!(
        postcondition_references_mutated_param(&func, &ensures_place_is_zero(&func, &field_a())),
        "a field store of a by-value parameter must fail-close an ensures over that field"
    );
    assert_eq!(
        rebound_parameter_places(&func),
        vec![
            ParameterRebind { parameter: 1, place_name: "s.0".into() },
            ParameterRebind { parameter: 1, place_name: "s".into() },
        ],
        "the walk names the written field; the seam union adds the whole parameter"
    );
}

#[test]
fn whole_param_clause_over_a_written_field_is_flagged() {
    // A clause that names the whole parameter reads every field, the written one too.
    let func = by_value(vec![assign(field_a(), const_u8(0))]);
    let post = Formula::Eq(
        Box::new(Formula::Var("s".into(), Sort::Int)),
        Box::new(Formula::Var("__ret".into(), Sort::Int)),
    );
    assert!(postcondition_references_mutated_param(&func, &post));
}

#[test]
fn unrelated_field_write_is_flagged_by_the_seam_union() {
    // `unrel`: `s.b = 0` under `ensures s.a == 0`. The clause reads the entry value of a
    // field nothing writes, and the walk names only `s.1`, which would keep it provable.
    // The seam union names `s` whole (a partial write makes it non-SSA), so the clause
    // is fail-closed: a capability cost, DECISION_QUEUE R-c.
    let func = by_value(vec![assign(field_b(), const_u8(0))]);
    assert!(
        postcondition_references_mutated_param(&func, &ensures_place_is_zero(&func, &field_a())),
        "the seam union fail-closes a clause over the other field of a written parameter"
    );
    assert_eq!(
        rebound_parameter_places(&func),
        vec![
            ParameterRebind { parameter: 1, place_name: "s.1".into() },
            ParameterRebind { parameter: 1, place_name: "s".into() },
        ],
    );
}

#[test]
fn index_assign_of_by_value_array_param_is_flagged() {
    // `s[_2] = 1` on `s: [u8; 4]`: an Index chain is recorded as the WHOLE parameter,
    // so a clause over any element (here the constant element 0) is fail-closed.
    let func = func_with_param(
        Ty::Array { elem: Box::new(Ty::u8()), len: 4 },
        Ty::usize(),
        vec![assign(Place { local: 1, projections: vec![Projection::Index(2)] }, const_u8(1))],
        Terminator::Return,
    );
    let element_zero = Place {
        local: 1,
        projections: vec![Projection::ConstantIndex { offset: 0, min_length: 4, from_end: false }],
    };
    assert!(postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &element_zero)
    ));
    assert_eq!(
        rebound_parameter_places(&func),
        vec![ParameterRebind { parameter: 1, place_name: "s".into() }],
    );
}

#[test]
fn mut_borrow_of_a_field_is_flagged() {
    // `viaref`: `let p = &mut s.a; *p = 9;` — the store's place is `*p`; the borrow is
    // where the alias is minted.
    let func = func_with_param(
        struct_s(),
        Ty::Ref { mutable: true, inner: Box::new(Ty::u8()) },
        vec![
            assign(Place::local(2), Rvalue::Ref { mutable: true, place: field_a() }),
            assign(Place { local: 2, projections: vec![Projection::Deref] }, const_u8(9)),
        ],
        Terminator::Return,
    );
    assert!(postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &field_a())
    ));
    // The walk names the borrow by its referent (`s.0`), but the seam union counts the
    // borrow as an escape of `s`'s own storage and names `s` whole: the sibling field is
    // fail-closed too (DECISION_QUEUE R-c).
    assert!(postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &field_b())
    ));
}

#[test]
fn pointee_borrow_through_a_mut_ref_param_is_not_flagged() {
    // `reset(&mut self.s)` for `self: &mut T` borrows `&mut (*_1).0`: the alias addresses
    // the POINTEE and cannot rebind `_1`. Both halves leave it out (the walk by its
    // `Deref`-through-a-reference rule, the seam by its pointee-borrow variant); the
    // strict seam variant turned a correct `ensures !self.s.detached` into a refutation
    // (`chc-entry-inputs/wedge_refutation_attests.rs`).
    let pointee_a = Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] };
    let func = func_with_param(
        Ty::Ref { mutable: true, inner: Box::new(struct_s()) },
        Ty::Ref { mutable: true, inner: Box::new(Ty::u8()) },
        vec![assign(Place::local(2), Rvalue::Ref { mutable: true, place: pointee_a.clone() })],
        Terminator::Return,
    );
    assert!(!postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &pointee_a)
    ));
    assert!(rebound_parameter_places(&func).is_empty());
}

#[test]
fn raw_address_of_a_field_records_the_whole_parameter() {
    // `&raw mut s.b` can reach `s.a` by pointer arithmetic, so it is recorded WHOLE and
    // a clause over the OTHER field is fail-closed too.
    let func = func_with_param(
        struct_s(),
        Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
        vec![assign(Place::local(2), Rvalue::AddressOf(true, field_b()))],
        Terminator::Return,
    );
    assert!(postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &field_a())
    ));
}

#[test]
fn call_destination_into_a_field_is_flagged() {
    // `callw`: `s.a = id(4)` — the field is a call destination.
    let call = Terminator::Call {
        func: "id".into(),
        args: vec![Operand::Constant(trust_types::ConstValue::Uint(4, 8))],
        dest: field_a(),
        target: Some(BlockId(1)),
        span: span(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: Default::default(),
        callee_identity: None,
        callee_key: None,
    };
    let func = func_with_param(struct_s(), Ty::u8(), vec![], call);
    assert!(postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &field_a())
    ));
}

#[test]
fn set_discriminant_of_a_by_value_enum_param_is_flagged() {
    // `SetDiscriminant` on the parameter itself changes every payload name below it.
    let func = func_with_param(
        struct_s(),
        Ty::u8(),
        vec![Statement::SetDiscriminant { place: Place::local(1), variant_index: 1 }],
        Terminator::Return,
    );
    let payload =
        Place { local: 1, projections: vec![Projection::Downcast(1), Projection::Field(0)] };
    assert!(postcondition_references_mutated_param(&func, &ensures_place_is_zero(&func, &payload)));
}

#[test]
fn store_through_a_mut_ref_param_is_not_flagged() {
    // `fn f(s: &mut S) ensures s.a == 0 { s.a = 0 }` — `(*s).a` is the CALLER's object.
    // Its unprimed name reads the pointee at exit until the PD-15 flip, pinned by
    // `tests/ui/trust/d2-primes/wedge_primed.rs`; this predicate must not touch it.
    let pointee_a = Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] };
    let func = func_with_param(
        Ty::Ref { mutable: true, inner: Box::new(struct_s()) },
        Ty::u8(),
        vec![assign(pointee_a.clone(), const_u8(0))],
        Terminator::Return,
    );
    assert!(
        !postcondition_references_mutated_param(&func, &ensures_place_is_zero(&func, &pointee_a)),
        "a store through a &mut parameter is the PD-15 exit read, not an entry-value rebind"
    );
    assert!(rebound_parameter_places(&func).is_empty());
}

#[test]
fn store_through_an_owned_pointer_param_is_flagged_whole() {
    // A `Deref` through a parameter that is NOT a reference or raw pointer (a `Box` is
    // an ADT here) writes storage the parameter owns: recorded whole, fail-closed.
    let pointee_a = Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] };
    let func = func_with_param(
        Ty::adt("alloc::boxed::Box<S>", vec![]),
        Ty::u8(),
        vec![assign(pointee_a.clone(), const_u8(0))],
        Terminator::Return,
    );
    assert!(postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &pointee_a)
    ));
    assert_eq!(
        rebound_parameter_places(&func),
        vec![ParameterRebind { parameter: 1, place_name: "s".into() }],
    );
}

#[test]
fn atomic_access_of_a_field_is_flagged() {
    // An atomic call's accessed place is written by the call (stores, RMWs).
    let call = Terminator::Call {
        func: "core::intrinsics::atomic_store_seqcst".into(),
        args: vec![],
        dest: Place::local(2),
        target: Some(BlockId(1)),
        span: span(),
        atomic: Some(AtomicOperation {
            place: field_a(),
            dest: None,
            op_kind: trust_types::AtomicOpKind::Store,
            ordering: trust_types::AtomicOrdering::SeqCst,
            failure_ordering: None,
            span: span(),
        }),
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: Default::default(),
        callee_identity: None,
        callee_key: None,
    };
    let func = func_with_param(struct_s(), Ty::u8(), vec![], call);
    assert!(postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &field_a())
    ));
}

#[test]
fn unsupported_statement_records_every_parameter() {
    // A statement the model does not represent may write any place: fail closed.
    let func = by_value(vec![Statement::Unsupported {
        kind: "Probe".into(),
        detail: "unmodelled".into(),
        operands: vec![],
        span: span(),
    }]);
    assert!(postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &field_a())
    ));
}

#[test]
fn assume_intrinsic_is_charged_by_the_seam_union() {
    // `assume` writes nothing, and the walk leaves it out. The seam classifies every
    // `Statement::Intrinsic` as an unlocatable write charged to EVERY local, so the
    // union fail-closes a clause over an untouched parameter in a body that contains
    // one: a capability cost, DECISION_QUEUE R-c.
    let func = by_value(vec![Statement::Intrinsic {
        name: "assume".into(),
        args: vec![Operand::Constant(trust_types::ConstValue::Bool(true))],
    }]);
    assert!(postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &field_a())
    ));
    assert_eq!(
        rebound_parameter_places(&func),
        vec![ParameterRebind { parameter: 1, place_name: "s".into() }],
    );
}

#[test]
fn drop_of_a_by_value_param_is_charged_by_the_seam_union() {
    // The walk leaves `Drop` out (drop glue mints no defined value). The seam counts a
    // `Drop` of the parameter as a partial write (a custom `Drop::drop` takes `&mut
    // self`), so the union fail-closes a clause over it: DECISION_QUEUE R-c.
    let drop = Terminator::Drop {
        place: Place::local(1),
        target: BlockId(1),
        span: span(),
        unwind: Default::default(),
    };
    let func = func_with_param(struct_s(), Ty::u8(), vec![], drop);
    assert!(postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &field_a())
    ));
    assert_eq!(
        rebound_parameter_places(&func),
        vec![ParameterRebind { parameter: 1, place_name: "s".into() }],
    );
}

#[test]
fn store_through_a_reference_held_in_a_field_is_flagged_by_the_seam_union() {
    // `self: Pin<&mut S>` writing `self.a = 0` stores to `(*(self.0)).0`: the `Deref`
    // goes through the `&mut S` the by-value `Pin` holds, so the write lands in the
    // caller's object, exactly as for a `&mut S` parameter (PD-15 scope), and the walk
    // leaves it out. The seam's `LocalWrite::of_place` counts any place whose FIRST
    // projection is not a `Deref` as a partial write of its root, so the union names
    // `self` whole and fail-closes the clause: a capability cost, DECISION_QUEUE R-c.
    let pin = Ty::adt(
        "core::pin::Pin<&mut S>",
        vec![("pointer".into(), Ty::Ref { mutable: true, inner: Box::new(struct_s()) })],
    );
    let pointee_a = Place {
        local: 1,
        projections: vec![Projection::Field(0), Projection::Deref, Projection::Field(0)],
    };
    let func = func_with_param(
        pin,
        Ty::u8(),
        vec![assign(pointee_a.clone(), const_u8(0))],
        Terminator::Return,
    );
    assert!(postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &pointee_a)
    ));
    assert_eq!(
        rebound_parameter_places(&func),
        vec![ParameterRebind { parameter: 1, place_name: "s".into() }],
        "only the seam half names it, and names it whole"
    );
}

#[test]
fn reseating_the_reference_a_field_holds_is_flagged() {
    // The same `Pin`, but the body overwrites the reference itself (`self.0 = ..`): that
    // is the parameter's own storage, so a clause through it is fail-closed.
    let pin = Ty::adt(
        "core::pin::Pin<&mut S>",
        vec![("pointer".into(), Ty::Ref { mutable: true, inner: Box::new(struct_s()) })],
    );
    let func = func_with_param(
        pin,
        Ty::Ref { mutable: true, inner: Box::new(struct_s()) },
        vec![assign(Place::field(1, 0), Rvalue::Use(Operand::Copy(Place::local(2))))],
        Terminator::Return,
    );
    let pointee_a = Place {
        local: 1,
        projections: vec![Projection::Field(0), Projection::Deref, Projection::Field(0)],
    };
    assert!(postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &pointee_a)
    ));
}

#[test]
fn unsupported_rvalue_operand_records_the_whole_parameter() {
    // The extractor lowers a mutable `Reborrow` of a user ADT to
    // `Unsupported { operands: [Copy(place)] }`: an alias the walk cannot name.
    let func = by_value(vec![assign(
        Place::local(2),
        Rvalue::Unsupported {
            kind: "Reborrow".into(),
            detail: "probe".into(),
            operands: vec![Operand::Copy(field_b())],
        },
    )]);
    assert!(postcondition_references_mutated_param(
        &func,
        &ensures_place_is_zero(&func, &field_a())
    ));
}
