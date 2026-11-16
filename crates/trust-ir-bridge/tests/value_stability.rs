//! Stable-value facts must not equate a historical value with later mutated storage.
#[path = "shared_cell_escape.rs"]
mod shared_cell;

use trust_types::{
    ConstValue, Operand, Place, Projection, Rvalue, Statement, Terminator, Ty, VerifiableFunction,
};

/// Answers are (one stable value, copy-source stability, reachable storage,
/// memoized copy-source stability). Undefined locals remain a separate case:
/// the one-value query refuses them; at-most-one queries permit zero definitions.
pub fn cases() -> Vec<(&'static str, VerifiableFunction, usize, (bool, bool, bool, bool))> {
    let mut cases: Vec<_> = shared_cell::cases()
        .into_iter()
        .map(|(name, f, stable)| (name, f, 3, (stable, stable, stable, stable)))
        .collect();
    let plain = || {
        let mut f = shared_cell::fixture(Ty::usize(), vec![], Ty::usize());
        f.body.blocks[0].stmts.pop();
        f.body.blocks[0].terminator = Terminator::Goto(trust_types::BlockId(1));
        f
    };
    let store = |f: &VerifiableFunction, local, projections| Statement::Assign {
        place: Place { local, projections },
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(9, 64))),
        span: f.span.clone(),
    };
    let mut f = plain();
    let write = store(&f, 1, vec![]);
    f.body.blocks[0].stmts.push(write);
    cases.push(("reassigned entry value", f, 1, (false, false, false, false)));
    let mut f = plain();
    f.body.locals.push(trust_types::LocalDecl { index: 5, ty: Ty::usize(), name: None });
    cases.push(("no explicit or entry value", f, 5, (false, true, true, true)));
    let pair = Ty::Tuple(vec![Ty::usize(), Ty::usize()]);
    let mut f = shared_cell::fixture(pair.clone(), vec![], pair);
    f.body.blocks[0].stmts.pop();
    f.body.blocks[0].terminator = Terminator::Goto(trust_types::BlockId(1));
    let write = store(&f, 3, vec![Projection::Field(0)]);
    f.body.blocks[0].stmts.push(write);
    cases.push(("part of owned value overwritten", f, 3, (false, false, false, false)));
    let pointer = Ty::Ref { mutable: true, inner: Box::new(Ty::usize()) };
    let mut f = shared_cell::fixture(pointer.clone(), vec![], pointer);
    f.body.blocks[0].stmts.pop();
    f.body.blocks[0].terminator = Terminator::Goto(trust_types::BlockId(1));
    let write = store(&f, 3, vec![Projection::Deref]);
    f.body.blocks[0].stmts.push(write);
    cases.push(("pointee store preserves pointer value", f, 3, (true, true, false, true)));
    let pointer = Ty::Ref { mutable: true, inner: Box::new(Ty::usize()) };
    let mut f = shared_cell::fixture(pointer.clone(), vec![], pointer);
    f.body.blocks[0].stmts.pop();
    let Terminator::Call { args, dest, .. } = &mut f.body.blocks[0].terminator else { panic!() };
    args.clear();
    *dest = Place { local: 3, projections: vec![Projection::Deref] };
    cases.push(("projected call keeps native one-value refusal", f, 3, (false, true, false, true)));
    let mut f = plain();
    f.body.blocks[0].terminator = Terminator::Drop {
        place: Place { local: 3, projections: vec![] },
        target: trust_types::BlockId(1),
        span: f.span.clone(),
        unwind: trust_types::UnwindEdge::Continue,
    };
    cases.push(("consumed value cannot license a later fact", f, 3, (false, false, false, false)));
    let mut f = plain();
    f.body.blocks[0].terminator = Terminator::Opaque {
        kind: "asm".into(),
        targets: vec![trust_types::BlockId(1)],
        span: f.span.clone(),
    };
    cases.push(("unlocatable assembly write", f, 3, (false, false, false, false)));
    let mut f = plain();
    f.body.blocks[0]
        .stmts
        .push(Statement::Deinit { place: Place { local: 3, projections: vec![] } });
    cases.push(("deinitialized value", f, 3, (false, false, false, false)));
    let mut f = shared_cell::fixture(Ty::usize(), vec![], Ty::usize());
    let Statement::Assign { rvalue, .. } = &mut f.body.blocks[0].stmts[0] else { panic!() };
    *rvalue = Rvalue::BinaryOp(
        trust_types::BinOp::BitAnd,
        Operand::Copy(Place { local: 1, projections: vec![] }),
        Operand::Constant(ConstValue::Uint(3, 64)),
    );
    let Statement::Assign { rvalue: Rvalue::Ref { mutable, .. }, .. } =
        &mut f.body.blocks[0].stmts[1]
    else {
        panic!()
    };
    *mutable = true;
    f.body.locals[4].ty = Ty::Ref { mutable: true, inner: Box::new(Ty::usize()) };
    cases.push(("masked scalar escapes before later read", f, 3, (false, false, false, false)));
    cases
}

#[test]
fn actual_stability_queries_obey_value_and_storage_invariants() {
    for (name, f, local, expected) in cases() {
        assert_eq!(trust_ir_bridge::local_stability_for_test(&f, local), expected, "{name}");
    }
}

#[test]
fn defined_mutations_separate_old_values_from_current_storage() {
    let before = std::cell::Cell::new(0usize);
    let owned = before;
    let old = owned.get();
    let alias = &owned;
    alias.set(9);
    assert_eq!(old, 0);
    assert_eq!(owned.get(), 9);
    let mut tuple = (1usize, 2usize);
    let historical = tuple;
    tuple.0 = 9;
    assert_eq!(historical, (1, 2));
    assert_eq!(tuple, (9, 2));
    let mut pointee = 1usize;
    let pointer = &mut pointee;
    let address = pointer as *mut usize;
    *pointer = 9;
    assert_eq!(pointer as *mut usize, address);
    assert_eq!(*pointer, 9);
}

#[test]
fn arithmetic_facts_use_value_stability_instead_of_count_only() {
    for (name, f, local, expected) in cases() {
        // This older native gate has no extra projected-call policy. That
        // caller may preserve a pointer value despite writing its pointee.
        let expected =
            if name == "projected call keeps native one-value refusal" { true } else { expected.0 };
        assert_eq!(trust_ir_bridge::native_math_stability_for_test(&f, local), expected, "{name}");
    }
    let mut masked = 15usize & 3;
    let historical = masked;
    let alias = &mut masked;
    *alias = 9;
    assert!(historical <= 3);
    assert!(masked > 3);
}
