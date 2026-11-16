// Regression: an ORDINARY path guard resolved from a bool `switchInt` discriminant to
// its reaching comparison must not survive a write to a compared operand between the
// comparison and the switch (docs/KNOWN_HAZARDS.md, 2026-10-05, "ordinary path guards
// resolve a bool discriminant to its comparison ...").
//
//   fn f(s: &mut S, x: usize, a: [u8; 4]) -> u8 {
//       let c = s.i < 4;
//       s.i = x;
//       if c { a[s.i] } else { 0 }
//   }
//
// in the MIR shape
//
//   bb0: _4 = Lt(copy (*_1).0, const 4); (*_1).0 = copy _2; switchInt(move _4) [0 -> bb3, otherwise -> bb1]
//   bb1: _5 = copy (*_1).0; _6 = Lt(copy _5, const 4); assert(move _6, BoundsCheck) -> bb2
//   bb2: _0 = copy _3[_5]; return
//   bb3: _0 = const 0; return
//
// The index in bb1 reads the POST-write `s.i == x`, which can be `>= 4`, so the bounds
// row is a real violation. The guard `(*_1).0 < 4`, renamed at bb0's terminal, names the
// post-write value and made the row UNSAT: a false proof. Variants write the compared
// field through a `&mut` reborrow, a call destination, and across the `Goto` hop the
// resolver follows; the control (no write) must stay proved.
use trust_types::*;

#[path = "support/test_router.rs"]
mod test_router;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Shape {
    /// No write between the comparison and the switch: the guard is exact.
    NoWrite,
    /// `(*_1).1 = copy _2` (a SIBLING field) between them: the guard is still exact.
    SiblingWrite,
    /// The comparison, `goto` the switch block, no write: the guard is exact.
    GotoNoWrite,
    /// `(*_1).0 = copy _2` in the comparison's block, before the switch.
    FieldWrite,
    /// `_7 = &mut (*_1).0; (*_7) = copy _2` in the comparison's block.
    Reborrow,
    /// `(*_1).0 = copy _2` after the comparison, then `goto` the switch block.
    WriteThenGoto,
    /// The comparison, `goto` the switch block, which writes `(*_1).0` before switching.
    GotoThenWrite,
    /// The comparison's block ends in `(*_1).0 = g(_2)`, returning to the switch block.
    CallDest,
    /// `_8 = &raw mut (*_1).0` BEFORE the comparison, then `(*_8) = copy _2` between
    /// it and the switch: the store names `_8*`, never `s*.0`.
    RawAliasStore,
}

fn s_ty() -> Ty {
    Ty::Adt {
        adt_kind: Some(AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: "c::S".into(),
        fields: vec![("i".to_string(), Ty::usize()), ("j".to_string(), Ty::usize())].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn s_i() -> Place {
    Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] }
}

fn four() -> Operand {
    Operand::Constant(ConstValue::Uint(4, 64))
}

fn blk(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn switch_on_c() -> Terminator {
    Terminator::SwitchInt {
        discr: Operand::Move(Place::local(4)),
        targets: vec![(0, BlockId(3))],
        otherwise: BlockId(1),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    }
}

fn build(shape: Shape) -> VerifiableFunction {
    let compare =
        assign(Place::local(4), Rvalue::BinaryOp(BinOp::Lt, Operand::Copy(s_i()), four()));
    let field_write = assign(s_i(), Rvalue::Use(Operand::Copy(Place::local(2))));
    let mut blocks = Vec::new();
    match shape {
        Shape::NoWrite => blocks.push(blk(0, vec![compare], switch_on_c())),
        Shape::FieldWrite => blocks.push(blk(0, vec![compare, field_write], switch_on_c())),
        Shape::SiblingWrite => blocks.push(blk(
            0,
            vec![
                compare,
                assign(
                    Place { local: 1, projections: vec![Projection::Deref, Projection::Field(1)] },
                    Rvalue::Use(Operand::Copy(Place::local(2))),
                ),
            ],
            switch_on_c(),
        )),
        Shape::Reborrow => blocks.push(blk(
            0,
            vec![
                compare,
                assign(Place::local(7), Rvalue::Ref { mutable: true, place: s_i() }),
                assign(
                    Place { local: 7, projections: vec![Projection::Deref] },
                    Rvalue::Use(Operand::Copy(Place::local(2))),
                ),
            ],
            switch_on_c(),
        )),
        Shape::RawAliasStore => blocks.push(blk(
            0,
            vec![
                assign(Place::local(8), Rvalue::AddressOf(true, s_i())),
                compare,
                assign(
                    Place { local: 8, projections: vec![Projection::Deref] },
                    Rvalue::Use(Operand::Copy(Place::local(2))),
                ),
            ],
            switch_on_c(),
        )),
        Shape::WriteThenGoto => {
            blocks.push(blk(0, vec![compare, field_write], Terminator::Goto(BlockId(4))));
        }
        Shape::GotoThenWrite | Shape::GotoNoWrite => {
            blocks.push(blk(0, vec![compare], Terminator::Goto(BlockId(4))));
        }
        Shape::CallDest => blocks.push(blk(
            0,
            vec![compare],
            Terminator::Call {
                func: "c::g".into(),
                args: vec![Operand::Copy(Place::local(2))],
                dest: s_i(),
                target: Some(BlockId(4)),
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                unwind: UnwindEdge::Continue,
                callee_identity: None,
                callee_key: None,
            },
        )),
    }
    blocks.push(blk(
        1,
        vec![
            assign(Place::local(5), Rvalue::Use(Operand::Copy(s_i()))),
            assign(
                Place::local(6),
                Rvalue::BinaryOp(BinOp::Lt, Operand::Copy(Place::local(5)), four()),
            ),
        ],
        Terminator::Assert {
            cond: Operand::Move(Place::local(6)),
            expected: true,
            msg: AssertMessage::BoundsCheck,
            target: BlockId(2),
            span: SourceSpan::default(),
            unwind: UnwindEdge::Unreachable,
        },
    ));
    blocks.push(blk(
        2,
        vec![assign(
            Place::local(0),
            Rvalue::Use(Operand::Copy(Place { local: 3, projections: vec![Projection::Index(5)] })),
        )],
        Terminator::Return,
    ));
    blocks.push(blk(
        3,
        vec![assign(Place::local(0), Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 8))))],
        Terminator::Return,
    ));
    match shape {
        Shape::WriteThenGoto | Shape::CallDest | Shape::GotoNoWrite => {
            blocks.push(blk(4, vec![], switch_on_c()));
        }
        Shape::GotoThenWrite => blocks.push(blk(
            4,
            vec![assign(s_i(), Rvalue::Use(Operand::Copy(Place::local(2))))],
            switch_on_c(),
        )),
        _ => {}
    }
    let u8_ty = Ty::Int { width: 8, signed: false };
    let locals = vec![
        (u8_ty.clone(), None),
        (Ty::Ref { mutable: true, inner: Box::new(s_ty()) }, Some("s")),
        (Ty::usize(), Some("x")),
        (Ty::Array { elem: Box::new(u8_ty), len: 4 }, Some("a")),
        (Ty::Bool, None),
        (Ty::usize(), None),
        (Ty::Bool, None),
        (Ty::Ref { mutable: true, inner: Box::new(Ty::usize()) }, None),
        (Ty::RawPtr { mutable: true, pointee: Box::new(Ty::usize()) }, None),
    ];
    VerifiableFunction {
        name: "f".into(),
        def_path: "c::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: locals[0].0.clone(),
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, (ty, name))| LocalDecl { index, ty, name: name.map(Into::into) })
                .collect(),
            blocks,
            arg_count: 3,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    let router = test_router::deterministic_test_router();
    router.verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

fn bounds_rows(shape: Shape) -> Vec<(VerificationCondition, VerificationResult)> {
    let vcs = trust_vcgen::generate_vcs(&build(shape));
    let rows: Vec<_> = vcs
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds))
        .map(|vc| {
            let v = verdict(&vc);
            (vc, v)
        })
        .collect();
    assert!(!rows.is_empty(), "{shape:?}: the guarded `a[s.i]` bounds row must be generated");
    rows
}

/// The bounds row is REFUTED: the violation `x >= 4` is reachable, and the guard no
/// longer forbids it.
fn assert_refuted(shape: Shape) {
    for (vc, v) in bounds_rows(shape) {
        assert!(
            matches!(v, VerificationResult::Failed { .. }),
            "{shape:?}: the index reads the post-write `s.i == x`, which may be >= 4; the \
             bounds row must be refuted (a PROVED row is a false proof).\nverdict: {v:?}\n\
             formula: {:?}",
            vc.formula
        );
    }
}

fn assert_proved(shape: Shape) {
    for (vc, v) in bounds_rows(shape) {
        assert!(
            matches!(v, VerificationResult::Proved { .. }),
            "{shape:?}: `s.i < 4` still guards `a[s.i]`; got {v:?}\nformula: {:?}",
            vc.formula
        );
    }
}

#[test]
fn no_write_between_compare_and_switch_still_proves_the_guarded_index() {
    assert_proved(Shape::NoWrite);
}

#[test]
fn a_sibling_field_write_between_compare_and_switch_still_proves_the_guarded_index() {
    assert_proved(Shape::SiblingWrite);
}

#[test]
fn a_write_free_goto_hop_still_proves_the_guarded_index() {
    assert_proved(Shape::GotoNoWrite);
}

#[test]
fn a_projected_compared_operand_written_before_the_switch_is_not_a_guard() {
    assert_refuted(Shape::FieldWrite);
}

#[test]
fn a_compared_field_written_through_a_reborrow_is_not_a_guard() {
    assert_refuted(Shape::Reborrow);
}

#[test]
fn a_compared_field_written_before_the_goto_hop_is_not_a_guard() {
    assert_refuted(Shape::WriteThenGoto);
}

#[test]
fn a_compared_field_written_in_the_switch_block_after_the_goto_hop_is_not_a_guard() {
    assert_refuted(Shape::GotoThenWrite);
}

#[test]
fn a_compared_field_written_by_a_call_destination_is_not_a_guard() {
    assert_refuted(Shape::CallDest);
}

#[test]
fn a_compared_field_stored_through_an_earlier_raw_alias_is_not_a_guard() {
    assert_refuted(Shape::RawAliasStore);
}
