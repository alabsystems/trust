use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place,
    Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody,
    VerifiableFunction,
};

use super::generate_v2_safety_vcs;

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// `fn read(arr: [f64; 4], i: usize) -> f64` whose bb0 performs the MIR
/// bounds-assert shape rustc emits for `arr[<index>]`:
///   _4 = <index def>; _5 = Len(_1); _6 = Lt(copy _4, copy _5);
///   Assert(move _6, expected: true, BoundsCheck) -> bb1
///   bb1: _0 = copy _1[_4]; return
/// `index_def`: None = the symbolic param `i` is the index; Some(k) = a
/// constant-assigned temp.
fn array_read_fn(index_def: Option<u128>) -> VerifiableFunction {
    let index_local = if index_def.is_some() { 4 } else { 2 };
    let mut bb0_stmts = Vec::new();
    if let Some(k) = index_def {
        bb0_stmts.push(assign(
            Place::local(4),
            Rvalue::Use(Operand::Constant(ConstValue::Uint(k, 64))),
        ));
    }
    bb0_stmts.push(assign(Place::local(5), Rvalue::Len(Place::local(1))));
    bb0_stmts.push(assign(
        Place::local(6),
        Rvalue::BinaryOp(
            BinOp::Lt,
            Operand::Copy(Place::local(index_local)),
            Operand::Copy(Place::local(5)),
        ),
    ));
    let read_place = Place { local: 1, projections: vec![Projection::Index(index_local)] };
    VerifiableFunction {
        name: "read".to_string(),
        def_path: "test::read".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::f64_ty(), name: Some("_0".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::f64_ty()), len: 4 },
                    name: Some("arr".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("i".into()),
                },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
                LocalDecl { index: 4, ty: Ty::Int { width: 64, signed: false }, name: None },
                LocalDecl { index: 5, ty: Ty::Int { width: 64, signed: false }, name: None },
                LocalDecl { index: 6, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: bb0_stmts,
                    terminator: Terminator::Assert {
                        unwind: trust_types::UnwindEdge::Unreachable,
                        cond: Operand::Move(Place::local(6)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Use(Operand::Copy(read_place)),
                    )],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::f64_ty(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn bounds_kind_count(func: &VerifiableFunction) -> usize {
    generate_v2_safety_vcs(func)
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .count()
}

#[test]
fn literal_in_range_index_suppresses_the_bounds_vc() {
    // `arr[0]` on `[f64; 4]`: index 0 and Len-resolved length 4 are both
    // compile-time constants with 0 < 4 — the assert can never fire, so no
    // obligation is minted (and no constant-false skeleton reaches the
    // vacuity gate to strip a proved row's authority).
    let func = array_read_fn(Some(0));
    assert_eq!(bounds_kind_count(&func), 0, "in-range literal index must mint no bounds VC");
}

#[test]
fn literal_out_of_range_index_keeps_the_bounds_vc() {
    // SOUNDNESS twin: `arr[7]` on `[f64; 4]` genuinely panics — the
    // refutation must surface, never be suppressed.
    let func = array_read_fn(Some(7));
    assert_eq!(
        bounds_kind_count(&func),
        1,
        "an out-of-range literal index must KEEP its bounds VC"
    );
}

#[test]
fn symbolic_index_keeps_the_bounds_vc() {
    // SOUNDNESS twin: `arr[i]` with an unconstrained parameter index stays
    // refutable.
    let func = array_read_fn(None);
    assert_eq!(bounds_kind_count(&func), 1, "a symbolic index must KEEP its bounds VC");
}

#[test]
fn call_written_index_local_keeps_the_bounds_vc() {
    // SOUNDNESS twin: the index temp is ALSO a call destination — its
    // value is not the scanned constant on every path (`index_local_const`'s
    // stmt-only blind spot, closed here), so the suppression must decline.
    let mut func = array_read_fn(Some(0));
    // Prepend a block whose call writes the index temp (_4).
    for block in &mut func.body.blocks {
        block.id = BlockId(block.id.0 + 1);
    }
    if let Terminator::Assert { target, .. } = &mut func.body.blocks[0].terminator {
        *target = BlockId(target.0 + 1);
    }
    func.body.blocks.insert(
        0,
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: trust_types::UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                is_foreign: false,
                func: "test::pick".to_string(),
                args: vec![],
                dest: Place::local(4),
                target: Some(BlockId(1)),
                span: SourceSpan::default(),
                atomic: None,
            },
        },
    );
    assert_eq!(
        bounds_kind_count(&func),
        1,
        "a call-written index local must KEEP its bounds VC"
    );
}
