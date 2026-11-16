// trust_vcgen/generate/int_abs_fact_tests.rs
//
// Trust: 2026-11-09 (WRAPPING-SUB-AND-INTERVAL-NEG-1, sibling) — `build_int_abs_facts`
// states `dest == ite(arg < 0, -arg, arg)` over MATHEMATICAL integers. For an
// argument read as field 0 of a `CheckedBinaryOp(op, l, r)` temp it spells `arg` as
// `l op r`, which is the temp's value only past the assert that traps the op's
// overflow flag. The lowered `*_with_overflow` intrinsics produce the same
// `CheckedBinaryOp` with NO such assert (`.0` is the wrapped value), so the fact must
// be stated only when that assert's success edge leads to the call.

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, Formula, LocalDecl, Operand, Place, Projection,
    Rvalue, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::build_int_abs_facts;

const ABS: &str = "core::num::<impl i64>::abs";

/// `fn f(a: i64, b: i64) -> i64 { (a - b).abs() }` with the subtraction's overflow
/// assert (`checked`), or the same `CheckedBinaryOp` reaching the call with no assert
/// (the `sub_with_overflow(a, b).0.abs()` shape).
///   bb0: _3 = CheckedSub(_1, _2); assert(!_3.1, Sub) -> bb1   |   goto bb1
///   bb1: _4 = abs(move _3.0) -> bb2
///   bb2: _0 = _4; return
fn abs_of_checked_sub(checked: bool) -> VerifiableFunction {
    let field = |k: usize| Place { local: 3, projections: vec![Projection::Field(k)] };
    let bb0_terminator = if checked {
        Terminator::Assert {
            unwind: UnwindEdge::Continue,
            cond: Operand::Move(field(1)),
            expected: false,
            msg: AssertMessage::Overflow(BinOp::Sub),
            target: BlockId(1),
            span: SourceSpan::default(),
        }
    } else {
        Terminator::Goto(BlockId(1))
    };
    VerifiableFunction {
        name: "f".to_string(),
        def_path: "int_abs::f".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::i64(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::i64(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: bb0_terminator,
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Continue,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(ABS),
                        is_foreign: false,
                        func: ABS.to_string(),
                        args: vec![Operand::Move(field(0))],
                        dest: Place::local(4),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::i64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Does `f` mention the mathematical difference `a - b`?
fn mentions_a_minus_b(f: &Formula) -> bool {
    let mut found = false;
    f.visit(&mut |node| {
        if let Formula::Sub(l, r) = node
            && let (Formula::Var(a, _), Formula::Var(b, _)) = (&**l, &**r)
            && a == "a"
            && b == "b"
        {
            found = true;
        }
    });
    found
}

/// The designed case: past the subtraction's own overflow assert, `abs(_3.0)` is
/// `|a - b|` (ordsweep2 structs/c02 needs this fact).
#[test]
fn an_asserted_checked_sub_argument_states_its_magnitude() {
    let facts = build_int_abs_facts(&abs_of_checked_sub(true));
    assert_eq!(facts.len(), 1, "one abs fact expected; got {facts:?}");
    assert!(
        mentions_a_minus_b(&facts[0]),
        "the fact must spell the argument `a - b`; got {facts:?}"
    );
}

/// With no overflow assert between the `CheckedBinaryOp` and the call, `_3.0` is the
/// WRAPPED difference (`a = i64::MAX, b = -1` gives `i64::MIN`), so no fact may spell
/// it as the mathematical `a - b`.
#[test]
fn an_unasserted_checked_sub_argument_states_no_magnitude() {
    let facts = build_int_abs_facts(&abs_of_checked_sub(false));
    assert!(
        facts.iter().all(|fact| !mentions_a_minus_b(fact)),
        "a wrapped `_3.0` must not be stated as `|a - b|`; got {facts:?}"
    );
}
