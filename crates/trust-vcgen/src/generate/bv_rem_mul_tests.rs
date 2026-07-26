use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue,
    SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
};

use super::generate_vcs;

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

/// `fn f(a: u32, b: u32) { _3 = a % 100; _5 = b % 50; _6 = _3 * _5 }` — the
/// checked-mul MIR shape (CheckedBinaryOp emits the overflow VC).
fn mod_mul_func(lhs_div: Option<u128>, rhs_div: Option<u128>) -> VerifiableFunction {
    let mut stmts = Vec::new();
    // _3 = a % C (or _3 = a, when no divisor: an UNBOUNDED operand)
    stmts.push(Statement::Assign {
        place: Place::local(3),
        rvalue: match lhs_div {
            Some(c) => Rvalue::BinaryOp(
                BinOp::Rem,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(c, 32)),
            ),
            None => Rvalue::Use(Operand::Copy(Place::local(1))),
        },
        span: SourceSpan::default(),
    });
    stmts.push(Statement::Assign {
        place: Place::local(5),
        rvalue: match rhs_div {
            Some(c) => Rvalue::BinaryOp(
                BinOp::Rem,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Uint(c, 32)),
            ),
            None => Rvalue::Use(Operand::Copy(Place::local(2))),
        },
        span: SourceSpan::default(),
    });
    stmts.push(Statement::Assign {
        place: Place::local(6),
        rvalue: Rvalue::CheckedBinaryOp(
            BinOp::Mul,
            Operand::Copy(Place::local(3)),
            Operand::Copy(Place::local(5)),
        ),
        span: SourceSpan::default(),
    });
    VerifiableFunction {
        name: "mod_mul".to_string(),
        def_path: "test::mod_mul".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: u32_ty(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: u32_ty(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: u32_ty(), name: None },
                LocalDecl { index: 4, ty: Ty::Bool, name: None },
                LocalDecl { index: 5, ty: u32_ty(), name: None },
                LocalDecl { index: 6, ty: Ty::Tuple(vec![u32_ty(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts,
                    // The checked mul's overflow flag `_6.1` is asserted false —
                    // the real MIR shape `v2_build_overflow_vc` keys on.
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(trust_types::Place {
                            local: 6,
                            projections: vec![trust_types::Projection::Field(1)],
                        }),
                        expected: false,
                        msg: trust_types::AssertMessage::Overflow(BinOp::Mul),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn mul_vc_formula(func: &VerifiableFunction) -> Formula {
    generate_vcs(func)
        .into_iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
        .expect("the var*var mul must emit an ArithmeticOverflow VC on the BV lane")
        .formula
}

/// Count the BvULt bounds referencing `__trust_ovf_bv_*` vars in the VC.
fn count_bv_bounds(f: &Formula) -> usize {
    match f {
        Formula::And(fs) | Formula::Or(fs) => fs.iter().map(count_bv_bounds).sum(),
        Formula::BvULt(l, r, _) | Formula::BvULe(l, r, _) => {
            let mentions = |g: &Formula| matches!(g, Formula::Var(n, _) if n.starts_with("__trust_ovf_bv_"));
            usize::from(mentions(l) && matches!(r.as_ref(), Formula::BitVec { .. }))
        }
        Formula::Not(inner) => count_bv_bounds(inner),
        _ => 0,
    }
}

#[test]
fn mod_bounded_mul_carries_rem_bounds() {
    // Both operands rem-bounded: the VC must conjoin BOTH `bv < C` facts so
    // the solver can discharge (99 * 49 fits u32) instead of false-refuting
    // on unconstrained fresh vars.
    let f = mul_vc_formula(&mod_mul_func(Some(100), Some(50)));
    assert!(
        count_bv_bounds(&f) >= 2,
        "the (a%100)*(b%50) mul VC must carry a rem bound for EACH operand's \
         fresh BV var; formula: {f:?}"
    );
}

#[test]
fn unbounded_mul_stays_refutable() {
    // SOUNDNESS floor: with no rem defs, no rem bound may appear — the
    // genuinely-overflowing a*b keeps its unconstrained (refutable) encoding.
    let f = mul_vc_formula(&mod_mul_func(None, None));
    assert_eq!(
        count_bv_bounds(&f),
        0,
        "an unbounded var*var mul must NOT pick up rem bounds; formula: {f:?}"
    );
}

#[test]
fn zero_divisor_rem_adds_no_bound() {
    // Degenerate `x % 0` (a genuine div-by-zero elsewhere): c <= 0 must add
    // no constraint rather than an absurd `bv < 0`.
    let f = mul_vc_formula(&mod_mul_func(Some(0), Some(50)));
    assert!(
        count_bv_bounds(&f) <= 1,
        "a zero divisor must contribute no rem bound; formula: {f:?}"
    );
}
