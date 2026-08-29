use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
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
            datatype_defs: Default::default(),
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
            let mentions =
                |g: &Formula| matches!(g, Formula::Var(n, _) if n.starts_with("__trust_ovf_bv_"));
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

/// Trust: UMUL RECORD, RE-LANDED (2026-08-20) — the unsigned `var*var` mul VC
/// carries an AUTHENTICATED Or-range record, and `reconstruct(record)` equals
/// the emitted formula BIT-FOR-BIT (the invariant `authenticated_record`
/// checks downstream).
///
/// THE HISTORY MATTERS, because this exact conjunct was retracted once. Adding
/// the Int core makes the query a mixed QF_BV + NIA problem that ay answers
/// with `internal-error`, which cost the class its refutation: an unguarded
/// overflowing `a*b` went from `Failed` WITH A COUNTEREXAMPLE to `Unknown`.
/// What makes it safe now is `trust-router`'s DISJOINT-COMPONENT REFUTATION
/// lane, which refutes such a query component-wise. The pair is held together
/// by `trust_router::in_process_ay_backend::tests::
/// umul_bare_bv_unguarded_refutes_with_counterexample` — if that pin ever goes
/// red, this conjunct must come back out.
#[test]
fn unsigned_var_var_mul_vc_carries_authenticated_record() {
    use trust_types::ObligationWrapper;
    for (l, r, label) in [(None, None, "unguarded"), (Some(100u128), Some(50u128), "rem-clamped")] {
        let func = mod_mul_func(l, r);
        let vcs = generate_vcs(&func);
        let vc = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
            .expect("the checked mul emits an overflow VC");
        let rec = vc
            .obligation
            .as_ref()
            .unwrap_or_else(|| panic!("{label}: the umul VC must carry a record"));
        // The body is the Or-range core over a Mul term, at the operand width.
        let Formula::Or(disjuncts) = &rec.body else { panic!("{label}: body must be the Or core") };
        let [Formula::Lt(under_t, min_f), Formula::Gt(over_t, max_f)] = disjuncts.as_slice() else {
            panic!("{label}: body must be [Lt, Gt]")
        };
        assert!(matches!(&**under_t, Formula::Mul(..)), "{label}: operator is Mul");
        assert_eq!(under_t, over_t, "{label}: both disjuncts over the same a*b");
        assert_eq!(&**min_f, &Formula::Int(0));
        assert_eq!(&**max_f, &Formula::Int(4_294_967_295));
        assert_eq!(rec.width, Some(32));
        // Reconstruction, innermost-first, mirroring the checker's semantics.
        let mut cur = rec.body.clone();
        for w in &rec.wrappers {
            cur = match w {
                ObligationWrapper::ConjoinFactsLast { facts } => {
                    let mut v = facts.clone();
                    v.push(cur);
                    Formula::And(v)
                }
                ObligationWrapper::PathGuardOr { paths } => {
                    use trust_types::PathGuardTerm as P;
                    let terms: Vec<Formula> = paths
                        .iter()
                        .map(|p| match p {
                            P::Raw => cur.clone(),
                            P::Guarded { guards } => {
                                let mut c = guards.clone();
                                match cur.clone() {
                                    Formula::And(inner) => c.extend(inner),
                                    other => c.push(other),
                                }
                                Formula::And(c)
                            }
                        })
                        .collect();
                    match terms.len() {
                        0 => cur,
                        1 => terms.into_iter().next().expect("len checked == 1"),
                        _ => Formula::Or(terms),
                    }
                }
            };
        }
        assert_eq!(cur, vc.formula, "{label}: reconstruct(record) must equal the formula");
    }
}
