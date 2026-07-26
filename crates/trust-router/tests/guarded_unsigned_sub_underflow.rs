// Regression: the interval backend must PROVE a guarded unsigned subtraction
// (`if len >= 8 { len - 8 }`) whose VC is a BARE `Lt(Sub(len,8), 0)` underflow
// goal — the aterm-hash `bytes[len - 8..]` shape. vcgen drops the symmetric
// `Gt(r, max)` disjunct for unsigned sub (the `usize::MAX` literal is
// unrepresentable in the i64 integer domain), so the obligation is a lone
// lower-bound goal rather than the `Or([Lt,Gt])` form `parse_overflow_goal`
// handles. Before the `parse_underflow_goal` fix, `prove_no_overflow` found no
// goal and DECLINED, so the guarded subtraction had no sound discharger and the
// router reported it unknown. The unguarded counterpart must still DECLINE.
use trust_router::VerificationBackend;
use trust_router::interval_backend::IntervalBackend;
use trust_types::*;

fn overflow_vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Sub,
            operand_tys: (Ty::usize(), Ty::usize()),
        },
        function: "hb".to_string().into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
    }
}

fn v(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

#[test]
fn guarded_unsigned_sub_proves_via_interval() {
    // Mirrors the real vcgen formula for `if len >= 8 { len - 8 }`:
    //   slice-len bounds ∧ defs ∧ guard(len>=8) ∧ input ranges ∧ Lt(Sub(len,8),0)
    let len = v("len");
    let formula = Formula::And(vec![
        Formula::Ge(Box::new(v("bytes__slice_len")), Box::new(Formula::Int(0))),
        Formula::Le(Box::new(v("bytes__slice_len")), Box::new(Formula::Int(9223372036854775807))),
        Formula::Eq(Box::new(len.clone()), Box::new(v("bytes__slice_len"))),
        // dominating guard len >= 8
        Formula::Ge(Box::new(len.clone()), Box::new(Formula::Int(8))),
        // input range for len: 0 <= len <= u64::MAX
        Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(len.clone())),
            Formula::Le(Box::new(len.clone()), Box::new(Formula::Int(18446744073709551615))),
        ]),
        // bare underflow goal: (len - 8) < 0
        Formula::Lt(
            Box::new(Formula::Sub(Box::new(len.clone()), Box::new(Formula::Int(8)))),
            Box::new(Formula::Int(0)),
        ),
    ]);
    let vc = overflow_vc(formula);
    assert!(IntervalBackend.can_handle(&vc), "guarded len-8 must prove no underflow");
}

#[test]
fn unguarded_unsigned_sub_does_not_prove() {
    // SOUNDNESS guard: with NO `len >= 8` guard, the subtraction CAN underflow,
    // so interval must DECLINE (false would be unsound otherwise).
    let len = v("len");
    let formula = Formula::And(vec![
        Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(len.clone())),
            Formula::Le(Box::new(len.clone()), Box::new(Formula::Int(18446744073709551615))),
        ]),
        Formula::Lt(
            Box::new(Formula::Sub(Box::new(len.clone()), Box::new(Formula::Int(8)))),
            Box::new(Formula::Int(0)),
        ),
    ]);
    let vc = overflow_vc(formula);
    assert!(!IntervalBackend.can_handle(&vc), "unguarded len-8 CAN underflow; must not prove");
}
