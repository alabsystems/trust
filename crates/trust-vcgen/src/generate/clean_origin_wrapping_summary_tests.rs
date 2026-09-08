// trust_vcgen/generate/clean_origin_wrapping_summary_tests.rs
//
// Trust (I5 cross-authority call modeling — `WrappingBinOp`): the ENCODING PIN.
//
// `modular::clean_origin_wrapping_binop_postconditions` mints the caller-side
// definitional summary for a Clean-origin wrapping-binop callee, and its doc
// states the soundness bar: the summary must restate THE EXTRACTOR'S OWN
// wrapping encoding — the single-`Ite` modular reduction
// `assert_refutation::wrapping_call_assert_model` produces when it models a
// call to the same `u{w}::wrapping_{op}` primitive inside an ordinary
// extracted Rust body. A summary that encoded wrapping differently would let
// one call be modeled two ways in one solver query.
//
// These tests hold the two producers together MECHANICALLY: build one caller,
// ask the extractor for its `(def, ranges)` model of the call, rebind the
// constructor's summary at the same call site (`rebind_callee_postconditions`,
// the production injection path — so the machine-arithmetic filter is part of
// what is pinned), and require the resulting formulas to be STRUCTURALLY
// IDENTICAL. If either side's encoding drifts, this fails before a fixture can.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::admissible_body::{ArithBinOp, ArithOperand};
use trust_types::{
    BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Sort, SourceSpan,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::assert_refutation::wrapping_call_assert_model;
use crate::generate::{callee_postcondition_is_injectable, rebind_callee_postconditions};
use crate::modular::{FunctionSummary, clean_origin_wrapping_binop_postconditions};

const ADD_MARKER: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add";
const SUB_MARKER: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_sub";

/// `fn f(x: u64, y: u64) { n = callee(args...) }` — one call, one successor.
fn wrapping_caller(callee: &str, args: Vec<Operand>) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::u64(), name: Some("n".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: callee.into(),
                        args,
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        is_foreign: false,
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

/// The constructor's summary for the callee, over synthetic formals — the
/// exact composition the compiler's Clean-origin lane performs.
fn wrapping_summary(
    callee: &str,
    op: ArithBinOp,
    left: ArithOperand,
    right: ArithOperand,
) -> FunctionSummary {
    let param_names =
        vec!["__trust_clean_origin_arg0".to_string(), "__trust_clean_origin_arg1".to_string()];
    let posts = clean_origin_wrapping_binop_postconditions(op, left, right, 64, &param_names)
        .expect("add/sub at width 64 over valid operands must be expressible");
    let mut summary = FunctionSummary::new(callee).with_param_names(param_names);
    for post in posts {
        summary = summary.with_definitional_postcondition(post);
    }
    summary
}

/// The pin itself: extractor model and rebound summary must be identical.
fn assert_summary_matches_extractor(
    callee: &str,
    op: ArithBinOp,
    left: ArithOperand,
    right: ArithOperand,
    args: Vec<Operand>,
) {
    let func = wrapping_caller(callee, args);
    let Terminator::Call { args, dest, .. } = &func.body.blocks[0].terminator else {
        unreachable!("built with a Call terminator");
    };
    let (extractor_def, extractor_ranges) =
        wrapping_call_assert_model(&func, callee, args, dest, true, false, false, false)
            .expect("the extractor must model an authenticated u64 wrapping call");

    let summary = wrapping_summary(callee, op, left, right);
    assert!(
        callee_postcondition_is_injectable(&func, dest, &summary, args),
        "the wrapping summary must pass the injection gate (the modular-Ite \
         exemption to the machine-arithmetic filter)"
    );
    let rebound = rebind_callee_postconditions(&func, args, dest, &summary);
    assert_eq!(
        rebound.len(),
        1 + extractor_ranges.len(),
        "every clause must survive the filter: def + one range per operand"
    );
    assert_eq!(
        rebound[0], extractor_def,
        "the rebound summary definition must be BYTE-IDENTICAL to the \
         extractor's own wrapping encoding — a divergence is a soundness bug"
    );
    assert_eq!(
        &rebound[1..],
        &extractor_ranges[..],
        "the operand range facts must match the extractor's own"
    );
}

#[test]
fn add_summary_is_the_extractor_own_encoding_param_param() {
    assert_summary_matches_extractor(
        ADD_MARKER,
        ArithBinOp::Add,
        ArithOperand::Param(0),
        ArithOperand::Param(1),
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
    );
}

#[test]
fn sub_summary_is_the_extractor_own_encoding_param_param() {
    assert_summary_matches_extractor(
        SUB_MARKER,
        ArithBinOp::Sub,
        ArithOperand::Param(0),
        ArithOperand::Param(1),
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
    );
}

#[test]
fn add_summary_is_the_extractor_own_encoding_param_const() {
    // The `winc`-shaped instance (`a + 1` at UInt64): a numeral operand must
    // take the same `Formula::Int` spelling on both sides, range fact included.
    assert_summary_matches_extractor(
        ADD_MARKER,
        ArithBinOp::Add,
        ArithOperand::Param(0),
        ArithOperand::Const(1),
        vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Uint(1, 64))],
    );
}

// ─── The filter exemption is EXACT: nothing else launders through ────────────

/// A definitional summary whose clause is the UNSOUND unbounded encoding
/// (`_0 == a + b`, no modular reduction) must still be rejected by the
/// machine-arithmetic filter — definitional authority does not exempt
/// arithmetic in general, only the exact modular shape.
#[test]
fn unbounded_add_clause_is_still_not_injectable() {
    let func = wrapping_caller(
        ADD_MARKER,
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
    );
    let Terminator::Call { args, dest, .. } = &func.body.blocks[0].terminator else {
        unreachable!("built with a Call terminator");
    };
    let a = || Box::new(Formula::var("a", Sort::Int));
    let b = || Box::new(Formula::var("b", Sort::Int));
    let unbounded =
        Formula::Eq(Box::new(Formula::var("_0", Sort::Int)), Box::new(Formula::Add(a(), b())));
    let summary = FunctionSummary::new(ADD_MARKER)
        .with_param_names(vec!["a".to_string(), "b".to_string()])
        .with_definitional_postcondition(unbounded);
    assert!(
        !callee_postcondition_is_injectable(&func, dest, &summary, args),
        "the unbounded mathematical-Int reading of a wrapping body is the \
         canonical false-PROVE and must stay filtered"
    );
    assert!(
        rebind_callee_postconditions(&func, args, dest, &summary).is_empty(),
        "the rebinding filter must agree with the injection gate"
    );
}

#[test]
fn recognizer_accepts_exactly_the_constructor_output() {
    let names = vec!["a".to_string(), "b".to_string()];
    for op in [ArithBinOp::Add, ArithBinOp::Sub] {
        let posts = clean_origin_wrapping_binop_postconditions(
            op,
            ArithOperand::Param(0),
            ArithOperand::Param(1),
            64,
            &names,
        )
        .expect("add/sub at width 64 must be expressible");
        assert!(
            crate::contracts::formula_is_exact_modular_wrapping_definition(&posts[0]),
            "the recognizer must accept the constructor's {op:?} definition"
        );
    }
}

#[test]
fn recognizer_rejects_near_miss_shapes() {
    use crate::contracts::formula_is_exact_modular_wrapping_definition as recognize;
    let a = || Box::new(Formula::var("a", Sort::Int));
    let b = || Box::new(Formula::var("b", Sort::Int));
    let s = || Box::new(Formula::Add(a(), b()));
    let dest = || Box::new(Formula::var("_0", Sort::Int));

    // Unbounded arithmetic — no Ite at all.
    assert!(!recognize(&Formula::Eq(dest(), s())));

    // Non-power-of-two modulus: `ite(s >= 100, s - 100, s)` is `mod 100`,
    // which is not any machine width — laundering, not wrapping.
    let m = || Box::new(Formula::Int(100));
    assert!(!recognize(&Formula::Eq(
        dest(),
        Box::new(Formula::Ite(
            Box::new(Formula::Ge(s(), m())),
            Box::new(Formula::Sub(s(), m())),
            s(),
        )),
    )));

    // Mismatched combination term between condition and branches: the
    // condition tests `a + b` but the wrap branch adjusts `a + a`.
    let m64 = || Box::new(Formula::Int(1i128 << 64));
    assert!(!recognize(&Formula::Eq(
        dest(),
        Box::new(Formula::Ite(
            Box::new(Formula::Ge(s(), m64())),
            Box::new(Formula::Sub(Box::new(Formula::Add(a(), a())), m64())),
            s(),
        )),
    )));

    // Mismatched modulus between condition and wrap branch.
    assert!(!recognize(&Formula::Eq(
        dest(),
        Box::new(Formula::Ite(
            Box::new(Formula::Ge(s(), m64())),
            Box::new(Formula::Sub(s(), Box::new(Formula::Int(1i128 << 32)))),
            s(),
        )),
    )));

    // A nested-arithmetic operand: only vars and in-range literals may appear.
    let nested = || Box::new(Formula::Add(Box::new(Formula::Mul(a(), b())), b()));
    assert!(!recognize(&Formula::Eq(
        dest(),
        Box::new(Formula::Ite(
            Box::new(Formula::Ge(nested(), m64())),
            Box::new(Formula::Sub(nested(), m64())),
            nested(),
        )),
    )));

    // An out-of-range literal operand (`2^64` at modulus `2^64`).
    let big = || Box::new(Formula::Add(a(), Box::new(Formula::Int(1i128 << 64))));
    assert!(!recognize(&Formula::Eq(
        dest(),
        Box::new(Formula::Ite(
            Box::new(Formula::Ge(big(), m64())),
            Box::new(Formula::Sub(big(), m64())),
            big(),
        )),
    )));
}
