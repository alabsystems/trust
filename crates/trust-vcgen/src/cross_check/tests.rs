// trust_vcgen/cross_check/tests.rs: Tests for cross-checking
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::UnwindEdge;
use trust_types::fx::FxHashSet;
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    ProofLevel, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody,
    VerifiableFunction, VerificationCondition,
};

use super::comparison::{VcCategory, categorize_vc, compare_vc_sets};
use super::*;

fn make_func(name: &str, locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    let return_ty = locals.first().map_or(Ty::Unit, |local| local.ty.clone());
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody { locals, blocks, arg_count: 0, return_ty },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn make_vc(kind: VcKind, function: &str, formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: function.into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
    }
}

// -----------------------------------------------------------------------
// Variable scope checks
// -----------------------------------------------------------------------

#[test]
fn test_cross_check_known_variables_no_warnings() {
    let func = make_func(
        "add_fn",
        vec![
            LocalDecl { index: 0, ty: Ty::usize(), name: None },
            LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
        ],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    let vc = make_vc(
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::usize(), Ty::usize()) },
        "add_fn",
        Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("a".into(), Sort::Int))),
            Formula::Le(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Int(i64::MAX as i128)),
            ),
            Formula::Not(Box::new(Formula::Le(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("a".into(), Sort::Int)),
                    Box::new(Formula::Var("b".into(), Sort::Int)),
                )),
                Box::new(Formula::Int(i64::MAX as i128)),
            ))),
        ]),
    );

    let warnings = cross_check_vc(&vc, &func);
    let var_warnings: Vec<_> = warnings
        .iter()
        .filter(|w| matches!(w, CrossCheckWarning::UnknownVariable { .. }))
        .collect();
    assert!(
        var_warnings.is_empty(),
        "all variables are known, no warnings expected, got: {var_warnings:?}"
    );
}

#[test]
fn test_cross_check_unknown_variable_warns() {
    let func = make_func(
        "fn_a",
        vec![
            LocalDecl { index: 0, ty: Ty::usize(), name: None },
            LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
        ],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    let vc = make_vc(
        VcKind::DivisionByZero,
        "fn_a",
        Formula::Eq(
            Box::new(Formula::Var("nonexistent_var".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
    );

    let warnings = cross_check_vc(&vc, &func);
    assert!(
        warnings.iter().any(|w| matches!(
            w,
            CrossCheckWarning::UnknownVariable { var_name, .. }
                if var_name == "nonexistent_var"
        )),
        "should warn about unknown variable, got: {warnings:?}"
    );
}

#[test]
fn test_cross_check_fallback_name_accepted() {
    let func = make_func(
        "fn_b",
        vec![
            LocalDecl { index: 0, ty: Ty::usize(), name: None },
            LocalDecl { index: 1, ty: Ty::usize(), name: None },
        ],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    let vc = make_vc(
        VcKind::DivisionByZero,
        "fn_b",
        Formula::Eq(Box::new(Formula::Var("_1".into(), Sort::Int)), Box::new(Formula::Int(0))),
    );

    let warnings = cross_check_vc(&vc, &func);
    let var_warnings: Vec<_> = warnings
        .iter()
        .filter(|w| matches!(w, CrossCheckWarning::UnknownVariable { .. }))
        .collect();
    assert!(var_warnings.is_empty(), "fallback _1 name should be accepted");
}

#[test]
fn test_cross_check_projected_name_accepted() {
    let func = make_func(
        "fn_c",
        vec![
            LocalDecl { index: 0, ty: Ty::usize(), name: None },
            LocalDecl { index: 1, ty: Ty::usize(), name: None },
            LocalDecl { index: 2, ty: Ty::usize(), name: None },
            LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
        ],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    let vc = make_vc(
        VcKind::Assertion { message: "test".into() },
        "fn_c",
        Formula::Var("_3.1".into(), Sort::Bool),
    );

    let warnings = cross_check_vc(&vc, &func);
    let var_warnings: Vec<_> = warnings
        .iter()
        .filter(|w| matches!(w, CrossCheckWarning::UnknownVariable { .. }))
        .collect();
    assert!(var_warnings.is_empty(), "projected name _3.1 should be accepted");
}

#[test]
fn test_cross_check_slice_len_var_accepted() {
    let func = make_func(
        "fn_d",
        vec![
            LocalDecl { index: 0, ty: Ty::usize(), name: None },
            LocalDecl { index: 1, ty: Ty::usize(), name: Some("i".into()) },
        ],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    let vc = make_vc(
        VcKind::SliceBoundsCheck,
        "fn_d",
        Formula::Ge(
            Box::new(Formula::Var("i".into(), Sort::Int)),
            Box::new(Formula::Var("i__slice_len".into(), Sort::Int)),
        ),
    );

    let warnings = cross_check_vc(&vc, &func);
    let var_warnings: Vec<_> = warnings
        .iter()
        .filter(|w| matches!(w, CrossCheckWarning::UnknownVariable { .. }))
        .collect();
    assert!(var_warnings.is_empty(), "slice_len auxiliary var should be accepted");
}

// -----------------------------------------------------------------------
// Overflow bounds checks
// -----------------------------------------------------------------------

#[test]
fn test_cross_check_i32_overflow_correct_bounds() {
    let func = make_func(
        "add_i32",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
        ],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    // Build a VC with correct i32 bounds: [-2^31, 2^31-1]
    let min_val = -(1i128 << 31);
    let max_val = (1i128 << 31) - 1;
    let formula = Formula::And(vec![
        Formula::Le(Box::new(Formula::Int(min_val)), Box::new(Formula::Var("a".into(), Sort::Int))),
        Formula::Le(Box::new(Formula::Var("a".into(), Sort::Int)), Box::new(Formula::Int(max_val))),
        Formula::Not(Box::new(Formula::Le(
            Box::new(Formula::Add(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Var("b".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(max_val)),
        ))),
    ]);

    let vc = make_vc(
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
        "add_i32",
        formula,
    );

    let warnings = cross_check_vc(&vc, &func);
    let bound_warnings: Vec<_> = warnings
        .iter()
        .filter(|w| matches!(w, CrossCheckWarning::OverflowBoundsMismatch { .. }))
        .collect();
    assert!(
        bound_warnings.is_empty(),
        "correct i32 bounds should produce no warnings, got: {bound_warnings:?}"
    );
}

#[test]
fn test_cross_check_i32_overflow_wrong_bounds_warns() {
    let func = make_func(
        "add_i32",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
        ],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    // Build a VC with WRONG bounds (using i64 bounds for an i32 type).
    let wrong_min = -(1i128 << 63);
    let wrong_max = (1i128 << 63) - 1;
    let formula = Formula::And(vec![
        Formula::Le(
            Box::new(Formula::Int(wrong_min)),
            Box::new(Formula::Var("a".into(), Sort::Int)),
        ),
        Formula::Le(
            Box::new(Formula::Var("a".into(), Sort::Int)),
            Box::new(Formula::Int(wrong_max)),
        ),
    ]);

    let vc = make_vc(
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
        "add_i32",
        formula,
    );

    let warnings = cross_check_vc(&vc, &func);
    assert!(
        warnings.iter().any(|w| matches!(w, CrossCheckWarning::OverflowBoundsMismatch { .. })),
        "wrong bounds should produce a warning, got: {warnings:?}"
    );
}

#[test]
fn test_cross_check_u32_overflow_correct_bounds() {
    let func = make_func(
        "add_u32",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
        ],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    // u32 bounds: [0, 2^32 - 1]
    let formula = Formula::And(vec![
        Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("a".into(), Sort::Int))),
        Formula::Le(
            Box::new(Formula::Var("a".into(), Sort::Int)),
            Box::new(Formula::Int((1i128 << 32) - 1)),
        ),
        Formula::Not(Box::new(Formula::Le(
            Box::new(Formula::Add(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Var("b".into(), Sort::Int)),
            )),
            Box::new(Formula::Int((1i128 << 32) - 1)),
        ))),
    ]);

    let vc = make_vc(
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::u32(), Ty::u32()) },
        "add_u32",
        formula,
    );

    let warnings = cross_check_vc(&vc, &func);
    let bound_warnings: Vec<_> = warnings
        .iter()
        .filter(|w| matches!(w, CrossCheckWarning::OverflowBoundsMismatch { .. }))
        .collect();
    assert!(
        bound_warnings.is_empty(),
        "correct u32 bounds should produce no warnings, got: {bound_warnings:?}"
    );
}

// -----------------------------------------------------------------------
// Division-by-zero structure checks
// -----------------------------------------------------------------------

#[test]
fn test_cross_check_divzero_correct_structure() {
    let func = make_func(
        "div_fn",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
        ],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    let vc = make_vc(
        VcKind::DivisionByZero,
        "div_fn",
        Formula::Eq(Box::new(Formula::Var("b".into(), Sort::Int)), Box::new(Formula::Int(0))),
    );

    let warnings = cross_check_vc(&vc, &func);
    let dz_warnings: Vec<_> = warnings
        .iter()
        .filter(|w| matches!(w, CrossCheckWarning::DivZeroMissingDivisorCheck { .. }))
        .collect();
    assert!(
        dz_warnings.is_empty(),
        "correct divzero structure should produce no warnings, got: {dz_warnings:?}"
    );
}

#[test]
fn test_cross_check_divzero_missing_eq_zero_warns() {
    let func = make_func(
        "div_fn",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
        ],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    // Malformed divzero VC: no `divisor == 0` check.
    let vc = make_vc(
        VcKind::DivisionByZero,
        "div_fn",
        Formula::Lt(Box::new(Formula::Var("a".into(), Sort::Int)), Box::new(Formula::Int(5))),
    );

    let warnings = cross_check_vc(&vc, &func);
    assert!(
        warnings.iter().any(|w| matches!(w, CrossCheckWarning::DivZeroMissingDivisorCheck { .. })),
        "missing divisor check should warn, got: {warnings:?}"
    );
}

#[test]
fn test_cross_check_remainder_by_zero_same_check() {
    let func = make_func(
        "rem_fn",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("b".into()) },
        ],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    let vc = make_vc(
        VcKind::RemainderByZero,
        "rem_fn",
        Formula::Eq(Box::new(Formula::Var("b".into(), Sort::Int)), Box::new(Formula::Int(0))),
    );

    let warnings = cross_check_vc(&vc, &func);
    let dz_warnings: Vec<_> = warnings
        .iter()
        .filter(|w| matches!(w, CrossCheckWarning::DivZeroMissingDivisorCheck { .. }))
        .collect();
    assert!(dz_warnings.is_empty(), "RemainderByZero with Eq(b, 0) should pass");
}

// -----------------------------------------------------------------------
// Sort consistency checks
// -----------------------------------------------------------------------

#[test]
fn test_cross_check_sort_mismatch_int_vs_bv() {
    let func = make_func(
        "sort_fn",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    // Sort mismatch: Add(Int-var, BitVec-var).
    let vc = make_vc(
        VcKind::Assertion { message: "test".into() },
        "sort_fn",
        Formula::Add(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::BitVec(32))),
        ),
    );

    let warnings = cross_check_vc(&vc, &func);
    assert!(
        warnings.iter().any(|w| matches!(w, CrossCheckWarning::SortMismatch { .. })),
        "Int + BitVec should produce sort mismatch warning, got: {warnings:?}"
    );
}

#[test]
fn test_cross_check_sort_consistent_int_ok() {
    let func = make_func(
        "sort_fn",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::usize(), name: Some("y".into()) },
        ],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    let vc = make_vc(
        VcKind::Assertion { message: "test".into() },
        "sort_fn",
        Formula::Add(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        ),
    );

    let warnings = cross_check_vc(&vc, &func);
    let sort_warnings: Vec<_> =
        warnings.iter().filter(|w| matches!(w, CrossCheckWarning::SortMismatch { .. })).collect();
    assert!(sort_warnings.is_empty(), "Int + Int should be OK, got: {sort_warnings:?}");
}

#[test]
fn test_cross_check_sort_bv_width_mismatch() {
    let func = make_func(
        "bv_fn",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    // BvAdd with width 32 but one operand is BitVec(64).
    let vc = make_vc(
        VcKind::Assertion { message: "test".into() },
        "bv_fn",
        Formula::BvAdd(
            Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("b".into(), Sort::BitVec(64))),
            32,
        ),
    );

    let warnings = cross_check_vc(&vc, &func);
    assert!(
        warnings.iter().any(|w| matches!(w, CrossCheckWarning::SortMismatch { .. })),
        "BvAdd(32) with BitVec(64) operand should warn, got: {warnings:?}"
    );
}

// -----------------------------------------------------------------------
// Degenerate connective checks
// -----------------------------------------------------------------------

#[test]
fn test_cross_check_degenerate_and() {
    let func = make_func(
        "degen_fn",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    let vc = make_vc(
        VcKind::Assertion { message: "test".into() },
        "degen_fn",
        Formula::And(vec![Formula::Bool(true)]),
    );

    let warnings = cross_check_vc(&vc, &func);
    assert!(
        warnings.iter().any(|w| matches!(
            w,
            CrossCheckWarning::DegenerateConnective { connective, child_count }
                if connective == "And" && *child_count == 1
        )),
        "single-child And should warn, got: {warnings:?}"
    );
}

#[test]
fn test_cross_check_degenerate_or_empty() {
    let func = make_func(
        "degen_fn",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    let vc = make_vc(VcKind::Assertion { message: "test".into() }, "degen_fn", Formula::Or(vec![]));

    let warnings = cross_check_vc(&vc, &func);
    assert!(
        warnings.iter().any(|w| matches!(
            w,
            CrossCheckWarning::DegenerateConnective { connective, child_count }
                if connective == "Or" && *child_count == 0
        )),
        "empty Or should warn, got: {warnings:?}"
    );
}

// -----------------------------------------------------------------------
// Trivial formula checks
// -----------------------------------------------------------------------

#[test]
fn test_cross_check_trivial_false_warns() {
    let func = make_func(
        "trivial_fn",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    let vc = make_vc(VcKind::IndexOutOfBounds, "trivial_fn", Formula::Bool(false));

    let warnings = cross_check_vc(&vc, &func);
    assert!(
        warnings.iter().any(|w| matches!(
            w,
            CrossCheckWarning::TrivialFormula { value, .. } if !value
        )),
        "Bool(false) formula should warn as trivial, got: {warnings:?}"
    );
}

#[test]
fn test_cross_check_trivial_true_warns() {
    let func = make_func(
        "trivial_fn",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    let vc =
        make_vc(VcKind::Assertion { message: "test".into() }, "trivial_fn", Formula::Bool(true));

    let warnings = cross_check_vc(&vc, &func);
    assert!(
        warnings.iter().any(|w| matches!(
            w,
            CrossCheckWarning::TrivialFormula { value, .. } if *value
        )),
        "Bool(true) formula should warn as trivial, got: {warnings:?}"
    );
}

// -----------------------------------------------------------------------
// Integration: cross-check generated VCs
// -----------------------------------------------------------------------

#[test]
fn test_cross_check_midpoint_vcs_pass() {
    let func = crate::tests::midpoint_function();
    let vcs = crate::generate_vcs(&func);

    let warnings = cross_check_all_vcs(&vcs, &func);
    // The midpoint overflow VC should pass all structural checks.
    // Filter out degenerate connective warnings — the VC generator
    // legitimately produces And(vec![...]) where the inner structure
    // may contain sub-And with 2+ elements.
    let serious_warnings: Vec<_> = warnings
        .iter()
        .filter(|w| !matches!(w, CrossCheckWarning::DegenerateConnective { .. }))
        .collect();
    assert!(
        serious_warnings.is_empty(),
        "midpoint VCs should pass cross-check (excluding degenerate connectives), \
         got: {serious_warnings:?}"
    );
}

#[test]
fn test_cross_check_all_vcs_empty() {
    let func = make_func(
        "empty_fn",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    );

    let warnings = cross_check_all_vcs(&[], &func);
    assert!(warnings.is_empty(), "no VCs means no warnings");
}

#[test]
fn test_cross_check_warning_description() {
    let w =
        CrossCheckWarning::UnknownVariable { var_name: "ghost".into(), function: "my_fn".into() };
    let desc = w.description();
    assert!(desc.contains("ghost"));
    assert!(desc.contains("my_fn"));

    let w2 = CrossCheckWarning::OverflowBoundsMismatch {
        expected_min: -128,
        expected_max_approx: 127,
        vc_description: "i8 overflow".into(),
    };
    assert!(w2.description().contains("-128"));
    assert!(w2.description().contains("127"));

    let w3 = CrossCheckWarning::DivZeroMissingDivisorCheck { function: "div_fn".into() };
    assert!(w3.description().contains("divisor"));

    let w4 = CrossCheckWarning::SortMismatch {
        context: "integer arithmetic".into(),
        lhs_sort: SortClass::Int,
        rhs_sort: SortClass::BitVec(32),
    };
    assert!(w4.description().contains("sort mismatch"));

    let w5 = CrossCheckWarning::DegenerateConnective { connective: "And".into(), child_count: 1 };
    assert!(w5.description().contains("And"));

    let w6 = CrossCheckWarning::TrivialFormula { function: "f".into(), value: false };
    assert!(w6.description().contains("trivially false"));
}

// -----------------------------------------------------------------------
// #192: CrossCheckResult and dual-method comparison tests
// -----------------------------------------------------------------------

/// Helper: build a midpoint-like function with `(a + b) / 2`.
fn midpoint_function_for_cross_check() -> VerifiableFunction {
    crate::tests::midpoint_function()
}

/// Helper: build a function that divides two u32s.
fn div_function() -> VerifiableFunction {
    make_func(
        "div_fn",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

/// Helper: build a function that divides two i32s (signed).
fn signed_div_function() -> VerifiableFunction {
    make_func(
        "signed_div_fn",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::i32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

/// Helper: build a function that computes remainder over two i32s (signed).
fn signed_rem_function() -> VerifiableFunction {
    make_func(
        "signed_rem_fn",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::i32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Rem,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

/// Helper: build a function with a left shift.
fn shift_function() -> VerifiableFunction {
    make_func(
        "shift_fn",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Shl,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

/// Helper: build a checked left shift with rustc-style overflow assert.
fn checked_shift_function() -> VerifiableFunction {
    make_func(
        "checked_shift_fn",
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: Ty::u64(), name: Some("value".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("shift".into()) },
            LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Shl,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert {
                    unwind: UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(3, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Shl),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
    )
}

/// Helper: build a function with negation of a signed value.
fn neg_function() -> VerifiableFunction {
    make_func(
        "neg_fn",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::UnaryOp(trust_types::UnOp::Neg, Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

/// Helper: build an empty function with no operations.
fn empty_function() -> VerifiableFunction {
    make_func(
        "empty_fn",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
    )
}

/// Helper: build a function with bitwise AND (no safety VCs expected).
fn bitwise_function() -> VerifiableFunction {
    make_func(
        "bitwise_fn",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::BitAnd,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

/// Helper: build a function with float division.
fn float_div_function() -> VerifiableFunction {
    make_func(
        "float_div_fn",
        vec![
            LocalDecl { index: 0, ty: Ty::Float { width: 64 }, name: None },
            LocalDecl { index: 1, ty: Ty::Float { width: 64 }, name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::Float { width: 64 }, name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Float { width: 64 }, name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

#[test]
fn test_full_cross_check_midpoint_agrees() {
    let func = midpoint_function_for_cross_check();
    let result = full_cross_check(&func);
    assert!(result.is_sound(), "midpoint cross-check should be sound (Agree or PrimaryOnly)");
}

// DivisionByZero, ShiftOverflow, ArithmeticOverflow, FloatDivisionByZero
// checks are now handled by trust-mc-lib. Neither primary nor reference generator
// produces these VcKinds anymore. Tests verify both generators agree on empty sets.

#[test]
fn test_full_cross_check_div_function_agrees() {
    // Both primary and reference generators emit DivisionByZero
    // VCs for `Div(_, var)` — cross-check must confirm agreement.
    let func = div_function();
    let result = full_cross_check(&func);
    assert!(
        result.primary_vc_kinds.iter().any(|k| matches!(k, VcKind::DivisionByZero)),
        "primary must emit DivisionByZero for Div(_, var)"
    );
    assert!(
        result.reference_vc_kinds.iter().any(|k| matches!(k, VcKind::DivisionByZero)),
        "reference must emit DivisionByZero for Div(_, var)"
    );
    assert!(result.is_sound(), "both agree => sound");
}

#[test]
fn test_full_cross_check_signed_div_overflow() {
    // Signed `Div(_, var)` must emit DivisionByZero plus the
    // `i32::MIN / -1` ArithmeticOverflow obligation in both generators.
    let func = signed_div_function();
    let result = full_cross_check(&func);
    assert!(
        result.primary_vc_kinds.iter().any(|k| matches!(k, VcKind::DivisionByZero)),
        "primary must emit DivisionByZero for signed Div(_, var)"
    );
    assert!(
        result.reference_vc_kinds.iter().any(|k| matches!(k, VcKind::DivisionByZero)),
        "reference must emit DivisionByZero for signed Div(_, var)"
    );
    assert!(
        result
            .primary_vc_kinds
            .iter()
            .any(|k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Div, .. })),
        "primary must emit signed Div overflow"
    );
    assert!(
        result
            .reference_vc_kinds
            .iter()
            .any(|k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Div, .. })),
        "reference must emit signed Div overflow"
    );
    assert!(result.is_sound(), "both agree => sound");
}

#[test]
fn test_full_cross_check_signed_rem_overflow() {
    // Signed `Rem(_, var)` must emit RemainderByZero plus the
    // `i32::MIN % -1` ArithmeticOverflow obligation in both generators.
    let func = signed_rem_function();
    let result = full_cross_check(&func);
    assert!(
        result.primary_vc_kinds.iter().any(|k| matches!(k, VcKind::RemainderByZero)),
        "primary must emit RemainderByZero for signed Rem(_, var)"
    );
    assert!(
        result.reference_vc_kinds.iter().any(|k| matches!(k, VcKind::RemainderByZero)),
        "reference must emit RemainderByZero for signed Rem(_, var)"
    );
    assert!(
        result
            .primary_vc_kinds
            .iter()
            .any(|k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Rem, .. })),
        "primary must emit signed Rem overflow"
    );
    assert!(
        result
            .reference_vc_kinds
            .iter()
            .any(|k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Rem, .. })),
        "reference must emit signed Rem overflow"
    );
    assert!(result.is_sound(), "both agree => sound");
}

#[test]
fn test_full_cross_check_shift_overflow() {
    let func = shift_function();
    let result = full_cross_check(&func);
    // raw shifts emit ShiftOverflow in both generators.
    assert!(
        result.primary_vc_kinds.iter().any(|k| matches!(k, VcKind::ShiftOverflow { .. })),
        "primary should have ShiftOverflow"
    );
    assert!(
        result.reference_vc_kinds.iter().any(|k| matches!(k, VcKind::ShiftOverflow { .. })),
        "reference should have ShiftOverflow"
    );
    assert!(result.is_sound(), "both agree => sound");
}

#[test]
fn test_full_cross_check_checked_shift_overflow() {
    let func = checked_shift_function();
    let result = full_cross_check(&func);

    assert!(
        result
            .primary_vc_kinds
            .iter()
            .any(|k| matches!(k, VcKind::ShiftOverflow { op: BinOp::Shl, .. })),
        "primary should classify checked Shl overflow as ShiftOverflow"
    );
    assert!(
        result
            .reference_vc_kinds
            .iter()
            .any(|k| matches!(k, VcKind::ShiftOverflow { op: BinOp::Shl, .. })),
        "reference should classify checked Shl overflow as ShiftOverflow"
    );
    assert!(
        !result
            .reference_vc_kinds
            .iter()
            .any(|k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Shl, .. })),
        "reference must not classify checked Shl overflow as ArithmeticOverflow"
    );
    assert!(
        matches!(result.verdict, CrossCheckVerdict::Agree),
        "checked shift mismatch: {result:?}"
    );
}

#[test]
fn test_full_cross_check_neg_overflow() {
    let func = neg_function();
    let result = full_cross_check(&func);
    // Both should have NegationOverflow
    assert!(
        result.primary_vc_kinds.iter().any(|k| matches!(k, VcKind::NegationOverflow { .. })),
        "primary should have NegationOverflow"
    );
    assert!(
        result.reference_vc_kinds.iter().any(|k| matches!(k, VcKind::NegationOverflow { .. })),
        "reference should have NegationOverflow"
    );
}

#[test]
fn test_full_cross_check_empty_function_agrees() {
    let func = empty_function();
    let result = full_cross_check(&func);
    assert!(matches!(result.verdict, CrossCheckVerdict::Agree));
    assert!(result.primary_vc_kinds.is_empty());
    assert!(result.reference_vc_kinds.is_empty());
}

#[test]
fn test_full_cross_check_bitwise_no_vcs() {
    let func = bitwise_function();
    let result = full_cross_check(&func);
    // Bitwise AND should not generate safety VCs in either generator
    assert!(matches!(result.verdict, CrossCheckVerdict::Agree));
}

#[test]
fn test_float_ops_cross_check_agreement() {
    let func = float_div_function();
    let result = full_cross_check(&func);
    // Trust §9: float Div is defined (±inf/NaN, never traps), so BOTH generators
    // emit NO division-by-zero obligation — they agree by non-emission (the
    // property under cross-check is that the two generators stay in lockstep).
    assert!(
        !result.primary_vc_kinds.iter().any(|k| matches!(k, VcKind::FloatDivisionByZero)),
        "primary must not emit FloatDivisionByZero for defined float division"
    );
    assert!(
        !result.reference_vc_kinds.iter().any(|k| matches!(k, VcKind::FloatDivisionByZero)),
        "reference must not emit FloatDivisionByZero for defined float division"
    );
    assert!(result.is_sound(), "both agree => sound");
}

// -----------------------------------------------------------------------
// CrossCheckResult soundness methods
// -----------------------------------------------------------------------

#[test]
fn test_cross_check_result_is_sound() {
    let result = CrossCheckResult {
        function_name: "test".into(),
        primary_vc_kinds: vec![VcKind::DivisionByZero],
        reference_vc_kinds: vec![VcKind::DivisionByZero],
        structural_warnings: vec![],
        verdict: CrossCheckVerdict::Agree,
    };
    assert!(result.is_sound());
    assert!(!result.has_soundness_alarm());
}

#[test]
fn test_cross_check_result_soundness_alarm_on_reference_only() {
    let result = CrossCheckResult {
        function_name: "test".into(),
        primary_vc_kinds: vec![],
        reference_vc_kinds: vec![VcKind::DivisionByZero],
        structural_warnings: vec![],
        verdict: CrossCheckVerdict::ReferenceOnly {
            missing_from_primary: vec![VcKind::DivisionByZero],
        },
    };
    assert!(!result.is_sound());
    assert!(result.has_soundness_alarm());
}

#[test]
fn test_cross_check_result_primary_only_is_sound() {
    // Extra VCs in primary = conservative, not unsound
    let result = CrossCheckResult {
        function_name: "test".into(),
        primary_vc_kinds: vec![VcKind::DivisionByZero, VcKind::RemainderByZero],
        reference_vc_kinds: vec![VcKind::DivisionByZero],
        structural_warnings: vec![],
        verdict: CrossCheckVerdict::PrimaryOnly {
            missing_from_reference: vec![VcKind::RemainderByZero],
        },
    };
    assert!(result.is_sound());
    assert!(!result.has_soundness_alarm());
}

// -----------------------------------------------------------------------
// compare_vc_sets tests
// -----------------------------------------------------------------------

#[test]
fn test_compare_vc_sets_agree() {
    let primary = vec![VcKind::DivisionByZero];
    let reference = vec![VcKind::DivisionByZero];
    assert!(matches!(compare_vc_sets(&primary, &reference), CrossCheckVerdict::Agree));
}

#[test]
fn test_compare_vc_sets_primary_only() {
    let primary = vec![VcKind::DivisionByZero, VcKind::IndexOutOfBounds];
    let reference = vec![VcKind::DivisionByZero];
    assert!(matches!(compare_vc_sets(&primary, &reference), CrossCheckVerdict::PrimaryOnly { .. }));
}

#[test]
fn test_compare_vc_sets_reference_only() {
    let primary = vec![VcKind::DivisionByZero];
    let reference = vec![VcKind::DivisionByZero, VcKind::IndexOutOfBounds];
    assert!(matches!(
        compare_vc_sets(&primary, &reference),
        CrossCheckVerdict::ReferenceOnly { .. }
    ));
}

#[test]
fn test_compare_vc_sets_divergent() {
    let primary = vec![VcKind::IndexOutOfBounds];
    let reference = vec![VcKind::DivisionByZero];
    assert!(matches!(compare_vc_sets(&primary, &reference), CrossCheckVerdict::Divergent { .. }));
}

// -----------------------------------------------------------------------
// Property-based tests for formula properties
// -----------------------------------------------------------------------

#[test]
fn test_weakening_does_not_lose_safety() {
    let original =
        Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100)));
    let weakened = Formula::Or(vec![original.clone(), Formula::Bool(true)]);
    assert!(weakening_preserves_safety(&original, &weakened));
}

#[test]
fn test_strengthening_does_not_add_spurious_proofs() {
    let formula = Formula::And(vec![
        Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100))),
        Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
    ]);
    let strengthened = strengthen_by_dropping_assumption(&formula);
    assert!(strengthened.is_some());
    // The strengthened formula should have fewer conjuncts.
    let s = strengthened.unwrap();
    // Should be the second conjunct only (Ge(x, 0))
    assert!(matches!(s, Formula::Ge(..)));
}

#[test]
fn test_strengthen_single_conjunct_returns_none() {
    let formula = Formula::And(vec![Formula::Bool(true)]);
    assert!(strengthen_by_dropping_assumption(&formula).is_none());
}

#[test]
fn test_vc_free_vars_subset_of_function_locals() {
    let func = midpoint_function_for_cross_check();
    let vcs = crate::generate_vcs(&func);
    let known_names: FxHashSet<String> = func
        .body
        .locals
        .iter()
        .flat_map(|decl| {
            let mut names = vec![format!("_{}", decl.index)];
            if let Some(name) = &decl.name {
                names.push(name.clone());
            }
            names
        })
        .collect();

    for vc in &vcs {
        for var in vc.formula.free_variables() {
            let base = var.split('.').next().unwrap_or(&var);
            let deref_stripped = base.strip_prefix('*').unwrap_or(base);
            let bracket_base = deref_stripped.split('[').next().unwrap_or(deref_stripped);
            assert!(
                known_names.contains(bracket_base)
                    || var.ends_with("__slice_len")
                    || var.starts_with("float_"),
                "free variable `{var}` not in function locals: {known_names:?}"
            );
        }
    }
}

#[test]
fn test_all_safety_vcs_are_l0() {
    let func = midpoint_function_for_cross_check();
    let vcs = crate::generate_vcs(&func);
    for vc in &vcs {
        let level = vc.kind.proof_level();
        assert!(
            level <= ProofLevel::L0Safety,
            "midpoint safety VC {:?} should be L0Safety, got {level:?}",
            vc.kind
        );
    }
}

#[test]
fn test_overflow_vc_contains_type_bounds() {
    let func = midpoint_function_for_cross_check();
    let vcs = crate::generate_vcs(&func);
    for vc in &vcs {
        if matches!(vc.kind, VcKind::ArithmeticOverflow { .. }) {
            // The overflow formula should contain at least one Int literal
            // representing a type bound.
            let mut has_bound = false;
            vc.formula.visit(&mut |f| {
                if matches!(f, Formula::Int(_) | Formula::UInt(_)) {
                    has_bound = true;
                }
            });
            assert!(
                has_bound,
                "overflow VC should contain type bound literals, got: {:?}",
                vc.formula
            );
        }
    }
}

#[test]
fn test_divzero_vc_contains_eq_zero() {
    let func = div_function();
    let vcs = crate::generate_vcs(&func);
    for vc in &vcs {
        if matches!(vc.kind, VcKind::DivisionByZero) {
            let mut found_eq_zero = false;
            vc.formula.visit(&mut |f| {
                if let Formula::Eq(lhs, rhs) = f {
                    let has_zero = matches!(lhs.as_ref(), Formula::Int(0))
                        || matches!(rhs.as_ref(), Formula::Int(0));
                    if has_zero {
                        found_eq_zero = true;
                    }
                }
            });
            assert!(found_eq_zero, "division-by-zero VC should contain Eq(..., 0)");
        }
    }
}

#[test]
fn test_constant_divisor_eliminates_divzero_vc() {
    // Division by a non-zero constant (2) should NOT generate a divzero VC
    // because the primary pipeline is smart enough to recognize that
    // the divisor is a known non-zero constant.
    let func = make_func(
        "const_div",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Uint(2, 32)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    );
    let vcs = crate::generate_vcs(&func);
    // The primary pipeline eliminates divzero VC for constant non-zero divisors
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "constant non-zero divisor should NOT generate divzero VC"
    );

    // Cross-check: both generators should agree (no divzero for constant 2)
    let result = full_cross_check(&func);
    assert!(result.is_sound(), "constant divisor cross-check should be sound");
}

#[test]
fn test_vc_count_monotonicity_across_types() {
    // Property: wider integer types should produce the same number
    // of VCs as narrower types for the same operations.
    let make_add_func = |ty: Ty, name: &str| {
        make_func(
            name,
            vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: ty.clone(), name: None },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
        )
    };

    let i32_vcs = crate::generate_vcs(&make_add_func(Ty::i32(), "add_i32"));
    let i64_vcs = crate::generate_vcs(&make_add_func(Ty::i64(), "add_i64"));
    assert_eq!(
        i32_vcs.len(),
        i64_vcs.len(),
        "i32 add and i64 add should produce the same number of VCs"
    );
}

#[test]
fn test_categorize_vc_covers_all_safety_kinds() {
    // Property: all safety-relevant VcKinds should have non-Other categories
    let kinds = vec![
        VcKind::DivisionByZero,
        VcKind::RemainderByZero,
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
        VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() },
        VcKind::NegationOverflow { ty: Ty::i32() },
        VcKind::IndexOutOfBounds,
        VcKind::SliceBoundsCheck,
        VcKind::CastOverflow { from_ty: Ty::i64(), to_ty: Ty::i32() },
        VcKind::FloatDivisionByZero,
        VcKind::FloatOverflowToInfinity { op: BinOp::Add, operand_ty: Ty::Float { width: 64 } },
    ];

    for kind in &kinds {
        let cat = categorize_vc(kind);
        assert!(
            !matches!(cat, VcCategory::Other(_)),
            "safety VC kind {:?} should have a specific category, got Other",
            kind
        );
    }
}
