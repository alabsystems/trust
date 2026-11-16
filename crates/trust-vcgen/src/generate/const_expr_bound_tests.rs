// The FAIL-CLOSED half of the unfolded-constant-bound fold
// (`overflow_vc::v2_const_expr_operand_int`), pinned directly on the resolver
// rather than through a compiled fixture.
//
// WHY NOT REAL MIR FOR THESE. The real-MIR file
// (`tests/unfolded_const_bound_mul_realmir.rs`) pins the verdicts, and it is the
// evidence that the fold FIRES on the shapes rustc really emits. It cannot pin
// the refusals: `1i64 << 64` is a deny-by-default `arithmetic_overflow` compile
// error, so no fixture can carry it, and `-(1i64 << 63)` is a program whose
// negation always panics — a fixture of it would measure the panic, not the fold.
// The refusals are where a wrong fold turns into a FALSE PROOF (a bound the
// machine never computes, conjoined as if it did), so they are pinned here, on
// the resolver's own inputs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnOp, VerifiableBody, VerifiableFunction,
};

use super::overflow_vc::{V2_CONST_EXPR_FUEL, v2_const_expr_operand_int};

fn i(width: u32) -> Ty {
    Ty::Int { width, signed: true }
}
fn u(width: u32) -> Ty {
    Ty::Int { width, signed: false }
}
fn int(value: i128) -> Operand {
    Operand::Constant(ConstValue::Int(value))
}
fn local(n: usize) -> Operand {
    Operand::Copy(Place::local(n))
}

fn assign(dest: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(dest), rvalue, span: SourceSpan::default() }
}

/// A one-block function whose locals are `(index, ty)` and whose statements are
/// `stmts`. `_0` is the return local; parameters are `arg_count` locals after it.
fn func(locals: &[(usize, Ty)], stmts: Vec<Statement>, arg_count: usize) -> VerifiableFunction {
    let locals: Vec<LocalDecl> = locals
        .iter()
        .map(|(index, ty)| LocalDecl { index: *index, ty: ty.clone(), name: None })
        .collect();
    let return_ty = locals.iter().find(|l| l.index == 0).expect("_0").ty.clone();
    VerifiableFunction {
        name: "synthetic".to_string(),
        def_path: "synthetic::synthetic".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `_1: <ty> = <rvalue>`, folded. The single-statement shape every case below
/// shares.
fn fold_one(ty: Ty, rvalue: Rvalue) -> Option<i128> {
    let f = func(&[(0, ty.clone()), (1, ty)], vec![assign(1, rvalue)], 0);
    v2_const_expr_operand_int(&f, &local(1), V2_CONST_EXPR_FUEL)
}

fn shl(lhs: Operand, rhs: Operand) -> Rvalue {
    Rvalue::BinaryOp(BinOp::Shl, lhs, rhs)
}

// ---------------------------------------------------------------------------
// It fires — otherwise every refusal below would pass vacuously.
// ---------------------------------------------------------------------------

#[test]
fn a_shift_that_stays_inside_the_type_folds_exactly() {
    assert_eq!(fold_one(i(64), shl(int(1), int(31))), Some(1 << 31));
    assert_eq!(fold_one(i(64), shl(int(1), int(62))), Some(1 << 62));
    assert_eq!(
        fold_one(i(64), Rvalue::BinaryOp(BinOp::Mul, int(65536), int(32768))),
        Some(1 << 31)
    );
    assert_eq!(
        fold_one(i(64), Rvalue::BinaryOp(BinOp::Add, int(2147483647), int(1))),
        Some(1 << 31)
    );
}

/// The walk is RECURSIVE: an unfolded operand of an unfolded operator resolves
/// too. `-((1i64 << 15) << 16)` is three levels (`Neg` over `Shl` over `Shl`) and
/// is exactly `-(2^31)`.
#[test]
fn an_operand_that_is_itself_an_unfolded_expression_folds() {
    let f = func(
        &[(0, i(64)), (1, i(64)), (2, i(64)), (3, i(64))],
        vec![
            assign(1, shl(int(1), int(15))),
            assign(2, shl(local(1), int(16))),
            assign(3, Rvalue::UnaryOp(UnOp::Neg, local(2))),
        ],
        0,
    );
    assert_eq!(v2_const_expr_operand_int(&f, &local(2), V2_CONST_EXPR_FUEL), Some(1 << 31));
    assert_eq!(v2_const_expr_operand_int(&f, &local(3), V2_CONST_EXPR_FUEL), Some(-(1 << 31)));

    // And the refusal composes: one level deeper the product leaves i64, so the
    // whole chain declines rather than handing back a truncated bound.
    let f = func(
        &[(0, i(64)), (1, i(64)), (2, i(64))],
        vec![assign(1, shl(int(1), int(48))), assign(2, shl(local(1), int(16)))],
        0,
    );
    assert_eq!(v2_const_expr_operand_int(&f, &local(1), V2_CONST_EXPR_FUEL), Some(1 << 48));
    assert_eq!(v2_const_expr_operand_int(&f, &local(2), V2_CONST_EXPR_FUEL), None);
}

/// Signedness is read off the DESTINATION type, not assumed: `1u64 << 63` is
/// `2^63`, which fits `u64` exactly and is a legitimate bound — while the same
/// shift at `i64` is refused by the test below. A fold that hard-coded either
/// answer would fail one of the two.
#[test]
fn the_same_shift_folds_for_u64_and_is_refused_for_i64() {
    assert_eq!(fold_one(u(64), shl(int(1), int(63))), Some(1i128 << 63));
    assert_eq!(fold_one(i(64), shl(int(1), int(63))), None);
}

// ---------------------------------------------------------------------------
// FAIL-CLOSED — the refusals. Each of these, folded wrongly, is a bound the
// machine never computes, conjoined into a proof as if it did.
// ---------------------------------------------------------------------------

/// `1i64 << 63` is `2^63`, one past `i64::MAX`. The machine's `<<` does not
/// panic here — it truncates to `i64::MIN` — so a fold that took the machine
/// value would hand back `-9223372036854775808` and a fold that ignored the
/// range would hand back `2^63`. Both are wrong as a BOUND, and both are
/// refused: the exact mathematical result must fit the destination type.
#[test]
fn a_shift_whose_result_leaves_the_type_is_not_a_bound() {
    assert_eq!(fold_one(i(64), shl(int(1), int(63))), None);
    assert_eq!(fold_one(i(64), shl(int(2), int(62))), None);
    assert_eq!(fold_one(i(8), shl(int(1), int(7))), None);
    assert_eq!(fold_one(i(64), Rvalue::BinaryOp(BinOp::Mul, int(1 << 32), int(1 << 32))), None);
}

/// `1i64 << 64` shifts by the full width — UB-adjacent in C and a panic in Rust,
/// and not a value at all. A fold that masked the amount (`64 % 64 == 0`) would
/// silently produce `1`.
#[test]
fn a_shift_by_the_width_or_more_is_refused_not_masked() {
    assert_eq!(fold_one(i(64), shl(int(1), int(64))), None);
    assert_eq!(fold_one(i(64), shl(int(1), int(200))), None);
    assert_eq!(fold_one(i(8), shl(int(1), int(8))), None);
    assert_eq!(fold_one(i(64), Rvalue::BinaryOp(BinOp::Shr, int(1024), int(64))), None);
}

/// A negative shift amount is not a shift.
#[test]
fn a_negative_shift_amount_is_refused() {
    assert_eq!(fold_one(i(64), shl(int(1), int(-1))), None);
}

/// Division and remainder by zero have no value.
#[test]
fn division_by_zero_is_refused() {
    assert_eq!(fold_one(i(64), Rvalue::BinaryOp(BinOp::Div, int(8), int(0))), None);
    assert_eq!(fold_one(i(64), Rvalue::BinaryOp(BinOp::Rem, int(8), int(0))), None);
}

/// THE CENTRAL REFUSAL: nothing with a VARIABLE inside it folds, at any depth.
/// Partially evaluating `a << 3` to `3` (or to anything) would attribute a bound
/// to a value the program chooses at runtime.
#[test]
fn a_term_containing_a_variable_never_folds() {
    // `_1` is the parameter itself.
    let f = func(&[(0, i(64)), (1, i(64)), (2, i(64))], vec![assign(2, shl(local(1), int(3)))], 1);
    assert_eq!(v2_const_expr_operand_int(&f, &local(2), V2_CONST_EXPR_FUEL), None);
    assert_eq!(
        v2_const_expr_operand_int(&f, &local(1), V2_CONST_EXPR_FUEL),
        None,
        "a parameter has no value definition and must never resolve"
    );
    // And one level deeper: `_3 = Neg(_2)` over the same tainted `_2`.
    let f = func(
        &[(0, i(64)), (1, i(64)), (2, i(64)), (3, i(64))],
        vec![assign(2, shl(local(1), int(3))), assign(3, Rvalue::UnaryOp(UnOp::Neg, local(2)))],
        1,
    );
    assert_eq!(v2_const_expr_operand_int(&f, &local(3), V2_CONST_EXPR_FUEL), None);
}

/// A local with more than one definition has no single value, whatever the
/// definitions say — `local_defs::unique_value_def` is the resolver, and this
/// pins that the fold really goes through it rather than taking the first
/// matching statement it finds.
#[test]
fn a_local_with_two_definitions_never_folds() {
    let f = func(
        &[(0, i(64)), (1, i(64))],
        vec![assign(1, shl(int(1), int(31))), assign(1, shl(int(1), int(30)))],
        0,
    );
    assert_eq!(v2_const_expr_operand_int(&f, &local(1), V2_CONST_EXPR_FUEL), None);
}

/// A cast folds to the value the MACHINE stores, never to the source value.
///
/// AMENDED 2026-09-21 (the closed-constant widening). This test used to pin
/// `300i64 as i8` as a REFUSAL, on the ground that the cast is not
/// value-preserving. The refusal was wider than its reason: `300i64 as i8` is
/// exactly `44` — a total, exactly computable function of the source value and
/// the destination type — and `x == 44` is TRUE on every execution that reaches
/// it, which is the only property a mined hypothesis has ever had to have. The
/// value-preserving rule was standing in for "computable exactly", and
/// `const_expr::v2_const_expr_cast_int` now computes it.
///
/// WHAT MUST STILL BE REFUSED, and is asserted here as the unsafe twin: the
/// SOURCE value. `300` as an `i8` bound is a number the machine never holds in
/// that local, and a fold that carried the operand through unchanged would mint
/// it. The refusals the widening does not touch — a float, a pointer, a
/// non-closed operand, a target that disagrees with the destination local, and
/// the `&mut` escape — are pinned in `const_expr`'s own test module.
#[test]
fn a_cast_folds_to_the_machine_value_and_never_to_the_source_value() {
    let f = func(
        &[(0, i(8)), (1, i(64)), (2, i(8))],
        vec![assign(1, Rvalue::Use(int(300))), assign(2, Rvalue::Cast(local(1), i(8)))],
        0,
    );
    let folded = v2_const_expr_operand_int(&f, &local(2), V2_CONST_EXPR_FUEL);
    assert_eq!(folded, Some(i128::from(300i64 as i8)), "the machine stores 44 in that i8");
    assert_ne!(
        folded,
        Some(300),
        "UNSAFE TWIN: `300` is not a value an `i8` can hold, and must never be mined as \
         one — a fold that carried the source value through would claim exactly that"
    );

    let f = func(
        &[(0, i(8)), (1, i(64)), (2, i(8))],
        vec![assign(1, Rvalue::Use(int(100))), assign(2, Rvalue::Cast(local(1), i(8)))],
        0,
    );
    assert_eq!(
        v2_const_expr_operand_int(&f, &local(2), V2_CONST_EXPR_FUEL),
        Some(100),
        "and a value-preserving cast is unchanged by the widening"
    );
}

/// A bitwise operation on a NEGATIVE operand has a width-dependent answer that
/// `i128`'s own operators do not give, so it is refused rather than
/// approximated. The non-negative case still folds.
#[test]
fn a_negative_bitwise_operand_is_refused() {
    assert_eq!(fold_one(i(64), Rvalue::BinaryOp(BinOp::BitAnd, int(-1), int(255))), None);
    assert_eq!(fold_one(i(64), Rvalue::BinaryOp(BinOp::BitOr, int(-2), int(1))), None);
    assert_eq!(fold_one(i(64), Rvalue::BinaryOp(BinOp::BitAnd, int(3072), int(255))), Some(0));
}

/// The `.0` VALUE half of a `CheckedBinaryOp` tuple is the WRAPPED value when the
/// operation overflows, so it is admitted only when the mathematical result fits
/// — and the `.1` overflow FLAG is never a value at all.
#[test]
fn a_checked_binop_tuple_folds_only_through_a_non_overflowing_value_field() {
    let tuple = Ty::Tuple(vec![i(64), Ty::Bool]);
    let ok = func(
        &[(0, i(64)), (1, tuple.clone())],
        vec![assign(1, Rvalue::CheckedBinaryOp(BinOp::Mul, int(65536), int(32768)))],
        0,
    );
    let field = |n: usize| {
        Operand::Copy(Place { local: 1, projections: vec![trust_types::Projection::Field(n)] })
    };
    assert_eq!(v2_const_expr_operand_int(&ok, &field(0), V2_CONST_EXPR_FUEL), Some(1 << 31));
    assert_eq!(
        v2_const_expr_operand_int(&ok, &field(1), V2_CONST_EXPR_FUEL),
        None,
        "the overflow flag is a bool, never a bound"
    );

    let overflows = func(
        &[(0, i(64)), (1, tuple)],
        vec![assign(1, Rvalue::CheckedBinaryOp(BinOp::Mul, int(1 << 32), int(1 << 32)))],
        0,
    );
    assert_eq!(
        v2_const_expr_operand_int(&overflows, &field(0), V2_CONST_EXPR_FUEL),
        None,
        "`2^32 * 2^32` overflows i64, so `.0` is the WRAPPED value and is not this product"
    );
}

/// The walk is bounded: a chain longer than the fuel declines rather than
/// recursing without limit.
#[test]
fn the_walk_is_bounded_by_its_fuel() {
    let mut locals = vec![(0usize, i(64))];
    let mut stmts = vec![assign(1, Rvalue::Use(int(7)))];
    locals.push((1, i(64)));
    let depth = (V2_CONST_EXPR_FUEL as usize) + 4;
    for n in 2..=depth {
        locals.push((n, i(64)));
        stmts.push(assign(n, Rvalue::Use(local(n - 1))));
    }
    let f = func(&locals, stmts, 0);
    assert_eq!(v2_const_expr_operand_int(&f, &local(2), V2_CONST_EXPR_FUEL), Some(7));
    assert_eq!(v2_const_expr_operand_int(&f, &local(depth), V2_CONST_EXPR_FUEL), None);
}
