//! A plain MIR `Shl`/`Shr` (`Rvalue::BinaryOp`, no overflow `Assert`: the shape
//! rustc emits under `-C overflow-checks=off`) is defined in the CHC/VC lane with
//! Rust's shift-count mask, `count.rem_euclid(width)`.
//!
//! # The defect
//!
//! `chc::try_binop_to_formula` emitted the count as a bare `IntToBv(rhs, w)`.
//! SMT-LIB's `bvshl`/`bvlshr` by a count `>= w` are `0` (and `bvashr` the sign
//! fill), so the body definition of `_0 = Shl(x, s)` said `_0 == 0` for every
//! `s >= 32`, where Rust computes `x << (s & 31)`. Conjoined as a hypothesis, that
//! definition is FALSE of exactly the out-of-range executions, and it proved
//! `ensures s < 32 || result == 0` while refuting the true
//! `ensures x != 1 || s != 33 || result == 2` (docs/KNOWN_HAZARDS.md, "shift
//! count"; the same false proof was measured end to end through trust-mc on the
//! TrustIr bundle, whose producer had the same unmasked count).
//!
//! MEASURED against the unfixed `chc.rs`/`contracts.rs` (2026-10-03, this file):
//! `false_unmasked_shl_value_is_refuted` was PROVED; `true_masked_shl_value_is_proved`
//! and `true_narrow_value_wide_count_is_proved` were REFUTED with `_0 = 0`;
//! `false_out_of_range_shl_is_zero_claim_is_refuted` was `Unknown`; the formula test
//! failed. `true_signed_negative_count_is_proved` (the unmasked `bvashr` sign fill
//! happens to agree there) and `false_out_of_range_lshr_is_zero_claim_is_not_proved`
//! held before as well; they are controls. The formula test pins the one spelling
//! the lane now uses, which is also the spelling
//! `contracts::machine_faithful_shift_amount` authenticates.

use trust_types::*;

#[path = "support/test_router.rs"]
mod test_router;

fn var(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}

fn int(value: i128) -> Formula {
    Formula::Int(value)
}

fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}

fn ne(a: Formula, b: Formula) -> Formula {
    Formula::Not(Box::new(eq(a, b)))
}

/// `min <= name <= max` for a parameter of integer type `ty` — the range every
/// execution gives it. The Int-sorted lane does not add it on its own, and without
/// it a count of `2^32 + 1` "wraps" to 1 inside `IntToBv` and refutes a shift claim
/// for a reason no execution has.
fn type_range(name: &str, ty: &Ty) -> Formula {
    let width = ty.int_width().expect("an integer parameter");
    let (min, max) = if ty.is_signed() {
        (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
    } else {
        (0, (1i128 << width) - 1)
    };
    Formula::And(vec![
        Formula::Le(Box::new(int(min)), Box::new(var(name))),
        Formula::Le(Box::new(var(name)), Box::new(int(max))),
    ])
}

/// `fn f(x: VALUE, s: COUNT) -> VALUE { x OP s }` with NO overflow assert, and
/// one `ensures` over `_0`. The parameters' type ranges are its preconditions.
fn plain_shift_fn(op: BinOp, value: Ty, count: Ty, post: Formula) -> VerifiableFunction {
    let preconditions = vec![type_range("x", &value), type_range("s", &count)];
    VerifiableFunction {
        name: "plain_shift".into(),
        def_path: "plain_shift".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: value.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: value.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: count, name: Some("s".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        op,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: value,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions,
        postconditions: vec![post],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn postcondition_outcome(func: &VerifiableFunction) -> VerificationResult {
    let vcs: Vec<_> = trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .collect();
    assert_eq!(vcs.len(), 1, "exactly one postcondition obligation: {vcs:#?}");
    let router = test_router::deterministic_test_router();
    router.verify_all(&vcs).into_iter().next().expect("one result").1
}

fn assert_refuted(func: &VerifiableFunction, what: &str) {
    let outcome = postcondition_outcome(func);
    assert!(
        matches!(outcome, VerificationResult::Failed { .. }),
        "{what} is FALSE of the Rust program and must be refuted, got {outcome:?}"
    );
}

fn assert_not_proved(func: &VerifiableFunction, what: &str) {
    let outcome = postcondition_outcome(func);
    assert!(
        !matches!(outcome, VerificationResult::Proved { .. }),
        "{what} is FALSE of the Rust program and must not be proved, got {outcome:?}"
    );
}

fn assert_proved(func: &VerifiableFunction, what: &str) {
    let outcome = postcondition_outcome(func);
    assert!(
        matches!(outcome, VerificationResult::Proved { .. }),
        "{what} is TRUE of the Rust program and must be proved, got {outcome:?}"
    );
}

/// `x << s`, `ensures s < 32 || result == 0`: false at `(1, 33)`, where Rust
/// returns 2. `Unknown` before the fix.
#[test]
fn false_out_of_range_shl_is_zero_claim_is_refuted() {
    let post = Formula::Or(vec![
        Formula::Lt(Box::new(var("s")), Box::new(int(32))),
        eq(var("_0"), int(0)),
    ]);
    assert_refuted(
        &plain_shift_fn(BinOp::Shl, Ty::u32(), Ty::u32(), post),
        "`s < 32 || result == 0` over `x << s`",
    );
}

/// `x >> s`, the same false claim. The in-process ay returns `Unknown` here, before
/// and after the fix ("incomplete", measured 2026-10-03), so the pin is the property
/// that matters for soundness: it is NOT proved.
#[test]
fn false_out_of_range_lshr_is_zero_claim_is_not_proved() {
    let post = Formula::Or(vec![
        Formula::Lt(Box::new(var("s")), Box::new(int(32))),
        eq(var("_0"), int(0)),
    ]);
    assert_not_proved(
        &plain_shift_fn(BinOp::Shr, Ty::u32(), Ty::u32(), post),
        "`s < 32 || result == 0` over `x >> s`",
    );
}

/// The scout's inverse control: `x << s` with `ensures x != 1 || s != 33 ||
/// result == 2` is TRUE (`33 & 31 == 1`). Refuted before the fix.
#[test]
fn true_masked_shl_value_is_proved() {
    let post =
        Formula::Or(vec![ne(var("x"), int(1)), ne(var("s"), int(33)), eq(var("_0"), int(2))]);
    assert_proved(
        &plain_shift_fn(BinOp::Shl, Ty::u32(), Ty::u32(), post),
        "`x != 1 || s != 33 || result == 2` over `x << s`",
    );
}

/// ...and its false twin `... || result == 0`, the unmasked value, PROVED before the
/// fix, is refuted.
#[test]
fn false_unmasked_shl_value_is_refuted() {
    let post =
        Formula::Or(vec![ne(var("x"), int(1)), ne(var("s"), int(33)), eq(var("_0"), int(0))]);
    assert_refuted(
        &plain_shift_fn(BinOp::Shl, Ty::u32(), Ty::u32(), post),
        "`x != 1 || s != 33 || result == 0` over `x << s`",
    );
}

/// A `u8` value with a `u32` count: `1u8 << 9u32 == 2` (`9 & 7 == 1`).
#[test]
fn true_narrow_value_wide_count_is_proved() {
    let post = Formula::Or(vec![ne(var("x"), int(1)), ne(var("s"), int(9)), eq(var("_0"), int(2))]);
    assert_proved(
        &plain_shift_fn(BinOp::Shl, Ty::u8(), Ty::u32(), post),
        "`x != 1 || s != 9 || result == 2` over `x: u8 << s: u32`",
    );
}

/// A signed value shifted arithmetically by a negative signed count:
/// `-64i32 >> -1i8` is `-64 >> 31 == -1`.
#[test]
fn true_signed_negative_count_is_proved() {
    let post =
        Formula::Or(vec![ne(var("x"), int(-64)), ne(var("s"), int(-1)), eq(var("_0"), int(-1))]);
    assert_proved(
        &plain_shift_fn(BinOp::Shr, Ty::i32(), Ty::Int { width: 8, signed: true }, post),
        "`x != -64 || s != -1 || result == -1` over `x: i32 >> s: i8`",
    );
}

/// The formula the lane emits: the count is `BvAnd(IntToBv(s, 32), 31)`, the
/// crate's one masked spelling, and a non-shift bitwise op is untouched.
#[test]
fn the_shift_count_formula_is_the_masked_spelling() {
    let x = var("x");
    let s = var("s");
    for op in [BinOp::Shl, BinOp::Shr] {
        let formula =
            trust_vcgen::chc::try_binop_to_formula(op, x.clone(), s.clone(), Some(32), false)
                .expect("a u32 shift lowers");
        let Formula::BvToInt(inner, 32, false) = &formula else {
            panic!("{op:?}: expected the BvToInt bridge, got {formula:?}");
        };
        let (Formula::BvShl(_, count, 32) | Formula::BvLShr(_, count, 32)) = inner.as_ref() else {
            panic!("{op:?}: expected a 32-bit shift, got {inner:?}");
        };
        assert_eq!(
            count.as_ref(),
            &Formula::BvAnd(
                Box::new(Formula::IntToBv(Box::new(s.clone()), 32)),
                Box::new(Formula::BitVec { value: 31, width: 32 }),
                32,
            ),
            "{op:?}: the count must carry Rust's `& (BITS - 1)` mask"
        );
    }
    let and = trust_vcgen::chc::try_binop_to_formula(BinOp::BitAnd, x, s.clone(), Some(32), false)
        .expect("a u32 and lowers");
    let Formula::BvToInt(inner, 32, false) = &and else { panic!("{and:?}") };
    assert!(
        matches!(inner.as_ref(), Formula::BvAnd(_, rhs, 32)
            if rhs.as_ref() == &Formula::IntToBv(Box::new(s), 32)),
        "a bitwise AND operand is not a shift count and stays unmasked: {inner:?}"
    );
}
