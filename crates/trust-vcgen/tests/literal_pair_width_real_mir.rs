//! REAL-ARTIFACT regression guard for LITERAL-PAIR-WIDTH-1 and
//! SELF-GUARDED-LITERAL-OPERAND-2: rows built at a width that a width-less signed
//! literal never had.
//!
//! Every fixture loaded here is the compiler's OWN extracted verification input
//! (`-Ztrust-dump=mir-only`), from `tests/data/literal_pair_width_arms.rs` (README,
//! "Literal pair width family").
//!
//! # What went wrong
//!
//! A signed literal reaches trust-vcgen as `ConstValue::Int`, with no width, and
//! `operand_ty` types it i64 (i128 when the value does not fit i64). `int_op_type`
//! recovers an operation's width from its NON-constant operand, so when BOTH
//! operands are such literals it had nothing to read and answered the fabricated
//! i64.
//!
//! * `core::intrinsics::unchecked_div(i8::MIN, -1)` lowers to a bare `_0 =
//!   Div(const -128, const -1)` into `_0: i8`, with no assert. Its only row,
//!   `v2_build_signed_div_overflow_vc`'s, read `-128 == i64::MIN` (UNSAT): the
//!   function was VERIFIED, the row clean-kernel `Certified` under the closed false
//!   hypothesis `h_0 : -128 = -9223372036854775808`, and every call is UB. MEASURED
//!   on stage1-w25f (integ7, `a971311ee2`): `1 proved, 0 failed ... of which 1
//!   kernel-certified` under default and certify; the i16, i32, i128 and `rem`
//!   twins the same.
//! * The checked `i32::MIN / -1` (under `#![allow(arithmetic_overflow,
//!   unconditional_panic)]`): the suppression of the statement row
//!   (`v2_divrem_overflow_assert_exactly_bound`) compared the cond's `Eq(const MIN,
//!   const MIN)` against `i64::MIN` and never bound, so the same certified false row
//!   sat beside the assert lane's FAILED one.
//! * `i8::MAX.unchecked_add(1)` (stable): the call arm's row read `127 + 1 outside
//!   i64` and shipped `unchecked_overflow:add` PROVED and certified.
//! * `x << 40` (`x: u32`; the amount defaults to `i32`): the assert compares the
//!   cast temporary `_t = const 40 as u32`, and the shift binder refused a LITERAL
//!   cast source, so the statement-lane `shift:left` row, under the assert's own
//!   guard, shipped kernel-certified beside the FAILED generic `overflow` row.
//!
//! # What each arm pins
//!
//! Every row is run through the in-process ay router and the clean-kernel
//! certifier. An operation that fails on every call keeps exactly ONE row, REFUTED,
//! and no row of its kind may certify. The safe twins keep one honest PROVED row,
//! and the controls, already typed at their true width, keep their one refuted row.

use trust_types::{
    BinOp, ConstValue, Operand, Projection, Rvalue, Statement, Terminator, Ty, VcKind,
    VerifiableFunction, VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");

fn load(name: &str) -> VerifiableFunction {
    // Straight from text: `literal_pair_ud128` carries `Int: i128::MIN`, which a
    // `serde_json::Value` round-trip would widen to `f64`.
    let text = std::fs::read_to_string(format!("{DATA}literal_pair_{name}.json"))
        .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must be readable: {e}"));
    let func: VerifiableFunction = serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must deserialize: {e}"));
    assert_eq!(func.name, name, "fixture drift: `literal_pair_{name}.json` names another fn");
    func
}

fn rows_of(func: &VerifiableFunction, pick: fn(&VcKind) -> bool) -> Vec<VerificationCondition> {
    trust_vcgen::generate_vcs(func).into_iter().filter(|vc| pick(&vc.kind)).collect()
}

/// Every row a signed `Div`/`Rem` overflow can take: the statement lane's and the
/// assert lane's (`overflow:div` / `overflow:rem`).
fn divrem_overflow(kind: &VcKind) -> bool {
    matches!(kind, VcKind::ArithmeticOverflow { op: BinOp::Div | BinOp::Rem, .. })
}

fn unchecked_overflow(kind: &VcKind) -> bool {
    matches!(kind, VcKind::UncheckedArithmeticOverflow { .. })
}

/// Every row a shift's amount check can take: the bound `shift:*` row, and the
/// assert lane's generic `overflow` fall-through when the binder refuses.
fn shift_check(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::ShiftOverflow { .. }
            | VcKind::ArithmeticOverflow { op: BinOp::Shl | BinOp::Shr, .. }
    )
}

fn literal_pair_unknown(kind: &VcKind) -> bool {
    matches!(kind, VcKind::UnsupportedMir { kind, .. } if kind == "LiteralPairWidthUnresolved")
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    let router = test_router::deterministic_test_router();
    let results = router.verify_all(std::slice::from_ref(vc));
    let (_, result) = results.into_iter().next().expect("one verdict per VC");
    result
}

/// THE PROPERTY for an operation that fails on every call: exactly one row,
/// refuted, uncertified.
fn assert_one_refuted_uncertified(name: &str, rows: &[VerificationCondition]) {
    assert_eq!(
        rows.len(),
        1,
        "{name}: exactly ONE row, and no statement-lane duplicate beside it: {:#?}",
        rows.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
    let vc = &rows[0];
    let result = verdict(vc);
    assert!(
        matches!(result, VerificationResult::Failed { .. }),
        "{name}: the row must be REFUTED, the operation fails on every call. Got \
         {result:?}\nformula: {}",
        vc.formula.to_smtlib()
    );
    assert!(
        trust_certify::certify_vc(vc).is_none(),
        "{name}: a row stating a check that fails must not kernel-certify: {}",
        vc.formula.to_smtlib()
    );
}

fn assert_one_proved(name: &str, rows: &[VerificationCondition]) {
    assert_eq!(rows.len(), 1, "{name}: one honest row");
    let result = verdict(&rows[0]);
    assert!(
        matches!(result, VerificationResult::Proved { .. }),
        "{name}: the operation cannot fail; got {result:?}\nformula: {}",
        rows[0].formula.to_smtlib()
    );
}

fn int(width: u32) -> Ty {
    Ty::Int { width, signed: true }
}

#[test]
fn a_two_literal_unchecked_divrem_reads_int_min_at_the_destination_width() {
    // The intrinsics: no assert, so this row is each function's ONLY obligation.
    // Before: one row each, PROVED and kernel-certified, at operand types i64 (i128
    // for the dividend of `ud128`).
    for (name, width) in [("ud8", 8), ("ud16", 16), ("ud32", 32), ("ud128", 128), ("ur8", 8)] {
        let func = load(name);
        let rows = rows_of(&func, divrem_overflow);
        assert_one_refuted_uncertified(name, &rows);
        let VcKind::ArithmeticOverflow { operand_tys, .. } = &rows[0].kind else {
            unreachable!("filtered on the kind")
        };
        assert_eq!(
            operand_tys,
            &(int(width), int(width)),
            "{name}: the recorded operand types are the operation's, not the fabricated i64"
        );
        assert!(rows_of(&func, literal_pair_unknown).is_empty(), "{name}: resolved, no unknown");
    }
}

#[test]
fn a_checked_two_literal_divrem_keeps_one_refuted_row() {
    // `i8::MIN / -1`, `i32::MIN / -1`, `i16::MIN % -1`, `i128::MIN / -1`: each panics
    // on every call. Before: the assert lane's FAILED row plus the statement row,
    // PROVED and kernel-certified at i64.
    for name in ["cd8", "cd32", "cr16", "cd128"] {
        let func = load(name);
        assert_one_refuted_uncertified(name, &rows_of(&func, divrem_overflow));
    }
}

#[test]
fn an_unchecked_call_on_a_literal_pair_reads_the_destination_width() {
    // `i8::MAX.unchecked_add(1)` and `100i8.unchecked_mul(2)`. Before: PROVED,
    // kernel-certified, at operand types i64.
    //
    // No in-process backend decides an `UncheckedArithmeticOverflow` row (the router
    // answers "no backend can handle this VC"; `x.unchecked_add(1)` over a parameter
    // reads `unknown` on stage1-w25f), so the row is not REFUTED here. What is pinned
    // instead: it no longer certifies, its formula is GROUND and evaluates to true
    // (the violation holds on every call), and the same formula as an ordinary
    // `ArithmeticOverflow` row is refuted by ay.
    for name in ["ua8", "um8"] {
        let func = load(name);
        let rows = rows_of(&func, unchecked_overflow);
        assert_eq!(rows.len(), 1, "{name}: one unchecked-overflow row");
        let vc = &rows[0];
        let VcKind::UncheckedArithmeticOverflow { op, operand_tys } = &vc.kind else {
            unreachable!("filtered on the kind")
        };
        assert_eq!(operand_tys, &(int(8), int(8)), "{name}: recorded at the call's i8");
        assert!(
            trust_certify::certify_vc(vc).is_none(),
            "{name}: a violated precondition must not kernel-certify: {}",
            vc.formula.to_smtlib()
        );
        assert!(
            trust_router::violation_is_forced(&vc.formula),
            "{name}: the violation is ground and holds: {}",
            vc.formula.to_smtlib()
        );
        let mut as_overflow = vc.clone();
        as_overflow.kind = VcKind::ArithmeticOverflow { op: *op, operand_tys: operand_tys.clone() };
        let result = verdict(&as_overflow);
        assert!(
            matches!(result, VerificationResult::Failed { .. }),
            "{name}: ay refutes the same formula; got {result:?}"
        );
    }
}

#[test]
fn a_signed_literal_shift_amount_keeps_one_refuted_row() {
    // `x << 40` (u32), `x >> 64` (i64), `x << 8` (u8), `x << 64i32` (u64) and
    // `x << -1` (u32): each panics on every call. Before: a FAILED generic `overflow`
    // row plus a `shift:*` statement row, PROVED and kernel-certified.
    for name in ["shl_lit", "shr_lit", "shl_u8x", "shl_i32c", "shl_neg"] {
        let func = load(name);
        let rows = rows_of(&func, shift_check);
        assert_one_refuted_uncertified(name, &rows);
        assert!(
            matches!(rows[0].kind, VcKind::ShiftOverflow { .. }),
            "{name}: the binder now binds the literal cast source, so the surviving row \
             is the assert lane's real shift obligation, not the generic fall-through: {:?}",
            rows[0].kind
        );
    }
}

#[test]
fn the_safe_twins_keep_their_honest_rows() {
    // `x << 8` (u32): ONE proved row, where there were two copies of one proposition
    // (the generic `overflow` row and the self-guarded statement row).
    assert_one_proved("ok_shl", &rows_of(&load("ok_shl"), shift_check));
    // `100i8.unchecked_add(27)`: its one row is proved (and certifies) at `i8`.
    let rows = rows_of(&load("ok_ua8"), unchecked_overflow);
    assert_eq!(rows.len(), 1, "ok_ua8: one row");
    assert!(trust_certify::certify_vc(&rows[0]).is_some(), "ok_ua8: 127 fits i8, certified");
    // `100 / 7`: the direct suppression still refuses a cond comparing two DIFFERENT
    // literals (`Eq(const 7, const -1)`; its binder takes the left literal as the
    // constant side), so both rows stay, and both are TRUE: the statement row, now at
    // `i32`, states `100 != i32::MIN`.
    let rows = rows_of(&load("ok_cd32"), divrem_overflow);
    assert_eq!(rows.len(), 2, "ok_cd32: the assert lane's row and the statement row");
    for vc in &rows {
        let result = verdict(vc);
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "ok_cd32: `100 / 7` cannot overflow; got {result:?}\nformula: {}",
            vc.formula.to_smtlib()
        );
    }
}

#[test]
fn the_controls_keep_their_one_refuted_row() {
    // Already typed at the true width before the fix: i64 and isize coincide with the
    // fabricated width, a place carries its own, and an UNSIGNED literal amount is
    // compared directly (no cast temporary).
    for name in ["ctl_ud64", "ctl_ud_px", "ctl_ud_py", "ctl_cd64", "ctl_cdsize"] {
        let func = load(name);
        assert_one_refuted_uncertified(name, &rows_of(&func, divrem_overflow));
    }
    for name in ["ctl_shl_u8", "ctl_shl_u64", "ctl_shl_usize"] {
        let func = load(name);
        assert_one_refuted_uncertified(name, &rows_of(&func, shift_check));
    }
}

// ---------------------------------------------------------------------------
// FORGED ARMS: one field of a real artifact changed at a time.
// ---------------------------------------------------------------------------

/// `ud8` with its one statement's destination re-typed or re-placed.
fn ud8_with(mutate: impl FnOnce(&mut VerifiableFunction)) -> VerifiableFunction {
    let mut func = load("ud8");
    let Statement::Assign { place, rvalue: Rvalue::BinaryOp(BinOp::Div, _, _), .. } =
        &func.body.blocks[0].stmts[0]
    else {
        unreachable!("fixture drift: ud8 bb0[0] is the division")
    };
    assert!(place.local == 0 && place.projections.is_empty(), "fixture drift: ud8 writes _0");
    mutate(&mut func);
    func
}

#[test]
fn an_unresolvable_destination_is_an_unknown_row_never_a_dropped_one() {
    // A PROJECTED destination (`_0.0` of an `(i8, i8)`, a well-typed body): the width
    // cannot be read, so the division's only obligation becomes the
    // `LiteralPairWidthUnresolved` unknown row. Dropping it (`None`) would leave the
    // UB function with no obligation at all. RED under: the builder returning `None`.
    let func = ud8_with(|func| {
        func.body.locals[0].ty = Ty::Tuple(vec![int(8), int(8)]);
        func.body.return_ty = Ty::Tuple(vec![int(8), int(8)]);
        let Statement::Assign { place, .. } = &mut func.body.blocks[0].stmts[0] else {
            unreachable!()
        };
        place.projections.push(Projection::Field(0));
    });
    assert!(rows_of(&func, divrem_overflow).is_empty(), "no width-fabricated overflow row");
    assert_eq!(
        rows_of(&func, literal_pair_unknown).len(),
        1,
        "the obligation survives as ONE unknown row: {:#?}",
        trust_vcgen::generate_vcs(&func).iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );

    // A NON-INTEGER destination never reaches the builder: admission refuses the
    // ill-typed body (`MalformedTrustIr`), which is itself an unknown row, so the
    // function is not left without one either. (The builder's own refusal of a
    // non-integer or unsigned destination is pinned in `checked_vcs.rs`,
    // `literal_pair_width_tests`.)
    let func = ud8_with(|func| {
        func.body.locals[0].ty = Ty::Bool;
        func.body.return_ty = Ty::Bool;
    });
    let rows = trust_vcgen::generate_vcs(&func);
    assert!(rows_of(&func, divrem_overflow).is_empty(), "no width-fabricated overflow row");
    assert!(
        !rows.is_empty() && rows.iter().all(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "the ill-typed body keeps an unknown row: {:#?}",
        rows.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}

/// `shl_lit` (`_2 = Cast(const 40, u32); _3 = Lt(move _2, 32); assert -> bb1;
/// bb1: _0 = Shl(_1, const 40)`) with the cast source and/or the shift amount
/// replaced.
fn shl_lit_with(cast_source: i128, shift_amount: i128) -> VerifiableFunction {
    let mut func = load("shl_lit");
    let Statement::Assign { rvalue: Rvalue::Cast(src, _), .. } = &mut func.body.blocks[0].stmts[0]
    else {
        unreachable!("fixture drift: shl_lit bb0[0] is the amount cast")
    };
    assert!(matches!(src, Operand::Constant(ConstValue::Int(40))), "fixture drift: cast of 40");
    *src = Operand::Constant(ConstValue::Int(cast_source));
    let Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Shl, _, amount), .. } =
        &mut func.body.blocks[1].stmts[0]
    else {
        unreachable!("fixture drift: shl_lit bb1[0] is the shift")
    };
    assert!(matches!(amount, Operand::Constant(ConstValue::Int(40))), "fixture drift: << 40");
    *amount = Operand::Constant(ConstValue::Int(shift_amount));
    assert!(
        matches!(func.body.blocks[0].terminator, Terminator::Assert { .. }),
        "fixture drift: bb0 ends in the shift assert"
    );
    func
}

#[test]
fn a_cast_of_a_different_literal_does_not_bind() {
    // The assert checks `8 as u32 < 32` (passes) while the shift reads 40. The two
    // literals are different values, so the assert is not this shift's guard: both
    // rows stay, and the shift's own row is refuted.
    let func = shl_lit_with(8, 40);
    let rows = rows_of(&func, shift_check);
    assert_eq!(
        rows.len(),
        2,
        "both rows stay: {:#?}",
        rows.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
    assert!(
        rows.iter().any(|vc| matches!(verdict(vc), VerificationResult::Failed { .. })),
        "the shift by 40 is still refuted"
    );
}

#[test]
fn a_literal_outside_the_signed_amount_type_does_not_bind() {
    // `5_000_000_000` is no `i32`: the cast `as u32` truncates it to 705032704 and the
    // value argument does not apply, so the binder refuses and both rows stay.
    let func = shl_lit_with(5_000_000_000, 5_000_000_000);
    let rows = rows_of(&func, shift_check);
    assert_eq!(
        rows.len(),
        2,
        "both rows stay: {:#?}",
        rows.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}

#[test]
fn the_real_literal_identity_binds() {
    // The same mutation helper with the fixture's own values, so the two refusals
    // above are refusals of the VALUE, not of the mutation.
    let func = shl_lit_with(40, 40);
    assert_one_refuted_uncertified("shl_lit(40, 40)", &rows_of(&func, shift_check));
}
