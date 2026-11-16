// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The bridge halves of three producer lowering gaps, through the PUBLIC lowering
//! API, on hand-built bodies whose shape is exactly what trust-mir-extract emits
//! (`trust-mir-extract/tests/producer_lowering_gaps.rs` compiles real Rust to the
//! same shapes and lowers them through this bridge):
//!
//! * T2 — a direct call with NO return target whose destination is `!`-typed
//!   (`std::thread::ThreadId::new`'s `exhausted()`) lowers as `call; unreachable`;
//! * T3 — `Rvalue::UncheckedBinaryOp(Shl | Shr, ..)` — MIR `ShlUnchecked` /
//!   `ShrUnchecked` (`core::ptr::align_offset::<u8>`) — lowers as the shift behind
//!   its asserted amount-range precondition;
//! * T4 — the `TRUST_TRANSMUTE_INTO_VALID_RANGE_KIND` sentinel — a transmute into
//!   a pattern type (`FileDesc::from_raw_fd` through `I32NotAllOnes::new`) — lowers
//!   as the identity behind its asserted valid range.
//!
//! Every row lowers, VALIDATES, and the T3/T4 rows then EXECUTE on the reference
//! interpreter, because the claim is that the lowered IR means what the MIR means
//! — the value on the defined domain, and a failed `assert` (the charged UB
//! precondition) outside it — not merely that a module came back `Ok`.

use trust_ir::inst::{BinOp as TrustIrBinOp, ICmpOp, Inst};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty as TrustIrTy;
use trust_ir::{Constant, InstrNode, Module};
use trust_ir_bridge::{BridgeError, lower_to_trust_ir, lower_to_trust_ir_functions};
use trust_types::{
    BasicBlock as TrustBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
    Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

/// `trust_types::TRUST_TRANSMUTE_INTO_VALID_RANGE_KIND`, spelled out: the sentinel's
/// kind is a cross-crate contract between the extractor and the bridge, so the
/// tests pin its exact spelling rather than re-reading the constant (and so they
/// also compile, and fail meaningfully, against a tree that predates it).
const VALID_RANGE_SENTINEL: &str = "CastKind::Transmute(valid-range)";

fn one_block_function(
    name: &str,
    locals: Vec<Ty>,
    arg_count: usize,
    rvalue: Rvalue,
) -> VerifiableFunction {
    let return_ty = locals[0].clone();
    VerifiableFunction {
        name: name.into(),
        def_path: format!("producer_gaps::{name}"),
        span: Default::default(),
        body: VerifiableBody {
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue,
                    span: Default::default(),
                }],
                terminator: Terminator::Return,
            }],
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

fn lowered_valid(func: &VerifiableFunction) -> Module {
    let module = lower_to_trust_ir(func)
        .unwrap_or_else(|error| panic!("`{}` must lower, got {error:?}", func.name));
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "`{}` lowered to an invalid module: {errors:?}\n{module}",
        func.name
    );
    module
}

fn run(module: &Module, args: Vec<InterpretValue>) -> Result<i128, InterpretErrorCode> {
    match Interpreter::with_module(module).execute_func(module.functions[0].id, args) {
        Ok(outcome) => {
            let value = &outcome.returns[0];
            let bits = value.as_int().unwrap_or_else(|| panic!("an integer result, got {value:?}"));
            let signed = matches!(
                value.ty,
                TrustIrTy::I8 | TrustIrTy::I16 | TrustIrTy::I32 | TrustIrTy::I64 | TrustIrTy::I128
            );
            Ok(if signed {
                bits.as_signed()
            } else {
                i128::try_from(bits.as_unsigned()).expect("fixture results fit i128")
            })
        }
        Err(error) => Err(error.code),
    }
}

fn int(ty: TrustIrTy, value: i128) -> InterpretValue {
    InterpretValue::int(ty, value).expect("in-range interpreter integer")
}

fn entry_insts(module: &Module) -> Vec<&Inst> {
    module.functions[0].blocks[0].body.iter().map(|node| &node.inst).collect()
}

/// `unchecked_shl::<u8, u32>(x, n)`: the precondition is decided on the AMOUNT at
/// its own type (`n <u 8` at `u32`), asserted with `ShiftInRange`, and only then
/// is the amount narrowed for the trust-ir `Shl`. Red before T3: the arm fell to
/// the arithmetic `UncheckedBinaryOp` lowering and refused (`Shl` has no
/// `Inst::Overflow` form).
#[test]
fn unchecked_shl_asserts_the_amount_range_at_the_amount_type_then_shifts() {
    let func = one_block_function(
        "shl_u8",
        vec![Ty::u8(), Ty::u8(), Ty::u32()],
        2,
        Rvalue::UncheckedBinaryOp(
            BinOp::Shl,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
    );
    let module = lowered_valid(&func);
    println!("{module}");
    let insts = entry_insts(&module);
    let cmp = insts
        .iter()
        .position(|inst| matches!(inst, Inst::ICmp { op: ICmpOp::Ult, ty: TrustIrTy::U32, .. }))
        .unwrap_or_else(|| panic!("an `icmp ult` at the amount's u32 type: {insts:?}"));
    let assert = insts
        .iter()
        .position(|inst| matches!(inst, Inst::Assert { .. }))
        .unwrap_or_else(|| panic!("the precondition assert: {insts:?}"));
    let shift = insts
        .iter()
        .position(|inst| {
            matches!(inst, Inst::BinOp { op: TrustIrBinOp::Shl, ty: TrustIrTy::U8, .. })
        })
        .unwrap_or_else(|| panic!("the u8 `shl`: {insts:?}"));
    assert!(cmp < assert && assert < shift, "compare, then assert, then shift: {insts:?}");
    assert!(
        module.functions[0].blocks[0].body[assert].proofs.contains(&ProofAnnotation::ShiftInRange),
        "the precondition is the shift-amount-in-range check"
    );
    // The value on the defined domain, and the charged precondition outside it:
    // `256` is out of range although it truncates to an in-range `0` at `u8`.
    assert_eq!(run(&module, vec![int(TrustIrTy::U8, 1), int(TrustIrTy::U32, 3)]), Ok(8));
    assert_eq!(run(&module, vec![int(TrustIrTy::U8, 0x81), int(TrustIrTy::U32, 7)]), Ok(0x80));
    for amount in [8, 9, 256] {
        assert_eq!(
            run(&module, vec![int(TrustIrTy::U8, 1), int(TrustIrTy::U32, amount)]),
            Err(InterpretErrorCode::Panic),
            "amount {amount} is outside 0..8 and must fail the precondition"
        );
    }
}

/// `unchecked_shr::<i32, i8>(x, n)`: a SIGNED value shifts arithmetically, and a
/// SIGNED amount owes `0 <= n && n < 32` (MIR: "UB if the RHS >= LHS::BITS or
/// RHS < 0").
#[test]
fn unchecked_shr_of_a_signed_value_by_a_signed_amount_owes_both_bounds() {
    let func = one_block_function(
        "shr_i32",
        vec![Ty::i32(), Ty::i32(), Ty::Int { width: 8, signed: true }],
        2,
        Rvalue::UncheckedBinaryOp(
            BinOp::Shr,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
    );
    let module = lowered_valid(&func);
    println!("{module}");
    let insts = entry_insts(&module);
    assert!(
        insts.iter().any(|i| matches!(i, Inst::ICmp { op: ICmpOp::Sge, ty: TrustIrTy::I8, .. }))
    );
    assert!(
        insts.iter().any(|i| matches!(i, Inst::ICmp { op: ICmpOp::Slt, ty: TrustIrTy::I8, .. }))
    );
    assert!(insts.iter().any(|i| matches!(i, Inst::BinOp { op: TrustIrBinOp::AShr, .. })));
    assert_eq!(run(&module, vec![int(TrustIrTy::I32, -64), int(TrustIrTy::I8, 3)]), Ok(-8));
    assert_eq!(run(&module, vec![int(TrustIrTy::I32, -1), int(TrustIrTy::I8, 31)]), Ok(-1));
    for amount in [-1, 32, 127] {
        assert_eq!(
            run(&module, vec![int(TrustIrTy::I32, 1), int(TrustIrTy::I8, amount)]),
            Err(InterpretErrorCode::Panic),
            "amount {amount} is outside 0..32 and must fail the precondition"
        );
    }
}

/// An `i8` amount on a 128-bit value: every non-negative `i8` is below 128, so
/// the precondition is exactly `0 <= n` — and 128 is not an `i8` value to compare
/// against, so no upper bound is emitted at all.
#[test]
fn a_narrow_signed_amount_on_a_wide_value_owes_only_non_negativity() {
    let func = one_block_function(
        "shl_i128",
        vec![
            Ty::Int { width: 128, signed: true },
            Ty::Int { width: 128, signed: true },
            Ty::Int { width: 8, signed: true },
        ],
        2,
        Rvalue::UncheckedBinaryOp(
            BinOp::Shl,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
    );
    let module = lowered_valid(&func);
    let insts = entry_insts(&module);
    assert!(
        insts.iter().any(|i| matches!(i, Inst::ICmp { op: ICmpOp::Sge, ty: TrustIrTy::I8, .. }))
    );
    assert!(!insts.iter().any(|i| matches!(i, Inst::ICmp { op: ICmpOp::Slt, .. })), "{insts:?}");
    assert_eq!(run(&module, vec![int(TrustIrTy::I128, 1), int(TrustIrTy::I8, 127)]), Ok(1 << 127));
    assert_eq!(
        run(&module, vec![int(TrustIrTy::I128, 1), int(TrustIrTy::I8, -1)]),
        Err(InterpretErrorCode::Panic)
    );
}

/// The arithmetic unchecked ops keep their own lowering (the control): an
/// `unchecked_add` still emits `Inst::Overflow` and asserts its flag false.
#[test]
fn unchecked_add_keeps_its_overflow_lowering() {
    let func = one_block_function(
        "add_u8",
        vec![Ty::u8(), Ty::u8(), Ty::u8()],
        2,
        Rvalue::UncheckedBinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
    );
    let module = lowered_valid(&func);
    assert!(entry_insts(&module).iter().any(|i| matches!(i, Inst::Overflow { .. })));
}

fn valid_range_sentinel(value: Operand, start: ConstValue, end: ConstValue) -> Rvalue {
    Rvalue::Unsupported {
        kind: VALID_RANGE_SENTINEL.into(),
        detail: "fixture".into(),
        operands: vec![value, Operand::Constant(start), Operand::Constant(end)],
    }
}

/// `transmute::<i32, pattern_type!(i32 is ..-1 | 0..)>(fd)` — `I32NotAllOnes::new`,
/// the `ValidRawFd` behind `FileDesc::from_raw_fd`. rustc's layout gives the
/// WRAPPING range `0..=-2`, so membership is `fd >= 0 || fd <= -2`: every `i32`
/// but `-1`. The value is the identity. Red before T4: the sentinel fell to the
/// generic `Rvalue::Unsupported` refusal.
#[test]
fn a_transmute_into_a_wrapping_pattern_type_is_the_identity_under_its_asserted_range() {
    let func = one_block_function(
        "not_all_ones",
        vec![Ty::i32(), Ty::i32()],
        1,
        valid_range_sentinel(
            Operand::Copy(Place::local(1)),
            ConstValue::Int(0),
            ConstValue::Int(-2),
        ),
    );
    let module = lowered_valid(&func);
    println!("{module}");
    let insts = entry_insts(&module);
    assert!(
        insts.iter().any(|i| matches!(i, Inst::ICmp { op: ICmpOp::Sge, ty: TrustIrTy::I32, .. }))
    );
    assert!(
        insts.iter().any(|i| matches!(i, Inst::ICmp { op: ICmpOp::Sle, ty: TrustIrTy::I32, .. }))
    );
    assert!(insts.iter().any(|i| matches!(i, Inst::Assert { .. })));
    for fd in [0, 3, i128::from(i32::MAX), -2, i128::from(i32::MIN)] {
        assert_eq!(run(&module, vec![int(TrustIrTy::I32, fd)]), Ok(fd), "fd {fd} is valid");
    }
    assert_eq!(
        run(&module, vec![int(TrustIrTy::I32, -1)]),
        Err(InterpretErrorCode::Panic),
        "-1 is the one value outside the pattern"
    );
}

/// A non-wrapping unsigned range (`u32 is 1..`, `NonZeroU32Inner`): membership is
/// `1 <= v && v <= u32::MAX`, i.e. `v != 0`.
#[test]
fn a_transmute_into_an_interval_pattern_type_asserts_the_interval() {
    let func = one_block_function(
        "non_zero",
        vec![Ty::u32(), Ty::u32()],
        1,
        valid_range_sentinel(
            Operand::Copy(Place::local(1)),
            ConstValue::Uint(1, 32),
            ConstValue::Uint(u128::from(u32::MAX), 32),
        ),
    );
    let module = lowered_valid(&func);
    let insts = entry_insts(&module);
    assert!(
        insts.iter().any(|i| matches!(i, Inst::ICmp { op: ICmpOp::Uge, ty: TrustIrTy::U32, .. }))
    );
    assert_eq!(run(&module, vec![int(TrustIrTy::U32, 1)]), Ok(1));
    assert_eq!(
        run(&module, vec![int(TrustIrTy::U32, i128::from(u32::MAX))]),
        Ok(i128::from(u32::MAX))
    );
    assert_eq!(run(&module, vec![int(TrustIrTy::U32, 0)]), Err(InterpretErrorCode::Panic));
}

/// A malformed sentinel is refused by name, never lowered on a guess: bounds of
/// the wrong signedness, a bound that is not a value of the type, and a missing
/// operand each fail closed.
#[test]
fn a_malformed_valid_range_sentinel_is_refused() {
    let cases = [
        valid_range_sentinel(
            Operand::Copy(Place::local(1)),
            ConstValue::Uint(0, 32),
            ConstValue::Uint(5, 32),
        ),
        valid_range_sentinel(
            Operand::Copy(Place::local(1)),
            ConstValue::Int(0),
            ConstValue::Int(1 << 40),
        ),
        Rvalue::Unsupported {
            kind: VALID_RANGE_SENTINEL.into(),
            detail: "fixture".into(),
            operands: vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Int(0))],
        },
    ];
    for rvalue in cases {
        let func = one_block_function("malformed", vec![Ty::i32(), Ty::i32()], 1, rvalue.clone());
        match lower_to_trust_ir(&func) {
            Err(BridgeError::UnsupportedOp(detail)) => {
                assert!(detail.contains("malformed"), "{detail}");
            }
            other => panic!("expected a named refusal for {rvalue:?}, got {other:?}"),
        }
    }
}

// ---------------------------------------------------------------------------
// T2 — a direct call with no return target and a `!`-typed destination.
// ---------------------------------------------------------------------------

/// `mycrate::probe`: one block whose terminator calls `callee` with NO
/// normal-return target, writing rustc's `!`-typed destination local, under
/// `unwind` — the shape the extractor emits for `exhausted()` on rustc's
/// never-type fact (`direct_callee_returns_never`).
fn never_call_body(callee: &str, unwind: UnwindEdge) -> VerifiableFunction {
    VerifiableFunction {
        name: "probe".into(),
        def_path: "mycrate::probe".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Never, name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: None,
                    is_foreign: false,
                    func: callee.to_string(),
                    args: vec![],
                    dest: Place::local(1),
                    target: None,
                    atomic: None,
                    span: Default::default(),
                },
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `pub fn never_returns() -> !` as a BUNDLED callee (a body that never returns).
fn bundled_never_callee() -> VerifiableFunction {
    VerifiableFunction {
        name: "never_returns".into(),
        def_path: "mycrate::never_returns".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Never, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(0)),
            }],
            arg_count: 0,
            return_ty: Ty::Never,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn validated(result: Result<Module, BridgeError>, what: &str) -> Module {
    let module = result.unwrap_or_else(|error| panic!("{what} must lower, got {error:?}"));
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{what} lowered to an invalid module: {errors:?}\n{module}");
    println!("==== {what}\n{module}");
    module
}

/// The tail every never-typed call site ends with: `%c = const false; assume %c;
/// unreachable`. The `Assume` is the never-type fact in the IR's own semantics
/// (control does not continue past a `!`-typed call); the `Unreachable` is the
/// charge that point carries. Returns the instructions BEFORE the tail, so a row
/// can pin what precedes it (the call, or the absent-callee marker).
fn before_never_continues_tail<'m>(body: &'m [InstrNode], what: &str) -> &'m [InstrNode] {
    let n = body.len();
    assert!(n >= 3, "{what}: a never-typed call site needs its three-node tail: {body:?}");
    let false_const =
        match &body[n - 3] {
            InstrNode {
                inst: Inst::Const { value: Constant::Bool(false), .. }, results, ..
            } if results.len() == 1 => results[0],
            other => panic!("{what}: expected `const false` third from the end, got {other:?}"),
        };
    match &body[n - 2].inst {
        Inst::Assume { cond } => assert_eq!(
            *cond, false_const,
            "{what}: the `Assume` must read the `false` constant, not some other value"
        ),
        other => panic!("{what}: expected `assume` second from the end, got {other:?}"),
    }
    assert!(matches!(body[n - 1].inst, Inst::Unreachable), "{what}: {body:?}");
    &body[..n - 3]
}

/// With the callee BUNDLED, every nounwind spelling lowers to a real
/// `Inst::Call` of it followed by the never-continues tail
/// (`assume false; unreachable`) — the call is followed (it is no panic/UB/abort
/// halt) and the `!` result type licenses the block's end. Red before T2: the
/// bridge's terminator tripwire refused each one by name.
#[test]
fn a_nounwind_never_typed_call_to_a_bundled_callee_lowers_as_call_then_unreachable() {
    for unwind in [UnwindEdge::Unreachable, UnwindEdge::Continue, UnwindEdge::Terminate] {
        let funcs =
            [never_call_body("mycrate::never_returns", unwind.clone()), bundled_never_callee()];
        let module = validated(
            lower_to_trust_ir_functions("never_module", &funcs),
            &format!("call of a bundled `-> !` callee ({unwind:?})"),
        );
        let callee_id = module
            .functions
            .iter()
            .find(|f| f.name.ends_with("never_returns"))
            .expect("the bundled callee")
            .id;
        let probe = module
            .functions
            .iter()
            .find(|f| f.name.ends_with("probe"))
            .expect("the caller is a module function");
        let what = format!("bundled `-> !` callee ({unwind:?})");
        match before_never_continues_tail(&probe.blocks[0].body, &what) {
            [.., InstrNode { inst: Inst::Call { callee, args }, .. }] => {
                assert_eq!(*callee, callee_id, "{unwind:?}: the call names the callee");
                assert!(args.is_empty());
            }
            other => {
                panic!("{unwind:?}: expected `.., call @never_returns(), <tail>`, got {other:?}")
            }
        }
    }
}

/// With the callee ABSENT, the absent-callee arm keeps its audited may-panic
/// marker (`Assert(false)` + `NoPanic`, plus the honest `PanicFreedom`
/// obligation) and the block then ends in the never-continues tail instead of
/// being refused. The marker PRECEDES the tail's `Assume(false)`, so the charge
/// is not pruned by it. `std::process::exit` is the measured instance of the shape.
#[test]
fn a_nounwind_never_typed_call_to_an_absent_callee_ends_behind_its_may_panic_marker() {
    for callee in ["mycrate::never_returns", "std::process::exit"] {
        let module = validated(
            lower_to_trust_ir(&never_call_body(callee, UnwindEdge::Unreachable)),
            &format!("call of an absent `-> !` callee `{callee}`"),
        );
        let body = &module.functions[0].blocks[0].body;
        let head = before_never_continues_tail(body, &format!("absent `{callee}`"));
        assert!(
            head.last().is_some_and(|marker| matches!(marker.inst, Inst::Assert { .. })
                && marker.proofs.contains(&ProofAnnotation::NoPanic)),
            "`{callee}`: the may-panic marker precedes the never-continues tail: {body:?}"
        );
        assert!(
            module.proof_obligations.iter().any(|o| o.description.contains(callee)),
            "`{callee}`: the absent-callee PanicFreedom obligation is still charged"
        );
    }
}
