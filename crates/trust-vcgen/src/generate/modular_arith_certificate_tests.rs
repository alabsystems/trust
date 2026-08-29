// The compiler's MODULAR-arithmetic certificate: `intrinsics::wrapping_add`
// must NOT be charged a no-overflow obligation, and a plain `+` in the SAME
// shape must still be.
//
// Why the certificate exists at all. `rustc_mir_transform::lower_intrinsics`
// rewrites `intrinsics::wrapping_{add,sub,mul}` into a bare
// `Rvalue::BinaryOp(Add|Sub|Mul, ..)` — the very rvalue a source-level `+`
// lowers to once overflow checks are off. Measured with the shipped stage2
// `trustc` (`rustc 1.99.0-dev (ccf52b40c 2026-08-19)`), at `-Coverflow-checks=off`
// the extracted MIR for
//
//     pub fn plain_add(a: u32, b: u32) -> u32 { a + b }
//     pub fn wrap_add (a: u32, b: u32) -> u32 { intrinsics::wrapping_add(a, b) }
//
// is byte-identical: `BinaryOp("Add", Copy(_1), Copy(_2))` in both. So the
// wrapping identity CANNOT be recovered at the extraction seam, and Trust
// charged the modular operation a no-overflow obligation it can never discharge
// (3 of the 43 failing obligations in the `core::num` leaf slice —
// `docs/design/2026-08-20-core-slice-blocker-histogram.md` §2.1).
//
// The fix carries the identity from the pass that destroys it:
// `mir::Statement::trust_modular_arith` -> `trust_verify::trust_modular_arith_ops`
// -> `VcgenContext::with_modular_arith_ops` -> the skip pinned below.
//
// THE POINT OF THESE TESTS IS THE PAIR. Both functions below are the same
// rvalue at the same span; the ONLY difference is whether the compiler
// certified that statement as modular. If the two ever answer the same way, the
// distinction has collapsed and the fix is wrong in one direction or the other.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::{
    BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
};

use crate::VcgenContext;
use crate::generate::entry::generate_vcs_with_context;

const DEF_PATH: &str = "probe::add";

fn op_span() -> SourceSpan {
    SourceSpan { file: "probe.rs".into(), line_start: 4, col_start: 41, line_end: 4, col_end: 71 }
}

/// `fn add(a: u32, b: u32) -> u32 { <op> }` as a single bare `BinaryOp` — the
/// exact shape `LowerIntrinsics` leaves behind for `wrapping_add`, and the exact
/// shape a source `+` leaves behind under `-Coverflow-checks=off`.
fn bare_binop_fn(op: BinOp) -> VerifiableFunction {
    VerifiableFunction {
        name: "add".into(),
        def_path: DEF_PATH.into(),
        span: SourceSpan { file: "probe.rs".into(), ..SourceSpan::default() },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
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
                    span: op_span(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn unchecked_binop_fn(op: BinOp) -> VerifiableFunction {
    let mut func = bare_binop_fn(op);
    let Statement::Assign { rvalue, .. } = &mut func.body.blocks[0].stmts[0] else {
        unreachable!();
    };
    *rvalue = Rvalue::UncheckedBinaryOp(
        op,
        Operand::Copy(Place::local(1)),
        Operand::Copy(Place::local(2)),
    );
    func
}

fn overflow_obligations(func: &VerifiableFunction, context: &VcgenContext) -> usize {
    generate_vcs_with_context(func, context)
        .iter()
        .filter(|vc| {
            matches!(
                vc.kind,
                // Trust: BOTH spellings count (2026-08-24). `UncheckedBinaryOp`
                // modelling gave the UB-bearing `*Unchecked` form its OWN kind, and
                // this helper still filtered for the plain one — so
                // `modular_certificate_never_silences_unchecked_arithmetic` counted
                // 0 and read as "the certificate silenced the obligation" when the
                // obligation was in fact emitted under the new kind. Verified by
                // measurement, not assumed: with only the plain kind counted the
                // certified-unchecked case is 0, and with both it is 1.
                //
                // Counting BOTH is also the fail-closed direction for a test whose
                // whole purpose is "this obligation must not disappear".
                VcKind::ArithmeticOverflow { .. } | VcKind::UncheckedArithmeticOverflow { .. }
            )
        })
        .count()
}

/// The context a compiler that certified this exact `(span, op)` as modular
/// installs.
fn certified(op: BinOp) -> VcgenContext {
    let mut ops = FxHashSet::default();
    ops.insert((op_span(), op));
    VcgenContext::for_function(DEF_PATH).with_modular_arith_ops(ops)
}

#[test]
fn plain_binop_without_a_certificate_is_still_charged() {
    // DIRECTION 1 — the one that must never regress. No certificate (an
    // ordinary `a + b`, or any caller that is not the compiler): the
    // no-overflow obligation stands.
    for op in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
        let func = bare_binop_fn(op);
        let empty = VcgenContext::for_function(DEF_PATH);
        assert_eq!(
            overflow_obligations(&func, &empty),
            1,
            "an uncertified bare {op:?} must keep its no-overflow obligation"
        );
    }
}

#[test]
fn certified_modular_binop_is_not_charged() {
    // DIRECTION 2 — the fix. Same rvalue, same span; the compiler says
    // `LowerIntrinsics` produced it from `intrinsics::wrapping_*`, so it cannot
    // overflow and the obligation is FALSE.
    for op in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
        let func = bare_binop_fn(op);
        assert_eq!(
            overflow_obligations(&func, &certified(op)),
            0,
            "a compiler-certified modular {op:?} must not be charged a no-overflow obligation"
        );
    }
}

#[test]
fn modular_certificate_never_silences_unchecked_arithmetic() {
    // The certificate authenticates only rustc's plain `BinaryOp` spelling
    // produced from `wrapping_*`. A forged/stale same-span certificate must
    // not turn overflow of the distinct UB-bearing `*Unchecked` spelling into
    // an obligation-free operation.
    for op in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
        let func = unchecked_binop_fn(op);
        assert_eq!(
            overflow_obligations(&func, &certified(op)),
            1,
            "a modular certificate must not silence {op:?}Unchecked"
        );
    }
}

#[test]
fn certificate_for_a_different_operation_does_not_transfer() {
    // The key is `(span, op)`, not the span alone: a certificate minted for the
    // `Add` at this span must not silence a `Sub` there. (It cannot happen in
    // practice — one statement, one op — but a span-only key would be the easy
    // wrong implementation, and it would silence real obligations.)
    let func = bare_binop_fn(BinOp::Sub);
    assert_eq!(
        overflow_obligations(&func, &certified(BinOp::Add)),
        1,
        "an `Add` certificate must not silence a `Sub` at the same span"
    );
}

#[test]
fn certificate_for_a_different_span_does_not_transfer() {
    let mut ops = FxHashSet::default();
    ops.insert((SourceSpan { file: "probe.rs".into(), line_start: 9, ..op_span() }, BinOp::Add));
    let context = VcgenContext::for_function(DEF_PATH).with_modular_arith_ops(ops);
    assert_eq!(
        overflow_obligations(&bare_binop_fn(BinOp::Add), &context),
        1,
        "a certificate at another span must not silence this operation"
    );
}

#[test]
fn certificate_owned_by_another_function_does_not_transfer() {
    // Every deep policy read is owner-checked against `func.def_path`; a
    // certificate minted while verifying some OTHER function must not lend this
    // one its authority. This is the same fail-closed discipline
    // `single_writer_hint_for` / `contract_panic_annotations_for` use.
    let mut ops = FxHashSet::default();
    ops.insert((op_span(), BinOp::Add));
    let foreign = VcgenContext::for_function("some::other::function").with_modular_arith_ops(ops);
    assert_eq!(
        overflow_obligations(&bare_binop_fn(BinOp::Add), &foreign),
        1,
        "a certificate owned by another function must not silence this one's obligation"
    );
}

#[test]
fn certificate_does_not_reach_the_assert_guarded_checked_form() {
    // A source-level `+` under overflow checks ON extracts as
    // `CheckedBinaryOp` + `Assert{Overflow}` — a DIFFERENT lane, and the shape
    // in which the overwhelming majority of real `+` obligations are minted.
    // The certificate is scoped to the direct bare-binop arm, so even an
    // (impossible) span collision with a checked op leaves that obligation
    // alone. This is the guard against a future "just key on the span"
    // simplification silencing ordinary arithmetic.
    let mut func = bare_binop_fn(BinOp::Add);
    func.body.locals.push(LocalDecl {
        index: 3,
        ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
        name: None,
    });
    func.body.blocks[0].stmts[0] = Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::CheckedBinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
        span: op_span(),
    };
    func.body.blocks[0].terminator = Terminator::Assert {
        cond: Operand::Move(Place {
            local: 3,
            projections: vec![trust_types::Projection::Field(1)],
        }),
        expected: false,
        msg: trust_types::AssertMessage::Overflow(BinOp::Add),
        target: BlockId(1),
        span: op_span(),
        unwind: trust_types::UnwindEdge::Unreachable,
    };
    func.body.blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place {
                local: 3,
                projections: vec![trust_types::Projection::Field(0)],
            })),
            span: op_span(),
        }],
        terminator: Terminator::Return,
    });
    assert_eq!(
        overflow_obligations(&func, &certified(BinOp::Add)),
        1,
        "the assert-guarded checked form keeps its obligation regardless of the certificate"
    );
}
