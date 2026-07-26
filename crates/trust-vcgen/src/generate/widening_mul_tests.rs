//! Program 3, Phase D diagnosis: why does an unsigned widening `var * var`
//! (`(a as u16) * (b as u16)`) not reach a discharge?
//!
//! Top corner is `255 * 255 = 65025 <= u16::MAX`, so it cannot overflow for any
//! input — yet it lands `runtime-checked` on the BV path, where `certify_vc` has
//! no BV-mul reconstruction family and therefore cannot mint exact authority.

use super::{v2_build_overflow_vc_for_operands, v2_widening_bv_source};
use trust_types::{
    BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

/// `fn f(a: u8, b: u8) -> u16 { (a as u16) * (b as u16) }`
///
/// locals: 0 ret:u16 · 1 a:u8 (arg) · 2 b:u8 (arg) · 3 wa:u16 · 4 wb:u16
fn widening_mul_fn(src: Ty, dst: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: dst.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: src.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: src.clone(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: dst.clone(), name: Some("wa".into()) },
                LocalDecl { index: 4, ty: dst.clone(), name: Some("wb".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), dst.clone()),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(2)), dst.clone()),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: dst,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// DIAGNOSTIC: does the widening-source predicate recognise the cast temps?
/// If this fails, the corner discharge can never open and the reason is here.
#[test]
fn widening_source_is_recognised_for_both_cast_temps() {
    let f = widening_mul_fn(Ty::u8(), Ty::u16());
    assert_eq!(
        v2_widening_bv_source(&f, &Operand::Copy(Place::local(3)), 16),
        Some((8, false)),
        "`wa = a as u16` is a strict value-preserving widening from u8"
    );
    assert_eq!(
        v2_widening_bv_source(&f, &Operand::Copy(Place::local(4)), 16),
        Some((8, false)),
        "`wb = b as u16` likewise"
    );
}

/// RECORDS the shape this obligation has today, which is why it cannot certify:
/// an exact BV encoding (`BvUDiv(BvMul(BvZeroExt(..), BvZeroExt(..)))`) that the
/// solver PROVES but `certify_vc` has no reconstruction family for.
#[test]
fn widening_mul_vc_is_an_uncertifiable_bv_formula() {
    let f = widening_mul_fn(Ty::u8(), Ty::u16());
    let block = &f.body.blocks[0];
    let vc = v2_build_overflow_vc_for_operands(
        &f,
        block,
        BinOp::Mul,
        &Operand::Copy(Place::local(3)),
        &Operand::Copy(Place::local(4)),
        &SourceSpan::default(),
        None,
    );
    println!("widening mul VC formula = {:?}", vc.as_ref().map(|v| &v.formula));
    let f = vc.expect("a widening mul emits an obligation today").formula;
    let rendered = format!("{f:?}");
    assert!(
        rendered.contains("BvMul") && rendered.contains("BvZeroExt"),
        "the obligation is a BV mul over zero-extended operands — exact, solver-provable, \
         and NOT reconstructible by certify_vc, which is precisely the authority gap. \
         got: {rendered}"
    );
}

/// NEGATIVE / guardrail for any future corner discharge: a same-width cast is not a
/// value-preserving widening, so u16*u16 into u16 really can overflow and must keep
/// its obligation.
#[test]
fn same_width_mul_is_not_discharged() {
    let f = widening_mul_fn(Ty::u16(), Ty::u16());
    let block = &f.body.blocks[0];
    let vc = v2_build_overflow_vc_for_operands(
        &f,
        block,
        BinOp::Mul,
        &Operand::Copy(Place::local(3)),
        &Operand::Copy(Place::local(4)),
        &SourceSpan::default(),
        None,
    );
    assert!(
        vc.is_some(),
        "u16*u16 -> u16 overflows at 65535*2; suppressing it would be a false PROVE"
    );
}
