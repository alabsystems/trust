// trust_ir_gate_bool_param.rs — WS7.13: the IN-COMPILER proven-output gate
// (`verify_trust_ir_output_preserved`) models a `bool` PARAMETER under the
// caller-owed zero-extension precondition.
//
// PROVENANCE (F-114, scout-f1.8 "bool ABI"). `signature_reg_width` refused
// `Ty::Bool` in parameter position outright, recording that an unconstrained
// 32-bit model of it had "fabricated six Refuted verdicts once already" — the
// `<bool as AsPrimitive<T>>::as_` functions of the 68-module corpus. A bool
// RETURN was already admitted (the callee owes the `Zext`); a bool PARAMETER
// is the caller's promise, which the gate cannot see any caller keep.
//
// WHAT THE FIX MAY NOT BE. The precondition is on the WHOLE extension width
// the target ABI makes the caller owe — on Apple AArch64 the caller extends a
// small argument to 32 bits, so it is `W{k}[31:1] == 0`, never `[7:1]`: a
// `[7:1]` precondition would leave bits 31:8 free, and emitted code that tests
// the whole `w` register (`cbz w0`) would be "refuted" with bit 0 clear and
// bit 8 set — the same fabricated-Refuted class. It is an AMBIENT assumption
// over the shared input variable both sides read, never a spec-side-only fact;
// the vacuity firewall covers it; it caps the verdict at `AyValidated`; and it
// appears in the obligation's assumption list (`ambient_pre`), not only in the
// grade. Without an attested cross-check, with an extension other than `Zext`,
// or on a target that makes no caller-side promise, the result stays `Unknown`
// by name.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(all(feature = "ay-proofs", feature = "test-hooks"))]

use trust_cg_bridge::codegen_backend::{
    BridgeOptimizationLevel, TrustCgCodegenBackend, TrustCgTargetArch,
};
use trust_cg_bridge::module_to_lir::lower_module_to_lir;
use trust_cg_bridge::verify_output::{OutputVerdict, ProvenEvidence};
use trust_cg_bridge::verify_output_trust_ir::{
    TrustIrGateSource, trust_ir_function_semantics, trust_ir_function_semantics_with,
    trust_ir_gate_obligation, verify_trust_ir_bytes, verify_trust_ir_output_preserved,
    verify_trust_ir_output_preserved_with_lowering,
};
use trust_cg_bridge::{AbiArgExtension, AbiParamExtensions, AbiPassModeCrossCheck};
use trust_ir::inst::{BinOp, CastOp, ICmpOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module, Producer, Ty};
use trust_types::Formula;

fn backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
        .with_optimization_level(BridgeOptimizationLevel::O0)
}

/// The cross-check the in-tree F1 frontend mints on Apple AArch64 for a
/// signature whose parameters carry the given extensions.
fn darwin_cross_check(per_param: &[Option<AbiArgExtension>]) -> AbiPassModeCrossCheck {
    AbiPassModeCrossCheck::attested_by("test: rustc FnAbi arg_ext facts on aarch64-apple-darwin")
        .with_param_extensions(AbiParamExtensions {
            per_param: per_param.to_vec(),
            caller_extends_to_bits: Some(32),
        })
}

fn source(
    module: Module,
    symbol: &str,
    cross_check: Option<AbiPassModeCrossCheck>,
) -> TrustIrGateSource {
    TrustIrGateSource {
        abi_cross_check: cross_check,
        symbol: symbol.to_string(),
        module: module.into(),
        func_id: FuncId::new(0),
    }
}

// ===========================================================================
// The positive fixture: `fn f(b: bool, x: u32) -> u32 { if b { x } else { 0 } }`
// ===========================================================================

/// The roadmap's positive fixture, spelled as rustc's trust-ir producer spells
/// an `if`: a `CondBr` on the bool parameter into two return blocks.
fn if_b_then_x_else_0() -> Module {
    let mut module = Module::new("bool_param");
    module.func_types.push(FuncTy {
        params: vec![Ty::Bool, Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut f = IrFunction::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
    f.producer = Some(Producer::TRust);
    let (b, x, zero) = (ValueId::new(0), ValueId::new(1), ValueId::new(2));

    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((b, Ty::Bool));
    bb0.params.push((x, Ty::U32));
    bb0.body.push(InstrNode::new(Inst::CondBr {
        cond: b,
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    }));

    let mut bb1 = Block::new(BlockId::new(1));
    bb1.body.push(InstrNode::new(Inst::Return { values: vec![x] }));

    let mut bb2 = Block::new(BlockId::new(2));
    bb2.body.push(
        InstrNode::new(Inst::Const { ty: Ty::U32, value: Constant::Int(0) }).with_result(zero),
    );
    bb2.body.push(InstrNode::new(Inst::Return { values: vec![zero] }));

    f.blocks.push(bb0);
    f.blocks.push(bb1);
    f.blocks.push(bb2);
    module.functions.push(f);
    module
}

fn bool_u32_cross_check() -> AbiPassModeCrossCheck {
    darwin_cross_check(&[Some(AbiArgExtension::Zext), Some(AbiArgExtension::None)])
}

/// POSITIVE: the fixture is validated (grade `AyValidated`) under the attested
/// cross-check, and the bytes it was validated over are shipped.
#[test]
fn bool_param_if_is_validated_under_the_attested_zext_precondition() {
    let subject = source(if_b_then_x_else_0(), "f", Some(bool_u32_cross_check()));
    let (verdict, obj) = verify_trust_ir_output_preserved(&subject, &backend());
    assert!(
        matches!(verdict, OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated }),
        "the bool-parameter fixture must be VALIDATED (ay, under the ambient caller \
         precondition) — never kernel-PROVED, never Refuted, never Unknown: {verdict:?}"
    );
    assert!(verdict.kernel_proofs().is_empty(), "an ambient precondition caps the kernel grade");
    assert!(
        obj.is_some(),
        "a validated function must ship the bytes the verdict was computed over"
    );
}

/// THE ASSUMPTION IS IN THE CERTIFICATE, NOT ONLY IN THE GRADE. The
/// obligation's `ambient_pre` carries `X0[31:1] == 0` — the WHOLE caller-owed
/// extension width — and the spec value reads bit 0 of the same register.
#[test]
fn precondition_is_the_whole_w_register_and_sits_in_the_assumption_list() {
    let module = if_b_then_x_else_0();
    let cross_check = bool_u32_cross_check();
    let spec = trust_ir_function_semantics_with(&module, FuncId::new(0), Some(&cross_check))
        .expect("an attested bool parameter is inside the modeled fragment");
    assert_eq!(spec.out_width, 32);
    let expected = Formula::Eq(
        Box::new(Formula::BvExtract {
            inner: Box::new(Formula::Var("X0".into(), trust_types::Sort::BitVec(64))),
            high: 31,
            low: 1,
        }),
        Box::new(Formula::BitVec { value: 0, width: 31 }),
    );
    assert_eq!(
        spec.ambient_pre,
        vec![expected.clone()],
        "exactly one ambient: the caller-owed zero-extension of W0 above bit 0"
    );
    let rendered = format!("{:?}", spec.value);
    assert!(
        rendered.contains("high: 0, low: 0"),
        "the spec value must read BIT 0 of the shared input register: {rendered}"
    );

    // The same list reaches the obligation the discharge step acts on.
    let subject = source(module, "f", Some(cross_check));
    let (_verdict, obj) = verify_trust_ir_output_preserved(&subject, &backend());
    let obligation =
        trust_ir_gate_obligation(&subject, &obj.expect("bytes"), TrustCgTargetArch::AArch64)
            .expect("obligation");
    assert_eq!(obligation.ambient_pre, vec![expected], "the certificate's assumption list");
}

// ===========================================================================
// Negative twins: one missing fact each, refused BY NAME as `Unknown`
// ===========================================================================

fn assert_unknown_naming(verdict: &OutputVerdict, needle: &str) {
    match verdict {
        OutputVerdict::Unknown { reason } => {
            assert!(reason.contains("`bool` in PARAMETER position"), "{reason}");
            assert!(reason.contains(needle), "expected `{needle}` in: {reason}");
            assert!(reason.contains("fail-closed"), "{reason}");
        }
        other => panic!("expected Unknown naming `{needle}`, got {other:?}"),
    }
}

/// NEGATIVE TWIN: the same fixture with NO cross-check gives `Unknown`.
#[test]
fn bool_param_without_cross_check_is_unknown() {
    let subject = source(if_b_then_x_else_0(), "f", None);
    let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
    assert_unknown_naming(&verdict, "no ABI pass-mode cross-check is attached");
    // The 2-argument semantics entry point carries no cross-check either.
    let err = trust_ir_function_semantics(&if_b_then_x_else_0(), FuncId::new(0))
        .expect_err("no cross-check, no bool parameter");
    assert!(err.contains("no ABI pass-mode cross-check is attached"), "{err}");
}

/// A cross-check WITHOUT extension facts (the pre-WS7.13 token) admits nothing.
#[test]
fn bool_param_with_a_token_that_records_no_extensions_is_unknown() {
    let token = AbiPassModeCrossCheck::attested_by("test: pre-WS7.13 token");
    let subject = source(if_b_then_x_else_0(), "f", Some(token));
    let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
    assert_unknown_naming(&verdict, "records no parameter-extension facts");
}

/// An `arg_ext` other than `Zext` on the slot admits nothing.
#[test]
fn bool_param_with_arg_ext_none_is_unknown() {
    let cross_check =
        darwin_cross_check(&[Some(AbiArgExtension::None), Some(AbiArgExtension::None)]);
    let subject = source(if_b_then_x_else_0(), "f", Some(cross_check));
    let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
    assert_unknown_naming(&verdict, "records `arg_ext: None` for this slot, not `Zext`");

    let cross_check =
        darwin_cross_check(&[Some(AbiArgExtension::Sext), Some(AbiArgExtension::None)]);
    let subject = source(if_b_then_x_else_0(), "f", Some(cross_check));
    let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
    assert_unknown_naming(&verdict, "records `arg_ext: Sext` for this slot, not `Zext`");
}

/// An UNRECORDED slot (a non-`Direct` pass mode) admits nothing — `None` is
/// never read as `ArgExtension::None`, and never as a wildcard.
#[test]
fn bool_param_with_an_unrecorded_slot_is_unknown() {
    let cross_check = darwin_cross_check(&[None, Some(AbiArgExtension::None)]);
    let subject = source(if_b_then_x_else_0(), "f", Some(cross_check));
    let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
    assert_unknown_naming(&verdict, "records no extension for this slot");

    // A list that is simply too short is the same case.
    let cross_check = darwin_cross_check(&[]);
    let subject = source(if_b_then_x_else_0(), "f", Some(cross_check));
    let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
    assert_unknown_naming(&verdict, "records no extension for this slot");
}

/// A target that makes NO caller-side promise (generic AAPCS64) admits nothing,
/// even with `Zext` recorded: the callee may not assume the caller extended.
#[test]
fn bool_param_on_a_target_without_a_caller_extension_promise_is_unknown() {
    let cross_check = AbiPassModeCrossCheck::attested_by("test: aarch64-unknown-linux-gnu")
        .with_param_extensions(AbiParamExtensions {
            per_param: vec![Some(AbiArgExtension::Zext), Some(AbiArgExtension::None)],
            caller_extends_to_bits: None,
        });
    let subject = source(if_b_then_x_else_0(), "f", Some(cross_check));
    let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
    assert_unknown_naming(&verdict, "NO caller-side extension promise");

    // A promise at a width this gate does not model is refused by that width.
    let cross_check = AbiPassModeCrossCheck::attested_by("test: hypothetical 64-bit extension")
        .with_param_extensions(AbiParamExtensions {
            per_param: vec![Some(AbiArgExtension::Zext), Some(AbiArgExtension::None)],
            caller_extends_to_bits: Some(64),
        });
    let subject = source(if_b_then_x_else_0(), "f", Some(cross_check));
    let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
    assert_unknown_naming(&verdict, "caller extend to 64 bits");
}

/// A STACK-PASSED bool (the 9th argument) is refused by the stack rule even
/// under a fully attested cross-check: the caller-owed extension is modeled
/// for register slots only.
#[test]
fn stack_passed_bool_param_is_unknown_even_when_attested() {
    let mut module = Module::new("stack_bool");
    let mut params = vec![Ty::U64; 8];
    params.push(Ty::Bool);
    module.func_types.push(FuncTy {
        params: params.clone(),
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut f = IrFunction::new(FuncId::new(0), "g", FuncTyId::new(0), BlockId::new(0));
    f.producer = Some(Producer::TRust);
    let mut bb0 = Block::new(BlockId::new(0));
    for (i, ty) in params.iter().enumerate() {
        bb0.params.push((ValueId::new(i as u32), ty.clone()));
    }
    let out = ValueId::new(9);
    bb0.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::Bool,
            dst_ty: Ty::U32,
            operand: ValueId::new(8),
        })
        .with_result(out),
    );
    bb0.body.push(InstrNode::new(Inst::Return { values: vec![out] }));
    f.blocks.push(bb0);
    module.functions.push(f);

    let mut per_param = vec![Some(AbiArgExtension::None); 8];
    per_param.push(Some(AbiArgExtension::Zext));
    let subject = source(module, "g", Some(darwin_cross_check(&per_param)));
    let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
    match verdict {
        OutputVerdict::Unknown { reason } => {
            assert!(reason.contains("STACK-PASSED"), "{reason}");
            assert!(reason.contains("register slots only"), "{reason}");
        }
        other => panic!("a stack-passed bool must be Unknown, got {other:?}"),
    }
}

// ===========================================================================
// Mutation control: emitted code that tests BIT 1 instead of bit 0
// ===========================================================================

/// The INJECTED WRONG LOWERING (WS7.12 hook): rewrite the module so the branch
/// tests bit 1 of the bool's carrier — `((b as u32) >> 1) != 0` — before
/// lowering. The spec side still reads the UNMUTATED module, whose bool is bit
/// 0, so the machine returns `0` on `b == true` where the IR returns `x`.
fn lower_testing_bit_1(
    module: &Module,
    func_id: FuncId,
) -> Result<trust_cg_lower::function::Function, String> {
    let mut mutated = module.clone();
    for function in &mut mutated.functions {
        for block in &mut function.blocks {
            let Some(pos) = block.body.iter().position(|n| matches!(n.inst, Inst::CondBr { .. }))
            else {
                continue;
            };
            let Inst::CondBr { cond, .. } = block.body[pos].inst.clone() else { unreachable!() };
            let (wide, one, shifted, zero, tested) = (
                ValueId::new(100),
                ValueId::new(101),
                ValueId::new(102),
                ValueId::new(103),
                ValueId::new(104),
            );
            let prefix = vec![
                InstrNode::new(Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::Bool,
                    dst_ty: Ty::U32,
                    operand: cond,
                })
                .with_result(wide),
                InstrNode::new(Inst::Const { ty: Ty::U32, value: Constant::Int(1) })
                    .with_result(one),
                InstrNode::new(Inst::BinOp { op: BinOp::LShr, ty: Ty::U32, lhs: wide, rhs: one })
                    .with_result(shifted),
                InstrNode::new(Inst::Const { ty: Ty::U32, value: Constant::Int(0) })
                    .with_result(zero),
                InstrNode::new(Inst::ICmp { op: ICmpOp::Ne, ty: Ty::U32, lhs: shifted, rhs: zero })
                    .with_result(tested),
            ];
            if let Inst::CondBr { cond, .. } = &mut block.body[pos].inst {
                *cond = tested;
            }
            let tail = block.body.split_off(pos);
            block.body.extend(prefix);
            block.body.extend(tail);
        }
    }
    lower_module_to_lir(&mutated, func_id).map_err(|e| e.to_string())
}

/// The CONTROL for the hook: the shipping lowering through the same entry
/// point still validates, so a `Refuted` below is the mutation's doing.
fn lower_faithfully(
    module: &Module,
    func_id: FuncId,
) -> Result<trust_cg_lower::function::Function, String> {
    lower_module_to_lir(module, func_id).map_err(|e| e.to_string())
}

#[test]
fn emitted_code_testing_bit_1_instead_of_bit_0_is_refuted() {
    let subject = source(if_b_then_x_else_0(), "f", Some(bool_u32_cross_check()));
    let (verdict, _obj) =
        verify_trust_ir_output_preserved_with_lowering(&subject, &backend(), lower_testing_bit_1);
    assert!(
        matches!(verdict, OutputVerdict::Refuted { .. }),
        "a lowering that branches on BIT 1 of the bool returns 0 where the IR returns x (bit 0 \
         set, bit 1 clear under the precondition); the gate must REFUTE it: {verdict:?}"
    );
}

#[test]
fn hook_with_the_shipping_lowering_still_validates() {
    let subject = source(if_b_then_x_else_0(), "f", Some(bool_u32_cross_check()));
    let (verdict, _obj) =
        verify_trust_ir_output_preserved_with_lowering(&subject, &backend(), lower_faithfully);
    assert!(
        matches!(verdict, OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated }),
        "MUTATION CONTROL: the refutation above must come from the bit-1 test, not from the \
         hook: {verdict:?}"
    );
}

// ===========================================================================
// The old six-case corpus: `<bool as AsPrimitive<T>>::as_` for six `T`
// ===========================================================================

/// `fn as_(self: bool) -> T { self as T }` in trust-ir: one `Cast ZExt`.
fn as_primitive(target: Ty) -> Module {
    let mut module = Module::new("as_primitive");
    module.func_types.push(FuncTy {
        params: vec![Ty::Bool],
        returns: vec![target.clone()],
        is_vararg: false,
        abi: None,
    });
    let mut f = IrFunction::new(FuncId::new(0), "as_", FuncTyId::new(0), BlockId::new(0));
    f.producer = Some(Producer::TRust);
    let (b, out) = (ValueId::new(0), ValueId::new(1));
    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((b, Ty::Bool));
    bb0.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::Bool,
            dst_ty: target,
            operand: b,
        })
        .with_result(out),
    );
    bb0.body.push(InstrNode::new(Inst::Return { values: vec![out] }));
    f.blocks.push(bb0);
    module.functions.push(f);
    module
}

/// The corpus that produced the six fabricated verdicts: under the modeled
/// precondition it must give NO `Refuted` — every case is validated.
#[test]
fn six_case_as_primitive_corpus_has_no_refuted_verdict() {
    let cross_check = darwin_cross_check(&[Some(AbiArgExtension::Zext)]);
    for target in [Ty::U8, Ty::U16, Ty::U32, Ty::U64, Ty::I32, Ty::I64] {
        let subject = source(as_primitive(target.clone()), "as_", Some(cross_check.clone()));
        let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
        assert!(
            !matches!(verdict, OutputVerdict::Refuted { .. }),
            "`<bool as AsPrimitive<{target:?}>>::as_` was a FABRICATED Refuted once; it must \
             never be again: {verdict:?}"
        );
        assert!(
            matches!(verdict, OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated }),
            "`<bool as AsPrimitive<{target:?}>>::as_` must be VALIDATED under the caller \
             precondition: {verdict:?}"
        );
    }
}

/// The same six cases WITHOUT the attested facts are `Unknown`, not `Refuted`:
/// the gate never again models a bool parameter as an unconstrained register.
#[test]
fn six_case_as_primitive_corpus_without_facts_is_unknown_never_refuted() {
    for target in [Ty::U8, Ty::U16, Ty::U32, Ty::U64, Ty::I32, Ty::I64] {
        let subject = source(as_primitive(target.clone()), "as_", None);
        let (verdict, _) = verify_trust_ir_output_preserved(&subject, &backend());
        assert_unknown_naming(&verdict, "no ABI pass-mode cross-check is attached");
    }
}

// ===========================================================================
// A machine body that tests ALL 32 bits (`cbz w0`) must NOT be refuted
// ===========================================================================

/// Mach-O `__text` file offset + size (the harness the narrow-width tests use).
fn text_span(obj: &[u8]) -> Option<(usize, usize)> {
    let rd32 = |o: usize| -> Option<u32> {
        obj.get(o..o + 4).and_then(|s| s.try_into().ok()).map(u32::from_le_bytes)
    };
    if rd32(0)? != 0xfeed_facf {
        return None;
    }
    let ncmds = rd32(16)? as usize;
    let mut off = 32usize;
    for _ in 0..ncmds {
        let cmd = rd32(off)?;
        let cmdsize = rd32(off + 4)? as usize;
        if cmd == 0x19 {
            let nsects = rd32(off + 64)? as usize;
            let mut s = off + 72;
            for _ in 0..nsects {
                if obj.get(s..s + 16)?.starts_with(b"__text\0") {
                    let size = u64::from_le_bytes(obj.get(s + 40..s + 48)?.try_into().ok()?);
                    return Some((rd32(s + 48)? as usize, size as usize));
                }
                s += 80;
            }
        }
        off += cmdsize;
    }
    None
}

/// Replace the whole `__text` of `obj` with `words`, padded with `nop`.
fn with_text(obj: &[u8], words: &[u32]) -> Vec<u8> {
    const NOP: u32 = 0xd503_201f;
    let (off, size) = text_span(obj).expect("__text");
    assert!(
        size >= words.len() * 4,
        "the emitted text ({size} bytes) is too small to host the body"
    );
    let mut out = obj.to_vec();
    for i in 0..size / 4 {
        let insn = words.get(i).copied().unwrap_or(NOP);
        out[off + i * 4..off + i * 4 + 4].copy_from_slice(&insn.to_le_bytes());
    }
    out
}

/// `if b { x } else { 0 }` written to test the WHOLE `w0` register:
///
/// ```text
///     cbz  w0, 1f        ; 34 00 00 40  — all 32 bits, not bit 0
///     mov  w0, w1        ; 2a 01 03 e0
///     ret                ; d6 5f 03 c0
/// 1:  mov  w0, #0        ; 52 80 00 00
///     ret                ; d6 5f 03 c0
/// ```
///
/// Under a `[7:1]` precondition bits 31:8 would be free and `b = 0x100` would
/// refute this body (spec: bit 0 clear, returns 0; machine: w0 != 0, returns
/// x). Under the WHOLE-width precondition it is exactly the IR, and the gate
/// must say so.
const CBZ_W0_PLUS_8: u32 = 0x3400_0040;
const MOV_W0_W1: u32 = 0x2a01_03e0;
const MOVZ_W0_0: u32 = 0x5280_0000;
const RET: u32 = 0xd65f_03c0;

#[test]
fn a_body_that_tests_all_32_bits_is_not_refuted() {
    let subject = source(if_b_then_x_else_0(), "f", Some(bool_u32_cross_check()));
    let (_verdict, obj) = verify_trust_ir_output_preserved(&subject, &backend());
    let obj = obj.expect("verified bytes");
    let whole_register = with_text(&obj, &[CBZ_W0_PLUS_8, MOV_W0_W1, RET, MOVZ_W0_0, RET]);
    let verdict = verify_trust_ir_bytes(&subject, &whole_register, TrustCgTargetArch::AArch64);
    assert!(
        matches!(verdict, OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated }),
        "`cbz w0` reads bits 31:8, which the precondition must cover; a `[7:1]` precondition \
         would fabricate a Refuted here: {verdict:?}"
    );
}

/// The SAME hand-assembled shape, testing BIT 1 (`tbz w0, #1`) instead: this
/// one really is a different function, and the negative twin of the test above.
///
/// ```text
///     tbz  w0, #1, 1f    ; 36 08 00 40
///     mov  w0, w1
///     ret
/// 1:  mov  w0, #0
///     ret
/// ```
const TBZ_W0_BIT1_PLUS_8: u32 = 0x3608_0040;

#[test]
fn a_hand_assembled_body_testing_bit_1_is_refuted() {
    let subject = source(if_b_then_x_else_0(), "f", Some(bool_u32_cross_check()));
    let (_verdict, obj) = verify_trust_ir_output_preserved(&subject, &backend());
    let obj = obj.expect("verified bytes");
    let bit_1 = with_text(&obj, &[TBZ_W0_BIT1_PLUS_8, MOV_W0_W1, RET, MOVZ_W0_0, RET]);
    let verdict = verify_trust_ir_bytes(&subject, &bit_1, TrustCgTargetArch::AArch64);
    assert!(
        matches!(verdict, OutputVerdict::Refuted { .. }),
        "a body branching on bit 1 returns 0 on `b = true`; the gate must REFUTE it: {verdict:?}"
    );
}

// ===========================================================================
// WS7.13 review: the PARAMETER INDEX and the REGISTER SLOT are two things
// ===========================================================================

/// `fn g(a: u128, b: bool, x: u32) -> u32 { if b { x } else { 0 } }` — the one
/// shape where the bool's parameter INDEX (1) and its register SLOT (2) differ,
/// because a 128-bit argument takes the consecutive pair X0/X1.
fn u128_then_bool() -> Module {
    let mut module = Module::new("bool_param_slot");
    module.func_types.push(FuncTy {
        params: vec![Ty::U128, Ty::Bool, Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut f = IrFunction::new(FuncId::new(0), "g", FuncTyId::new(0), BlockId::new(0));
    f.producer = Some(Producer::TRust);
    let (a, b, x, zero) = (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3));

    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((a, Ty::U128));
    bb0.params.push((b, Ty::Bool));
    bb0.params.push((x, Ty::U32));
    bb0.body.push(InstrNode::new(Inst::CondBr {
        cond: b,
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    }));

    let mut bb1 = Block::new(BlockId::new(1));
    bb1.body.push(InstrNode::new(Inst::Return { values: vec![x] }));

    let mut bb2 = Block::new(BlockId::new(2));
    bb2.body.push(
        InstrNode::new(Inst::Const { ty: Ty::U32, value: Constant::Int(0) }).with_result(zero),
    );
    bb2.body.push(InstrNode::new(Inst::Return { values: vec![zero] }));

    f.blocks.push(bb0);
    f.blocks.push(bb1);
    f.blocks.push(bb2);
    module.functions.push(f);
    module
}

fn w_zext_ambient(slot: u32) -> Formula {
    Formula::Eq(
        Box::new(Formula::BvExtract {
            inner: Box::new(Formula::Var(format!("X{slot}"), trust_types::Sort::BitVec(64))),
            high: 31,
            low: 1,
        }),
        Box::new(Formula::BitVec { value: 0, width: 31 }),
    )
}

/// The precondition names the register the CALLER wrote, which is the SLOT —
/// X2 here, because the leading `u128` consumed the X0/X1 pair — while the
/// attested `arg_ext` is looked up at the PARAMETER INDEX (1), because
/// `AbiParamExtensions::per_param` mirrors `FnAbi.args`, which is per
/// parameter. Reading either one with the other's number is a silent
/// mis-binding: the ambient would constrain a register nothing reads, or the
/// gate would admit a slot rustc never marked `Zext`.
#[test]
fn the_precondition_names_the_register_slot_and_the_fact_is_read_at_the_index() {
    let module = u128_then_bool();
    let cross_check = darwin_cross_check(&[
        Some(AbiArgExtension::None),
        Some(AbiArgExtension::Zext),
        Some(AbiArgExtension::None),
    ]);
    let spec = trust_ir_function_semantics_with(&module, FuncId::new(0), Some(&cross_check))
        .expect("an attested bool parameter after a 128-bit pair is inside the fragment");
    assert_eq!(
        spec.ambient_pre,
        vec![w_zext_ambient(2)],
        "the ambient is over W2, the register the bool actually arrives in"
    );
    let rendered = format!("{:?}", spec.value);
    assert!(rendered.contains("\"X2\""), "the spec value reads X2's bit 0: {rendered}");
    assert!(!rendered.contains("\"X1\""), "and not the high half of the u128: {rendered}");
}

/// NEGATIVE TWIN of the above: the SAME signature, with the `Zext` recorded at
/// index 2 (where the `u32` is) instead of index 1 (the bool). If the lookup
/// used the register slot, or drifted by the pair's extra slot, this would be
/// admitted. It must be `Unknown`, by name.
#[test]
fn an_extension_recorded_at_another_parameters_index_does_not_admit_the_bool() {
    let module = u128_then_bool();
    for per_param in [
        // Zext at index 0 (the u128) and at index 2 (the u32), never at 1.
        vec![Some(AbiArgExtension::Zext), Some(AbiArgExtension::None), Some(AbiArgExtension::Zext)],
        // The bool's own slot NOT RECORDED (a non-Direct pass mode).
        vec![Some(AbiArgExtension::Zext), None, Some(AbiArgExtension::Zext)],
    ] {
        let cross_check = darwin_cross_check(&per_param);
        let err = trust_ir_function_semantics_with(&module, FuncId::new(0), Some(&cross_check))
            .expect_err("the bool's own index carries no Zext");
        assert!(err.contains("`bool` in PARAMETER position (parameter 1"), "{err}");
        assert!(err.contains("register slot W2"), "the refusal names the slot too: {err}");
        assert!(err.contains("fail-closed"), "{err}");
    }
}

/// TWO bool parameters get ONE ambient EACH, at their own slots, and the
/// extensions are read at their own indices. A single shared precondition, or
/// one built from the first bool's slot twice, would leave the second
/// parameter's register unconstrained while the spec still read its bit 0.
#[test]
fn every_attested_bool_parameter_contributes_its_own_precondition() {
    let mut module = Module::new("two_bools");
    module.func_types.push(FuncTy {
        params: vec![Ty::Bool, Ty::Bool, Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut f = IrFunction::new(FuncId::new(0), "h", FuncTyId::new(0), BlockId::new(0));
    f.producer = Some(Producer::TRust);
    let (p, q, x, zero) = (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3));

    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((p, Ty::Bool));
    bb0.params.push((q, Ty::Bool));
    bb0.params.push((x, Ty::U32));
    bb0.body.push(InstrNode::new(Inst::CondBr {
        cond: p,
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(3),
        else_args: vec![],
    }));
    let mut bb1 = Block::new(BlockId::new(1));
    bb1.body.push(InstrNode::new(Inst::CondBr {
        cond: q,
        then_target: BlockId::new(2),
        then_args: vec![],
        else_target: BlockId::new(3),
        else_args: vec![],
    }));
    let mut bb2 = Block::new(BlockId::new(2));
    bb2.body.push(InstrNode::new(Inst::Return { values: vec![x] }));
    let mut bb3 = Block::new(BlockId::new(3));
    bb3.body.push(
        InstrNode::new(Inst::Const { ty: Ty::U32, value: Constant::Int(0) }).with_result(zero),
    );
    bb3.body.push(InstrNode::new(Inst::Return { values: vec![zero] }));
    f.blocks.push(bb0);
    f.blocks.push(bb1);
    f.blocks.push(bb2);
    f.blocks.push(bb3);
    module.functions.push(f);

    let both = darwin_cross_check(&[
        Some(AbiArgExtension::Zext),
        Some(AbiArgExtension::Zext),
        Some(AbiArgExtension::None),
    ]);
    let spec = trust_ir_function_semantics_with(&module, FuncId::new(0), Some(&both))
        .expect("two attested bool parameters");
    assert_eq!(
        spec.ambient_pre,
        vec![w_zext_ambient(0), w_zext_ambient(1)],
        "one ambient per bool slot, in parameter order"
    );

    // ONE missing fact is enough: with only the first bool attested the whole
    // function is `Unknown`, never "the attested one, and the other by
    // analogy".
    let only_first = darwin_cross_check(&[
        Some(AbiArgExtension::Zext),
        Some(AbiArgExtension::Sext),
        Some(AbiArgExtension::None),
    ]);
    let err = trust_ir_function_semantics_with(&module, FuncId::new(0), Some(&only_first))
        .expect_err("the second bool carries `Sext`, not `Zext`");
    assert!(err.contains("(parameter 1, register slot W1)"), "{err}");
    assert!(err.contains("Sext"), "{err}");
}
