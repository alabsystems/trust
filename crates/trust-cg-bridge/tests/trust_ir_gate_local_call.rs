// trust_ir_gate_local_call.rs — WS7.12: the IN-COMPILER proven-output gate
// (`verify_trust_ir_output_preserved`) models a MODULE-LOCAL `Inst::Call`.
//
// PROVENANCE (F-114, measured on `5b45b83b8a`). The Part A F1 control
// `parta/f1/f1_rust.rs` — a Rust-only C-ABI crate whose entry calls one
// `#[inline(never)]` local helper — printed 87 == native only under
// `-Ztrust-cg-output-gate=allow-unknown`. Under the DEFAULT strict gate it was
// refused with "instruction `Call` is outside the modeled fragment", because
// the gate's spec side had no `Inst::Call` arm at all while the SHIPPING path
// lowers the same function through `inline_local_pure_leaf_calls`. The row
// `a.f1.codegen.rust_control.strict_gate` recorded that as a GAP.
//
// WHAT THE FIX MAY NOT BE. The machine side ships the INLINER's splice. The
// spec side must NOT read that splice back, or the obligation becomes
// "the inliner agrees with itself" — a tautology. So the spec is derived from
// the CALLEE'S OWN trust-ir body, and this file pins that distinction with a
// mutation control: an injected lowering that swaps the call's arguments
// (`verify_trust_ir_output_preserved_with_lowering`, the WS7.12 `test-hooks`
// hook) must come back `Refuted`, never `Proven` and never `Unknown`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(all(feature = "ay-proofs", feature = "test-hooks"))]

use trust_cg_bridge::codegen_backend::{
    BridgeOptimizationLevel, TrustCgCodegenBackend, TrustCgTargetArch,
};
use trust_cg_bridge::module_to_lir::lower_module_to_lir;
use trust_cg_bridge::verify_output::OutputVerdict;
use trust_cg_bridge::verify_output_trust_ir::{
    TrustIrGateSource, trust_ir_function_semantics, verify_trust_ir_output_preserved,
    verify_trust_ir_output_preserved_with_lowering,
};
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module, Producer, Ty};

fn backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
        .with_optimization_level(BridgeOptimizationLevel::O0)
}

fn source(module: Module, func_id: u32, symbol: &str) -> TrustIrGateSource {
    TrustIrGateSource {
        abi_cross_check: None,
        symbol: symbol.to_string(),
        module: module.into(),
        func_id: FuncId::new(func_id),
    }
}

// ===========================================================================
// The Part A F1 control, spelled in trust-ir
// ===========================================================================

/// The exact shape of trust-ir's archived `first-party/trust-ir/reports/
/// 2026-09-17-two-language-proof-program/parta/f1/f1_rust.rs`:
///
/// ```text
/// #[inline(never)] pub fn f1_rust_half(x: u64) -> u64 { x ^ 0x55 }
/// #[no_mangle] pub extern "C" fn parta_f1_program() -> u64 { f1_rust_half(5) ^ 7 }
/// ```
///
/// `f0` is the helper, `f1` the C-ABI entry. `(5 ^ 0x55) ^ 7 == 87`.
fn f1_control_module() -> Module {
    let mut module = Module::new("parta_f1");
    // ty0: (u64) -> u64, ty1: () -> u64
    module.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });

    // --- f1_rust_half(x) = x ^ 0x55 ---------------------------------------
    let mut half =
        IrFunction::new(FuncId::new(0), "f1_rust_half", FuncTyId::new(0), BlockId::new(0));
    half.producer = Some(Producer::TRust);
    let x = ValueId::new(0);
    let mask = ValueId::new(1);
    let out = ValueId::new(2);
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((x, Ty::U64));
    bb.body.push(
        InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(0x55) }).with_result(mask),
    );
    bb.body.push(
        InstrNode::new(Inst::BinOp { op: BinOp::Xor, ty: Ty::U64, lhs: x, rhs: mask })
            .with_result(out),
    );
    bb.body.push(InstrNode::new(Inst::Return { values: vec![out] }));
    half.blocks.push(bb);

    // --- parta_f1_program() = f1_rust_half(5) ^ 7 -------------------------
    let mut entry =
        IrFunction::new(FuncId::new(1), "parta_f1_program", FuncTyId::new(1), BlockId::new(0));
    entry.producer = Some(Producer::TRust);
    let five = ValueId::new(0);
    let called = ValueId::new(1);
    let seven = ValueId::new(2);
    let result = ValueId::new(3);
    let mut bb = Block::new(BlockId::new(0));
    bb.body.push(
        InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(5) }).with_result(five),
    );
    bb.body.push(
        InstrNode::new(Inst::Call { callee: FuncId::new(0), args: vec![five] }).with_result(called),
    );
    bb.body.push(
        InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(7) }).with_result(seven),
    );
    bb.body.push(
        InstrNode::new(Inst::BinOp { op: BinOp::Xor, ty: Ty::U64, lhs: called, rhs: seven })
            .with_result(result),
    );
    bb.body.push(InstrNode::new(Inst::Return { values: vec![result] }));
    entry.blocks.push(bb);

    module.functions.push(half);
    module.functions.push(entry);
    module
}

/// RATCHET ROW `a.f1.codegen.rust_control.strict_gate` (GAP -> PASS).
///
/// The row's GAP text was the DEFAULT strict gate refusing the Rust-only F1
/// control. It asserts the named refusal is gone AND that the outcome is
/// `Proven` — not merely "some other Unknown", which would flip the row for the
/// wrong reason.
#[test]
fn a_f1_codegen_rust_control_strict_gate() {
    let subject = source(f1_control_module(), 1, "parta_f1_program");
    let (verdict, obj) = verify_trust_ir_output_preserved(&subject, &backend());
    if let OutputVerdict::Unknown { reason } = &verdict {
        assert!(
            !reason.contains("instruction `Call` is outside the modeled fragment"),
            "the F-114 headline refusal is back: {reason}"
        );
    }
    assert!(
        matches!(verdict, OutputVerdict::Proven { .. }),
        "the Part A F1 control must be PROVED under the DEFAULT strict gate: {verdict:?}"
    );
    assert!(obj.is_some(), "a proven function must ship the bytes the verdict was computed over");
}

/// The gate's SPEC side reaches INTO the callee's body: the derived term is the
/// CALLEE's `x ^ 0x55` nested inside the CALLER's `^ 7`, closed over no machine
/// variable. (The Formula algebra does not constant-fold, which is exactly why
/// this checks the STRUCTURE — a spec that had stopped at the call boundary
/// would carry an opaque symbol where `85` now sits, and one taken from the
/// inliner's splice would be indistinguishable from the caller's own body.)
#[test]
fn local_call_spec_is_derived_from_the_callee_body() {
    let module = f1_control_module();
    let spec = trust_ir_function_semantics(&module, FuncId::new(1))
        .expect("the local call must be inside the modeled fragment");
    assert_eq!(spec.out_width, 64);
    assert!(matches!(spec.reach, trust_types::Formula::Bool(true)), "{:?}", spec.reach);
    let rendered = format!("{:?}", spec.value);
    // 85 == 0x55 is the CALLEE's constant and appears nowhere in the caller.
    assert!(
        rendered.contains("value: 85"),
        "the callee's own mask must be in the caller's spec: {rendered}"
    );
    assert_eq!(
        rendered.matches("BvXor").count(),
        2,
        "the caller's xor over the callee's xor: {rendered}"
    );
    assert!(
        !rendered.contains("Var("),
        "`parta_f1_program` takes no arguments, so its spec is a CLOSED term: {rendered}"
    );
}

// ===========================================================================
// Negative twin + mutation control: the argument-swapped lowering
// ===========================================================================

/// `sub_helper(a, b) = a - b` (NOT commutative, so swapping the arguments is
/// observable), called as `sub_caller(a, b) = sub_helper(a, b)`.
fn sub_chain_module() -> Module {
    let mut module = Module::new("sub_chain");
    module.func_types.push(FuncTy {
        params: vec![Ty::U64, Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });

    let mut helper =
        IrFunction::new(FuncId::new(0), "sub_helper", FuncTyId::new(0), BlockId::new(0));
    helper.producer = Some(Producer::TRust);
    let (a, b, d) = (ValueId::new(0), ValueId::new(1), ValueId::new(2));
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((a, Ty::U64));
    bb.params.push((b, Ty::U64));
    bb.body.push(
        InstrNode::new(Inst::BinOp { op: BinOp::Sub, ty: Ty::U64, lhs: a, rhs: b }).with_result(d),
    );
    bb.body.push(InstrNode::new(Inst::Return { values: vec![d] }));
    helper.blocks.push(bb);

    let mut caller =
        IrFunction::new(FuncId::new(1), "sub_caller", FuncTyId::new(0), BlockId::new(0));
    caller.producer = Some(Producer::TRust);
    let (ca, cb, cr) = (ValueId::new(0), ValueId::new(1), ValueId::new(2));
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((ca, Ty::U64));
    bb.params.push((cb, Ty::U64));
    bb.body.push(
        InstrNode::new(Inst::Call { callee: FuncId::new(0), args: vec![ca, cb] }).with_result(cr),
    );
    bb.body.push(InstrNode::new(Inst::Return { values: vec![cr] }));
    caller.blocks.push(bb);

    module.functions.push(helper);
    module.functions.push(caller);
    module
}

/// The INJECTED WRONG LOWERING: swap the arguments of every `Inst::Call` in the
/// module before lowering. The spec side still reads the UNMUTATED module the
/// gate was handed, so this is exactly "the inliner bound the wrong argument".
fn lower_with_swapped_call_args(
    module: &Module,
    func_id: FuncId,
) -> Result<trust_cg_lower::function::Function, String> {
    let mut mutated = module.clone();
    for function in &mut mutated.functions {
        for block in &mut function.blocks {
            for node in &mut block.body {
                if let Inst::Call { args, .. } = &mut node.inst {
                    args.reverse();
                }
            }
        }
    }
    lower_module_to_lir(&mutated, func_id).map_err(|e| e.to_string())
}

/// The CONTROL for the hook itself: the same entry point with the SHIPPING
/// lowering must still prove. Without it, a `Refuted` below could be the hook's
/// own doing rather than the mutation's.
fn lower_faithfully(
    module: &Module,
    func_id: FuncId,
) -> Result<trust_cg_lower::function::Function, String> {
    lower_module_to_lir(module, func_id).map_err(|e| e.to_string())
}

/// Trust (2026-09-30, plan §5 fail-open item 1): the SHIPPING lowering now
/// refuses a body whose (inlined) callee carries an `Assert`, so the two
/// callee-guard tests below reach the gate's `Assert`-reach model through the
/// trap oracle — the pre-refusal `Brif`/`Trap` lowering, kept under test for
/// item P — and pin the shipping refusal beside it.
fn lower_through_trap_oracle(
    module: &Module,
    func_id: FuncId,
) -> Result<trust_cg_lower::function::Function, String> {
    let function = module.function_by_id(func_id).ok_or("function id absent")?;
    trust_cg_bridge::module_to_lir::lower_trust_ir_function_to_lir_trap_assert_oracle(
        module, function, false,
    )
    .map_err(|e| e.to_string())
}

/// The shipping gate path refuses the same subject at the converter, by name.
fn assert_shipping_gate_refuses_the_implicit_panic(subject: &TrustIrGateSource) {
    match verify_trust_ir_output_preserved(subject, &backend()) {
        (OutputVerdict::Unknown { reason }, None) => assert!(
            reason.contains("[implicit-panic-unfaithful]"),
            "the shipping converter must refuse the callee's Assert by name: {reason}"
        ),
        other => panic!("the shipping gate must refuse an implicit panic, got {other:?}"),
    }
}

#[test]
fn swapped_call_arguments_are_refuted() {
    let subject = source(sub_chain_module(), 1, "sub_caller");
    let (verdict, _obj) = verify_trust_ir_output_preserved_with_lowering(
        &subject,
        &backend(),
        lower_with_swapped_call_args,
    );
    assert!(
        matches!(verdict, OutputVerdict::Refuted { .. }),
        "a lowering that binds `sub_helper`'s arguments in the wrong order computes `b - a` \
         where the IR says `a - b`; the gate must REFUTE it (an `Unknown` here would mean the \
         spec side never reached the callee): {verdict:?}"
    );
}

#[test]
fn hook_with_the_shipping_lowering_still_proves() {
    let subject = source(sub_chain_module(), 1, "sub_caller");
    let (verdict, _obj) =
        verify_trust_ir_output_preserved_with_lowering(&subject, &backend(), lower_faithfully);
    assert!(
        matches!(verdict, OutputVerdict::Proven { .. }),
        "MUTATION CONTROL: the refutation above must come from the swapped arguments, not from \
         the hook: {verdict:?}"
    );
}

// ===========================================================================
// Adversarial shapes
// ===========================================================================

/// `rec(x) = rec(x)`, called from `rec_caller`. The evaluator has no fixed
/// point for it and must say so by name rather than unroll to the budget.
#[test]
fn recursive_callee_is_unknown() {
    let mut module = Module::new("recursion");
    module.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });

    let mut rec = IrFunction::new(FuncId::new(0), "rec", FuncTyId::new(0), BlockId::new(0));
    rec.producer = Some(Producer::TRust);
    let (x, r) = (ValueId::new(0), ValueId::new(1));
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((x, Ty::U64));
    bb.body
        .push(InstrNode::new(Inst::Call { callee: FuncId::new(0), args: vec![x] }).with_result(r));
    bb.body.push(InstrNode::new(Inst::Return { values: vec![r] }));
    rec.blocks.push(bb);

    let mut caller =
        IrFunction::new(FuncId::new(1), "rec_caller", FuncTyId::new(0), BlockId::new(0));
    caller.producer = Some(Producer::TRust);
    let (cx, cr) = (ValueId::new(0), ValueId::new(1));
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((cx, Ty::U64));
    bb.body.push(
        InstrNode::new(Inst::Call { callee: FuncId::new(0), args: vec![cx] }).with_result(cr),
    );
    bb.body.push(InstrNode::new(Inst::Return { values: vec![cr] }));
    caller.blocks.push(bb);

    module.functions.push(rec);
    module.functions.push(caller);

    let err = trust_ir_function_semantics(&module, FuncId::new(1))
        .expect_err("a recursive callee has no modeled semantics");
    assert!(err.contains("recursive call to `rec`"), "{err}");
    assert!(err.contains("fail-closed"), "{err}");
}

/// `self_rec(x) = self_rec(x)` as the ROOT function: the root is seeded onto
/// the call stack, so a direct self-call is refused by the same rule.
#[test]
fn direct_self_recursion_is_unknown() {
    let mut module = Module::new("self_recursion");
    module.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });
    let mut rec = IrFunction::new(FuncId::new(0), "self_rec", FuncTyId::new(0), BlockId::new(0));
    rec.producer = Some(Producer::TRust);
    let (x, r) = (ValueId::new(0), ValueId::new(1));
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((x, Ty::U64));
    bb.body
        .push(InstrNode::new(Inst::Call { callee: FuncId::new(0), args: vec![x] }).with_result(r));
    bb.body.push(InstrNode::new(Inst::Return { values: vec![r] }));
    rec.blocks.push(bb);
    module.functions.push(rec);

    let err = trust_ir_function_semantics(&module, FuncId::new(0))
        .expect_err("a self-recursive root has no modeled semantics");
    assert!(err.contains("recursive call to `self_rec`"), "{err}");
}

/// A callee carrying its own `Inst::Assert`: the guard becomes a guard on the
/// CALLER's path, matching the trap the inliner's splice emits. The gate must
/// prove the CONDITIONAL obligation rather than refuse it.
#[test]
fn callee_assert_guard_proves_the_conditional_obligation() {
    let mut module = Module::new("guarded_callee");
    module.func_types.push(FuncTy {
        params: vec![Ty::U64, Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });

    // safe_div(a, b) = { assert b != 0; a / b }
    let mut helper = IrFunction::new(FuncId::new(0), "safe_div", FuncTyId::new(0), BlockId::new(0));
    helper.producer = Some(Producer::TRust);
    let (a, b, zero, ok, q) =
        (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3), ValueId::new(4));
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((a, Ty::U64));
    bb.params.push((b, Ty::U64));
    bb.body.push(
        InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(0) }).with_result(zero),
    );
    bb.body.push(
        InstrNode::new(Inst::ICmp { op: ICmpOp::Ne, ty: Ty::U64, lhs: b, rhs: zero })
            .with_result(ok),
    );
    bb.body.push(InstrNode::new(Inst::Assert {
        cond: ok,
        kind: trust_ir::AssertKind::Unspecified,
        site: None,
    }));
    bb.body.push(
        InstrNode::new(Inst::BinOp { op: BinOp::UDiv, ty: Ty::U64, lhs: a, rhs: b }).with_result(q),
    );
    bb.body.push(InstrNode::new(Inst::Return { values: vec![q] }));
    helper.blocks.push(bb);

    let mut caller =
        IrFunction::new(FuncId::new(1), "div_caller", FuncTyId::new(0), BlockId::new(0));
    caller.producer = Some(Producer::TRust);
    let (ca, cb, cr) = (ValueId::new(0), ValueId::new(1), ValueId::new(2));
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((ca, Ty::U64));
    bb.params.push((cb, Ty::U64));
    bb.body.push(
        InstrNode::new(Inst::Call { callee: FuncId::new(0), args: vec![ca, cb] }).with_result(cr),
    );
    bb.body.push(InstrNode::new(Inst::Return { values: vec![cr] }));
    caller.blocks.push(bb);

    module.functions.push(helper);
    module.functions.push(caller);

    // The callee's guard is visible in the CALLER's `reach`: it is not
    // `Bool(true)`, i.e. the gate did not quietly drop it.
    let spec = trust_ir_function_semantics(&module, FuncId::new(1))
        .expect("the guarded callee is inside the modeled fragment");
    assert!(
        !matches!(spec.reach, trust_types::Formula::Bool(true)),
        "the callee's own assert must reach the caller's `reach`: {:?}",
        spec.reach
    );

    let subject = source(module, 1, "div_caller");
    assert_shipping_gate_refuses_the_implicit_panic(&subject);
    let (verdict, _obj) = verify_trust_ir_output_preserved_with_lowering(
        &subject,
        &backend(),
        lower_through_trap_oracle,
    );
    assert!(
        matches!(verdict, OutputVerdict::Proven { .. }),
        "the conditional obligation `spec_reach -> machine_reach AND equal` must discharge for \
         a callee whose guard traps: {verdict:?}"
    );
}

/// A callee that can NEVER return (its own guard is unsatisfiable) makes the
/// caller's obligation vacuous. The vacuity firewall must give `Unknown`, and
/// the reason must name the vacuity — not report it as `Proven`.
#[test]
fn callee_with_unsatisfiable_reach_is_unknown() {
    let mut module = Module::new("vacuous_callee");
    module.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });

    // never(x) = { assert x != x; x }
    let mut helper = IrFunction::new(FuncId::new(0), "never", FuncTyId::new(0), BlockId::new(0));
    helper.producer = Some(Producer::TRust);
    let (x, ok) = (ValueId::new(0), ValueId::new(1));
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((x, Ty::U64));
    bb.body.push(
        InstrNode::new(Inst::ICmp { op: ICmpOp::Ne, ty: Ty::U64, lhs: x, rhs: x }).with_result(ok),
    );
    bb.body.push(InstrNode::new(Inst::Assert {
        cond: ok,
        kind: trust_ir::AssertKind::Unspecified,
        site: None,
    }));
    bb.body.push(InstrNode::new(Inst::Return { values: vec![x] }));
    helper.blocks.push(bb);

    let mut caller =
        IrFunction::new(FuncId::new(1), "never_caller", FuncTyId::new(0), BlockId::new(0));
    caller.producer = Some(Producer::TRust);
    let (cx, cr) = (ValueId::new(0), ValueId::new(1));
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((cx, Ty::U64));
    bb.body.push(
        InstrNode::new(Inst::Call { callee: FuncId::new(0), args: vec![cx] }).with_result(cr),
    );
    bb.body.push(InstrNode::new(Inst::Return { values: vec![cr] }));
    caller.blocks.push(bb);

    module.functions.push(helper);
    module.functions.push(caller);

    let subject = source(module, 1, "never_caller");
    assert_shipping_gate_refuses_the_implicit_panic(&subject);
    let (verdict, _obj) = verify_trust_ir_output_preserved_with_lowering(
        &subject,
        &backend(),
        lower_through_trap_oracle,
    );
    match verdict {
        OutputVerdict::Unknown { reason } => assert!(
            reason.contains("VACUOUS"),
            "the conjoined callee guard must trip the VACUITY firewall by name: {reason}"
        ),
        other => panic!("a callee that never returns must never be reported as proven: {other:?}"),
    }
}

/// A TWO-LEVEL chain `outer -> middle -> inner`: `inner(x) = x ^ 0x55`,
/// `middle(x) = inner(x) ^ 7`, `outer(x) = middle(x) ^ 1`.
#[test]
fn two_level_call_chain_proves() {
    let mut module = Module::new("chain");
    module.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });

    let push_level = |module: &mut Module, id: u32, name: &str, k: i128, callee: Option<u32>| {
        let mut f = IrFunction::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0));
        f.producer = Some(Producer::TRust);
        let (x, lhs, konst, out) =
            (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3));
        let mut bb = Block::new(BlockId::new(0));
        bb.params.push((x, Ty::U64));
        let lhs = match callee {
            Some(c) => {
                bb.body.push(
                    InstrNode::new(Inst::Call { callee: FuncId::new(c), args: vec![x] })
                        .with_result(lhs),
                );
                lhs
            }
            None => x,
        };
        bb.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(k) }).with_result(konst),
        );
        bb.body.push(
            InstrNode::new(Inst::BinOp { op: BinOp::Xor, ty: Ty::U64, lhs, rhs: konst })
                .with_result(out),
        );
        bb.body.push(InstrNode::new(Inst::Return { values: vec![out] }));
        f.blocks.push(bb);
        module.functions.push(f);
    };

    push_level(&mut module, 0, "inner", 0x55, None);
    push_level(&mut module, 1, "middle", 7, Some(0));
    push_level(&mut module, 2, "outer", 1, Some(1));

    let subject = source(module, 2, "outer");
    let (verdict, _obj) = verify_trust_ir_output_preserved(&subject, &backend());
    assert!(
        matches!(verdict, OutputVerdict::Proven { .. }),
        "a two-level local call chain must prove: {verdict:?}"
    );
}

/// A `Producer::Clean` callee is refused BY NAME, on the spec side as well as
/// in the converter. The gate must never be the component that first admits a
/// Clean-origin body to codegen.
#[test]
fn clean_callee_is_refused_by_the_named_producer_gate() {
    let mut module = f1_control_module();
    module.functions[0].producer = Some(Producer::Clean);

    let err = trust_ir_function_semantics(&module, FuncId::new(1))
        .expect_err("a Clean-origin callee has no admitted semantics here");
    assert!(err.contains("CleanOriginBelowCodegenGate"), "{err}");
    assert!(err.contains("f1_rust_half"), "{err}");

    let subject = source(module, 1, "parta_f1_program");
    let (verdict, obj) = verify_trust_ir_output_preserved(&subject, &backend());
    match verdict {
        OutputVerdict::Unknown { reason } => {
            assert!(reason.contains("is not admitted to codegen"), "{reason}");
        }
        other => panic!("a Clean-origin callee must be refused, not {other:?}"),
    }
    assert!(obj.is_none(), "no bytes may be produced for a refused unit");

    // CONTROL: the identical module with the callee stamped `TRust` proves.
    let control = source(f1_control_module(), 1, "parta_f1_program");
    let (verdict, _obj) = verify_trust_ir_output_preserved(&control, &backend());
    assert!(
        matches!(verdict, OutputVerdict::Proven { .. }),
        "the refusal above must come from the PRODUCER stamp, not the shape: {verdict:?}"
    );
}

/// A callee this module does not define has no IR to read, and the gate does
/// not compose the emitted `bl` against an assumed semantics.
#[test]
fn non_local_callee_is_unknown() {
    let mut module = f1_control_module();
    // Re-point the call at a FuncId no `Function` in the module carries.
    for block in &mut module.functions[1].blocks {
        for node in &mut block.body {
            if let Inst::Call { callee, .. } = &mut node.inst {
                *callee = FuncId::new(97);
            }
        }
    }
    let err = trust_ir_function_semantics(&module, FuncId::new(1))
        .expect_err("a non-local callee has no modeled semantics");
    assert!(err.contains("this module does not define"), "{err}");
    assert!(err.contains("fail-closed"), "{err}");
}

/// `Inst::CallIndirect` carries no `FuncId`, so there is no body to read. It
/// stays outside the modeled fragment and is refused by name.
#[test]
fn indirect_call_stays_outside_the_modeled_fragment() {
    let mut module = Module::new("indirect");
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });
    let mut f = IrFunction::new(FuncId::new(0), "via_ptr", FuncTyId::new(0), BlockId::new(0));
    f.producer = Some(Producer::TRust);
    let (p, r) = (ValueId::new(0), ValueId::new(1));
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((p, Ty::Ptr));
    bb.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: p,
            sig: FuncTyId::new(1),
            args: vec![],
            calling_conv: trust_ir::CallingConv::C,
        })
        .with_result(r),
    );
    bb.body.push(InstrNode::new(Inst::Return { values: vec![r] }));
    f.blocks.push(bb);
    module.functions.push(f);

    let err = trust_ir_function_semantics(&module, FuncId::new(0))
        .expect_err("an indirect call has no modeled semantics");
    assert!(err.contains("`CallIndirect` is outside the modeled fragment"), "{err}");
}

// ===========================================================================
// Review (WS7.12): adversarial shapes the first cut did not pin
// ===========================================================================

/// `sub_helper(a, b) - sub_helper(b, a)`: the SAME callee twice in one block
/// with DIFFERENT argument formulas. The memo is keyed on `(callee, block)`
/// plus the live-in slice, so the second call must MISS (a hit would hand it
/// the first call's value) — and the whole thing must still prove.
fn twice_module() -> Module {
    let mut module = sub_chain_module();
    // Replace `sub_caller`'s body with `sub_helper(a, b) - sub_helper(b, a)`.
    let caller = &mut module.functions[1];
    let (ca, cb, r1, r2, out) =
        (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3), ValueId::new(4));
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((ca, Ty::U64));
    bb.params.push((cb, Ty::U64));
    bb.body.push(
        InstrNode::new(Inst::Call { callee: FuncId::new(0), args: vec![ca, cb] }).with_result(r1),
    );
    bb.body.push(
        InstrNode::new(Inst::Call { callee: FuncId::new(0), args: vec![cb, ca] }).with_result(r2),
    );
    bb.body.push(
        InstrNode::new(Inst::BinOp { op: BinOp::Sub, ty: Ty::U64, lhs: r1, rhs: r2 })
            .with_result(out),
    );
    bb.body.push(InstrNode::new(Inst::Return { values: vec![out] }));
    caller.blocks = vec![bb];
    module
}

#[test]
fn same_callee_called_twice_with_different_arguments_proves() {
    let module = twice_module();
    let spec = trust_ir_function_semantics(&module, FuncId::new(1))
        .expect("two calls to one callee are inside the modeled fragment");
    let rendered = format!("{:?}", spec.value);
    assert_eq!(
        rendered.matches("BvSub").count(),
        3,
        "the caller's sub over TWO distinct callee subs (a memo hit on the second call would \
         collapse them): {rendered}"
    );

    let subject = source(module, 1, "sub_caller");
    let (verdict, _obj) = verify_trust_ir_output_preserved(&subject, &backend());
    assert!(matches!(verdict, OutputVerdict::Proven { .. }), "{verdict:?}");
}

/// The negative twin of the above: swapping the arguments of BOTH calls turns
/// `(a-b) - (b-a)` into `(b-a) - (a-b)`, its negation. The gate must refute —
/// which also shows the memo did not serve the second call a stale value.
#[test]
fn same_callee_twice_with_swapped_lowering_is_refuted() {
    let subject = source(twice_module(), 1, "sub_caller");
    let (verdict, _obj) = verify_trust_ir_output_preserved_with_lowering(
        &subject,
        &backend(),
        lower_with_swapped_call_args,
    );
    assert!(matches!(verdict, OutputVerdict::Refuted { .. }), "{verdict:?}");
}

/// A callee gets a FRESH environment. This callee reads `%7`, which it never
/// defines but which the CALLER does define: the spec side must refuse it as
/// an undefined SSA read, never resolve it through the caller's map.
#[test]
fn callee_reading_a_caller_only_value_is_refused() {
    let mut module = sub_chain_module();
    // Caller: define %7 = const 1 before the call.
    {
        let caller = &mut module.functions[1];
        let seven = ValueId::new(7);
        caller.blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(1) }).with_result(seven),
        );
    }
    // Callee: return `a - %7` instead of `a - b`. `%7` is undefined HERE.
    {
        let helper = &mut module.functions[0];
        for node in &mut helper.blocks[0].body {
            if let Inst::BinOp { rhs, .. } = &mut node.inst {
                *rhs = ValueId::new(7);
            }
        }
    }
    let err = trust_ir_function_semantics(&module, FuncId::new(1))
        .expect_err("a callee must not see the caller's SSA values");
    assert!(err.contains("read of undefined SSA value %7"), "{err}");
}

/// Arity and width mismatches at the call boundary are refused by name, not
/// bound positionally.
#[test]
fn call_boundary_arity_and_width_mismatches_are_refused() {
    // Arity: one argument for a two-parameter callee.
    let mut module = sub_chain_module();
    for node in &mut module.functions[1].blocks[0].body {
        if let Inst::Call { args, .. } = &mut node.inst {
            args.truncate(1);
        }
    }
    let err = trust_ir_function_semantics(&module, FuncId::new(1)).expect_err("arity");
    assert!(err.contains("passes 1 arg(s) for 2 declared param(s)"), "{err}");

    // Width: a 32-bit constant into a 64-bit parameter.
    let mut module = sub_chain_module();
    {
        let caller = &mut module.functions[1];
        let narrow = ValueId::new(9);
        caller.blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Const { ty: Ty::U32, value: Constant::Int(1) })
                .with_result(narrow),
        );
        for node in &mut caller.blocks[0].body {
            if let Inst::Call { args, .. } = &mut node.inst {
                args[1] = narrow;
            }
        }
    }
    let err = trust_ir_function_semantics(&module, FuncId::new(1)).expect_err("width");
    assert!(err.contains("passes a 32-bit value into a 64-bit param 1"), "{err}");
}

/// A chain of `n` nested callees: `f_k(x) = f_{k-1}(x) ^ k`, `f_0(x) = x`.
fn nested_chain_module(n: u32) -> Module {
    let mut module = Module::new("deep_chain");
    module.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });
    for k in 0..=n {
        let mut f =
            IrFunction::new(FuncId::new(k), &format!("f_{k}"), FuncTyId::new(0), BlockId::new(0));
        f.producer = Some(Producer::TRust);
        let (x, called, konst, out) =
            (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3));
        let mut bb = Block::new(BlockId::new(0));
        bb.params.push((x, Ty::U64));
        if k == 0 {
            bb.body.push(InstrNode::new(Inst::Return { values: vec![x] }));
        } else {
            bb.body.push(
                InstrNode::new(Inst::Call { callee: FuncId::new(k - 1), args: vec![x] })
                    .with_result(called),
            );
            bb.body.push(
                InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(i128::from(k)) })
                    .with_result(konst),
            );
            bb.body.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Xor,
                    ty: Ty::U64,
                    lhs: called,
                    rhs: konst,
                })
                .with_result(out),
            );
            bb.body.push(InstrNode::new(Inst::Return { values: vec![out] }));
        }
        f.blocks.push(bb);
        module.functions.push(f);
    }
    module
}

/// The call-depth budget is exactly 8 nested callees: `f_8` (eight callees
/// below the root) derives a spec, `f_9` is refused by name.
#[test]
fn call_depth_budget_admits_eight_and_refuses_nine() {
    let ok = nested_chain_module(8);
    trust_ir_function_semantics(&ok, FuncId::new(8))
        .expect("eight nested callees are within MAX_IR_CALL_DEPTH");

    let deep = nested_chain_module(9);
    let err = trust_ir_function_semantics(&deep, FuncId::new(9))
        .expect_err("nine nested callees exceed MAX_IR_CALL_DEPTH");
    assert!(err.contains("call nesting deeper than 8 at `f_0`"), "{err}");
    assert!(err.contains("fail-closed"), "{err}");
}

/// A callee carrying `Inst::Assume` is outside the modeled fragment on the
/// SPEC side (an assumption is not a guard the machine enforces), even though
/// the inliner's multi-block splice admits it. The verdict must be `Unknown`.
#[test]
fn callee_with_assume_is_unknown_not_a_free_guard() {
    let mut module = sub_chain_module();
    {
        let helper = &mut module.functions[0];
        let (b, zero, nz) = (ValueId::new(1), ValueId::new(5), ValueId::new(6));
        let body = &mut helper.blocks[0].body;
        body.insert(
            0,
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(0) }).with_result(zero),
        );
        body.insert(
            1,
            InstrNode::new(Inst::ICmp { op: ICmpOp::Ne, ty: Ty::U64, lhs: b, rhs: zero })
                .with_result(nz),
        );
        body.insert(2, InstrNode::new(Inst::Assume { cond: nz }));
    }
    let err = trust_ir_function_semantics(&module, FuncId::new(1))
        .expect_err("an assumption in the callee is not modeled");
    assert!(err.contains("`Assume` is outside the modeled fragment"), "{err}");
}

/// A `bool`-returning callee feeding the caller's branch, and a callee at a
/// NARROW (8-bit) width: both must be inside the fragment and prove — and,
/// above all, neither may be REFUTED (a fabricated verdict).
#[test]
fn bool_returning_and_narrow_callees_prove() {
    // is_zero(x: u64) -> bool; pick(x) = if is_zero(x) { 1 } else { 2 }
    let mut module = Module::new("bool_ret");
    module.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::Bool],
        is_vararg: false,
        abi: None,
    });
    module.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });
    let mut is_zero = IrFunction::new(FuncId::new(0), "is_zero", FuncTyId::new(0), BlockId::new(0));
    is_zero.producer = Some(Producer::TRust);
    {
        let (x, zero, eq) = (ValueId::new(0), ValueId::new(1), ValueId::new(2));
        let mut bb = Block::new(BlockId::new(0));
        bb.params.push((x, Ty::U64));
        bb.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(0) }).with_result(zero),
        );
        bb.body.push(
            InstrNode::new(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::U64, lhs: x, rhs: zero })
                .with_result(eq),
        );
        bb.body.push(InstrNode::new(Inst::Return { values: vec![eq] }));
        is_zero.blocks.push(bb);
    }
    let mut pick = IrFunction::new(FuncId::new(1), "pick", FuncTyId::new(1), BlockId::new(0));
    pick.producer = Some(Producer::TRust);
    {
        let (x, c, one, two) = (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3));
        let mut bb0 = Block::new(BlockId::new(0));
        bb0.params.push((x, Ty::U64));
        bb0.body.push(
            InstrNode::new(Inst::Call { callee: FuncId::new(0), args: vec![x] }).with_result(c),
        );
        bb0.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(1) }).with_result(one),
        );
        bb0.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(2) }).with_result(two),
        );
        bb0.body.push(InstrNode::new(Inst::CondBr {
            cond: c,
            then_target: BlockId::new(1),
            then_args: vec![one],
            else_target: BlockId::new(1),
            else_args: vec![two],
        }));
        let mut bb1 = Block::new(BlockId::new(1));
        let r = ValueId::new(4);
        bb1.params.push((r, Ty::U64));
        bb1.body.push(InstrNode::new(Inst::Return { values: vec![r] }));
        pick.blocks.push(bb0);
        pick.blocks.push(bb1);
    }
    module.functions.push(is_zero);
    module.functions.push(pick);
    let subject = source(module, 1, "pick");
    let (verdict, _obj) = verify_trust_ir_output_preserved(&subject, &backend());
    assert!(
        !matches!(verdict, OutputVerdict::Refuted { .. }),
        "a bool-returning callee must never yield a FABRICATED refutation: {verdict:?}"
    );
    assert!(matches!(verdict, OutputVerdict::Proven { .. }), "{verdict:?}");

    // h(x: u8) -> u8 = x ^ 0x55; c(x: u8) -> u8 = h(x) ^ 7 — at 8 bits.
    let mut narrow = f1_control_module();
    narrow.func_types[0] =
        FuncTy { params: vec![Ty::U8], returns: vec![Ty::U8], is_vararg: false, abi: None };
    narrow.func_types[1] =
        FuncTy { params: vec![Ty::U8], returns: vec![Ty::U8], is_vararg: false, abi: None };
    for f in &mut narrow.functions {
        for block in &mut f.blocks {
            for (_, ty) in &mut block.params {
                *ty = Ty::U8;
            }
            for node in &mut block.body {
                match &mut node.inst {
                    Inst::Const { ty, .. } | Inst::BinOp { ty, .. } => *ty = Ty::U8,
                    _ => {}
                }
            }
        }
    }
    // The entry now takes `x` and calls `h(x)` instead of `h(5)`.
    {
        let entry = &mut narrow.functions[1];
        let x = ValueId::new(9);
        entry.blocks[0].params.push((x, Ty::U8));
        for node in &mut entry.blocks[0].body {
            if let Inst::Call { args, .. } = &mut node.inst {
                args[0] = x;
            }
        }
    }
    let spec = trust_ir_function_semantics(&narrow, FuncId::new(1)).expect("narrow chain");
    assert_eq!(spec.out_width, 8, "the obligation is at the DECLARED width");
    let subject = source(narrow, 1, "parta_f1_program");
    let (verdict, _obj) = verify_trust_ir_output_preserved(&subject, &backend());
    assert!(
        !matches!(verdict, OutputVerdict::Refuted { .. }),
        "a narrow callee must never yield a FABRICATED refutation: {verdict:?}"
    );
    assert!(matches!(verdict, OutputVerdict::Proven { .. }), "{verdict:?}");
}

/// THE REVIEW ITEM IN THE SPEC: if a lowering ever ships a REAL `bl` for a
/// gated function, the gate must not model it by assumption. Injected through
/// the hook: the REAL-CALLS lowering leaves `sub_caller`'s call as a genuine
/// `Bl`. The spec side models the call from the callee's IR, but the MACHINE
/// side runs with an empty callee environment, so the `bl` is refused by name
/// and the verdict is `Unknown` — never `Proven`.
#[test]
fn a_real_bl_in_the_lowered_body_is_unknown_never_modeled_by_assumption() {
    fn lower_with_real_calls(
        module: &Module,
        func_id: FuncId,
    ) -> Result<trust_cg_lower::function::Function, String> {
        let function = module.function_by_id(func_id).ok_or("missing")?;
        trust_cg_bridge::module_to_lir::lower_trust_ir_function_to_lir_real_calls(module, function)
            .map_err(|e| e.to_string())
    }
    let subject = source(sub_chain_module(), 1, "sub_caller");
    let (verdict, _obj) =
        verify_trust_ir_output_preserved_with_lowering(&subject, &backend(), lower_with_real_calls);
    match verdict {
        OutputVerdict::Unknown { reason } => assert!(
            reason.contains("bl at") && reason.contains("fail-closed"),
            "the `bl` must be refused BY NAME on the machine side: {reason}"
        ),
        other => panic!("a real `bl` must be Unknown, never {other:?}"),
    }
}

// ===========================================================================
// Step 2 increment 3: the codegen module the instance lane builds for the goal
// ===========================================================================

/// The exact shape `rustc_codegen_trust_cg`'s instance lane hands the gate for
///
/// ```text
/// #[inline(never)] fn ident<T>(x: T) -> T { x }
/// #[no_mangle] pub extern "C" fn f(x: u64) -> u64 { ident::<u64>(x) ^ 7 }
/// ```
///
/// `f` (the finalize-assembled body, C ABI) has had its call edge RELINKED from
/// the leftover bodyless declaration `ident` (FuncId 1, now unreferenced) to the
/// APPENDED instance body `ident::<u64>` (FuncId 2, Rust ABI, named by its
/// mangled symbol).
fn instance_spliced_module() -> Module {
    let mut module = Module::new("inc3_subject");
    module.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });

    let mut f = IrFunction::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
    f.producer = Some(Producer::TRust);
    f.calling_conv = trust_ir::CallingConv::C;
    let (x, called, seven, out) =
        (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3));
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((x, Ty::U64));
    bb.body.push(
        InstrNode::new(Inst::Call { callee: FuncId::new(2), args: vec![x] }).with_result(called),
    );
    bb.body.push(
        InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(7) }).with_result(seven),
    );
    bb.body.push(
        InstrNode::new(Inst::BinOp { op: BinOp::Xor, ty: Ty::U64, lhs: called, rhs: seven })
            .with_result(out),
    );
    bb.body.push(InstrNode::new(Inst::Return { values: vec![out] }));
    f.blocks.push(bb);

    let mut leftover = IrFunction::new(FuncId::new(1), "ident", FuncTyId::new(0), BlockId::new(0));
    leftover.producer = Some(Producer::TRust);
    leftover.calling_conv = trust_ir::CallingConv::Rust;

    let mut ident = IrFunction::new(
        FuncId::new(2),
        "_RINvCs0_12inc3_subject5identyEB2_",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    ident.producer = Some(Producer::TRust);
    ident.calling_conv = trust_ir::CallingConv::Rust;
    let p = ValueId::new(0);
    let mut bb = Block::new(BlockId::new(0));
    bb.params.push((p, Ty::U64));
    bb.body.push(InstrNode::new(Inst::Return { values: vec![p] }));
    ident.blocks.push(bb);

    module.functions.push(f);
    module.functions.push(leftover);
    module.functions.push(ident);
    module
}

/// The spliced callee is INLINED (no LIR call survives in `f`) and both work
/// items prove under the strict gate: `f` composes `ident::<u64>` from its own
/// trust-ir, and `ident::<u64>` is emitted under its own symbol.
#[test]
fn instance_spliced_generic_callee_inlines_and_proves() {
    let module = instance_spliced_module();
    let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("the spliced caller lowers");
    for block in lir.blocks.values() {
        for inst in &block.instructions {
            assert!(
                !matches!(
                    inst.opcode,
                    trust_cg_lower::instructions::Opcode::Call { .. }
                        | trust_cg_lower::instructions::Opcode::CallIndirect
                ),
                "the spliced instance body must be inlined, not called: {:?}",
                inst.opcode
            );
        }
    }
    for (id, symbol) in [(0, "f"), (2, "_RINvCs0_12inc3_subject5identyEB2_")] {
        let subject = source(module.clone(), id, symbol);
        let (verdict, obj) = verify_trust_ir_output_preserved(&subject, &backend());
        assert!(
            matches!(verdict, OutputVerdict::Proven { .. }),
            "`{symbol}` must prove under the strict gate: {verdict:?}"
        );
        assert!(obj.is_some(), "`{symbol}`: a proven function ships the bytes it was proved over");
    }
}
