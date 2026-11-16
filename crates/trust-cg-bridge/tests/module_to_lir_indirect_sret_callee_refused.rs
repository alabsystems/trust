// Regression pin for the indirect half of the sret convention in the
// Module -> LIR converter (trust-cg de95c72d6, L01-P5,
// `Function::sret_arg_indirect_callees`).
//
// trust-cg's adapter records, keyed by LIR callee value, every `CallIndirect`
// whose fn-pointer resolves statically to a declaration whose argument 0 is a
// hidden return-buffer (`sret`) pointer. This converter's real-call arm can
// never emit such a callee — its composable fragment admits only callees that
// return one single-register scalar, and an sret callee has an EMPTY return
// list — so the set it hands trust-cg is provably empty. What this file pins is
// that the impossible case is refused BY NAME before emission
// (`[TCG-SRET-ABI]`, naming the callee), rather than falling through to the
// generic "not composable" refusal with the ABI fact silently dropped, and that
// the same shape without the attribute is NOT refused for that reason.
//
// The shape is the converter's own KNOWN-target shape: `GlobalAddr` of a module
// global whose NAME is the function symbol (exactly how the fixtures in
// `module_to_lir_indirect_call_proven_output.rs` spell `&ir_addf`).

use trust_cg_bridge::lower_trust_ir_function_to_lir_real_calls;
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, GlobalId, ValueId};
use trust_ir::{Block, FuncAttrs, Function as IrFunction, Global, Linkage, Module, ParamAttrs};

/// `ir_sink(buf: ptr, x: i32, y: i32)` with no return values; when `sret` is
/// set, `buf` is declared as the hidden return buffer. The caller
/// `ir_ci(buf, a, b)` takes `&ir_sink` and calls it indirectly.
fn make_module(sret: bool) -> Module {
    let mut module = Module::new("indirect_sret_callee_module");
    // FuncTy 0: caller(ptr,i32,i32)->() ; FuncTy 1: callee(ptr,i32,i32)->().
    for _ in 0..2 {
        module.func_types.push(FuncTy {
            params: vec![Ty::Ptr, Ty::I32, Ty::I32],
            returns: vec![],
            is_vararg: false,
            abi: None,
        });
    }

    module.globals.push(Global {
        name: "ir_sink".to_string(),
        ty: Ty::Ptr,
        mutable: false,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });

    // --- callee: ir_sink(buf, x, y) = ()  (FuncId 1) ---
    let mut sink = IrFunction::new(FuncId::new(1), "ir_sink", FuncTyId::new(1), BlockId::new(0));
    sink.attrs = FuncAttrs {
        params: vec![
            ParamAttrs { sret, ..Default::default() },
            ParamAttrs::default(),
            ParamAttrs::default(),
        ],
        ..Default::default()
    };
    let (buf, x, y) = (ValueId::new(10), ValueId::new(11), ValueId::new(12));
    let mut sb = Block::new(BlockId::new(0));
    sb.params.push((buf, Ty::Ptr));
    sb.params.push((x, Ty::I32));
    sb.params.push((y, Ty::I32));
    sb.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    sink.blocks.push(sb);

    // --- caller: ir_ci(buf, a, b) = (let f = &ir_sink; f(buf, a, b))  (FuncId 0) ---
    let mut caller = IrFunction::new(FuncId::new(0), "ir_ci", FuncTyId::new(0), BlockId::new(0));
    let (cbuf, a, b, fptr) = (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3));
    let mut cb = Block::new(BlockId::new(0));
    cb.params.push((cbuf, Ty::Ptr));
    cb.params.push((a, Ty::I32));
    cb.params.push((b, Ty::I32));
    cb.body.push(InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(fptr));
    cb.body.push(InstrNode::new(Inst::CallIndirect {
        callee: fptr,
        sig: FuncTyId::new(1),
        args: vec![cbuf, a, b],
        calling_conv: Default::default(),
    }));
    cb.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    caller.blocks.push(cb);

    module.functions.push(caller);
    module.functions.push(sink);
    module
}

fn lower_caller(module: &Module) -> Result<(), String> {
    let caller = &module.functions[0];
    lower_trust_ir_function_to_lir_real_calls(module, caller)
        .map(|_| ())
        .map_err(|err| format!("{err:?}"))
}

#[test]
fn indirect_call_to_a_statically_known_sret_callee_is_refused_by_name() {
    let module = make_module(true);
    let err =
        lower_caller(&module).expect_err("an sret callee behind an indirect call must be refused");
    assert!(err.contains("[TCG-SRET-ABI]"), "refusal must carry the sret ABI tag, got: {err}");
    assert!(err.contains("ir_sink"), "refusal must name the resolved callee, got: {err}");
    assert!(
        err.contains("sret_arg_indirect_callees"),
        "refusal must name the convention it would otherwise drop, got: {err}"
    );
}

#[test]
fn the_same_shape_without_the_attribute_is_not_refused_for_sret() {
    // Non-vacuity control: with `sret` cleared the callee is still not a
    // composable pure leaf (it returns nothing), so the converter may refuse it
    // for THAT reason — but never with the sret tag. If this control ever
    // starts carrying `[TCG-SRET-ABI]`, the scan has stopped reading the
    // declaration and is refusing on shape alone.
    let module = make_module(false);
    if let Err(err) = lower_caller(&module) {
        assert!(
            !err.contains("[TCG-SRET-ABI]"),
            "an sret-free callee must not be refused as sret, got: {err}"
        );
    }
}
