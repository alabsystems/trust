//! Trust: typed first-class adapters for by-value Rust closure environments.
//!
//! Trust-IR applies a closure by passing its capture lanes before its apparent
//! arguments. A Rust FnOnce body instead receives one closure environment before
//! those arguments. This adapter constructs that environment from the actual
//! parameter values; it never seeds a reference or invents a closure target.

use trust_ir::{
    Block, BlockId, CallingConv, ClosureTy, ClosureTyId, FuncId, FuncTy, FuncTyId, Function, Inst,
    InstrNode, Linkage, Producer, ValueId,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Shape {
    pub(crate) closure: ClosureTyId,
    pub(crate) body: FuncId,
}

pub(crate) fn physical_signature(closure: &ClosureTy, apparent: &FuncTy) -> Option<FuncTy> {
    // A present ABI describes the apparent parameters, not the prepended
    // captures. Reclassifying it needs real target ABI evidence; do not drop it.
    if apparent.is_vararg || apparent.returns.len() > 1 || apparent.abi.is_some() {
        return None;
    }
    let mut params = closure.captures.clone();
    params.extend(apparent.params.iter().cloned());
    Some(FuncTy { params, returns: apparent.returns.clone(), is_vararg: false, abi: None })
}

pub(crate) fn build(
    id: FuncId,
    signature: FuncTyId,
    name: String,
    shape: Shape,
    closure: &ClosureTy,
    apparent: &FuncTy,
) -> Option<Function> {
    if id == shape.body {
        return None;
    }
    let physical = physical_signature(closure, apparent)?;
    let n = u32::try_from(physical.params.len()).ok()?;
    let capture_count = u32::try_from(closure.captures.len()).ok()?;
    let result = n.checked_add(1)?;
    let env = ValueId::new(n);
    let mut block = Block::new(BlockId::new(0));
    for (i, ty) in physical.params.iter().enumerate() {
        block = block.with_param(ValueId::new(u32::try_from(i).ok()?), ty.clone());
    }
    block.body.push(
        InstrNode::new(Inst::MakeClosure {
            ty: shape.closure,
            func: id,
            captures: (0..capture_count).map(ValueId::new).collect(),
        })
        .with_result(env),
    );
    let mut args = vec![env];
    args.extend((capture_count..n).map(ValueId::new));
    let call = InstrNode::new(Inst::Call { callee: shape.body, args });
    let returns = if apparent.returns.is_empty() {
        block.body.push(call);
        Vec::new()
    } else {
        block.body.push(call.with_result(ValueId::new(result)));
        vec![ValueId::new(result)]
    };
    block.body.push(InstrNode::new(Inst::Return { values: returns }));
    let mut function =
        Function::new(id, name, signature, BlockId::new(0)).with_producer(Producer::TRust);
    function.calling_conv = CallingConv::Rust;
    function.linkage = Linkage::Internal;
    function.blocks = vec![block];
    Some(function)
}

/// Recover only the exact construction protocol emitted above. Used before
/// assembly allocates any function IDs, so malformed synthetic bodies cannot
/// acquire an adapter identity or silently shed operations during transport.
pub(crate) fn inspect(
    function: &Function,
    closures: &[ClosureTy],
    signatures: &[FuncTy],
) -> Option<Shape> {
    let block = function.blocks.first()?;
    let Inst::MakeClosure { ty, func, .. } = &block.body.first()?.inst else {
        return None;
    };
    if *func != function.id {
        return None;
    }
    let Inst::Call { callee, .. } = &block.body.get(1)?.inst else {
        return None;
    };
    let shape = Shape { closure: *ty, body: *callee };
    let closure = closures.get(ty.as_usize())?;
    let apparent = signatures.get(closure.func.as_usize())?;
    if signatures.get(function.ty.as_usize())? != &physical_signature(closure, apparent)? {
        return None;
    }
    let expected =
        build(function.id, function.ty, function.name.clone(), shape, closure, apparent)?;
    let mut observed = function.clone();
    // The publication gate is added after assembly; it is not an executable
    // part of the construction protocol and is checked by the license owner.
    observed.body_gate = None;
    (observed == expected).then_some(shape)
}

/// Auxiliary functions inherit a source license only from an explicit
/// constructor in the already admitted source prefix and a real admitted Rust
/// closure body. Self-reference alone is not an ownership witness.
pub(crate) fn licensed_adapters(
    module: &trust_ir::Module,
    source_count: usize,
) -> Option<Vec<FuncId>> {
    if source_count > module.functions.len() {
        return None;
    }
    let source = &module.functions[..source_count];
    let mut licensed = Vec::new();
    for function in &module.functions[source_count..] {
        if function.is_declaration() || function.producer == Some(Producer::Clean) {
            continue;
        }
        let Some(shape) = inspect(function, &module.closure_types, &module.func_types) else {
            continue;
        };
        module.validate_closure_layouts().ok()?;
        module.closure_layout_descriptor(shape.closure).ok().flatten()?;
        let body = source.get(shape.body.as_usize())?;
        if body.id != shape.body || body.is_declaration() || body.producer != Some(Producer::TRust)
        {
            return None;
        }
        let owned = source.iter().any(|owner| owner.blocks.iter().flat_map(|block| &block.body).any(|node| {
            matches!(node.inst, Inst::MakeClosure { ty, func, .. } if ty == shape.closure && func == function.id)
        }));
        if !owned {
            return None;
        }
        licensed.push(function.id);
    }
    Some(licensed)
}

#[cfg(test)]
mod tests {
    use trust_ir::Ty;

    use super::*;

    fn fixture(captures: Vec<Ty>, returns: Vec<Ty>) -> (Vec<ClosureTy>, Vec<FuncTy>, Function) {
        let apparent = FuncTy { params: vec![Ty::I32], returns, is_vararg: false, abi: None };
        let closure = ClosureTy { func: FuncTyId::new(0), captures };
        let physical = physical_signature(&closure, &apparent).unwrap();
        let shape = Shape { closure: ClosureTyId::new(0), body: FuncId::new(1) };
        let function =
            build(FuncId::new(100), FuncTyId::new(1), "adapter".into(), shape, &closure, &apparent)
                .unwrap();
        (vec![closure], vec![apparent, physical], function)
    }

    #[test]
    fn recorded_abi_is_refused_without_reclassification() {
        use trust_ir::signature_abi::{
            AbiArgument, AbiFrontend, AbiPassMode, AbiTarget, SignatureAbi,
        };
        let closure = ClosureTy { func: FuncTyId::new(0), captures: vec![Ty::Ptr] };
        let mut apparent = FuncTy { params: vec![], returns: vec![], is_vararg: false, abi: None };
        assert!(physical_signature(&closure, &apparent).is_some());
        apparent.abi = Some(SignatureAbi {
            target: AbiTarget {
                triple: "aarch64-apple-darwin".into(),
                data_layout: String::new(),
                abi: String::new(),
                cpu: "generic".into(),
                features: vec![],
                target_spec: "fixture".into(),
                pointer_bytes: 8,
                little_endian: true,
            },
            frontend: AbiFrontend { name: "fixture".into(), revision: "fixture".into() },
            convention: "Rust".into(),
            lowered_convention: CallingConv::Rust,
            source_abi: "Rust".into(),
            can_unwind: false,
            variadic: false,
            fixed_count: 0,
            arguments: vec![],
            result: AbiArgument { size: 0, align: 1, mode: AbiPassMode::Ignore, bindings: vec![] },
        });
        assert!(physical_signature(&closure, &apparent).is_none());
    }

    #[test]
    fn captured_references_are_actual_parameters_not_seeds() {
        let (closures, signatures, adapter) = fixture(vec![Ty::Ptr, Ty::I32], vec![Ty::I32]);
        assert_eq!(
            inspect(&adapter, &closures, &signatures),
            Some(Shape { closure: ClosureTyId::new(0), body: FuncId::new(1) })
        );
        assert_eq!(
            adapter.blocks[0].params.iter().map(|(_, ty)| ty.clone()).collect::<Vec<_>>(),
            vec![Ty::Ptr, Ty::I32, Ty::I32]
        );
        assert!(
            matches!(&adapter.blocks[0].body[0].inst, Inst::MakeClosure { captures, .. } if captures == &[ValueId::new(0), ValueId::new(1)])
        );
        assert!(
            matches!(&adapter.blocks[0].body[1].inst, Inst::Call { args, .. } if args == &[ValueId::new(3), ValueId::new(2)])
        );
    }

    #[test]
    fn void_result_has_no_fabricated_value() {
        let (closures, signatures, adapter) = fixture(vec![Ty::Ptr], vec![]);
        assert!(inspect(&adapter, &closures, &signatures).is_some());
        assert!(adapter.blocks[0].body[1].results.is_empty());
        assert!(
            matches!(&adapter.blocks[0].body[2].inst, Inst::Return { values } if values.is_empty())
        );
    }

    #[test]
    fn wrong_capture_order_and_extra_effects_refuse() {
        let (closures, signatures, adapter) = fixture(vec![Ty::Ptr, Ty::I32], vec![Ty::I32]);
        let mut changed = adapter.clone();
        let Inst::MakeClosure { captures, .. } = &mut changed.blocks[0].body[0].inst else {
            unreachable!()
        };
        captures.swap(0, 1);
        assert!(inspect(&changed, &closures, &signatures).is_none());
        let mut changed = adapter.clone();
        changed.blocks[0].body.insert(0, InstrNode::new(Inst::Unreachable));
        assert!(inspect(&changed, &closures, &signatures).is_none());
        let mut changed = adapter;
        changed.calling_conv = CallingConv::C;
        assert!(inspect(&changed, &closures, &signatures).is_none());
    }

    fn executable_fixture(expected: i128) -> trust_ir::Module {
        use trust_ir::{BinOp, Constant, ICmpOp, Module};
        let mut module = Module::new("typed_fn_once");
        let apparent =
            FuncTy { params: vec![Ty::I32], returns: vec![Ty::I32], is_vararg: false, abi: None };
        let closure = ClosureTy { func: FuncTyId::new(0), captures: vec![Ty::Ptr] };
        module.func_types = vec![
            apparent.clone(),
            FuncTy { params: vec![], returns: vec![Ty::I32], is_vararg: false, abi: None },
            FuncTy {
                params: vec![Ty::Closure(ClosureTyId::new(0)), Ty::I32],
                returns: vec![Ty::I32],
                is_vararg: false,
                abi: None,
            },
            physical_signature(&closure, &apparent).unwrap(),
        ];
        module.closure_types = vec![closure.clone()];
        module.target_info = Some(trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        });
        module.closure_layouts = vec![trust_ir::ClosureLayoutDescriptor {
            origin: None,
            closure: ClosureTyId::new(0),
            size: 8,
            align: 8,
            capture_offsets: vec![0],
        }];
        let v = ValueId::new;
        let mut entry = Block::new(BlockId::new(0));
        entry.body = vec![
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(10) }).with_result(v(0)),
            InstrNode::new(Inst::Alloca { ty: Ty::I32, count: None, align: Some(4) })
                .with_result(v(1)),
            InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: v(1),
                value: v(0),
                volatile: false,
                align: Some(4),
            }),
            InstrNode::new(Inst::MakeClosure {
                ty: ClosureTyId::new(0),
                func: FuncId::new(2),
                captures: vec![v(1)],
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(5) }).with_result(v(3)),
            InstrNode::new(Inst::CallIndirect {
                callee: v(2),
                sig: FuncTyId::new(0),
                args: vec![v(3)],
                calling_conv: CallingConv::Rust,
            })
            .with_result(v(4)),
            InstrNode::new(Inst::Load { ty: Ty::I32, ptr: v(1), volatile: false, align: Some(4) })
                .with_result(v(5)),
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(expected) })
                .with_result(v(6)),
            InstrNode::new(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::I32, lhs: v(5), rhs: v(6) })
                .with_result(v(7)),
            InstrNode::new(Inst::Assert {
                cond: v(7),
                kind: trust_ir::AssertKind::Unspecified,
                site: None,
            }),
            InstrNode::new(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::I32, lhs: v(4), rhs: v(5) })
                .with_result(v(8)),
            InstrNode::new(Inst::Assert {
                cond: v(8),
                kind: trust_ir::AssertKind::Unspecified,
                site: None,
            }),
            InstrNode::new(Inst::Return { values: vec![v(5)] }),
        ];
        let mut main = Function::new(FuncId::new(0), "main", FuncTyId::new(1), BlockId::new(0))
            .with_producer(Producer::TRust);
        main.calling_conv = CallingConv::Rust;
        main.blocks = vec![entry];
        let mut body = Block::new(BlockId::new(0))
            .with_param(v(0), Ty::Closure(ClosureTyId::new(0)))
            .with_param(v(1), Ty::I32);
        body.body = vec![
            InstrNode::new(Inst::ExtractField { ty: Ty::Ptr, aggregate: v(0), field: 0 })
                .with_result(v(2)),
            InstrNode::new(Inst::Load { ty: Ty::I32, ptr: v(2), volatile: false, align: Some(4) })
                .with_result(v(3)),
            InstrNode::new(Inst::BinOp { op: BinOp::Add, ty: Ty::I32, lhs: v(3), rhs: v(1) })
                .with_result(v(4)),
            InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: v(2),
                value: v(4),
                volatile: false,
                align: Some(4),
            }),
            InstrNode::new(Inst::Return { values: vec![v(4)] }),
        ];
        let mut body_fn =
            Function::new(FuncId::new(1), "rust_closure_body", FuncTyId::new(2), BlockId::new(0))
                .with_producer(Producer::TRust);
        body_fn.calling_conv = CallingConv::Rust;
        body_fn.blocks = vec![body];
        let adapter = build(
            FuncId::new(2),
            FuncTyId::new(3),
            "adapter".into(),
            Shape { closure: ClosureTyId::new(0), body: FuncId::new(1) },
            &closure,
            &apparent,
        )
        .unwrap();
        module.functions = vec![main, body_fn, adapter];
        module
    }

    #[test]
    fn moved_pointer_capture_preserves_identity_and_effects() {
        let module = executable_fixture(15);
        assert!(
            trust_ir_build::validate_module(&module).is_empty(),
            "{:?}",
            trust_ir_build::validate_module(&module)
        );
        let before = module.stable_digest();
        let outcome = trust_ir::interpret::Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap();
        assert_eq!(outcome.returns[0].as_int().unwrap().as_signed(), 15);
        assert_eq!(outcome.host_calls, 0);
        assert_eq!(module.stable_digest(), before);
        assert_eq!(licensed_adapters(&module, 2), Some(vec![FuncId::new(2)]));
    }

    #[test]
    fn real_failure_survives_the_adapter() {
        let module = executable_fixture(16);
        assert!(
            trust_ir_build::validate_module(&module).is_empty(),
            "{:?}",
            trust_ir_build::validate_module(&module)
        );
        assert!(
            trust_ir::interpret::Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .is_err()
        );
    }

    #[test]
    fn detached_or_changed_adapter_has_no_codegen_license() {
        let mut module = executable_fixture(15);
        module.functions[0].blocks[0]
            .body
            .retain(|node| !matches!(node.inst, Inst::MakeClosure { .. }));
        assert!(licensed_adapters(&module, 2).is_none());
        let mut module = executable_fixture(15);
        module.functions[1].blocks.clear();
        assert!(licensed_adapters(&module, 2).is_none());
        let mut module = executable_fixture(15);
        module.closure_layouts.clear();
        assert!(licensed_adapters(&module, 2).is_none());
    }
}
