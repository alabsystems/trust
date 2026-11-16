//! Rust's `()` return convention after language-independent S substitution.
//!
//! Only exact actual-Rust Unit plans reach this adapter. Every call remains in
//! place with its arguments, span and scope; a zero-result call is followed by
//! the canonical Unit constant at the ORIGINAL result ValueId. All SSA uses
//! therefore survive, including later calls, stores, aggregates and branches.
//! Return operand producers remain. Never is not Unit. No proof/license is
//! minted, repaired, cleared or transported by this bounded data transform.

use std::collections::{BTreeMap, BTreeSet};
use trust_ir::{BodyGate, CallingConv, Constant, FuncId, FuncTy, Inst, InstrNode, Module, Ty};
use super::callable_header::UnitReturnPlan;

pub(super) fn adapt(module: Module, plans: &[UnitReturnPlan<'_>]) -> Result<Module, String> {
    let shapes = plans.iter().map(|p| {
        let (function, symbol, before, after) = p.shape()?;
        Ok(Shape { function, symbol: symbol.into(), before: before.clone(), after: after.clone() })
    }).collect::<Result<Vec<_>, String>>()?;
    adapt_shapes(module, &shapes)
}

// Data-only controls may construct a Shape. Production gets it exclusively
// from the private actual instance/FnAbi plans above, never from IR type alone.
#[derive(Clone)]
struct Shape { function: FuncId, symbol: String, before: FuncTy, after: FuncTy }

fn invalid(why: impl std::fmt::Display) -> String { format!("Rust Unit return adapter: {why}") }

/// Total shape inventory: adding a carrier must decide this scope. `None` is a shape the
/// adapter carries untouched; `Some` names why it refuses the module.
fn transport_refusal(shape: trust_ir::inst::InstShape) -> Option<String> {
    use trust_ir::inst::InstShape::*;
    match shape {
        CallIndirect | CallIndirectCannotUnwind | InvokeIndirect | OpenFrame | BindSlot
            | LoadSlot | CloseFrame | CoroSuspend | DialectOp | Undef =>
            Some("indirect/frame/coroutine/dialect/undefined transport is unavailable".to_string()),
        // Trust: trust-ir v67-v69 tensor instructions, refused by name: the adapter has no
        // tensor transport.
        TensorContract | TensorMap | TensorReduce | TensorView | TensorGather | TensorScatter =>
            Some(format!("tensor instruction {shape:?} transport is unavailable")),
        BinOp | UnOp | Overflow | ICmp | FCmp | Cast | Load | Store | Alloca | Drop
            | HeapAlloc | GEP | PtrData | PtrMetadata | PtrFromParts | AtomicLoad | AtomicStore
            | AtomicRMW | CmpXchg | Fence | Br | CondBr | Switch | Call | Return | ExtractField
            | InsertField | ExtractElement | InsertElement | Const | NullPtr | GlobalAddr
            | Assume | Assert | Unreachable | Copy | Select | SeqMapAddK | SeqMapNot
            | SeqMap | Borrow | BorrowMut | EndBorrow | Retain | Release | IsUnique | Dealloc
            | MemCopy | MemSet | Invoke | LandingPad | Resume | AssertInvoke | MakeAggregate
            | ArraySplat | CallCannotUnwind | DropInvoke | MakeClosure => None,
    }
}

fn adapt_shapes(mut module: Module, shapes: &[Shape]) -> Result<Module, String> {
    if shapes.is_empty() { return Ok(module); }
    let errors = trust_ir_build::validate::validate_module(&module);
    if !errors.is_empty() { return Err(invalid(format!("input is not validated: {errors:?}"))); }
    // This is not a proof or semantic-provenance rewrite. Refuse such inputs
    // rather than retaining stale evidence or manufacturing replacement claims.
    if !module.proof_obligations.is_empty() || !module.proof_certificates.is_empty()
        || !module.obligation_diagnostics.is_empty() || !module.spec_modules.is_empty()
        || module.completeness.is_some() || !module.global_asm.is_empty()
        || !module.imports.is_empty() || !module.globals.is_empty()
    { return Err(invalid("proof/spec/import/assembly claims require explicit transport")); }
    let mut selected = BTreeMap::new();
    for shape in shapes {
        let mut erased = shape.before.clone(); erased.returns.clear();
        let f = module.function_by_id(shape.function).ok_or_else(|| invalid("planned function disappeared"))?;
        if shape.before.returns != [Ty::Unit] || erased != shape.after
            || !shape.after.returns.is_empty() || shape.before.abi.is_some()
            || module.func_type(f.ty) != Some(&shape.before) || f.name != shape.symbol
            || f.calling_conv != CallingConv::Rust
            || (!f.is_declaration() && f.body_gate != Some(BodyGate::Ungated))
            || selected.insert(shape.function, shape).is_some()
        { return Err(invalid("plan does not bind an exact unique Rust Unit signature")); }
    }
    let names: BTreeSet<_> = selected.values().map(|s| s.symbol.as_str()).collect();
    if module.drop_glue.iter().any(|row| selected.contains_key(&row.glue)) {
        return Err(invalid("adapted destructor requires explicit transport"));
    }
    for f in &module.functions {
        if !f.proofs.is_empty() || f.summary.is_some() || f.source_provenance.is_some()
            || (!f.is_declaration() && f.body_gate != Some(BodyGate::Ungated))
        { return Err(invalid("function proof/source/gate claims require explicit transport")); }
        for node in f.instructions() {
            if !node.proofs.is_empty() || node.proof_context.is_some() {
                return Err(invalid("instruction proof/context requires explicit transport"));
            }
            match &node.inst {
                Inst::Invoke { callee, .. } | Inst::SeqMap { fwd: callee, .. }
                    | Inst::MakeClosure { func: callee, .. } if selected.contains_key(callee) =>
                    return Err(invalid("adapted unwind/map/closure reference requires explicit transport")),
                Inst::Const { value, .. } => {
                    let mut reference = false;
                    let mut uninit = false;
                    value.visit_constants(|c| { reference |= match c {
                        Constant::FnDef(id) | Constant::Closure { func: id, .. } => selected.contains_key(id),
                        Constant::SymbolAddr { symbol, .. } => names.contains(symbol.as_str()),
                        _ => false,
                    }; uninit |= matches!(c, Constant::Uninit); });
                    if reference { return Err(invalid("adapted function address requires explicit transport")); }
                    if uninit { return Err(invalid("unwritten carriers require explicit value transport")); }
                }
                _ => {}
            }
            if let Some(why) = transport_refusal(node.inst.shape()) { return Err(invalid(why)); }
        }
    }
    // Append signatures; leave every old row and unrelated signature use intact.
    for shape in shapes {
        let ty = module.add_func_type(shape.after.clone()).map_err(invalid)?;
        module.function_by_id_mut(shape.function).ok_or_else(|| invalid("planned function lost"))?.ty = ty;
    }
    for f in &mut module.functions {
        let erase_return = selected.contains_key(&f.id);
        for block in &mut f.blocks {
            let mut body = Vec::with_capacity(block.body.len());
            for mut node in std::mem::take(&mut block.body) {
                if let Inst::Return { values } = &mut node.inst {
                    if erase_return {
                        if values.len() != 1 { return Err(invalid("Unit return lost its typed operand")); }
                        values.clear();
                    }
                }
                let adapted_call = matches!(&node.inst,
                    Inst::Call { callee, .. } | Inst::CallCannotUnwind { callee, .. }
                        if selected.contains_key(callee));
                if adapted_call {
                    if node.results.len() != 1 { return Err(invalid("Unit call lost its unique typed SSA result")); }
                    let result = node.results.remove(0);
                    let mut unit = InstrNode::new(Inst::Const { ty: Ty::Unit, value: Constant::PhantomData })
                        .with_result(result);
                    // Same original location, no invented file/scope identity.
                    unit.span = node.span.clone(); unit.scope = node.scope;
                    body.push(node); body.push(unit);
                } else { body.push(node); }
            }
            block.body = body;
        }
    }
    let errors = trust_ir_build::validate::validate_module(&module);
    if !errors.is_empty() { return Err(invalid(format!("adapted output invalid: {errors:?}"))); }
    Ok(module)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{Block, BlockId, FuncTyId, Function, InterpretValue, InterpretValueKind, Interpreter, ValueId};
    fn v(id:u32)->ValueId {ValueId::new(id)}
    fn fixture()->Module {
        let mut module=Module::new("unit-adapter-data-control");
        let ty=module.add_func_type(FuncTy::unrecorded(vec![Ty::Unit],vec![Ty::Unit],false)).unwrap();
        for id in 0..2 {
            let mut f=Function::new(FuncId::new(id),format!("unit_{id}"),ty,BlockId::new(0));
            f.calling_conv=CallingConv::Rust;f.body_gate=Some(BodyGate::Ungated);
            let mut block=Block::new(BlockId::new(0)).with_param(v(0),Ty::Unit);
            if id==0 {
                block.body.push(InstrNode::new(Inst::Call{callee:FuncId::new(1),args:vec![v(0)]}).with_result(v(1)));
                block.body.push(InstrNode::new(Inst::Copy{ty:Ty::Unit,operand:v(1)}).with_result(v(2)));
                block.body.push(InstrNode::new(Inst::Call{callee:FuncId::new(1),args:vec![v(1)]}).with_result(v(3)));
                block.body.push(InstrNode::new(Inst::Call{callee:FuncId::new(1),args:vec![v(2)]}).with_result(v(4)));
                block.body.push(InstrNode::new(Inst::Return{values:vec![v(4)]}));
            } else {block.body.push(InstrNode::new(Inst::Return{values:vec![v(0)]}));}
            f.blocks.push(block);module.try_add_function(f).unwrap();
        }
        assert!(trust_ir_build::validate::validate_module(&module).is_empty());module
    }
    // These are deliberately only pure IR data controls, not fabricated actual
    // Rust FnAbi/TCX positives. The maintained TCX probe checks the real factory.
    fn shapes(module:&Module)->Vec<Shape> {
        module.functions.iter().map(|f| {
            let before=module.func_type(f.ty).unwrap().clone();let mut after=before.clone();after.returns.clear();
            Shape{function:f.id,symbol:f.name.clone(),before,after}
        }).collect()
    }
    #[test]
    fn s_unit_adapter_keeps_all_calls_and_original_ssa_uses() {
        let original=fixture();let output=adapt_shapes(original.clone(),&shapes(&original)).unwrap();
        assert_eq!(output.func_types[0],original.func_types[0],"old shared signature row survives");
        let body=&output.functions[0].blocks[0].body;
        let calls:Vec<_>=body.iter().filter_map(|n|if let Inst::Call{callee,args}=&n.inst {
            assert!(n.results.is_empty());Some((*callee,args.clone()))
        }else{None}).collect();
        assert_eq!(calls,vec![(FuncId::new(1),vec![v(0)]),(FuncId::new(1),vec![v(1)]),(FuncId::new(1),vec![v(2)])]);
        for result in [v(1),v(3),v(4)] {
            assert_eq!(body.iter().filter(|n|n.results==[result]&&matches!(n.inst,Inst::Const{ty:Ty::Unit,value:Constant::PhantomData})).count(),1);
        }
        assert!(matches!(&body[2].inst,Inst::Copy{ty:Ty::Unit,operand}if *operand==v(1)));
        assert!(matches!(&body.last().unwrap().inst,Inst::Return{values}if values.is_empty()));
        for f in &output.functions {assert_eq!(output.func_type(f.ty).unwrap().params,[Ty::Unit]);assert!(output.func_type(f.ty).unwrap().returns.is_empty());}
        let input=InterpretValue{ty:Ty::Unit,kind:InterpretValueKind::Unit};
        let before=Interpreter::with_module(&original).execute_func(FuncId::new(0),vec![input.clone()]).unwrap();
        let after=Interpreter::with_module(&output).execute_func(FuncId::new(0),vec![input]).unwrap();
        assert_eq!(before.returns.len(),1);assert!(after.returns.is_empty());
    }
    #[test]
    fn s_unit_adapter_no_plan_is_exact_identity() {
        let module=fixture();assert_eq!(adapt_shapes(module.clone(),&[]).unwrap(),module);
    }
    #[test]
    fn s_unit_adapter_does_not_normalize_unselected_language_signatures() {
        let module=fixture();let shape=shapes(&module).remove(0);
        let output=adapt_shapes(module.clone(),&[shape]).unwrap();
        assert_eq!(output.functions[1],module.functions[1]);
        assert!(output.functions[0].instructions().filter(|n|matches!(n.inst,Inst::Call{..})).all(|n|n.results.len()==1));
    }
    #[test]
    fn s_unit_adapter_rejects_wrong_identity_parameters_never_and_duplicate_rows() {
        let module=fixture();let good=shapes(&module);
        let mut rows=good.clone();rows[0].symbol.push_str("wrong");assert!(adapt_shapes(module.clone(),&rows).is_err());
        let mut rows=good.clone();rows[0].after.params.clear();assert!(adapt_shapes(module.clone(),&rows).is_err());
        let mut rows=good.clone();rows[0].before.returns=vec![Ty::Never];assert!(adapt_shapes(module.clone(),&rows).is_err());
        let mut rows=good.clone();rows.push(rows[0].clone());assert!(adapt_shapes(module,&rows).is_err());
    }
    #[test]
    fn s_unit_adapter_refuses_materialized_function_addresses() {
        let mut module=fixture();let shapes=shapes(&module);
        module.functions[0].blocks[0].body.insert(0,InstrNode::new(Inst::Const{
            ty:Ty::Func(FuncTyId::new(0)),value:Constant::FnDef(FuncId::new(1))}).with_result(v(5)));
        assert!(trust_ir_build::validate::validate_module(&module).is_empty());
        assert!(adapt_shapes(module,&shapes).unwrap_err().contains("function address"));
    }
    #[test]
    fn s_unit_adapter_preserves_undefined_and_below_tier_refusals() {
        let mut module=fixture();let shapes=shapes(&module);
        module.functions[0].blocks[0].body.insert(0,InstrNode::new(Inst::Undef{ty:Ty::Unit}).with_result(v(5)));
        assert!(trust_ir_build::validate::validate_module(&module).is_empty());
        assert!(adapt_shapes(module,&shapes).unwrap_err().contains("undefined"));
        let mut module=fixture();module.functions[0].body_gate=None;
        assert!(adapt_shapes(module,&shapes).unwrap_err().contains("exact unique Rust Unit"));
    }
    #[test]
    fn s_unit_adapter_refuses_each_tensor_instruction_by_name() {
        use trust_ir::inst::InstShape;
        for (shape, name) in [
            (InstShape::TensorContract, "TensorContract"), (InstShape::TensorMap, "TensorMap"),
            (InstShape::TensorReduce, "TensorReduce"), (InstShape::TensorView, "TensorView"),
            (InstShape::TensorGather, "TensorGather"), (InstShape::TensorScatter, "TensorScatter"),
        ] {
            let why = transport_refusal(shape).expect("a tensor instruction is refused");
            assert!(why.contains(name), "{name} must be refused by name: {why}");
        }
        assert!(transport_refusal(InstShape::CallIndirect).is_some(), "existing refusal kept");
        assert!(transport_refusal(InstShape::Call).is_none(), "positive control");
    }
}
