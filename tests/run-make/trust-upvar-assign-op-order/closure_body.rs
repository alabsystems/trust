//! Diagnostic caller for an unchanged emitted closure body; not production closure lowering.

use super::reference;
use reference::{Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId};

pub fn caller(module: &Module, name: &str, ty: Ty, initial: i128) -> (Module, FuncId) {
    let path = format!("{name}::{{closure#0}}");
    let matches: Vec<_> = module.functions.iter()
        .filter(|f| f.display_path.as_deref() == Some(path.as_str())).collect();
    assert_eq!(matches.len(), 1, "exact emitted closure {path}");
    let callee = matches[0];
    let sig = module.func_type(callee.ty).unwrap();
    let by_value = name == "by_value_capture";
    assert_eq!(sig.params, vec![Ty::Ptr]);
    assert_eq!(sig.returns, if by_value { vec![ty.clone()] } else { vec![] });
    assert!(!sig.is_vararg);
    let mut block = Block::new(BlockId::new(0));
    let mut next = 0;
    macro_rules! value {
        ($inst:expr) => {{
            let value = ValueId::new(next);
            next += 1;
            block.body.push(InstrNode::new($inst).with_result(value));
            value
        }};
    }
    let initial = value!(Inst::Const { ty: ty.clone(), value: Constant::Int(initial) });
    let slot = value!(Inst::Alloca { ty: ty.clone(), count: None, align: None });
    block.body.push(InstrNode::new(Inst::Store {
        ty: ty.clone(), ptr: slot, value: initial, volatile: false, align: None,
    }));
    let env_ty = Ty::Tuple(vec![if by_value { ty.clone() } else { Ty::Ptr }]);
    let empty = value!(Inst::Const {
        ty: env_ty.clone(), value: Constant::Aggregate(vec![Constant::Uninit]),
    });
    let env_value = value!(Inst::InsertField {
        ty: env_ty.clone(), aggregate: empty, field: 0,
        value: if by_value { initial } else { slot },
    });
    let env = value!(Inst::Alloca { ty: env_ty.clone(), count: None, align: None });
    block.body.push(InstrNode::new(Inst::Store {
        ty: env_ty, ptr: env, value: env_value, volatile: false, align: None,
    }));
    let result = if by_value {
        value!(Inst::Call { callee: callee.id, args: vec![env] })
    } else {
        block.body.push(InstrNode::new(Inst::Call { callee: callee.id, args: vec![env] }));
        value!(Inst::Load { ty: ty.clone(), ptr: slot, volatile: false, align: None })
    };
    let _ = next;
    block.body.push(InstrNode::new(Inst::Return { values: vec![result] }));
    let mut extended = module.clone();
    let id = FuncId::new(module.functions.iter().map(|f| f.id.0).max().unwrap().checked_add(1).unwrap());
    let function_type = extended.add_func_type(FuncTy {
        params: vec![], returns: vec![ty], is_vararg: false, abi: None,
    }).unwrap();
    let mut function = Function::new(id, "diagnostic_upvar_caller", function_type, BlockId::new(0));
    function.blocks.push(block);
    extended.try_add_function(function).unwrap();
    // The harness adds a caller only. It cannot repair or replace an emitted instruction.
    let mut restored = extended.clone();
    restored.functions.truncate(module.functions.len());
    restored.func_types.truncate(module.func_types.len());
    assert_eq!(reference::binary::serialize_module(&restored), reference::binary::serialize_module(module));
    (extended, id)
}
