//! Concrete execution of the actual array-place producer; never a replacement callee.

use trust_ir::interpret::{InterpretErrorCode, InterpretOptions, Interpreter};
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode, Module,
    ProofStatus, Ty, ValueId,
};

const NAMES: [&str; 3] =
    ["reseat_array", "array_index_value_is_captured", "reseat_array_through_alias"];
const A: [u8; 4] = [11, 22, 33, 44];
const B: [u8; 4] = [101, 102, 103, 104];

#[path = "array_support/projected_support.rs"]
mod projected_support;
#[path = "array_support/rvalue_support.rs"]
mod rvalue_support;

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Returned(u8),
    Panic,
    Other(String),
}

fn function<'a>(module: &'a Module, name: &str) -> &'a Function {
    let matches: Vec<_> = module.functions.iter().filter(|f| f.name == name).collect();
    assert_eq!(matches.len(), 1, "missing/duplicate actual function {name}");
    matches[0]
}

fn run(module: &Module, name: &str, index: u64) -> Outcome {
    let callee = function(module, name);
    let signature = module.func_type(callee.ty).unwrap();
    let two_arrays = name != NAMES[1];
    assert_eq!(signature.params.len(), if two_arrays { 3 } else { 2 });
    assert_eq!(signature.params.last(), Some(&Ty::Usize));
    assert_eq!(signature.returns, vec![Ty::U8]);
    assert!(!signature.is_vararg);
    let mut block = Block::new(BlockId::new(0));
    let mut args = Vec::new();
    for (position, ty) in signature.params[..signature.params.len() - 1].iter().enumerate() {
        assert!(matches!(ty, Ty::Array(id, 4) if module.types.get(id.0 as usize) == Some(&Ty::U8)));
        let values = if position == 0 { A } else { B };
        let id = ValueId::new(position as u32);
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::array(values.map(|v| Constant::Int(i128::from(v))).to_vec()),
            })
            .with_result(id),
        );
        args.push(id);
    }
    let index_id = ValueId::new(args.len() as u32);
    block.body.push(
        InstrNode::new(Inst::Const { ty: Ty::Usize, value: Constant::Int(i128::from(index)) })
            .with_result(index_id),
    );
    args.push(index_id);
    let result_id = ValueId::new(args.len() as u32);
    block.body.push(InstrNode::new(Inst::Call { callee: callee.id, args }).with_result(result_id));
    block.body.push(InstrNode::new(Inst::Return { values: vec![result_id] }));
    let mut extended = module.clone();
    let id =
        FuncId::new(module.functions.iter().map(|f| f.id.0).max().unwrap().checked_add(1).unwrap());
    let ty = extended
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U8],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut wrapper = Function::new(id, "diagnostic_array_caller", ty, BlockId::new(0));
    wrapper.blocks.push(block);
    extended.try_add_function(wrapper).expect("Module::try_add_function: test fixture");
    assert!(trust_ir_build::validate_module(&extended).is_empty(), "invalid actual module/wrapper");
    let mut restored = extended.clone();
    restored.functions.truncate(module.functions.len());
    restored.func_types.truncate(module.func_types.len());
    assert_eq!(
        trust_ir::binary::serialize_module(&restored),
        trust_ir::binary::serialize_module(module),
        "all original bodies, instructions and obligations must remain unchanged"
    );
    match Interpreter::with_module(&extended)
        .with_options(InterpretOptions { fuel: 10_000, max_call_depth: 8, ..Default::default() })
        .execute_func(id, [])
    {
        Ok(result) => {
            assert_eq!(result.returns.len(), 1);
            assert_eq!(result.returns[0].ty, Ty::U8);
            Outcome::Returned(
                u8::try_from(result.returns[0].as_int().unwrap().as_unsigned()).unwrap(),
            )
        }
        Err(error) if error.code == InterpretErrorCode::Panic => Outcome::Panic,
        Err(error) => Outcome::Other(error.to_string()),
    }
}

fn check_subject(module: &Module) {
    let mut cases = 0;
    for name in NAMES {
        let function = function(module, name);
        let nodes: Vec<_> = function.blocks.iter().flat_map(|b| &b.body).collect();
        assert_eq!(nodes.iter().filter(|n| matches!(n.inst, Inst::Assert { .. })).count(), 1);
        let obligations: Vec<_> =
            module.proof_obligations.iter().filter(|r| r.function == Some(function.id)).collect();
        assert_eq!(obligations.len(), 1);
        assert_eq!(obligations[0].status, ProofStatus::Pending);
        for index in [0, 1, 2, 3, 4, u64::MAX] {
            let expected = if index >= 4 {
                Outcome::Panic
            } else {
                Outcome::Returned(if name == NAMES[1] { A } else { B }[index as usize])
            };
            assert_eq!(run(module, name, index), expected, "{name}: index={index}");
            cases += 1;
        }
    }
    assert_eq!(cases, 18);
}

#[test]
#[ignore = "requires the freshly emitted, compiler-bound array-place module"]
fn actual_array_places_read_after_index_effects_and_preserve_bounds() {
    check_subject(&super::module("TRUST_ARRAY_PLACE_IR"));
}

#[test]
#[ignore = "requires the fixed subject; diagnostic mutations never supply authority"]
fn actual_array_place_controls_detect_stale_values_and_changed_indices() {
    let module = super::module("TRUST_ARRAY_PLACE_IR");
    check_subject(&module);
    for name in [NAMES[0], NAMES[2]] {
        let mut stale = module.clone();
        let function = stale.functions.iter_mut().find(|f| f.name == name).unwrap();
        let original = function.blocks.iter().find(|b| b.id == function.entry).unwrap().params[0].0;
        let mut changed = 0;
        for node in function.blocks.iter_mut().flat_map(|b| &mut b.body) {
            if let Inst::ExtractElement { array, .. } = &mut node.inst {
                assert_ne!(*array, original, "subject already uses the stale array");
                *array = original;
                changed += 1;
            }
        }
        assert_eq!(changed, 1);
        assert_eq!(run(&stale, name, 0), Outcome::Returned(A[0]));
    }
    let mut reversed = module.clone();
    let function = reversed.functions.iter_mut().find(|f| f.name == NAMES[1]).unwrap();
    let mut changed = 0;
    for node in function.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::ICmp { op, .. } = &mut node.inst {
            assert_eq!(*op, ICmpOp::Ult);
            *op = ICmpOp::Uge;
            changed += 1;
        }
    }
    assert_eq!(changed, 1);
    assert_eq!(run(&reversed, NAMES[1], 0), Outcome::Panic);
    let mut recaptured = module.clone();
    let function = recaptured.functions.iter_mut().find(|f| f.name == NAMES[1]).unwrap();
    let zeros: Vec<_> = function
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter_map(|n| {
            matches!(n.inst, Inst::Const { ty: Ty::Usize, value: Constant::Int(0) })
                .then(|| n.results[0])
        })
        .collect();
    assert_eq!(zeros.len(), 1);
    let mut changed = 0;
    for node in function.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::ExtractElement { index, .. } = &mut node.inst {
            assert_ne!(*index, zeros[0]);
            *index = zeros[0];
            changed += 1;
        }
    }
    assert_eq!(changed, 1);
    assert_eq!(run(&recaptured, NAMES[1], 1), Outcome::Returned(A[0]));
}
