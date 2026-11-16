//! Diagnostic execution of unchanged producer modules and exact assignment cases.

#[path = "array_write_tests/temporary_support.rs"]
pub mod temporary_support;

use trust_ir::interpret::{InterpretErrorCode, InterpretOptions, Interpreter};
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

const A: [u8; 4] = [11, 22, 33, 44];
const B: [u8; 4] = [101, 102, 103, 104];

#[derive(Debug, Clone, Copy)]
pub enum Arg {
    Array([u8; 4]),
    Index(u64),
    Byte(u8),
}

fn run(module: &Module, name: &str, args: &[Arg]) -> Outcome {
    let found: Vec<_> = module.functions.iter().filter(|f| f.name == name).collect();
    assert_eq!(found.len(), 1, "missing/duplicate actual function {name}");
    let callee = found[0];
    let sig = module.func_type(callee.ty).unwrap();
    assert_eq!(sig.params.len(), args.len());
    assert_eq!(sig.returns, vec![Ty::U8]);
    assert!(!sig.is_vararg);
    let mut block = Block::new(BlockId::new(0));
    let mut values = Vec::new();
    for (i, (arg, ty)) in args.iter().zip(&sig.params).enumerate() {
        let value = match arg {
            Arg::Array(bytes) => {
                assert!(
                    matches!(ty, Ty::Array(id, 4) if module.types.get(id.0 as usize) == Some(&Ty::U8))
                );
                Constant::array(bytes.iter().map(|v| Constant::Int(i128::from(*v))).collect())
            }
            Arg::Index(index) => {
                assert_eq!(*ty, Ty::Usize);
                Constant::Int(i128::from(*index))
            }
            Arg::Byte(byte) => {
                assert_eq!(*ty, Ty::U8);
                Constant::Int(i128::from(*byte))
            }
        };
        let id = ValueId::new(u32::try_from(i).unwrap());
        block.body.push(InstrNode::new(Inst::Const { ty: ty.clone(), value }).with_result(id));
        values.push(id);
    }
    let result = ValueId::new(u32::try_from(args.len()).unwrap());
    block
        .body
        .push(InstrNode::new(Inst::Call { callee: callee.id, args: values }).with_result(result));
    block.body.push(InstrNode::new(Inst::Return { values: vec![result] }));
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
    let mut caller = Function::new(id, "diagnostic_write_caller", ty, BlockId::new(0));
    caller.blocks.push(block);
    extended.try_add_function(caller).expect("Module::try_add_function: test fixture");
    assert!(trust_ir_build::validate_module(&extended).is_empty());
    let mut restored = extended.clone();
    restored.functions.truncate(module.functions.len());
    restored.func_types.truncate(module.func_types.len());
    assert_eq!(
        trust_ir::binary::serialize_module(&restored),
        trust_ir::binary::serialize_module(module)
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    Returned(u8),
    Panic,
    Other(String),
}

#[derive(Debug)]
pub struct Observation {
    pub function: &'static str,
    pub args: Vec<Arg>,
    pub expected: Outcome,
    pub actual: Outcome,
}

fn after_store(array: [u8; 4], index: u64, value: u8, read: u64) -> Outcome {
    if index >= 4 || read >= 4 {
        Outcome::Panic
    } else {
        Outcome::Returned(if index == read { value } else { array[read as usize] })
    }
}

/// The same 180-case population measured against the actual native Rust fixture.
/// This finite diagnostic is not a universal source-refinement certificate.
pub fn observe(module: &Module) -> Vec<Observation> {
    let mut cases = Vec::new();
    let mut add = |function, args: &[Arg], expected| {
        cases.push(Observation {
            function,
            args: args.to_vec(),
            expected,
            actual: run(module, function, args),
        });
    };
    for index in [0, 1, 2, 3, 4, u64::MAX] {
        for read in [0, 1, 2, 3, 4] {
            let args = [Arg::Array(A), Arg::Array(B), Arg::Index(index), Arg::Index(read)];
            add("rhs_reseats_array", &args, after_store(B, index, 99, read));
            add("index_reseats_array", &args, after_store(B, index, 99, read));
            for value in [5, 77, 129] {
                let args = [Arg::Array(A), Arg::Index(index), Arg::Byte(value), Arg::Index(read)];
                add("pure_array_write", &args, after_store(A, index, value, read));
            }
        }
        add("rhs_before_index", &[Arg::Array(A), Arg::Index(index)], Outcome::Returned(99));
        for value in [5, 77, 129] {
            let args = [Arg::Array(A), Arg::Index(index), Arg::Byte(value)];
            add("rhs_value_is_captured", &args, after_store(A, index, value, index));
        }
        add(
            "const_write_preserves_rhs_reseat",
            &[Arg::Array(A), Arg::Array(B), Arg::Index(index)],
            after_store(B, 1, 99, index),
        );
    }
    assert_eq!(cases.len(), 180);
    cases
}

fn module() -> Module {
    let path = std::env::var_os("TRUST_ARRAY_WRITE_IR")
        .expect("fresh compiler-bound array-write IR required");
    let bytes = std::fs::read(path).unwrap();
    assert!(bytes.len() < 4 * 1024 * 1024);
    let module = trust_ir::binary::deserialize_module(&bytes).unwrap();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

fn check_subject(module: &Module) {
    for name in [
        "rhs_reseats_array",
        "index_reseats_array",
        "rhs_before_index",
        "rhs_value_is_captured",
        "pure_array_write",
        "const_write_preserves_rhs_reseat",
    ] {
        let found: Vec<_> = module.functions.iter().filter(|f| f.name == name).collect();
        assert_eq!(found.len(), 1);
        let f = found[0];
        assert_eq!(
            f.blocks
                .iter()
                .flat_map(|b| &b.body)
                .filter(|n| matches!(n.inst, Inst::Assert { .. }))
                .count(),
            2
        );
        let obligations: Vec<_> =
            module.proof_obligations.iter().filter(|r| r.function == Some(f.id)).collect();
        assert_eq!(obligations.len(), 2);
        assert!(obligations.iter().all(|r| r.status == trust_ir::ProofStatus::Pending));
    }
    for observation in observe(module) {
        assert_eq!(observation.actual, observation.expected, "{observation:?}");
    }
}

#[test]
#[ignore = "requires freshly emitted compiler-bound array assignment module"]
fn actual_array_writes_preserve_rhs_index_and_current_destination() {
    check_subject(&module());
}

#[test]
#[ignore = "requires fixed subject; changed IR is diagnostic only"]
fn actual_array_write_controls_detect_stale_operands_and_wrong_bounds() {
    let module = module();
    check_subject(&module);
    for name in ["rhs_reseats_array", "index_reseats_array", "const_write_preserves_rhs_reseat"] {
        let mut stale = module.clone();
        let f = stale.functions.iter_mut().find(|f| f.name == name).unwrap();
        let original = f.blocks.iter().find(|b| b.id == f.entry).unwrap().params[0].0;
        let mut edits = 0;
        for node in f.blocks.iter_mut().flat_map(|b| &mut b.body) {
            if let Inst::InsertElement { array, .. } = &mut node.inst {
                assert_ne!(*array, original);
                *array = original;
                edits += 1;
            }
        }
        assert_eq!(edits, 1);
        let mut args = vec![Arg::Array(A), Arg::Array(B)];
        if name != "const_write_preserves_rhs_reseat" {
            args.push(Arg::Index(1));
        }
        args.push(Arg::Index(0));
        assert_eq!(run(&stale, name, &args), Outcome::Returned(11));
    }
    let mut recaptured = module.clone();
    let f = recaptured.functions.iter_mut().find(|f| f.name == "rhs_value_is_captured").unwrap();
    let wrong: Vec<_> = f
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter_map(|n| {
            matches!(n.inst, Inst::Const { ty: Ty::U8, value: Constant::Int(77) })
                .then(|| n.results[0])
        })
        .collect();
    assert_eq!(wrong.len(), 1);
    let mut edits = 0;
    for node in f.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::InsertElement { value, .. } = &mut node.inst {
            assert_ne!(*value, wrong[0]);
            *value = wrong[0];
            edits += 1;
        }
    }
    assert_eq!(edits, 1);
    assert_eq!(
        run(&recaptured, "rhs_value_is_captured", &[Arg::Array(A), Arg::Index(1), Arg::Byte(129)]),
        Outcome::Returned(77)
    );

    let mut old_index = module.clone();
    let f = old_index.functions.iter_mut().find(|f| f.name == "rhs_before_index").unwrap();
    let wrong = f.blocks.iter().find(|b| b.id == f.entry).unwrap().params[1].0;
    let mut edits = 0;
    for node in f.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::InsertElement { index, .. } = &mut node.inst {
            assert_ne!(*index, wrong);
            *index = wrong;
            edits += 1;
        }
    }
    assert_eq!(edits, 1);
    assert_eq!(
        run(&old_index, "rhs_before_index", &[Arg::Array(A), Arg::Index(0)]),
        Outcome::Returned(33)
    );

    let mut reversed = module.clone();
    let f = reversed.functions.iter_mut().find(|f| f.name == "pure_array_write").unwrap();
    let comparison = f
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.body)
        .find(|n| matches!(n.inst, Inst::ICmp { .. }))
        .unwrap();
    let Inst::ICmp { op, .. } = &mut comparison.inst else { unreachable!() };
    assert_eq!(*op, trust_ir::ICmpOp::Ult);
    *op = trust_ir::ICmpOp::Uge;
    assert_eq!(
        run(
            &reversed,
            "pure_array_write",
            &[Arg::Array(A), Arg::Index(1), Arg::Byte(129), Arg::Index(0)]
        ),
        Outcome::Panic
    );
}
