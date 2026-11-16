//! Shared diagnostic controls over actual emitted modules, never copied IR.
//! Only std and the existing trust-ir/trust-ir-build APIs are required.

use std::path::Path;

use trust_ir::interpret::{InterpretErrorCode, InterpretOptions, Interpreter};
use trust_ir::{
    Block, BlockId, Constant, FatPtrKind, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode,
    Module, Ty, ValueId,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Returned(u8),
    Panic,
    Other(String),
}

#[derive(Clone, Debug)]
pub struct Observation {
    pub case: String,
    pub function: String,
    pub function_id: u32,
    pub a_len: u64,
    pub b_len: Option<u64>,
    pub index: Option<u64>,
    pub expected: Outcome,
    pub actual: Outcome,
    pub details: String,
    pub original_functions: usize,
    pub original_obligations: usize,
    pub source_call_count: usize,
    pub expected_call_count: Option<usize>,
}

impl Observation {
    pub fn agrees(&self) -> bool {
        self.actual == self.expected
            && self.expected_call_count.is_none_or(|count| self.source_call_count == count)
    }
}

struct Driver {
    block: Block,
    next: u32,
}
impl Driver {
    fn new() -> Self {
        Self { block: Block::new(BlockId::new(0)), next: 0 }
    }
    fn value(&mut self, inst: Inst) -> ValueId {
        let value = ValueId::new(self.next);
        self.next += 1;
        self.block.body.push(InstrNode::new(inst).with_result(value));
        value
    }
    fn constant(&mut self, ty: Ty, value: i128) -> ValueId {
        self.value(Inst::Const { ty, value: Constant::Int(value) })
    }
    fn slice(&mut self, fat_ty: Ty, bytes: [u8; 4], len: u64) -> ValueId {
        assert!(len <= 4, "metadata must describe a valid slice within the allocation");
        let count = self.constant(Ty::U64, 4);
        let data = self.value(Inst::Alloca { ty: Ty::U8, count: Some(count), align: None });
        for (offset, byte) in bytes.into_iter().enumerate() {
            let offset = self.constant(Ty::U64, offset as i128);
            let pointer = self.value(Inst::GEP {
                pointee_ty: Ty::U8,
                base: data,
                indices: vec![offset],
                inbounds: false,
            });
            let byte = self.constant(Ty::U8, i128::from(byte));
            self.block.body.push(InstrNode::new(Inst::Store {
                ty: Ty::U8,
                ptr: pointer,
                value: byte,
                volatile: false,
                align: None,
            }));
        }
        let metadata = self.constant(Ty::U64, i128::from(len));
        self.value(Inst::PtrFromParts { ptr_ty: fat_ty, metadata_ty: Ty::U64, data, metadata })
    }
}

fn slice_u8(module: &Module, ty: &Ty) -> bool {
    matches!(ty, Ty::FatPtr(FatPtrKind::Slice(id)) if module.types.get(id.0 as usize) == Some(&Ty::U8))
}

fn selected_id(module: &Module, name: &str) -> FuncId {
    let matches: Vec<_> =
        module.functions.iter().filter(|function| function.name == name).collect();
    assert_eq!(matches.len(), 1, "exact diagnostic function selection: {name}");
    matches[0].id
}

fn run_case(
    module: &Module,
    function_name: &str,
    case: &str,
    a_len: u64,
    b_len: Option<u64>,
    index: Option<u64>,
    expected: Outcome,
    expected_calls: Option<usize>,
) -> Observation {
    let id = selected_id(module, function_name);
    let callee = module.function_by_id(id).unwrap();
    let signature = module.func_type(callee.ty).expect("actual signature").clone();
    assert_eq!(signature.returns, vec![Ty::U8]);
    assert!(!signature.is_vararg);
    let mut driver = Driver::new();
    let mut args = Vec::new();
    if function_name == "read_array" {
        assert!(
            matches!(&signature.params[0], Ty::Array(elem, 4) if module.types.get(elem.0 as usize) == Some(&Ty::U8))
        );
        args.push(driver.value(Inst::Const {
            ty: signature.params[0].clone(),
            value: Constant::Array([11, 22, 33, 44].map(Constant::Int).to_vec()),
        }));
    } else {
        assert!(slice_u8(module, &signature.params[0]));
        args.push(driver.slice(signature.params[0].clone(), [11, 22, 33, 44], a_len));
        if let Some(b_len) = b_len {
            assert!(slice_u8(module, &signature.params[1]));
            args.push(driver.slice(signature.params[1].clone(), [101, 102, 103, 104], b_len));
        }
    }
    if let Some(index) = index {
        let index_ty = signature.params[args.len()].clone();
        assert!(matches!(index_ty, Ty::Usize | Ty::U64));
        args.push(driver.constant(index_ty, i128::from(index)));
    }
    assert_eq!(signature.params.len(), args.len(), "do not ignore an actual formal parameter");
    let source_call_count = callee
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .filter(|node| matches!(node.inst, Inst::Call { .. } | Inst::CallIndirect { .. }))
        .count();
    let result = driver.value(Inst::Call { callee: id, args });
    driver.block.body.push(InstrNode::new(Inst::Return { values: vec![result] }));
    let mut extended = module.clone();
    let wrapper_id = FuncId::new(
        module
            .functions
            .iter()
            .map(|function| function.id.0)
            .max()
            .unwrap()
            .checked_add(1)
            .unwrap(),
    );
    let sig = extended
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U8],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut wrapper =
        Function::new(wrapper_id, format!("diagnostic_driver_{case}"), sig, BlockId::new(0));
    wrapper.blocks.push(driver.block);
    extended.try_add_function(wrapper).expect("Module::try_add_function: test fixture");
    let errors = trust_ir_build::validate_module(&extended);
    assert!(errors.is_empty(), "invalid extended diagnostic module: {errors:?}");
    // Preserve all original computational and noncomputational fields, not
    // only the callee instructions. Adding a wrapper cannot hide obligations.
    let mut restored = extended.clone();
    restored.functions.truncate(module.functions.len());
    restored.func_types.truncate(module.func_types.len());
    assert_eq!(
        trust_ir::binary::serialize_module(&restored),
        trust_ir::binary::serialize_module(module)
    );
    let result = Interpreter::with_module(&extended)
        .with_options(InterpretOptions { fuel: 10_000, max_call_depth: 8, ..Default::default() })
        .execute_func(wrapper_id, []);
    let (actual, details) = match result {
        Ok(outcome) => {
            assert_eq!(outcome.returns.len(), 1);
            assert_eq!(outcome.returns[0].ty, Ty::U8);
            let value = u8::try_from(outcome.returns[0].as_int().expect("u8 result").as_unsigned())
                .unwrap();
            (Outcome::Returned(value), format!("steps={}", outcome.steps))
        }
        Err(error) => (
            if error.code == InterpretErrorCode::Panic {
                Outcome::Panic
            } else {
                Outcome::Other(error.code.as_str().into())
            },
            error.to_string(),
        ),
    };
    Observation {
        case: case.into(),
        function: function_name.into(),
        function_id: id.0,
        a_len,
        b_len,
        index,
        expected,
        actual,
        details,
        original_functions: module.functions.len(),
        original_obligations: module.proof_obligations.len(),
        source_call_count,
        expected_call_count: expected_calls,
    }
}

pub fn read_module(path: &Path) -> Module {
    assert!(std::fs::metadata(path).expect("actual module metadata").len() < 4 * 1024 * 1024);
    let bytes = std::fs::read(path).expect("actual emitted module bytes");
    let module = trust_ir::binary::deserialize_module(&bytes).expect("actual tMBC module decode");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "actual module is invalid: {errors:?}");
    module
}

/// A cast captures both the slice data and its metadata before index effects.
pub fn observe_rvalue_slice_cases(module: &Module) -> Vec<Observation> {
    use Outcome::{Panic, Returned};
    [
        ("cast_slice_value", 4, 4, 1, Returned(22)),
        ("cast_slice_a_short", 1, 4, 1, Panic),
        ("cast_slice_b_short", 4, 1, 1, Returned(22)),
        ("cast_slice_a_empty", 0, 4, 0, Panic),
        ("cast_slice_b_empty", 4, 0, 0, Returned(11)),
        ("cast_slice_last", 4, 4, 3, Returned(44)),
        ("cast_slice_boundary", 4, 4, 4, Panic),
        ("cast_slice_max", 4, 4, u64::MAX, Panic),
    ]
    .into_iter()
    .map(|(case, a_len, b_len, index, expected)| {
        run_case(module, "cast_slice_value", case, a_len, Some(b_len), Some(index), expected, None)
    })
    .collect()
}

pub fn check_rvalue_slice_mutants(module: &Module) {
    for metadata in [false, true] {
        let mut changed = module.clone();
        let id = selected_id(&changed, "cast_slice_value");
        let f = changed.functions.iter_mut().find(|f| f.id == id).unwrap();
        let wrong = f.blocks.iter().find(|b| b.id == f.entry).unwrap().params[1].0;
        let mut edits = 0;
        for node in f.blocks.iter_mut().flat_map(|b| &mut b.body) {
            let operand = match &mut node.inst {
                Inst::PtrMetadata { ptr, .. } if metadata => Some(ptr),
                Inst::PtrData { ptr, .. } if !metadata => Some(ptr),
                _ => None,
            };
            if let Some(operand) = operand {
                assert_ne!(*operand, wrong);
                *operand = wrong;
                edits += 1;
            }
        }
        assert_eq!(edits, 1);
        let observation = run_case(
            &changed,
            "cast_slice_value",
            if metadata { "recaptured_slice_metadata" } else { "recaptured_slice_data" },
            if metadata { 1 } else { 4 },
            Some(4),
            Some(1),
            if metadata { Outcome::Panic } else { Outcome::Returned(22) },
            None,
        );
        assert!(!observation.agrees(), "mutation escaped: {observation:?}");
        assert_eq!(observation.actual, Outcome::Returned(if metadata { 22 } else { 102 }));
    }
}

/// The unchanged original 15 runtime controls. Every mismatch remains visible.
pub fn observe_original_cases(slice: &Module, place_order: &Module) -> Vec<Observation> {
    use Outcome::{Panic, Returned};
    let mut cases = Vec::new();
    for (case, len, index, expected) in [
        ("slice_in_bounds", 4, 1, Returned(22)),
        ("slice_short_in_bounds", 1, 0, Returned(11)),
        ("slice_length_oob_inside_allocation", 1, 1, Panic),
        ("slice_empty_inside_allocation", 0, 0, Panic),
        ("slice_allocation_boundary", 4, 4, Panic),
        ("slice_last_in_bounds", 4, 3, Returned(44)),
        ("slice_short_far_inside_allocation", 1, 3, Panic),
    ] {
        cases.push(run_case(slice, "read_slice", case, len, None, Some(index), expected, None));
    }
    for (case, a_len, b_len, index, expected) in [
        ("reseat_selects_b", 4, 4, 1, Returned(102)),
        ("reseat_b_short", 4, 1, 1, Panic),
        ("reseat_a_short_b_valid", 1, 4, 1, Returned(102)),
        ("reseat_a_empty_b_valid", 0, 4, 0, Returned(101)),
        ("reseat_b_empty", 4, 0, 0, Panic),
    ] {
        cases.push(run_case(
            place_order,
            "reseat_index",
            case,
            a_len,
            Some(b_len),
            Some(index),
            expected,
            None,
        ));
    }
    cases.push(run_case(
        place_order,
        "index_value_is_captured",
        "index_value_capture",
        4,
        None,
        Some(1),
        Returned(22),
        None,
    ));
    cases.push(run_case(
        slice,
        "read_array",
        "array_in_bounds",
        4,
        None,
        Some(1),
        Returned(22),
        None,
    ));
    cases.push(run_case(
        slice,
        "read_array",
        "array_boundary_panics",
        4,
        None,
        Some(4),
        Panic,
        None,
    ));
    cases
}

/// Two additional effectful-base controls, including exact static call count.
/// These do not pretend to execute the separately refused alias/counted body.
pub fn observe_effect_cases(effects: &Module) -> Vec<Observation> {
    vec![
        run_case(
            effects,
            "call_base_is_captured",
            "effectful_base_uses_original_selector",
            4,
            Some(4),
            Some(1),
            Outcome::Returned(22),
            Some(1),
        ),
        run_case(
            effects,
            "base_effect_precedes_index",
            "base_effect_precedes_captured_index",
            4,
            Some(4),
            None,
            Outcome::Returned(102),
            Some(1),
        ),
    ]
}

pub fn missing_effect_functions(effects: &Module) -> Vec<&'static str> {
    ["reseat_through_alias", "call_base_runs_once"]
        .into_iter()
        .filter(|name| !effects.functions.iter().any(|function| function.name == *name))
        .collect()
}

/// Independent negative mutants of FRESH subject modules. Mutation is confined
/// to diagnostic clones. Each must produce a wrong runtime result, not merely
/// an invalid-module error. The unmutated subject must first pass all cases.
pub fn observe_subject_mutants(slice: &Module, place_order: &Module) -> Vec<Observation> {
    for case in observe_original_cases(slice, place_order) {
        assert!(case.agrees(), "unfixed subject cannot qualify mutants: {case:?}");
    }
    let mut cases = Vec::new();
    let id = selected_id(slice, "read_slice");
    let mut removed = slice.clone();
    let function = removed.functions.iter_mut().find(|function| function.id == id).unwrap();
    assert_eq!(function.blocks.len(), 1);
    let sites: Vec<_> = function.blocks[0]
        .body
        .iter()
        .enumerate()
        .filter_map(|(i, node)| matches!(node.inst, Inst::Assert { .. }).then_some(i))
        .collect();
    assert_eq!(sites.len(), 1);
    function.blocks[0].body.remove(sites[0]);
    // This mutant DELIBERATELY drops exactly that born policy row as well.
    // It demonstrates the missing-check behavior, never valid source authority.
    assert_eq!(removed.proof_obligations.iter().filter(|row| row.function == Some(id)).count(), 1);
    removed.proof_obligations.retain(|row| row.function != Some(id));
    cases.push(run_case(
        &removed,
        "read_slice",
        "mutant_drop_assert_and_its_policy_row",
        1,
        None,
        Some(1),
        Outcome::Panic,
        None,
    ));
    let mut reversed = slice.clone();
    let function = reversed.functions.iter_mut().find(|function| function.id == id).unwrap();
    let mut count = 0;
    for node in function.blocks.iter_mut().flat_map(|block| &mut block.body) {
        if let Inst::ICmp { op, .. } = &mut node.inst {
            assert_eq!(*op, ICmpOp::Ult);
            *op = ICmpOp::Uge;
            count += 1;
        }
    }
    assert_eq!(count, 1);
    cases.push(run_case(
        &reversed,
        "read_slice",
        "mutant_reverse_bounds_comparator",
        1,
        None,
        Some(0),
        Outcome::Returned(11),
        None,
    ));
    for metadata in [true, false] {
        let id = selected_id(place_order, "reseat_index");
        let mut stale = place_order.clone();
        let function = stale.functions.iter_mut().find(|function| function.id == id).unwrap();
        let a =
            function.blocks.iter().find(|block| block.id == function.entry).unwrap().params[0].0;
        let mut count = 0;
        for node in function.blocks.iter_mut().flat_map(|block| &mut block.body) {
            match &mut node.inst {
                Inst::PtrMetadata { ptr, .. } if metadata => {
                    assert_ne!(*ptr, a);
                    *ptr = a;
                    count += 1;
                }
                Inst::PtrData { ptr, .. } if !metadata => {
                    assert_ne!(*ptr, a);
                    *ptr = a;
                    count += 1;
                }
                _ => {}
            }
        }
        assert_eq!(count, 1);
        cases.push(run_case(
            &stale,
            "reseat_index",
            if metadata {
                "mutant_metadata_reads_original_a"
            } else {
                "mutant_data_reads_original_a"
            },
            1,
            Some(4),
            Some(1),
            Outcome::Returned(102),
            None,
        ));
    }
    cases
}
