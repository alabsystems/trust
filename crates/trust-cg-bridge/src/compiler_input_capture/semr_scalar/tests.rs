// Copyright 2026 Andrew Yates | Apache-2.0
//! Typed input controls over the maintained ACTUAL original producer Module.
//! Constructing a request here does not claim a fresh Compiler/TCX execution.
use std::sync::Arc;

use super::*;
use crate::compiled_object::RelocationModel;
use crate::f1_compile::{F1CompileConfig, F1OptLevel, F1Target};
use crate::verify_output::EmitPolicy;

const ORIGINAL: &[u8] =
    include_bytes!("../../../tests/fixtures/direct_ir_observation/original-module.bin");

fn module() -> trust_ir::Module {
    let m = trust_ir::binary::deserialize_module(ORIGINAL).unwrap();
    assert!(trust_ir_build::validate_module(&m).is_empty());
    assert_eq!(trust_ir::binary::serialize_module(&m).unwrap(), ORIGINAL);
    m
}
fn derive(m: trust_ir::Module) -> Result<ExpectedScalarInput, String> {
    let symbol = m.functions[0].name.clone();
    let producers = [ProducerModule::named_by_symbols(Arc::new(m))];
    let bodies = [(symbol.clone(), ProducerBody { producer: 0, func: FuncId::new(0) })]
        .into_iter()
        .collect();
    ExpectedScalarInput::derive(&producers, &bodies, &symbol)
}

#[test]
fn expected_canonical_bytes_and_literal_come_from_actual_original() {
    let m = module();
    let expected = derive(m.clone()).unwrap();
    assert_eq!(expected.module_bytes(), ORIGINAL);
    assert_eq!(expected.literal(), 7);
    assert_eq!(expected.symbol(), "addition");
    let producers = [ProducerModule::named_by_symbols(Arc::new(m.clone()))];
    let bodies = [("addition".into(), ProducerBody { producer: 0, func: FuncId::new(0) })]
        .into_iter()
        .collect();
    let config = F1CompileConfig {
        target: F1Target::Aarch64AppleDarwin,
        opt_level: F1OptLevel::O3,
        relocation: RelocationModel::Static,
        force_frame_pointers: false,
        never_inline: Default::default(),
        upstream_mir_lane: false,
    };
    let input = F1CompileInput {
        m_cg: &m,
        producers: &producers,
        bodies: &bodies,
        placements: &BTreeMap::new(),
        policy: EmitPolicy::AllowUnknown,
        config: &config,
    };
    assert_eq!(ExpectedScalarInput::from_compile_input(&input, "addition").unwrap(), expected);
    // A real different, well-typed Module has DIFFERENT derived bytes/literal.
    // It is not rejected as invalid IR or mislabeled a source/NoUB refutation.
    let mut changed = m;
    let Inst::Const { value: Constant::Int(n), .. } =
        &mut changed.functions[0].blocks[0].body[0].inst
    else {
        panic!("actual literal");
    };
    *n = 8;
    assert!(trust_ir_build::validate_module(&changed).is_empty());
    let other = derive(changed).unwrap();
    assert_eq!(other.literal(), 8);
    assert_ne!(expected.module_bytes(), other.module_bytes());
    assert_ne!(expected.binding, other.binding);
}

#[test]
fn unreferenced_blob_data_is_preserved_in_actual_scalar_input() {
    let mut m = module();
    let digest = m.intern_blob(vec![0x41, 0x00, 0xff]);
    let expected = derive(m.clone()).unwrap();
    let (decoded, version) =
        trust_ir::binary::deserialize_module_with_wire_version(expected.module_bytes()).unwrap();
    assert_eq!(version.get(), trust_ir::binary::TENSOR_BLOB_FORMAT_VERSION);
    assert_eq!(decoded, m);
    assert_eq!(decoded.blob(&digest).unwrap().data, [0x41, 0x00, 0xff]);
    assert_eq!(expected.literal(), 7);
    assert_ne!(expected.module_bytes(), ORIGINAL);
    // Keep the original body and all table data. The canonical Lean profile
    // separately proves execution independent of every unreferenced table.
    assert_eq!(decoded.functions, module().functions);
}

#[test]
fn scalar_source_shape_identity_and_unsupported_controls_refuse() {
    for change in 0..7 {
        let mut m = module();
        match change {
            0 => m.functions[0].calling_conv = CallingConv::C,
            1 => m.target_info = None,
            2 => m.func_types[0].returns = vec![Ty::I64],
            3 => {
                m.functions[0].blocks[0].body[1].inst = Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::U64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                }
            }
            4 => {
                m.functions[0].blocks[0].body[2].inst =
                    Inst::Return { values: vec![ValueId::new(0)] }
            }
            5 => {
                m.functions[0].blocks[0].body[0].inst =
                    Inst::Call { callee: FuncId::new(0), args: vec![ValueId::new(0)] }
            }
            _ => {
                m.functions[0].blocks[0].body[0].inst = Inst::MakeClosure {
                    ty: trust_ir::value::ClosureTyId::new(0),
                    func: FuncId::new(0),
                    captures: vec![],
                }
            }
        }
        if matches!(change, 3 | 4) {
            assert!(
                trust_ir_build::validate_module(&m).is_empty(),
                "Sub and parameter-return controls are valid IR outside this exact scalar theorem domain"
            );
        }
        assert!(derive(m).is_err(), "source-shape mutation {change}");
    }
    let m = Arc::new(module());
    let mut producer = ProducerModule::named_by_symbols(m);
    let symbol = "addition";
    let mut bodies = [(symbol.into(), ProducerBody { producer: 0, func: FuncId::new(0) })]
        .into_iter()
        .collect::<BTreeMap<_, _>>();
    producer.symbols.insert(FuncId::new(0), "unrelated".into());
    assert!(ExpectedScalarInput::derive(&[producer.clone()], &bodies, symbol).is_err());
    producer.symbols.insert(FuncId::new(0), symbol.into());
    bodies.get_mut(symbol).unwrap().func = FuncId::new(1);
    assert!(ExpectedScalarInput::derive(&[producer], &bodies, symbol).is_err());
}
