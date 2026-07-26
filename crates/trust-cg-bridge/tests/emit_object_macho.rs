// Integration test for #969: real machine code emission via trust_cg-codegen.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;

use trust_cg_bridge::codegen_backend::{
    CodegenBackendError, CompiledModule, TrustCgCodegenBackend, TrustCgTargetArch,
};
use trust_cg_lower::instructions::{Block, Opcode};
use trust_cg_lower::types::Type as LirType;
use trust_types::{
    AggregateKind, AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand,
    Place, Rvalue, SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

fn make_add() -> VerifiableFunction {
    VerifiableFunction {
        name: "add".to_string(),
        def_path: "integration::add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn make_identity() -> VerifiableFunction {
    VerifiableFunction {
        name: "identity".to_string(),
        def_path: "integration::identity".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn make_unit_main() -> VerifiableFunction {
    VerifiableFunction {
        name: "main".to_string(),
        def_path: "integration::nested::main".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn make_checked_div_option() -> VerifiableFunction {
    let option_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "Option".to_string(),
        fields: vec![("tag".to_string(), Ty::i64()), ("value".to_string(), Ty::i32())],
        disc_index_safe: false,
        // Trust (B3-1 field completion): pre-existing E0063 missed by 11598e13fe.
        faithful_enum_repr: None, enum_layout: None, };

    VerifiableFunction {
        name: "checked_div".to_string(),
        def_path: "integration::checked_div".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: option_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: Some("quot".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Option".into(),
                                variant: 0,
                                active_field: None,
                            },
                            vec![],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Aggregate(
                                AggregateKind::Adt {
                                    name: "Option".into(),
                                    variant: 1,
                                    active_field: None,
                                },
                                vec![Operand::Copy(Place::local(3))],
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: option_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn pair_ty() -> Ty {
    Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "Pair".to_string(),
        fields: vec![("left".to_string(), Ty::i64()), ("right".to_string(), Ty::i32())],
        disc_index_safe: false,
        // Trust (B3-1 field completion): pre-existing E0063 missed by 11598e13fe.
        faithful_enum_repr: None, enum_layout: None, }
}

fn make_pair_helper() -> VerifiableFunction {
    let pair_ty = pair_ty();

    VerifiableFunction {
        name: "make_pair_helper".to_string(),
        def_path: "integration::make_pair_helper".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: pair_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("left".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("right".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt { name: "Pair".into(), variant: 0, active_field: None },
                        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: pair_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn make_pair_via_helper_call() -> VerifiableFunction {
    let pair_ty = pair_ty();

    VerifiableFunction {
        name: "pair_via_helper_call".to_string(),
        def_path: "integration::pair_via_helper_call".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: pair_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("left".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("right".into()) },
                LocalDecl { index: 3, ty: pair_ty.clone(), name: Some("pair".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "make_pair_helper".to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: pair_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
fn make_checked_add_overflowing() -> VerifiableFunction {
    VerifiableFunction {
        name: "checked_add_overflowing".to_string(),
        def_path: "integration::checked_add_overflowing".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl {
                    index: 3,
                    ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]),
                    name: Some("checked".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
fn make_checked_add_overflow_main() -> VerifiableFunction {
    VerifiableFunction {
        name: "main".to_string(),
        def_path: "integration::main".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("result".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "checked_add_overflowing".to_string(),
                        args: vec![
                            Operand::Constant(ConstValue::Int(i128::from(i32::MAX))),
                            Operand::Constant(ConstValue::Int(1)),
                        ],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn assert_object_magic(bytes: &[u8]) {
    assert!(bytes.len() >= 4, "object must be at least 4 bytes");
    let magic = &bytes[..4];
    let is_macho = magic == [0xCF, 0xFA, 0xED, 0xFE];
    let is_elf = magic == [0x7F, b'E', b'L', b'F'];
    assert!(is_macho || is_elf, "expected Mach-O or ELF magic, got {magic:02X?}",);
}

fn native_backend_arch() -> TrustCgTargetArch {
    TrustCgTargetArch::from_rustc_arch(std::env::consts::ARCH)
        .expect("test only supports native aarch64/x86_64 targets")
}

fn assert_object_header_arch(bytes: &[u8], expected_arch: TrustCgTargetArch) {
    assert!(bytes.len() >= 20, "object must contain a full native header");

    match &bytes[..4] {
        [0xCF, 0xFA, 0xED, 0xFE] => {
            let cpu_type = u32::from_le_bytes(bytes[4..8].try_into().expect("cputype"));
            let expected_cpu_type = match expected_arch {
                TrustCgTargetArch::AArch64 => 0x0100_000C,
                TrustCgTargetArch::X86_64 => 0x0100_0007,
            };
            assert_eq!(
                cpu_type, expected_cpu_type,
                "Mach-O cputype should match configured backend arch"
            );
        }
        [0x7F, b'E', b'L', b'F'] => {
            let machine = u16::from_le_bytes(bytes[18..20].try_into().expect("e_machine"));
            let expected_machine = match expected_arch {
                TrustCgTargetArch::AArch64 => 183,
                TrustCgTargetArch::X86_64 => 62,
            };
            assert_eq!(
                machine, expected_machine,
                "ELF e_machine should match configured backend arch"
            );
        }
        magic => panic!("expected Mach-O or ELF magic, got {magic:02X?}"),
    }
}

#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
fn command_stdout(program: &str, args: &[&std::ffi::OsStr]) -> String {
    let output = std::process::Command::new(program)
        .args(args)
        .output()
        .unwrap_or_else(|err| panic!("{program} should run: {err}"));
    assert!(
        output.status.success(),
        "{program} should succeed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("tool output should be UTF-8")
}

#[test]
fn emit_object_writes_real_object_file() {
    let backend = TrustCgCodegenBackend::host();
    let func = make_add();
    let lir = backend.lower_function(&func).expect("lower_function should succeed");
    let bytes = backend.emit_object(&[lir]).expect("emit_object should succeed");

    let temp_dir = tempfile::tempdir().expect("tempdir should succeed");
    let object_path = temp_dir.path().join("add.o");
    fs::write(&object_path, &bytes).expect("write should succeed");

    let metadata = fs::metadata(&object_path).expect("metadata should succeed");
    assert!(metadata.is_file(), "expected object file to exist");
    assert!(metadata.len() > 0, "object file should not be empty");

    let file_bytes = fs::read(&object_path).expect("read should succeed");
    assert_object_magic(&file_bytes);
}

#[test]
fn emit_module_objects_splits_two_function_module_with_stable_names_and_native_arch_headers() {
    let expected_arch = native_backend_arch();
    let backend = TrustCgCodegenBackend::new(expected_arch);
    let lir_functions =
        backend.lower_module(&[make_add(), make_identity()]).expect("lower_module should succeed");
    let module = CompiledModule {
        name: "multi.codegen_unit.0".to_string(),
        lir_functions,
        object_path: None,
        function_count: 2,
        source_functions: None,
    };

    let objects = backend.emit_module_objects(&module).expect("emit_module_objects should succeed");

    assert_eq!(objects.len(), 2, "two-function module should split into two objects");
    assert_eq!(objects[0].artifact_name, "multi.codegen_unit.0.f0");
    assert_eq!(objects[0].source_name, "add");
    assert_eq!(objects[1].artifact_name, "multi.codegen_unit.0.f1");
    assert_eq!(objects[1].source_name, "identity");

    for object in &objects {
        assert_object_magic(&object.bytes);
        assert_object_header_arch(&object.bytes, expected_arch);
    }
}

#[test]
fn emit_module_objects_rejects_empty_module_without_object_output() {
    let backend = TrustCgCodegenBackend::host();
    let module = CompiledModule {
        name: "empty.codegen_unit.0".to_string(),
        lir_functions: vec![],
        object_path: None,
        function_count: 0,
        source_functions: None,
    };

    let err = backend
        .emit_module_objects(&module)
        .expect_err("native object emission must fail closed for objectless modules");
    assert!(
        matches!(err, CodegenBackendError::EmitFailed { .. }),
        "empty module should fail as an emission error: {err:?}"
    );
    assert!(
        err.to_string().contains("refusing objectless output"),
        "empty module error should explain that no native object was emitted: {err}"
    );
}

#[test]
fn emit_object_checked_div_option_regression_emits_object() {
    let expected_arch = native_backend_arch();
    let backend = TrustCgCodegenBackend::new(expected_arch);
    let lir = backend
        .lower_function(&make_checked_div_option())
        .expect("checked_div Option lowering should succeed");

    let bytes =
        backend.emit_object(&[lir]).expect("checked_div Option object emission should succeed");
    assert!(!bytes.is_empty(), "object emission should produce bytes");
    assert_object_magic(&bytes);
    assert_object_header_arch(&bytes, expected_arch);
}

#[test]
fn emit_object_nested_unit_main_does_not_infer_process_abi() {
    let expected_arch = native_backend_arch();
    let backend = TrustCgCodegenBackend::new(expected_arch);
    let lir = backend.lower_function(&make_unit_main()).expect("unit main lowering should succeed");

    assert_eq!(lir.signature.params, Vec::<LirType>::new());
    assert_eq!(lir.signature.returns, Vec::<LirType>::new());

    let entry = &lir.blocks[&Block(0)];
    assert!(
        !entry
            .instructions
            .iter()
            .any(|instr| matches!(instr.opcode, Opcode::Iconst { ty: LirType::I32, imm: 0 })),
        "a bare function name must not synthesize a C process exit status"
    );

    let bytes = backend.emit_object(&[lir]).expect("unit main object emission should succeed");
    assert!(!bytes.is_empty(), "object emission should produce bytes");
    assert_object_magic(&bytes);
    assert_object_header_arch(&bytes, expected_arch);
}

#[test]
fn emit_object_helper_call_struct_return_regression_emits_native_objects() {
    let expected_arch = native_backend_arch();
    let backend = TrustCgCodegenBackend::new(expected_arch);
    let lir_functions = backend
        .lower_module(&[make_pair_helper(), make_pair_via_helper_call()])
        .expect("helper-call Pair module lowering should succeed");

    let caller_lir = lir_functions
        .iter()
        .find(|func| func.name == "pair_via_helper_call")
        .expect("caller LIR should be present");
    let caller_block = &caller_lir.blocks[&Block(0)];
    let call_instr = caller_block
        .instructions
        .iter()
        .find(
            |instr| matches!(instr.opcode, Opcode::Call { ref name } if name == "make_pair_helper"),
        )
        .expect("caller should contain helper call");
    let call_result =
        call_instr.results.first().copied().expect("helper call should produce a result value");
    assert_eq!(
        caller_lir.value_types.get(&call_result),
        Some(&LirType::Struct(vec![LirType::I64, LirType::I32])),
        "helper call result should retain Pair type for trust_cg ISel"
    );

    let module = CompiledModule {
        name: "helper_pair.codegen_unit.0".to_string(),
        lir_functions,
        object_path: None,
        function_count: 2,
        source_functions: None,
    };
    let objects = backend
        .emit_module_objects(&module)
        .expect("helper-call Pair objects should emit successfully");
    assert_eq!(objects.len(), 2, "helper-call Pair module should split into two objects");

    for object in &objects {
        assert!(!object.bytes.is_empty(), "object emission should produce bytes");
        assert_object_magic(&object.bytes);
        assert_object_header_arch(&object.bytes, expected_arch);
    }
}

#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
#[test]
fn emit_objects_overflow_caller_preserves_external_branch_relocation() {
    let backend = TrustCgCodegenBackend::host();
    let lir_functions = backend
        .lower_module(&[make_checked_add_overflowing(), make_checked_add_overflow_main()])
        .expect("overflow module lowering should succeed");
    let caller_lir =
        lir_functions.iter().find(|func| func.name == "main").expect("main LIR should be present");
    let caller_block = &caller_lir.blocks[&Block(0)];
    let call_instr = caller_block
        .instructions
        .iter()
        .find(|instr| {
            matches!(instr.opcode, Opcode::Call { ref name } if name == "checked_add_overflowing")
        })
        .expect("main should contain the checked_add_overflowing call");
    let call_result = call_instr.results.first().copied().expect("call should produce a result");
    assert_eq!(
        caller_lir.value_types.get(&call_result),
        Some(&LirType::I32),
        "overflow caller should preserve the call result type before object emission"
    );

    let objects = backend.emit_objects(&lir_functions).expect("emit_objects should succeed");
    let caller_bytes = objects
        .iter()
        .find(|(name, _)| name == "main")
        .map(|(_, bytes)| bytes)
        .expect("main object should be present");
    assert_object_magic(caller_bytes);

    let temp_dir = tempfile::tempdir().expect("tempdir should succeed");
    let caller_path = temp_dir.path().join("main.o");
    fs::write(&caller_path, caller_bytes).expect("caller object write should succeed");

    let nm_output = command_stdout("nm", &[std::ffi::OsStr::new("-m"), caller_path.as_os_str()]);
    assert!(
        nm_output.contains("(undefined) external _checked_add_overflowing"),
        "main.o should preserve checked_add_overflowing as an undefined external symbol:\n{nm_output}"
    );

    let reloc_output =
        command_stdout("otool", &[std::ffi::OsStr::new("-rv"), caller_path.as_os_str()]);
    assert!(
        reloc_output.contains("BR26") && reloc_output.contains("_checked_add_overflowing"),
        "main.o should preserve a BR26 relocation against checked_add_overflowing:\n{reloc_output}"
    );
}
