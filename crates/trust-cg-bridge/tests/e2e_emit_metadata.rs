//! E2E smoke test: simulates --emit=metadata pipeline through trust_cg codegen backend.
//!
//! This exercises the full path that `--emit=metadata` would take:
//! 1. Construct synthetic VerifiableFunctions (simulating MIR extraction)
//! 2. Run codegen_crate (bridge lowering of all functions)
//! 3. Run join_codegen (finalization, collecting CompiledModules)
//! 4. Validate each lowered LIR function for structural consistency
//!
//! The --emit=metadata path does NOT invoke link() or emit_object() -- it only
//! needs the LIR metadata (types, signatures, block structure) to be produced
//! correctly. This is the fastest path to a passing e2e test because it exercises
//! MIR extraction and bridge lowering without hitting the linker.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;

use trust_cg_bridge::codegen_backend::{
    CrateInfo, OngoingCodegen, OutputFilenames, RustcCodegenBackend, TrustCgCodegenBackend,
};
use trust_cg_bridge::validation::validate_lir;
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// Synthetic MIR functions (simulating what trust-mir-extract produces)
// ---------------------------------------------------------------------------

/// `fn add(a: i32, b: i32) -> i32 { a + b }`
fn make_add() -> VerifiableFunction {
    VerifiableFunction {
        name: "add".to_string(),
        def_path: "smoke::add".to_string(),
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

/// `fn identity(x: u64) -> u64 { x }`
fn make_identity() -> VerifiableFunction {
    VerifiableFunction {
        name: "identity".to_string(),
        def_path: "smoke::identity".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("x".into()) },
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
            return_ty: Ty::i64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `fn checked_div(a: i32, b: i32) -> i32 { if b == 0 { 0 } else { a / b } }`
/// Exercises branching (SwitchInt) and multi-block CFG.
fn make_checked_div() -> VerifiableFunction {
    VerifiableFunction {
        name: "checked_div".to_string(),
        def_path: "smoke::checked_div".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![
                // bb0: switch on b == 0
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(1))], // b == 0 -> bb1
                        otherwise: BlockId(2),          // b != 0 -> bb2
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb1: return 0
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                // bb2: return a / b
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
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

/// `fn sum_loop(n: u32) -> u32 { ... }` -- loop with back-edge.
/// bb0: switch n == 0 -> bb2 else bb1
/// bb1: n = n - 1; goto bb0
/// bb2: return n
fn make_sum_loop() -> VerifiableFunction {
    VerifiableFunction {
        name: "sum_loop".to_string(),
        def_path: "smoke::sum_loop".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("n".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(0)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// E2E test: --emit=metadata pipeline
// ---------------------------------------------------------------------------

/// Full e2e smoke test: simulates --emit=metadata through the trust_cg codegen backend.
///
/// This is the "fastest path to a passing e2e test" because --emit=metadata
/// exercises MIR extraction and bridge lowering without invoking the linker.
/// The pipeline:
///   VerifiableFunction -> codegen_crate -> join_codegen -> validate LIR
#[test]
fn test_emit_metadata_e2e_smoke() {
    let backend = TrustCgCodegenBackend::host();

    // Simulate what rustc would feed the backend: a crate with multiple functions.
    let crate_info = CrateInfo {
        crate_name: "trust_cg_smoke".to_string(),
        functions: vec![make_add(), make_identity(), make_checked_div(), make_sum_loop()],
    };

    // Step 1: codegen_crate (MIR -> LIR lowering for all functions)
    let ongoing = backend
        .codegen_crate(&crate_info)
        .expect("codegen_crate should succeed for smoke test functions");

    // Verify ongoing state before join.
    let ongoing_ref =
        ongoing.downcast_ref::<OngoingCodegen>().expect("ongoing should be OngoingCodegen");
    assert_eq!(ongoing_ref.crate_name(), "trust_cg_smoke");
    assert_eq!(ongoing_ref.compiled_count(), 4, "all 4 functions should compile successfully");
    assert_eq!(ongoing_ref.failure_count(), 0, "no functions should fail to lower");

    // Step 2: join_codegen (finalize -- this is where --emit=metadata stops)
    let outputs = OutputFilenames {
        out_dir: PathBuf::from("/tmp"),
        crate_stem: "trust_cg_smoke".to_string(),
    };
    let (compiled, _work_products) =
        backend.join_codegen(ongoing, &outputs).expect("join_codegen should succeed");

    // Verify compiled modules structure.
    assert_eq!(compiled.modules.len(), 1, "should have 1 codegen unit");
    let module = &compiled.modules[0];
    assert_eq!(module.function_count, 4);
    assert_eq!(module.lir_functions.len(), 4);

    // Step 3: Validate each LIR function for structural consistency.
    // This is what --emit=metadata would check: the LIR is well-formed.
    let expected_names = ["add", "identity", "checked_div", "sum_loop"];
    for (lir, expected_name) in module.lir_functions.iter().zip(expected_names.iter()) {
        assert_eq!(&lir.name, expected_name, "function order should match input order");

        // Run structural validation.
        if let Err(errors) = validate_lir(lir) {
            panic!("LIR validation failed for `{}`: {:?}", lir.name, errors);
        }

        // Verify entry block exists and has instructions.
        let entry = lir
            .blocks
            .get(&lir.entry_block)
            .unwrap_or_else(|| panic!("entry block missing for `{}`", lir.name));
        assert!(
            !entry.instructions.is_empty(),
            "entry block of `{}` should have instructions",
            lir.name
        );
    }

    // Verify specific function signatures.
    let add_lir = &module.lir_functions[0];
    assert_eq!(add_lir.signature.params.len(), 2, "add takes 2 params");
    assert_eq!(add_lir.signature.returns.len(), 1, "add returns 1 value");

    let identity_lir = &module.lir_functions[1];
    assert_eq!(identity_lir.signature.params.len(), 1, "identity takes 1 param");
    assert_eq!(identity_lir.signature.returns.len(), 1, "identity returns 1 value");

    let checked_div_lir = &module.lir_functions[2];
    assert_eq!(checked_div_lir.signature.params.len(), 2, "checked_div takes 2 params");
    assert!(
        checked_div_lir.blocks.len() >= 3,
        "checked_div should have >= 3 blocks (branch), got {}",
        checked_div_lir.blocks.len()
    );

    let sum_loop_lir = &module.lir_functions[3];
    assert!(
        sum_loop_lir.blocks.len() >= 3,
        "sum_loop should have >= 3 blocks (loop), got {}",
        sum_loop_lir.blocks.len()
    );
}

/// Verify that the backend can emit metadata for an empty crate (zero functions).
/// This is a valid edge case that --emit=metadata must handle gracefully.
#[test]
fn test_emit_metadata_empty_crate() {
    let backend = TrustCgCodegenBackend::host();
    let crate_info = CrateInfo { crate_name: "empty_crate".to_string(), functions: vec![] };

    let ongoing =
        backend.codegen_crate(&crate_info).expect("empty crate should codegen successfully");

    let outputs =
        OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "empty_crate".to_string() };
    let (compiled, _) =
        backend.join_codegen(ongoing, &outputs).expect("join should succeed for empty crate");

    assert_eq!(compiled.modules[0].function_count, 0);
    assert!(compiled.modules[0].lir_functions.is_empty());
}

/// Verify metadata pipeline with a function using float types.
/// Ensures the bridge handles non-integer types in the --emit=metadata path.
#[test]
fn test_emit_metadata_float_function() {
    let backend = TrustCgCodegenBackend::host();

    let float_add = VerifiableFunction {
        name: "fadd".to_string(),
        def_path: "smoke::fadd".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::f64_ty(), name: None },
                LocalDecl { index: 1, ty: Ty::f64_ty(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::f64_ty(), name: Some("b".into()) },
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
            return_ty: Ty::f64_ty(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let crate_info =
        CrateInfo { crate_name: "float_crate".to_string(), functions: vec![float_add] };

    let ongoing = backend.codegen_crate(&crate_info).expect("float function should codegen");

    let outputs =
        OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "float_crate".to_string() };
    let (compiled, _) =
        backend.join_codegen(ongoing, &outputs).expect("join should succeed for float crate");

    let lir = &compiled.modules[0].lir_functions[0];
    assert_eq!(lir.name, "fadd");

    // Validate structural consistency.
    validate_lir(lir).unwrap_or_else(|errors| {
        panic!("LIR validation failed for fadd: {:?}", errors);
    });
}
