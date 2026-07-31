//! Tests for trust-ir-bridge.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::UnwindEdge;
use trust_ir::Constant as TrustIrConstant;
use trust_ir::dialect::AttrValue;
use trust_ir::inst::{
    BinOp as TrustIrBinOp, CastOp as TrustIrCastOp, FCmpOp as TrustIrFCmpOp, ICmpOp, Inst,
    OverflowOp, UnOp as TrustIrUnOp,
};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::ty::Ty as TrustIrTy;
use trust_ir::value::ValueId;
use trust_ir_build::validate_module;
use trust_types::{
    AggregateKind, AtomicOpKind, AtomicOperation, AtomicOrdering, BasicBlock as TrustBlock, BinOp,
    BinaryArtifactDigest, BinaryArtifactMetadata, BinaryOrigin, BinarySelectedImageIdentity,
    BinarySourceProvenanceSummary, BlockId, CallableDefPathHash, CallableKind, ClosureCallKind, ConstValue, Contract, ContractKind,
    DecompilationArtifact, DecompiledFunction, EnumReprHint, Formula, LocalDecl, Operand, Place,
    Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, UnOp, VariantDef,
    VerifiableBody, VerifiableFunction, stable_sha256_hex,
};

use crate::lower::{
    ARBITRARY_PRECISION_TY_FUEL, BinOpMapping, BridgeError, SYMBOLIC_AGGREGATE_ATTR_FIELD_COUNT,
    SYMBOLIC_AGGREGATE_ATTR_KIND, SYMBOLIC_AGGREGATE_OP, SYMBOLIC_FORMULA_ATTR_DEBUG,
    SYMBOLIC_FORMULA_ATTR_JSON, SYMBOLIC_FORMULA_ATTR_SCHEMA, SYMBOLIC_FORMULA_ATTR_SMTLIB,
    SYMBOLIC_FORMULA_ATTR_SORT, SYMBOLIC_FORMULA_DIALECT, SYMBOLIC_FORMULA_OP,
    SYMBOLIC_MEMORY_STATE_OP, TRUST_CONTRACT_PREDICATE_SCHEMA,
    is_arbitrary_precision_candidate_arith_method, is_arbitrary_precision_ty,
    is_element_free_total_std_type, is_ratio_new_absent_callee, is_ratio_recip_absent_callee,
    is_trusted_panic_free_absent_callee, lower_functions_to_trust_ir, lower_to_trust_ir,
    lower_to_trust_ir_functions, lower_to_trust_ir_functions_with_assumed_total_context,
    lower_to_trust_ir_functions_with_context,
    lower_to_trust_ir_functions_with_test_paired_context, map_binop, map_type, map_unop,
    verifiable_function_lowers_in_module_context,
};
use crate::{
    BINARY_PROVENANCE_ATTR_ARTIFACT_SHA256, BINARY_PROVENANCE_ATTR_INSTRUCTION_BYTES,
    BINARY_PROVENANCE_ATTR_PROVENANCE_STATUS, BINARY_PROVENANCE_ATTR_RECORD_DIGEST,
    BINARY_PROVENANCE_ATTR_SCHEMA, BINARY_PROVENANCE_DIALECT, BINARY_PROVENANCE_OP,
    BINARY_PROVENANCE_SCHEMA, BINARY_PROVENANCE_STATUS_AMBIGUOUS,
    BINARY_PROVENANCE_STATUS_CHECKED_EXACT, BINARY_PROVENANCE_STATUS_UNAVAILABLE,
    CanonicalBinaryProvenanceAcceptance, TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_FEATURE,
    TRUST_IR_LAYOUT_EVIDENCE_COMMIT, canonical_binary_provenance_target_blockers,
    collect_canonical_binary_provenance, collect_layout_sensitive_cast_blockers,
    ensure_layout_sensitive_cast_evidence, lower_decompilation_artifact_to_trust_ir,
};

fn assert_valid_module(module: &trust_ir::Module) {
    let errors = validate_module(module);
    assert!(errors.is_empty(), "TrustIr validator errors: {errors:?}");
}

/// Count reachable-panic sentinels by resolving each `Assert` operand to its local
/// `Const(false)` definition. `Assert(true)` discharge witnesses are deliberately
/// excluded.
fn no_panic_false_assert_count(module: &trust_ir::Module) -> usize {
    module
        .functions
        .iter()
        .map(|func| {
            let const_bools: std::collections::HashMap<trust_ir::ValueId, bool> = func
                .blocks
                .iter()
                .flat_map(|block| block.body.iter())
                .filter_map(|node| match (&node.inst, node.results.as_slice()) {
                    (Inst::Const { value: trust_ir::Constant::Bool(value), .. }, [id]) => {
                        Some((*id, *value))
                    }
                    _ => None,
                })
                .collect();
            func.blocks
                .iter()
                .flat_map(|block| block.body.iter())
                .filter(|node| {
                    matches!(&node.inst, Inst::Assert { cond }
                        if const_bools.get(cond) == Some(&false))
                        && node.proofs.contains(&trust_ir::ProofAnnotation::NoPanic)
                })
                .count()
        })
        .sum()
}

fn assert_slice_fat_ptr_element(
    module: &trust_ir::Module,
    ty: &TrustIrTy,
    expected_element: &TrustIrTy,
) {
    let TrustIrTy::FatPtr(trust_ir::FatPtrKind::Slice(element_id)) = ty else {
        panic!("expected a first-class slice fat pointer, got {ty:?}");
    };
    assert_eq!(
        module.types.get(element_id.as_usize()),
        Some(expected_element),
        "slice fat pointer must retain the exact registered element type"
    );
}

// ---------------------------------------------------------------------------
// Type mapping tests
// ---------------------------------------------------------------------------

#[test]
fn test_map_type_bool() {
    assert_eq!(map_type(&Ty::Bool).unwrap(), TrustIrTy::Bool);
}

#[test]
fn test_map_type_integers() {
    assert_eq!(map_type(&Ty::i8()).unwrap(), TrustIrTy::I8);
    assert_eq!(map_type(&Ty::u8()).unwrap(), TrustIrTy::U8);
    assert_eq!(map_type(&Ty::i16()).unwrap(), TrustIrTy::I16);
    assert_eq!(map_type(&Ty::u16()).unwrap(), TrustIrTy::U16);
    assert_eq!(map_type(&Ty::i32()).unwrap(), TrustIrTy::I32);
    assert_eq!(map_type(&Ty::u32()).unwrap(), TrustIrTy::U32);
    assert_eq!(map_type(&Ty::i64()).unwrap(), TrustIrTy::I64);
    assert_eq!(map_type(&Ty::u64()).unwrap(), TrustIrTy::U64);
    assert_eq!(map_type(&Ty::i128()).unwrap(), TrustIrTy::I128);
    assert_eq!(map_type(&Ty::u128()).unwrap(), TrustIrTy::U128);
}

#[test]
fn test_map_type_signed_unsigned_distinct() {
    assert_ne!(map_type(&Ty::i32()).unwrap(), map_type(&Ty::u32()).unwrap());
    assert_ne!(map_type(&Ty::i64()).unwrap(), map_type(&Ty::u64()).unwrap());
}

#[test]
fn test_map_type_floats() {
    assert_eq!(map_type(&Ty::f32_ty()).unwrap(), TrustIrTy::F32);
    assert_eq!(map_type(&Ty::f64_ty()).unwrap(), TrustIrTy::F64);
}

#[test]
fn test_map_type_unit_and_never() {
    assert_eq!(map_type(&Ty::Unit).unwrap(), TrustIrTy::Unit);
    assert_eq!(map_type(&Ty::Never).unwrap(), TrustIrTy::Never);
}

#[test]
fn test_map_type_pointers() {
    assert_eq!(
        map_type(&Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) }).unwrap(),
        TrustIrTy::Ptr
    );
    assert_eq!(
        map_type(&Ty::Ref { mutable: true, inner: Box::new(Ty::i32()) }).unwrap(),
        TrustIrTy::Ptr
    );
    assert_eq!(
        map_type(&Ty::RawPtr { mutable: false, pointee: Box::new(Ty::i32()) }).unwrap(),
        TrustIrTy::Ptr
    );
    // Trust (B2-1b): slice shapes DELIBERATELY fail closed in the STATELESS
    // mapper — the first-class `FatPtr(FatPtrKind::Slice(TyId))` spelling needs
    // the module `types` table, so only context-aware lowering can produce it.
    assert!(matches!(
        map_type(&Ty::Slice { elem: Box::new(Ty::u8()) }),
        Err(BridgeError::UnsupportedType(msg)) if msg.contains("requires module type registration")
    ));
    assert!(matches!(
        map_type(&Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
        }),
        Err(BridgeError::UnsupportedType(msg)) if msg.contains("requires module type registration")
    ));
}

#[test]
fn test_map_type_bv() {
    assert_eq!(map_type(&Ty::Bv(32)).unwrap(), TrustIrTy::I32);
    assert_eq!(map_type(&Ty::Bv(64)).unwrap(), TrustIrTy::I64);
    assert!(map_type(&Ty::Bv(7)).is_err());
}

#[test]
fn test_map_type_tuple_precise_and_layout_dependent_types_fail_closed() {
    assert_eq!(
        map_type(&Ty::Tuple(vec![Ty::i32(), Ty::Bool])).unwrap(),
        TrustIrTy::Tuple(vec![TrustIrTy::I32, TrustIrTy::Bool])
    );
    assert!(matches!(
        map_type(&Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Pair".into(),
            fields: vec![("x".into(), Ty::i32())],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, }),
        Err(BridgeError::UnsupportedType(_))
    ));
    assert!(matches!(
        map_type(&Ty::Array { elem: Box::new(Ty::i32()), len: 4 }),
        Err(BridgeError::UnsupportedType(_))
    ));
    assert!(matches!(
        map_type(&Ty::Closure { name: "test::closure".into(), upvars: vec![], call: None }),
        Err(BridgeError::UnsupportedType(_))
    ));
}

// ---------------------------------------------------------------------------
// BinOp mapping tests
// ---------------------------------------------------------------------------

#[test]
fn test_map_binop_arithmetic() {
    assert_eq!(map_binop(BinOp::Add, false).unwrap(), BinOpMapping::Arith(TrustIrBinOp::Add));
    assert_eq!(map_binop(BinOp::Sub, false).unwrap(), BinOpMapping::Arith(TrustIrBinOp::Sub));
    assert_eq!(map_binop(BinOp::Mul, false).unwrap(), BinOpMapping::Arith(TrustIrBinOp::Mul));
}

#[test]
fn test_map_binop_division_signedness() {
    assert_eq!(map_binop(BinOp::Div, false).unwrap(), BinOpMapping::Arith(TrustIrBinOp::UDiv));
    assert_eq!(map_binop(BinOp::Div, true).unwrap(), BinOpMapping::Arith(TrustIrBinOp::SDiv));
    assert_eq!(map_binop(BinOp::Rem, false).unwrap(), BinOpMapping::Arith(TrustIrBinOp::URem));
    assert_eq!(map_binop(BinOp::Rem, true).unwrap(), BinOpMapping::Arith(TrustIrBinOp::SRem));
}

#[test]
fn test_map_binop_bitwise() {
    assert_eq!(map_binop(BinOp::BitAnd, false).unwrap(), BinOpMapping::Arith(TrustIrBinOp::And));
    assert_eq!(map_binop(BinOp::BitOr, false).unwrap(), BinOpMapping::Arith(TrustIrBinOp::Or));
    assert_eq!(map_binop(BinOp::BitXor, false).unwrap(), BinOpMapping::Arith(TrustIrBinOp::Xor));
}

#[test]
fn test_map_binop_shifts() {
    assert_eq!(map_binop(BinOp::Shl, false).unwrap(), BinOpMapping::Arith(TrustIrBinOp::Shl));
    assert_eq!(map_binop(BinOp::Shr, false).unwrap(), BinOpMapping::Arith(TrustIrBinOp::LShr));
    assert_eq!(map_binop(BinOp::Shr, true).unwrap(), BinOpMapping::Arith(TrustIrBinOp::AShr));
}

#[test]
fn test_map_binop_comparisons() {
    assert_eq!(map_binop(BinOp::Eq, false).unwrap(), BinOpMapping::Cmp(ICmpOp::Eq));
    assert_eq!(map_binop(BinOp::Ne, false).unwrap(), BinOpMapping::Cmp(ICmpOp::Ne));
    assert_eq!(map_binop(BinOp::Lt, false).unwrap(), BinOpMapping::Cmp(ICmpOp::Ult));
    assert_eq!(map_binop(BinOp::Lt, true).unwrap(), BinOpMapping::Cmp(ICmpOp::Slt));
    assert_eq!(map_binop(BinOp::Ge, true).unwrap(), BinOpMapping::Cmp(ICmpOp::Sge));
    assert_eq!(map_binop(BinOp::Ge, false).unwrap(), BinOpMapping::Cmp(ICmpOp::Uge));
}

#[test]
fn test_map_binop_cmp_unsupported() {
    assert!(map_binop(BinOp::Cmp, false).is_err());
}

// ---------------------------------------------------------------------------
// UnOp mapping tests
// ---------------------------------------------------------------------------

#[test]
fn test_map_unop() {
    assert_eq!(map_unop(UnOp::Not).unwrap(), trust_ir::inst::UnOp::Not);
    assert_eq!(map_unop(UnOp::Neg).unwrap(), trust_ir::inst::UnOp::Neg);
    assert!(map_unop(UnOp::PtrMetadata).is_err());
}

// ---------------------------------------------------------------------------
// Full function lowering tests
// ---------------------------------------------------------------------------

/// Helper: build MIR for `fn add(a: i32, b: i32) -> i32 { a + b }`
fn make_add_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "add".to_string(),
        def_path: "test::add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
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

#[test]
fn test_lower_add_function() {
    let func = make_add_function();
    let module = lower_to_trust_ir(&func).expect("should lower");

    assert_eq!(module.name, "add");
    assert_eq!(module.functions.len(), 1);

    let trust_ir_func = &module.functions[0];
    assert_eq!(trust_ir_func.name, "add");
    assert_eq!(trust_ir_func.blocks.len(), 1);
    assert_eq!(
        trust_ir_func.producer,
        Some(trust_ir::Producer::TrustIr),
        "MIR compatibility output must not impersonate a direct source frontend"
    );

    // Check function type.
    let ft = &module.func_types[trust_ir_func.ty.index() as usize];
    assert_eq!(ft.params, vec![TrustIrTy::I32, TrustIrTy::I32]);
    assert_eq!(ft.returns, vec![TrustIrTy::I32]);

    // Check the block has BinOp::Add and Return.
    let bb0 = &trust_ir_func.blocks[0];
    assert_eq!(
        bb0.params,
        vec![(ValueId::new(0), TrustIrTy::I32), (ValueId::new(1), TrustIrTy::I32)],
        "entry block params must define MIR argument locals"
    );
    let has_add = bb0.body.iter().any(|node| {
        matches!(&node.inst, Inst::BinOp { op: TrustIrBinOp::Add, ty: TrustIrTy::I32, .. })
    });
    assert!(has_add, "should have an Add instruction");

    let has_return = bb0.body.iter().any(|node| matches!(&node.inst, Inst::Return { .. }));
    assert!(has_return, "should have a Return instruction");
    assert_valid_module(&module);
}

#[test]
fn test_lower_multiple_functions_into_one_module() {
    let add = make_add_function();
    let noop = VerifiableFunction {
        name: "noop".to_string(),
        def_path: "test::noop".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![TrustBlock {
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
    };

    let module = lower_functions_to_trust_ir("binary", [&add, &noop]).expect("should lower");

    assert_eq!(module.name, "binary");
    assert_eq!(module.functions.len(), 2);
    assert_eq!(module.functions[0].name, "add");
    assert_eq!(module.functions[0].id.index(), 0);
    assert_eq!(module.functions[1].name, "noop");
    assert_eq!(module.functions[1].id.index(), 1);
    assert_eq!(module.func_types.len(), 2);
}

#[test]
fn test_lower_noncapturing_closure_aggregate_as_unit_environment() {
    let closure_name = "test::contract::{closure#0}".to_string();
    let func = VerifiableFunction {
        name: "noncapturing_contract_closure".to_string(),
        def_path: "test::noncapturing_contract_closure".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Closure { name: closure_name.clone(), upvars: vec![], call: None },
                    name: Some("closure".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Closure {
                            name: closure_name,
                            captures: vec![],
                            call_kind: ClosureCallKind::FnOnce,
                        },
                        vec![],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("noncapturing closure env should lower");
    assert!(module.structs.is_empty(), "noncapturing closure env is represented as unit");
    let bb0 = &module.functions[0].blocks[0];
    assert!(bb0.body.iter().any(|node| {
        matches!(
            &node.inst,
            Inst::Const { ty: TrustIrTy::Unit, value: TrustIrConstant::PhantomData }
        )
    }));
    assert_valid_module(&module);
}

#[test]
fn test_lower_closure_aggregate_refines_unsupported_rustc_marker_from_captures() {
    let closure_name = "test::midpoint::{closure#0}".to_string();
    let unsupported_closure = Ty::Unsupported {
        kind: "TyKind::Closure".into(),
        detail: "closure test::midpoint::{closure#0} needs captured-environment modeling".into(),
    };
    let func = VerifiableFunction {
        name: "capturing_contract_closure".to_string(),
        def_path: "test::capturing_contract_closure".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("low".into()) },
                LocalDecl { index: 2, ty: unsupported_closure, name: Some("closure".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Closure {
                                name: closure_name.clone(),
                                captures: vec![],
                                call_kind: ClosureCallKind::FnOnce,
                            },
                            vec![Operand::Copy(Place::local(1))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(2),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module =
        lower_to_trust_ir(&func).expect("closure aggregate operands should recover env type");
    assert_eq!(module.structs.len(), 1);
    assert_eq!(module.structs[0].name, format!("closure_env::{closure_name}"));
    assert_eq!(module.structs[0].fields.len(), 1);
    assert_eq!(module.structs[0].fields[0].name, "__capture0");
    assert_eq!(module.structs[0].fields[0].ty, TrustIrTy::U32);
    let env_ty = TrustIrTy::Struct(module.structs[0].id);
    assert!(module.functions[0].blocks[0].body.iter().any(|node| {
        matches!(&node.inst, Inst::InsertField { ty, field: 0, .. } if *ty == env_ty)
    }));
    assert_valid_module(&module);
}

#[test]
fn test_lower_rust_call_closure_shim_uses_registered_env_and_flattens_tuple_args() {
    let closure_name = "test::caller::{closure#0}".to_string();
    let unsupported_closure = Ty::Unsupported {
        kind: "TyKind::Closure".into(),
        detail: format!("closure {closure_name} needs captured-environment modeling"),
    };

    let caller = VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("captured".into()) },
                LocalDecl {
                    index: 2,
                    ty: unsupported_closure.clone(),
                    name: Some("closure".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Tuple(vec![Ty::u32()]),
                    name: Some("rust_call_args".into()),
                },
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("call_result".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Aggregate(
                                AggregateKind::Closure {
                                    name: closure_name.clone(),
                                    captures: vec![],
                                    call_kind: ClosureCallKind::FnOnce,
                                },
                                vec![Operand::Copy(Place::local(1))],
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Aggregate(
                                AggregateKind::Tuple,
                                vec![Operand::Constant(ConstValue::Uint(7, 32))],
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "core::ops::function::FnOnce::call_once".to_string(),
                        args: vec![Operand::Move(Place::local(2)), Operand::Move(Place::local(3))],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let closure_body = VerifiableFunction {
        name: closure_name.clone(),
        def_path: closure_name.clone(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: unsupported_closure, name: Some("self".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("arg".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::field(1, 0)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir_functions("closure_call", &[caller, closure_body])
        .expect("closure shim should resolve to typed closure body");

    assert_eq!(module.structs.len(), 1);
    assert_eq!(module.structs[0].name, format!("closure_env::{closure_name}"));
    assert_eq!(module.structs[0].fields[0].ty, TrustIrTy::U32);

    let caller_bb0 = &module.functions[0].blocks[0];
    assert!(
        caller_bb0.body.iter().any(|node| matches!(&node.inst, Inst::Call { callee, args }
            if callee.index() == 1 && args.len() == 2)),
        "callable trait shim should emit a direct call to the closure body with flattened args"
    );
    assert!(
        caller_bb0.body.iter().any(|node| {
            matches!(&node.inst, Inst::ExtractField { ty: TrustIrTy::U32, field: 0, .. })
        }),
        "rust-call tuple argument should be projected before the closure body call"
    );

    let closure_entry = &module.functions[1].blocks[0];
    let env_ty = TrustIrTy::Struct(module.structs[0].id);
    assert_eq!(closure_entry.params[0].1, env_ty);
    assert_eq!(closure_entry.params[1].1, TrustIrTy::U32);
    assert!(
        closure_entry.body.iter().any(|node| {
            matches!(&node.inst, Inst::ExtractField { ty: TrustIrTy::U32, field: 0, .. })
        }),
        "closure body should read the typed captured environment field"
    );
    assert_valid_module(&module);
}

#[test]
fn test_rust_call_closure_shim_without_body_fails_closed() {
    let closure_name = "test::caller::{closure#0}".to_string();
    let func = VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("captured".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Unsupported {
                        kind: "TyKind::Closure".into(),
                        detail: format!(
                            "closure {closure_name} needs captured-environment modeling"
                        ),
                    },
                    name: Some("closure".into()),
                },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Closure {
                                name: closure_name.clone(),
                                captures: vec![],
                                call_kind: ClosureCallKind::FnOnce,
                            },
                            vec![Operand::Copy(Place::local(1))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "core::ops::function::FnOnce::call_once".to_string(),
                        args: vec![
                            Operand::Move(Place::local(2)),
                            Operand::Constant(ConstValue::Unit),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("closure shim must not fabricate missing body");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(ref msg)
            if msg.contains("Rust callable trait shim")
                && msg.contains("closure body is not present")),
        "expected missing closure-body diagnostic, got {err:?}"
    );
}

#[test]
fn test_unsupported_rustc_closure_marker_without_aggregate_fails_closed() {
    let func = VerifiableFunction {
        name: "closure_arg_blocked".to_string(),
        def_path: "test::closure_arg_blocked".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Unsupported {
                        kind: "TyKind::Closure".into(),
                        detail: "closure test::f::{closure#0} needs captured-environment modeling"
                            .into(),
                    },
                    name: Some("closure".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("unmaterialized rustc closure marker must fail");
    assert!(
        matches!(err, BridgeError::UnsupportedType(ref msg)
            if msg.contains("TyKind::Closure")
                && msg.contains("without captured-environment metadata")
                && msg.contains("AggregateKind::Closure operands")),
        "expected actionable closure marker diagnostic, got {err:?}"
    );
}

#[test]
fn test_symbolic_operand_lowers_to_formula_dialect_op() {
    let formula = trust_types::Formula::BitVec { value: 0x2a, width: 64 };
    let func = VerifiableFunction {
        name: "symbolic_return".to_string(),
        def_path: "test::symbolic_return".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i64(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Symbolic(formula.clone())),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("symbolic formula should lower");
    assert_valid_module(&module);

    let op = module.functions[0].blocks[0]
        .body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::DialectOp(op)
                if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_FORMULA_OP =>
            {
                Some((node, op))
            }
            _ => None,
        })
        .expect("symbolic formula dialect op");

    assert_eq!(op.1.result_tys.as_slice(), [TrustIrTy::I64]);
    assert_eq!(op.0.results.len(), 1);
    assert!(matches!(
        op.1.attr(SYMBOLIC_FORMULA_ATTR_SCHEMA),
        Some(AttrValue::Str(s)) if s == "trust-types.Formula@1"
    ));
    let formula_json =
        op.1.attr(SYMBOLIC_FORMULA_ATTR_JSON)
            .and_then(AttrValue::as_str)
            .expect("formula_json attr");
    let roundtripped: trust_types::Formula =
        serde_json::from_str(formula_json).expect("formula JSON should round-trip");
    assert_eq!(roundtripped, formula);
}

#[test]
fn test_bool_symbolic_operand_lowers_with_json_and_schema_attrs() {
    let formula = Formula::Bool(true);
    let func = VerifiableFunction {
        name: "symbolic_bool_return".to_string(),
        def_path: "test::symbolic_bool_return".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Bool, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Symbolic(formula.clone())),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("bool symbolic formula should lower");
    let op = module.functions[0].blocks[0]
        .body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::DialectOp(op)
                if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_FORMULA_OP =>
            {
                Some(op.as_ref())
            }
            _ => None,
        })
        .expect("symbolic formula dialect op");

    assert_eq!(op.result_tys, vec![TrustIrTy::Bool]);
    assert!(matches!(
        op.attr(SYMBOLIC_FORMULA_ATTR_SCHEMA),
        Some(AttrValue::Str(s)) if s == "trust-types.Formula@1"
    ));
    let formula_json =
        op.attr(SYMBOLIC_FORMULA_ATTR_JSON).and_then(AttrValue::as_str).expect("formula_json attr");
    let roundtripped: Formula =
        serde_json::from_str(formula_json).expect("formula JSON should round-trip");
    assert_eq!(roundtripped, formula);
    assert_valid_module(&module);
}

#[test]
fn test_u64_symbolic_operand_preserves_unsigned_destination_type() {
    let formula = Formula::BitVec { value: 0x2a, width: 64 };
    let func = VerifiableFunction {
        name: "symbolic_u64_return".to_string(),
        def_path: "test::symbolic_u64_return".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::u64(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Symbolic(formula)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("u64 symbolic formula should lower");
    let op = module.functions[0].blocks[0]
        .body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::DialectOp(op)
                if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_FORMULA_OP =>
            {
                Some(op.as_ref())
            }
            _ => None,
        })
        .expect("symbolic formula dialect op");

    assert_eq!(op.result_tys, vec![TrustIrTy::U64]);
    assert_valid_module(&module);
}

#[test]
fn test_contextual_i64_symbolic_operand_preserves_signed_binary_lowering() {
    let formula = Formula::Var("x".into(), Sort::BitVec(64));
    let func = VerifiableFunction {
        name: "symbolic_i64_div".to_string(),
        def_path: "test::symbolic_i64_div".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i64(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Symbolic(formula),
                        Operand::Constant(ConstValue::Int(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("contextual i64 symbolic formula should lower");
    let bb0 = &module.functions[0].blocks[0];
    let formula_op = bb0
        .body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::DialectOp(op)
                if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_FORMULA_OP =>
            {
                Some(op.as_ref())
            }
            _ => None,
        })
        .expect("symbolic formula dialect op");

    assert_eq!(formula_op.result_tys, vec![TrustIrTy::I64]);
    assert!(
        bb0.body.iter().any(|node| matches!(
            &node.inst,
            Inst::BinOp { op: TrustIrBinOp::SDiv, ty: TrustIrTy::I64, .. }
        )),
        "i64 contextual symbolic division should lower with signed semantics"
    );
    assert_valid_module(&module);
}

#[test]
fn test_contextless_int_and_array_symbolic_sorts_fail_closed_with_destination_context() {
    let array_sort = Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8)));
    let cases = [
        (
            "int",
            Formula::Var("lhs_int".into(), Sort::Int),
            Formula::Var("rhs_int".into(), Sort::Int),
            "Int",
        ),
        (
            "array",
            Formula::Var("lhs_array".into(), array_sort.clone()),
            Formula::Var("rhs_array".into(), array_sort),
            "(Array Int (_ BitVec 8))",
        ),
    ];

    for (case, lhs, rhs, sort_text) in cases {
        let func = VerifiableFunction {
            name: format!("contextless_{case}_symbolic_eq"),
            def_path: format!("test::contextless_{case}_symbolic_eq"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Bool, name: None }],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Symbolic(lhs),
                            Operand::Symbolic(rhs),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let err = match lower_to_trust_ir(&func) {
            Ok(_) => panic!("contextless {case} symbolic formula unexpectedly lowered"),
            Err(err) => err,
        };
        let BridgeError::UnsupportedType(msg) = err else {
            panic!("contextless {case} symbolic formula returned wrong error: {err:?}");
        };

        assert!(
            msg.contains("contextless symbolic formula sort"),
            "diagnostic should name contextless symbolic formula lowering: {msg}"
        );
        assert!(msg.contains(sort_text), "diagnostic should name sort {sort_text}: {msg}");
        assert!(
            msg.contains("contextual destination type"),
            "diagnostic should require destination type context: {msg}"
        );
        assert!(
            msg.contains("proof-grade lowering"),
            "diagnostic should identify the proof-grade blocker context: {msg}"
        );
        assert!(
            !msg.contains("Undef"),
            "contextless symbolic formula sorts must fail closed, not lower through Undef: {msg}"
        );
    }
}

#[test]
fn test_lifted_memory_array_formula_preserves_typed_memory_state_not_u64_coercion() {
    let memory_sort = Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8)));
    let memory = Formula::Var("MEM".into(), memory_sort.clone());
    let address = Formula::Var("X1".into(), Sort::BitVec(64));
    let value = Formula::BitVec { value: 0xaa, width: 8 };
    let store = Formula::Store(Box::new(memory), Box::new(address), Box::new(value));
    let func = VerifiableFunction {
        name: "lifted_memory_state".to_string(),
        def_path: "test::lifted_memory_state".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("MEM".to_string()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Symbolic(store.clone())),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("lifted MEM array formula should be preserved");
    let bb0 = &module.functions[0].blocks[0];
    let memory_node = bb0
        .body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::DialectOp(op)
                if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_MEMORY_STATE_OP =>
            {
                Some((node, op.as_ref()))
            }
            _ => None,
        })
        .expect("symbolic memory-state dialect op");

    assert!(
        memory_node.0.results.is_empty(),
        "memory array state must not be coerced into a scalar TrustIr result"
    );
    assert!(
        memory_node.1.result_tys.is_empty(),
        "memory array state must not declare a u64 result type"
    );
    assert_eq!(
        memory_node.1.attr(SYMBOLIC_FORMULA_ATTR_SORT),
        Some(&AttrValue::Str(memory_sort.to_smtlib()))
    );
    let formula_json = memory_node
        .1
        .attr(SYMBOLIC_FORMULA_ATTR_JSON)
        .and_then(AttrValue::as_str)
        .expect("memory formula JSON attr");
    let roundtripped: Formula =
        serde_json::from_str(formula_json).expect("memory formula JSON should round-trip");
    assert_eq!(roundtripped, store);
    assert!(
        !bb0.body.iter().any(|node| matches!(&node.inst, Inst::Copy { ty: TrustIrTy::U64, .. })),
        "memory array state must not lower through a u64 Copy"
    );
    assert_valid_module(&module);
}

#[test]
fn test_non_memory_array_formula_to_u64_stays_fail_closed() {
    let array_sort = Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8)));
    let func = VerifiableFunction {
        name: "array_to_u64".to_string(),
        def_path: "test::array_to_u64".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl {
                index: 0,
                ty: Ty::Int { width: 64, signed: false },
                name: Some("not_memory".to_string()),
            }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Symbolic(Formula::Var(
                        "ARR".into(),
                        array_sort.clone(),
                    ))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Int { width: 64, signed: false },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("non-memory array formula must fail closed");
    let BridgeError::UnsupportedType(msg) = err else {
        panic!("array-to-u64 returned wrong error: {err:?}");
    };
    assert!(
        msg.contains("symbolic formula sort (Array (_ BitVec 64) (_ BitVec 8)) is incompatible"),
        "diagnostic should name incompatible array sort: {msg}"
    );
    assert!(
        msg.contains("contextual destination type Int { width: 64, signed: false }"),
        "diagnostic should name scalar destination type: {msg}"
    );
}

#[test]
fn test_lower_unit_return_function() {
    let func = VerifiableFunction {
        name: "noop".to_string(),
        def_path: "test::noop".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![TrustBlock {
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
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    let ft = &module.func_types[module.functions[0].ty.index() as usize];
    assert!(ft.returns.is_empty(), "Unit return should produce empty returns");
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body
            .iter()
            .any(|node| matches!(&node.inst, Inst::Return { values } if values.is_empty())),
        "Unit return should emit an empty TrustIr return"
    );
    assert_valid_module(&module);
}

#[test]
fn test_lower_never_return_emits_empty_return_values() {
    let func = VerifiableFunction {
        name: "never_ret".to_string(),
        def_path: "test::never_ret".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Never, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Never,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body
            .iter()
            .any(|node| matches!(&node.inst, Inst::Return { values } if values.is_empty())),
        "Never return should emit an empty TrustIr return"
    );
    assert_valid_module(&module);
}

#[test]
fn test_lower_constant_use() {
    let func = VerifiableFunction {
        name: "const_fn".to_string(),
        def_path: "test::const_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_const = bb0.body.iter().any(|node| matches!(&node.inst, Inst::Const { .. }));
    assert!(has_const, "should have a Const instruction");
}

#[test]
fn test_symbolic_operand_lowers_to_formula_dialect_not_undef() {
    let symbolic = Formula::BvAdd(
        Box::new(Formula::Var("x0".into(), Sort::BitVec(64))),
        Box::new(Formula::BitVec { value: 1, width: 64 }),
        64,
    );
    let func = VerifiableFunction {
        name: "symbolic_formula_fn".to_string(),
        def_path: "test::symbolic_formula_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
                    name: Some("ordinary_aggregate".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Tuple,
                            vec![
                                Operand::Constant(ConstValue::Uint(7, 64)),
                                Operand::Constant(ConstValue::Bool(true)),
                            ],
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Symbolic(symbolic)),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("symbolic formula should lower conservatively");
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|node| matches!(&node.inst, Inst::Undef { ty: TrustIrTy::Tuple(_) })),
        "ordinary aggregate construction should still use regular Undef"
    );

    let symbolic_node = bb0
        .body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::DialectOp(op)
                if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_FORMULA_OP =>
            {
                Some((node, op.as_ref()))
            }
            _ => None,
        })
        .expect("symbolic operand should lower to a formula dialect op");

    assert_eq!(symbolic_node.0.results.len(), 1);
    assert_eq!(symbolic_node.1.result_tys, vec![TrustIrTy::U64]);
    assert!(matches!(
        symbolic_node.1.attr(SYMBOLIC_FORMULA_ATTR_SMTLIB),
        Some(AttrValue::Str(s)) if s == "(bvadd x0 (_ bv1 64))"
    ));
    assert!(matches!(
        symbolic_node.1.attr(SYMBOLIC_FORMULA_ATTR_SORT),
        Some(AttrValue::Str(s)) if s == "(_ BitVec 64)"
    ));
    assert!(matches!(
        symbolic_node.1.attr(SYMBOLIC_FORMULA_ATTR_DEBUG),
        Some(AttrValue::Str(s)) if s.contains("BvAdd")
    ));
    assert!(matches!(
        symbolic_node.1.attr(SYMBOLIC_FORMULA_ATTR_SCHEMA),
        Some(AttrValue::Str(s)) if s == "trust-types.Formula@1"
    ));
    assert!(symbolic_node.1.attr(SYMBOLIC_FORMULA_ATTR_JSON).is_some());
    assert!(
        !matches!(&symbolic_node.0.inst, Inst::Undef { .. }),
        "symbolic formulas must not be represented as plain Undef"
    );
    assert_valid_module(&module);
}

#[test]
fn test_symbolic_formula_survives_canonical_trust_ir_roundtrip() {
    let symbolic = Formula::BvAdd(
        Box::new(Formula::Var("x0".into(), Sort::BitVec(64))),
        Box::new(Formula::BitVec { value: 1, width: 64 }),
        64,
    );
    let func = VerifiableFunction {
        name: "symbolic_canonical_fn".to_string(),
        def_path: "test::symbolic_canonical_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::u64(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Symbolic(symbolic.clone())),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("symbolic formula should lower");
    let canonical = trust_ir::format::canonical(&module);
    assert!(canonical.contains("dialect_op trust_symbolic.formula"));
    assert!(canonical.contains(SYMBOLIC_FORMULA_ATTR_JSON));
    assert!(!canonical.contains("undef u64"));

    let reparsed = trust_ir::parser::parse_module(&canonical).expect("parse canonical TrustIr");
    let recanonical = trust_ir::format::canonical(&reparsed);
    assert_eq!(canonical, recanonical, "canonical TrustIr must be a fixed point");

    let formula_json = reparsed.functions[0].blocks[0]
        .body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::DialectOp(op)
                if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_FORMULA_OP =>
            {
                op.attr(SYMBOLIC_FORMULA_ATTR_JSON).and_then(AttrValue::as_str)
            }
            _ => None,
        })
        .expect("symbolic formula JSON attr after canonical roundtrip");
    let roundtripped: Formula =
        serde_json::from_str(formula_json).expect("formula JSON should round-trip");
    assert_eq!(roundtripped, symbolic);
}

const EXACT_BINARY_SOURCE_PROVENANCE_FIXTURE_PATH: &str = "fixtures/exact-aarch64-nop.bin";
const EXACT_BINARY_SOURCE_PROVENANCE_FIXTURE_BYTES: [u8; 4] = [0x1f, 0x20, 0x03, 0xd5];

fn exact_binary_source_provenance_artifact_fixture() -> DecompilationArtifact {
    let source = SourceSpan {
        file: "src/lifted.rs".to_string(),
        line_start: 7,
        col_start: 5,
        line_end: 7,
        col_end: 23,
    };
    let origin = BinaryOrigin {
        binary_path: None,
        function_entry: Some(0x401000),
        instruction_address: 0x401004,
        instruction_size: Some(4),
        encoding: Some(0xd503_201f),
        instruction_bytes: EXACT_BINARY_SOURCE_PROVENANCE_FIXTURE_BYTES.to_vec(),
        source: Some(source.clone()),
    };
    let lifted = VerifiableFunction {
        name: "canonical_binary_prov".to_string(),
        def_path: "test::canonical_binary_prov".to_string(),
        span: source.clone(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::u32(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                    span: source,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let digest = stable_sha256_hex(&EXACT_BINARY_SOURCE_PROVENANCE_FIXTURE_BYTES);

    DecompilationArtifact {
        binary: BinaryArtifactMetadata {
            path: Some(EXACT_BINARY_SOURCE_PROVENANCE_FIXTURE_PATH.to_string()),
            byte_len: Some(EXACT_BINARY_SOURCE_PROVENANCE_FIXTURE_BYTES.len() as u64),
            root_artifact_digest: Some(BinaryArtifactDigest::sha256(digest.clone())),
            selected_image: Some(BinarySelectedImageIdentity {
                file_offset: 0,
                file_size: EXACT_BINARY_SOURCE_PROVENANCE_FIXTURE_BYTES.len() as u64,
                sha256: digest,
            }),
            ..Default::default()
        },
        target: trust_types::DecompileTarget::TrustIr,
        source_provenance: BinarySourceProvenanceSummary {
            status: "exact".to_string(),
            exact_mapping_count: 1,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
            source_backpropagation_allowed: true,
        },
        functions: vec![DecompiledFunction {
            name: "canonical_binary_prov".to_string(),
            entry: 0x401000,
            origin: Some(origin.clone()),
            instruction_provenance: vec![origin],
            lifted: Some(lifted),
            ..Default::default()
        }],
        ..Default::default()
    }
}

fn canonical_binary_provenance_artifact() -> DecompilationArtifact {
    exact_binary_source_provenance_artifact_fixture()
}

fn binary_address_only_provenance_artifact_fixture(
    source_provenance: BinarySourceProvenanceSummary,
) -> DecompilationArtifact {
    let mut artifact = exact_binary_source_provenance_artifact_fixture();
    let binary_span = SourceSpan::binary_address(0x401004);
    artifact.source_provenance = source_provenance;
    artifact.functions[0].origin.as_mut().expect("function origin").source =
        Some(binary_span.clone());
    artifact.functions[0].instruction_provenance[0].source = Some(binary_span.clone());
    let lifted = artifact.functions[0].lifted.as_mut().expect("lifted function");
    lifted.span = binary_span.clone();
    match &mut lifted.body.blocks[0].stmts[0] {
        Statement::Assign { span, .. } | Statement::Unsupported { span, .. } => {
            *span = binary_span;
        }
        _ => unreachable!("fixture statement carries a source span"),
    }
    artifact
}

fn mutate_first_binary_provenance_attr(module: &mut trust_ir::Module, attr: &str, value: &str) {
    let op = module.functions[0].blocks[0]
        .body
        .iter_mut()
        .find_map(|node| match &mut node.inst {
            Inst::DialectOp(op)
                if op.dialect == BINARY_PROVENANCE_DIALECT && op.op == BINARY_PROVENANCE_OP =>
            {
                Some(op.as_mut())
            }
            _ => None,
        })
        .expect("binary provenance op");
    let entry = op.attrs.iter_mut().find(|entry| entry.name == attr).expect("attr exists");
    entry.value = AttrValue::Str(value.to_string());
}

#[test]
fn test_binary_provenance_survives_canonical_trust_ir_roundtrip() {
    let artifact = canonical_binary_provenance_artifact();
    let module = lower_decompilation_artifact_to_trust_ir(&artifact)
        .expect("digest-bound provenance artifact should lower");
    let canonical = trust_ir::format::canonical(&module);

    assert!(canonical.contains("dialect_op trust_binary.provenance"));
    assert!(canonical.contains(BINARY_PROVENANCE_SCHEMA));
    assert!(canonical.contains(BINARY_PROVENANCE_ATTR_PROVENANCE_STATUS));
    assert!(canonical.contains(BINARY_PROVENANCE_ATTR_RECORD_DIGEST));
    assert!(canonical.contains(BINARY_PROVENANCE_ATTR_ARTIFACT_SHA256));
    assert!(canonical.contains(EXACT_BINARY_SOURCE_PROVENANCE_FIXTURE_PATH));

    let reparsed = trust_ir::parser::parse_module(&canonical).expect("parse canonical TrustIr");
    let recanonical = trust_ir::format::canonical(&reparsed);
    assert_eq!(canonical, recanonical, "canonical TrustIr provenance must be a fixed point");

    let report = collect_canonical_binary_provenance(&reparsed);
    assert!(report.rejections.is_empty(), "unexpected provenance rejections: {report:?}");
    assert_eq!(report.records.len(), 1);
    let record = &report.records[0];
    assert_eq!(record.function, "canonical_binary_prov");
    assert_eq!(record.block, 0);
    assert_eq!(record.statement_index, 0);
    assert_eq!(
        record.origin.binary_path.as_deref(),
        Some(EXACT_BINARY_SOURCE_PROVENANCE_FIXTURE_PATH)
    );
    assert_eq!(record.origin.function_entry, Some(0x401000));
    assert_eq!(record.origin.instruction_address, 0x401004);
    assert_eq!(record.origin.instruction_size, Some(4));
    assert_eq!(
        record.origin.instruction_bytes,
        EXACT_BINARY_SOURCE_PROVENANCE_FIXTURE_BYTES.to_vec()
    );
    assert_eq!(record.origin.source.as_ref().map(|span| span.file.as_str()), Some("src/lifted.rs"));
    let expected_digest = stable_sha256_hex(&EXACT_BINARY_SOURCE_PROVENANCE_FIXTURE_BYTES);
    assert_eq!(
        record
            .artifact_digest_identity
            .root_artifact_digest
            .as_ref()
            .map(|digest| digest.value.as_str()),
        Some(expected_digest.as_str())
    );
    assert_eq!(record.source_status, "exact");
    assert_eq!(record.provenance_status, BINARY_PROVENANCE_STATUS_CHECKED_EXACT);
    assert_eq!(record.record_digest.len(), 64);

    let blockers = canonical_binary_provenance_target_blockers(&report.records, &[]);
    assert!(
        blockers
            .iter()
            .any(|blocker| blocker.contains("is not accepted by a target proof consumer")),
        "provenance must remain fail-closed until target consumer acceptance"
    );
    assert!(
        canonical_binary_provenance_target_blockers(
            &report.records,
            &[CanonicalBinaryProvenanceAcceptance {
                record_digest: record.record_digest.clone(),
                consumer: "unit-test-target-consumer".to_string(),
            }],
        )
        .is_empty()
    );
}

#[test]
fn test_canonical_trust_ir_rejects_layout_sensitive_cast_without_typed_layout_evidence() {
    let mut artifact = canonical_binary_provenance_artifact();
    let lifted = artifact.functions[0]
        .lifted
        .as_mut()
        .expect("canonical artifact should carry lifted TrustIr");
    let source = lifted.span.clone();
    lifted.body = VerifiableBody {
        locals: vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Tuple(vec![Ty::u64(), Ty::u64()]),
                name: Some("pair".into()),
            },
        ],
        blocks: vec![TrustBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u64()),
                span: source,
            }],
            terminator: Terminator::Return,
        }],
        arg_count: 1,
        return_ty: Ty::u64(),
    };

    let error = lower_decompilation_artifact_to_trust_ir(&artifact)
        .expect_err("layout-sensitive cast without typed layout evidence must fail closed");
    assert!(matches!(
        error,
        BridgeError::UnsupportedOp(reason)
            if reason.contains("typed layout evidence")
                && reason.contains(TRUST_IR_LAYOUT_EVIDENCE_COMMIT)
    ));
}

#[test]
fn test_binary_provenance_exact_source_fixture_emits_checked_status() {
    let artifact = exact_binary_source_provenance_artifact_fixture();
    assert!(artifact.source_provenance.effective_source_backpropagation_allowed());

    let module = lower_decompilation_artifact_to_trust_ir(&artifact)
        .expect("exact fixture should produce canonical provenance");
    let report = collect_canonical_binary_provenance(&module);

    assert!(report.rejections.is_empty(), "unexpected provenance rejections: {report:?}");
    assert_eq!(report.records.len(), 1);
    let record = &report.records[0];
    assert_eq!(record.source_status, "exact");
    assert_eq!(record.provenance_status, BINARY_PROVENANCE_STATUS_CHECKED_EXACT);
    assert!(record.origin.source.as_ref().is_some_and(|source| !source.is_binary()));
    let expected_digest = stable_sha256_hex(&EXACT_BINARY_SOURCE_PROVENANCE_FIXTURE_BYTES);
    assert_eq!(
        record
            .artifact_digest_identity
            .selected_image
            .as_ref()
            .map(|selected| selected.sha256.as_str()),
        Some(expected_digest.as_str())
    );
}

#[test]
fn test_binary_provenance_producer_rejects_wrong_binary_path_fixture() {
    let mut artifact = exact_binary_source_provenance_artifact_fixture();
    artifact.functions[0].instruction_provenance[0].binary_path =
        Some("fixtures/wrong-binary.bin".to_string());

    let error = lower_decompilation_artifact_to_trust_ir(&artifact)
        .expect_err("wrong-binary provenance must fail closed");
    let error = error.to_string();
    assert!(error.contains("names binary path"), "{error}");
    assert!(error.contains(EXACT_BINARY_SOURCE_PROVENANCE_FIXTURE_PATH), "{error}");
}

#[test]
fn test_binary_provenance_producer_rejects_wrong_whole_file_digest_fixture() {
    let mut artifact = exact_binary_source_provenance_artifact_fixture();
    artifact.binary.selected_image.as_mut().expect("selected image").sha256 =
        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string();

    let error = lower_decompilation_artifact_to_trust_ir(&artifact)
        .expect_err("wrong whole-file digest must fail closed");
    assert!(
        error
            .to_string()
            .contains("root artifact digest does not match whole-file selected image digest"),
        "{error}"
    );
}

#[test]
fn test_binary_provenance_marks_ambiguous_and_unavailable_fixtures_not_checked_exact() {
    let cases = [
        (
            BinarySourceProvenanceSummary {
                status: "ambiguous".to_string(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 1,
                diagnostics: vec!["ambiguous source rows withheld".to_string()],
                source_backpropagation_allowed: false,
            },
            BINARY_PROVENANCE_STATUS_AMBIGUOUS,
        ),
        (
            BinarySourceProvenanceSummary {
                status: "unavailable".to_string(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: vec!["debug/source provenance unavailable".to_string()],
                source_backpropagation_allowed: false,
            },
            BINARY_PROVENANCE_STATUS_UNAVAILABLE,
        ),
    ];

    for (source_provenance, expected_status) in cases {
        let artifact = binary_address_only_provenance_artifact_fixture(source_provenance);
        assert!(!artifact.source_provenance.effective_source_backpropagation_allowed());

        let module = lower_decompilation_artifact_to_trust_ir(&artifact)
            .expect("non-exact provenance can be carried only as fail-closed metadata");
        let report = collect_canonical_binary_provenance(&module);

        assert!(report.rejections.is_empty(), "unexpected provenance rejections: {report:?}");
        assert_eq!(report.records.len(), 1);
        let record = &report.records[0];
        assert_eq!(record.provenance_status, expected_status);
        assert_ne!(record.provenance_status, BINARY_PROVENANCE_STATUS_CHECKED_EXACT);
        assert!(record.origin.source.as_ref().is_some_and(SourceSpan::is_binary));
        assert!(
            canonical_binary_provenance_target_blockers(&report.records, &[])
                .iter()
                .any(|blocker| blocker.contains("is not accepted by a target proof consumer")),
            "non-exact fixture must not open target/source rewrite acceptance"
        );
    }
}

#[test]
fn test_binary_provenance_parser_rejects_wrong_schema() {
    let artifact = canonical_binary_provenance_artifact();
    let mut module = lower_decompilation_artifact_to_trust_ir(&artifact)
        .expect("digest-bound provenance artifact should lower");
    mutate_first_binary_provenance_attr(
        &mut module,
        BINARY_PROVENANCE_ATTR_SCHEMA,
        "trust-types.BinaryProvenance@999",
    );

    let report = collect_canonical_binary_provenance(&module);
    assert!(report.records.is_empty());
    assert_eq!(report.rejections.len(), 1);
    assert!(
        report.rejections[0].reason.contains("unsupported binary provenance schema"),
        "{:?}",
        report.rejections[0]
    );
}

#[test]
fn test_binary_provenance_parser_rejects_tampered_digest() {
    let artifact = canonical_binary_provenance_artifact();
    let mut module = lower_decompilation_artifact_to_trust_ir(&artifact)
        .expect("digest-bound provenance artifact should lower");
    mutate_first_binary_provenance_attr(
        &mut module,
        BINARY_PROVENANCE_ATTR_INSTRUCTION_BYTES,
        "ffffffff",
    );

    let report = collect_canonical_binary_provenance(&module);
    assert!(report.records.is_empty());
    assert_eq!(report.rejections.len(), 1);
    assert!(
        report.rejections[0].reason.contains("record_digest")
            && report.rejections[0].reason.contains("does not match"),
        "{:?}",
        report.rejections[0]
    );
}

#[test]
fn test_binary_provenance_parser_ignores_forged_target_consumption_claim() {
    let artifact = canonical_binary_provenance_artifact();
    let mut module = lower_decompilation_artifact_to_trust_ir(&artifact)
        .expect("digest-bound provenance artifact should lower");
    mutate_first_binary_provenance_attr(
        &mut module,
        crate::BINARY_PROVENANCE_ATTR_TARGET_SEMANTICS_CONSUMED,
        "true",
    );

    let report = collect_canonical_binary_provenance(&module);
    assert_eq!(report.records.len(), 1);
    assert_eq!(report.records[0].input_claimed_target_semantics_consumed, Some(true));
    assert!(
        canonical_binary_provenance_target_blockers(&report.records, &[])
            .iter()
            .any(|blocker| blocker.contains("is not accepted by a target proof consumer")),
        "input target_semantics_consumed attr must be audit-only"
    );
}

#[test]
fn test_canonical_trust_ir_preserves_typed_symbolic_formula_not_undef() {
    let symbolic = Formula::Var("flag".into(), Sort::Bool);
    let func = VerifiableFunction {
        name: "typed_symbolic_canonical_fn".to_string(),
        def_path: "test::typed_symbolic_canonical_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Bool, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Symbolic(symbolic.clone())),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("symbolic formula should lower");
    let canonical = trust_ir::format::canonical(&module);
    assert!(canonical.contains("dialect_op trust_symbolic.formula"));
    assert!(!canonical.contains("undef"), "canonical symbolic formula must not become Undef");

    let reparsed = trust_ir::parser::parse_module(&canonical).expect("parse canonical TrustIr");
    assert_eq!(
        canonical,
        trust_ir::format::canonical(&reparsed),
        "canonical TrustIr must remain stable after parsing"
    );

    let bb0 = &reparsed.functions[0].blocks[0];
    assert!(
        !bb0.body.iter().any(|node| matches!(&node.inst, Inst::Undef { .. })),
        "reparsed canonical symbolic formula must not contain Undef"
    );

    let symbolic_node = bb0
        .body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::DialectOp(op)
                if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_FORMULA_OP =>
            {
                Some((node, op.as_ref()))
            }
            _ => None,
        })
        .expect("symbolic formula dialect op after canonical parse");

    assert_eq!(symbolic_node.0.results.len(), 1);
    assert_eq!(symbolic_node.1.result_tys, vec![TrustIrTy::Bool]);
    assert!(matches!(
        symbolic_node.1.attr(SYMBOLIC_FORMULA_ATTR_SORT),
        Some(AttrValue::Str(s)) if s == "Bool"
    ));
    let formula_json = symbolic_node
        .1
        .attr(SYMBOLIC_FORMULA_ATTR_JSON)
        .and_then(AttrValue::as_str)
        .expect("formula_json attr after canonical parse");
    let roundtripped: Formula =
        serde_json::from_str(formula_json).expect("formula JSON should round-trip");
    assert_eq!(roundtripped, symbolic);
}

#[test]
fn test_symbolic_aggregate_lowers_without_undef_seed() {
    let func = VerifiableFunction {
        name: "symbolic_aggregate_fn".to_string(),
        def_path: "test::symbolic_aggregate_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl {
                index: 0,
                ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
                name: None,
            }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Tuple,
                        vec![
                            Operand::Symbolic(Formula::Var("x0".into(), Sort::BitVec(64))),
                            Operand::Constant(ConstValue::Bool(true)),
                        ],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("symbolic aggregate should lower");
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        !bb0.body.iter().any(|node| matches!(&node.inst, Inst::Undef { ty: TrustIrTy::Tuple(_) })),
        "symbolic aggregate must not be seeded from tuple Undef"
    );
    let aggregate_op = bb0
        .body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::DialectOp(op)
                if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_AGGREGATE_OP =>
            {
                Some(op.as_ref())
            }
            _ => None,
        })
        .expect("symbolic aggregate dialect op");
    assert_eq!(aggregate_op.operands.len(), 2);
    assert_eq!(
        aggregate_op.result_tys,
        vec![TrustIrTy::Tuple(vec![TrustIrTy::U64, TrustIrTy::Bool])]
    );
    assert!(matches!(
        aggregate_op.attr(SYMBOLIC_AGGREGATE_ATTR_KIND),
        Some(AttrValue::Str(s)) if s == "tuple"
    ));
    assert!(matches!(
        aggregate_op.attr(SYMBOLIC_AGGREGATE_ATTR_FIELD_COUNT),
        Some(AttrValue::U64(2))
    ));
    let canonical = trust_ir::format::canonical(&module);
    assert!(canonical.contains("dialect_op trust_symbolic.aggregate"));
    assert!(!canonical.contains("undef (u64, bool)"));
    let reparsed =
        trust_ir::parser::parse_module(&canonical).expect("parse canonical aggregate TrustIr");
    assert_eq!(
        canonical,
        trust_ir::format::canonical(&reparsed),
        "symbolic aggregate canonical TrustIr must be a fixed point"
    );
    assert_valid_module(&module);
}

#[test]
fn test_symbolic_array_repeat_lowers_without_undef_seed() {
    let func = VerifiableFunction {
        name: "symbolic_repeat_fn".to_string(),
        def_path: "test::symbolic_repeat_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl {
                index: 0,
                ty: Ty::Array { elem: Box::new(Ty::u64()), len: 2 },
                name: None,
            }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Repeat(
                        Operand::Symbolic(Formula::Var("x0".into(), Sort::BitVec(64))),
                        2,
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Array { elem: Box::new(Ty::u64()), len: 2 },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("symbolic repeat should lower");
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        !bb0.body
            .iter()
            .any(|node| matches!(&node.inst, Inst::Undef { ty: TrustIrTy::Array(_, 2) })),
        "symbolic repeat must not be seeded from array Undef"
    );
    let aggregate_op = bb0
        .body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::DialectOp(op)
                if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_AGGREGATE_OP =>
            {
                Some(op.as_ref())
            }
            _ => None,
        })
        .expect("symbolic repeat aggregate dialect op");
    assert_eq!(aggregate_op.operands.len(), 2);
    assert!(matches!(
        aggregate_op.attr(SYMBOLIC_AGGREGATE_ATTR_KIND),
        Some(AttrValue::Str(s)) if s == "array_repeat"
    ));
    assert_valid_module(&module);
}

#[test]
fn test_symbolic_local_aggregate_lowers_without_undef_seed() {
    let func = VerifiableFunction {
        name: "symbolic_local_aggregate_fn".to_string(),
        def_path: "test::symbolic_local_aggregate_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Symbolic(Formula::Var(
                            "x0".into(),
                            Sort::BitVec(64),
                        ))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Tuple,
                            vec![
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Bool(true)),
                            ],
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("copied symbolic aggregate should lower");
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        !bb0.body.iter().any(|node| matches!(&node.inst, Inst::Undef { ty: TrustIrTy::Tuple(_) })),
        "copied symbolic aggregate must not be seeded from tuple Undef"
    );
    assert!(bb0.body.iter().any(|node| matches!(
        &node.inst,
        Inst::DialectOp(op)
            if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_AGGREGATE_OP
    )));
    assert_valid_module(&module);
}

#[test]
fn test_binary_origin_symbolic_aggregate_lowers_without_undef_seed() {
    let func = VerifiableFunction {
        name: "binary_origin_symbolic_aggregate_fn".to_string(),
        def_path: "test::binary_origin_symbolic_aggregate_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("sum".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Symbolic(Formula::Var("x0".into(), Sort::BitVec(64))),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Tuple,
                            vec![
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Bool(true)),
                            ],
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("binary-origin symbolic aggregate should lower");
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        !bb0.body.iter().any(|node| matches!(&node.inst, Inst::Undef { ty: TrustIrTy::Tuple(_) })),
        "binary-origin symbolic aggregate must not be seeded from tuple Undef"
    );
    assert!(bb0.body.iter().any(|node| matches!(
        &node.inst,
        Inst::DialectOp(op)
            if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_AGGREGATE_OP
    )));
    assert_valid_module(&module);
}

#[test]
fn test_symbolic_checked_binary_lowers_without_undef_tuple() {
    let func = VerifiableFunction {
        name: "symbolic_checked_add_fn".to_string(),
        def_path: "test::symbolic_checked_add_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl {
                index: 0,
                ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
                name: None,
            }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Symbolic(Formula::Var("x0".into(), Sort::BitVec(64))),
                        Operand::Constant(ConstValue::Uint(1, 64)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("symbolic checked tuple should lower");
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        !bb0.body.iter().any(|node| matches!(&node.inst, Inst::Undef { ty: TrustIrTy::Tuple(_) })),
        "symbolic checked tuple must not be seeded from tuple Undef"
    );
    let aggregate_op = bb0
        .body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::DialectOp(op)
                if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_AGGREGATE_OP =>
            {
                Some(op.as_ref())
            }
            _ => None,
        })
        .expect("symbolic checked tuple aggregate dialect op");
    assert_eq!(aggregate_op.operands.len(), 2);
    assert!(matches!(
        aggregate_op.attr(SYMBOLIC_AGGREGATE_ATTR_KIND),
        Some(AttrValue::Str(s)) if s == "checked_binary_op_tuple"
    ));
    assert_valid_module(&module);
}

#[test]
fn test_symbolic_slice_raw_ptr_aggregate_lowers_without_undef_seed() {
    let data_ptr_ty = Ty::RawPtr { pointee: Box::new(Ty::u8()), mutable: false };
    let slice_ptr_ty =
        Ty::RawPtr { pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }), mutable: false };
    let func = VerifiableFunction {
        name: "symbolic_slice_raw_ptr_aggregate_fn".to_string(),
        def_path: "test::symbolic_slice_raw_ptr_aggregate_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: data_ptr_ty, name: Some("data".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("len".into()) },
                LocalDecl { index: 3, ty: slice_ptr_ty, name: Some("out".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Symbolic(Formula::Var(
                            "len0".into(),
                            Sort::BitVec(64),
                        ))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::RawPtr {
                                pointee_ty: Ty::Slice { elem: Box::new(Ty::u8()) },
                                mutable: false,
                            },
                            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("symbolic slice fat pointer should lower");
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        !bb0.body.iter().any(|node| matches!(
            &node.inst,
            Inst::Undef { ty: TrustIrTy::FatPtr(trust_ir::FatPtrKind::Slice(_)) }
        )),
        "symbolic slice fat pointer must not be seeded from fat-pointer Undef"
    );
    let aggregate_op = bb0
        .body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::DialectOp(op)
                if op.dialect == SYMBOLIC_FORMULA_DIALECT && op.op == SYMBOLIC_AGGREGATE_OP =>
            {
                Some(op.as_ref())
            }
            _ => None,
        })
        .expect("symbolic slice fat pointer aggregate dialect op");
    assert_eq!(aggregate_op.operands.len(), 2);
    // Trust (B2-1b): the symbolic lane keeps the DialectOp channel but at the
    // FIRST-CLASS fat type — FatPtr(Slice(elem TyId)) with the element interned
    // into the module `types` table (the anonymous Tuple([Ptr, I64]) is retired).
    let u8_tid = module
        .types
        .iter()
        .position(|t| *t == TrustIrTy::U8)
        .expect("u8 slice element should be interned in the module types table");
    assert_eq!(
        aggregate_op.result_tys,
        vec![TrustIrTy::FatPtr(trust_ir::FatPtrKind::Slice(trust_ir::value::TyId::new(
            u8_tid as u32
        )))]
    );
    assert!(matches!(
        aggregate_op.attr(SYMBOLIC_AGGREGATE_ATTR_KIND),
        Some(AttrValue::Str(s)) if s == "slice_fat_pointer"
    ));
    assert_valid_module(&module);
}

#[test]
fn test_lower_goto_terminator() {
    let func = VerifiableFunction {
        name: "goto_fn".to_string(),
        def_path: "test::goto_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    assert_eq!(module.functions[0].blocks.len(), 2);

    let bb0 = &module.functions[0].blocks[0];
    let has_br = bb0.body.iter().any(|node| {
        matches!(
            &node.inst,
            Inst::Br { target, .. } if target.index() == 1
        )
    });
    assert!(has_br, "bb0 should branch to bb1");
}

#[test]
fn test_lower_goto_to_entry_passes_entry_args() {
    let func = VerifiableFunction {
        name: "loop_to_entry".to_string(),
        def_path: "test::loop_to_entry".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(0)),
                },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    assert_valid_module(&module);
    let bb1 = &module.functions[0].blocks[1];
    assert!(
        bb1.body.iter().any(|node| matches!(
            &node.inst,
            Inst::Br { target, args } if target.index() == 0 && args.as_slice() == [ValueId::new(0)]
        )),
        "backedge to entry block should pass MIR argument locals as block args"
    );
}

#[test]
fn test_lower_condbr_to_entry_passes_entry_args() {
    let func = VerifiableFunction {
        name: "cond_to_entry".to_string(),
        def_path: "test::cond_to_entry".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("cond".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(0))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    assert_valid_module(&module);
    let bb1 = &module.functions[0].blocks[1];
    assert!(
        bb1.body.iter().any(|node| matches!(
            &node.inst,
            Inst::CondBr { then_target, then_args, else_target, else_args, .. }
                if then_target.index() == 0
                    && then_args.as_slice() == [ValueId::new(0)]
                    && else_target.index() == 2
                    && else_args.is_empty()
        )),
        "CondBr edge into entry block should pass entry block args"
    );
}

#[test]
fn test_lower_switch_int_binary() {
    let func = VerifiableFunction {
        name: "branch_fn".to_string(),
        def_path: "test::branch_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("cond".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                TrustBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];

    // Should have ICmp + CondBr for a single-target SwitchInt.
    let has_condbr = bb0.body.iter().any(|node| matches!(&node.inst, Inst::CondBr { .. }));
    assert!(has_condbr, "single-target SwitchInt should emit CondBr");
    assert!(
        bb0.body.iter().any(|node| matches!(
            &node.inst,
            Inst::Const { ty: TrustIrTy::Bool, value: TrustIrConstant::Bool(true) }
        )),
        "bool SwitchInt should materialize a bool case constant"
    );
    assert!(
        bb0.body.iter().any(|node| matches!(&node.inst, Inst::ICmp { ty: TrustIrTy::Bool, .. })),
        "bool SwitchInt should compare with the discriminator type"
    );
}

#[test]
fn test_lower_switch_int_bool_out_of_range_fails_closed() {
    let func = VerifiableFunction {
        name: "bad_bool_switch".to_string(),
        def_path: "test::bad_bool_switch".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("cond".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(2, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                TrustBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("invalid bool case should fail closed");
    assert!(matches!(err, BridgeError::UnsupportedOp(msg) if msg.contains("does not fit bool")));
}

#[test]
fn test_lower_switch_int_u8_preserves_unsigned_width() {
    let func = VerifiableFunction {
        name: "u8_switch".to_string(),
        def_path: "test::u8_switch".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u8(), name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(255, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                TrustBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|node| matches!(
            &node.inst,
            Inst::Const { ty: TrustIrTy::U8, value: TrustIrConstant::Int(255) }
        )),
        "u8 SwitchInt should preserve the unsigned discriminator width"
    );
    assert!(
        bb0.body.iter().any(|node| matches!(&node.inst, Inst::ICmp { ty: TrustIrTy::U8, .. })),
        "u8 SwitchInt should compare as u8"
    );
}

#[test]
fn test_lower_switch_int_multiway() {
    let func = VerifiableFunction {
        name: "switch_fn".to_string(),
        def_path: "test::switch_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1)), (7, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                TrustBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                TrustBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_switch = bb0.body.iter().any(|node| matches!(&node.inst, Inst::Switch { .. }));
    assert!(has_switch, "multi-target SwitchInt should emit Switch");
}

#[test]
fn test_lower_switch_to_entry_passes_entry_args() {
    let func = VerifiableFunction {
        name: "switch_to_entry".to_string(),
        def_path: "test::switch_to_entry".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(0)), (1, BlockId(2))],
                        otherwise: BlockId(0),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    assert_valid_module(&module);
    let bb1 = &module.functions[0].blocks[1];
    assert!(
        bb1.body.iter().any(|node| matches!(
            &node.inst,
            Inst::Switch { default, default_args, cases, .. }
                if default.index() == 0
                    && default_args.as_slice() == [ValueId::new(0)]
                    && cases.iter().any(|case| {
                        case.target.index() == 0 && case.args.as_slice() == [ValueId::new(0)]
                    })
                    && cases.iter().any(|case| case.target.index() == 2 && case.args.is_empty())
        )),
        "Switch edges into entry block should pass entry block args"
    );
}

#[test]
fn test_lower_unreachable() {
    let func = VerifiableFunction {
        name: "unr".to_string(),
        def_path: "test::unr".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Never, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Unreachable,
            }],
            arg_count: 0,
            return_ty: Ty::Never,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_unreachable = bb0.body.iter().any(|node| matches!(&node.inst, Inst::Unreachable));
    assert!(has_unreachable, "should emit Unreachable");
}

#[test]
fn test_unreachable_mir_blocks_are_pruned_before_trust_ir_validation() {
    let func = VerifiableFunction {
        name: "dead_block".to_string(),
        def_path: "test::dead_block".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                TrustBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("dead MIR blocks should be pruned");
    assert_valid_module(&module);
    assert!(
        module.functions[0].blocks.iter().all(|block| block.id.index() != 1),
        "unreachable MIR blocks should not become TrustIr CFG blocks"
    );
}

#[test]
fn test_lower_unary_not() {
    let func = VerifiableFunction {
        name: "not_fn".to_string(),
        def_path: "test::not_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::UnaryOp(UnOp::Not, Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_not = bb0
        .body
        .iter()
        .any(|node| matches!(&node.inst, Inst::UnOp { op: trust_ir::inst::UnOp::Not, .. }));
    assert!(has_not, "should have a Not instruction");
}

#[test]
fn test_lower_signed_comparison_uses_operand_type() {
    let func = VerifiableFunction {
        name: "signed_lt".to_string(),
        def_path: "test::signed_lt".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|node| matches!(
            &node.inst,
            Inst::ICmp { op: ICmpOp::Slt, ty: TrustIrTy::I32, .. }
        )),
        "signed i32 comparison should lower to ICmp::Slt over i32 operands"
    );
}

#[test]
fn test_lower_unsigned_comparison_uses_operand_type() {
    let func = VerifiableFunction {
        name: "unsigned_lt".to_string(),
        def_path: "test::unsigned_lt".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|node| matches!(
            &node.inst,
            Inst::ICmp { op: ICmpOp::Ult, ty: TrustIrTy::U32, .. }
        )),
        "unsigned u32 comparison should lower to ICmp::Ult over u32 operands"
    );
}

#[test]
fn test_lower_cmp_i32_to_i8_uses_icmp_selects() {
    let func = VerifiableFunction {
        name: "cmp_i32".to_string(),
        def_path: "test::cmp_i32".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i8(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Cmp,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i8(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("three-way signed cmp should lower");
    assert_valid_module(&module);
    let body = &module.functions[0].blocks[0].body;
    assert!(
        body.iter().any(|node| matches!(
            &node.inst,
            Inst::ICmp { op: ICmpOp::Slt, ty: TrustIrTy::I32, .. }
        )),
        "signed Cmp should test lhs < rhs with signed comparison"
    );
    assert!(
        body.iter().any(|node| matches!(
            &node.inst,
            Inst::ICmp { op: ICmpOp::Sgt, ty: TrustIrTy::I32, .. }
        )),
        "signed Cmp should test lhs > rhs with signed comparison"
    );
    assert!(
        body.iter()
            .filter(|node| matches!(&node.inst, Inst::Select { ty: TrustIrTy::I8, .. }))
            .count()
            >= 2,
        "Cmp should use nested selects to choose -1, 0, or 1"
    );
    for expected in [-1, 0, 1] {
        assert!(
            body.iter().any(|node| matches!(
                &node.inst,
                Inst::Const { ty: TrustIrTy::I8, value: TrustIrConstant::Int(value) }
                    if *value == expected
            )),
            "Cmp should materialize {expected}"
        );
    }
}

#[test]
fn test_lower_cmp_u32_uses_unsigned_icmp() {
    let func = VerifiableFunction {
        name: "cmp_u32".to_string(),
        def_path: "test::cmp_u32".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i8(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Cmp,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i8(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("three-way unsigned cmp should lower");
    assert_valid_module(&module);
    let body = &module.functions[0].blocks[0].body;
    assert!(
        body.iter().any(|node| matches!(
            &node.inst,
            Inst::ICmp { op: ICmpOp::Ult, ty: TrustIrTy::U32, .. }
        )),
        "unsigned Cmp should use unsigned less-than"
    );
    assert!(
        body.iter().any(|node| matches!(
            &node.inst,
            Inst::ICmp { op: ICmpOp::Ugt, ty: TrustIrTy::U32, .. }
        )),
        "unsigned Cmp should use unsigned greater-than"
    );
}

#[test]
fn test_lower_cmp_float_rejected() {
    let func = VerifiableFunction {
        name: "cmp_f64".to_string(),
        def_path: "test::cmp_f64".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i8(), name: None },
                LocalDecl { index: 1, ty: Ty::f64_ty(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::f64_ty(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Cmp,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i8(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("float Cmp must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(ref msg) if msg.contains("float Cmp")),
        "expected float Cmp diagnostic, got {err:?}"
    );
}

#[test]
fn test_lower_checked_add() {
    // fn checked(a: u64, b: u64) -> u64 with CheckedBinaryOp(Add)
    let func = VerifiableFunction {
        name: "checked_add".to_string(),
        def_path: "test::checked_add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
            ],
            blocks: vec![TrustBlock {
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
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_overflow = bb0
        .body
        .iter()
        .any(|node| matches!(&node.inst, Inst::Overflow { op: OverflowOp::AddOverflow, .. }));
    assert!(has_overflow, "CheckedBinaryOp(Add) should emit Overflow(AddOverflow)");

    // The Overflow instruction should have a NoOverflow proof annotation.
    let overflow_node = bb0
        .body
        .iter()
        .find(|node| matches!(&node.inst, Inst::Overflow { .. }))
        .expect("overflow node");
    assert!(
        overflow_node
            .proofs
            .iter()
            .any(|p| matches!(p, trust_ir::proof::ProofAnnotation::NoOverflow)),
        "Overflow instruction should carry NoOverflow proof annotation"
    );
    assert!(
        bb0.body.iter().any(|node| matches!(
            &node.inst,
            Inst::Undef { ty: TrustIrTy::Tuple(fields) } if fields.as_slice() == [TrustIrTy::U64, TrustIrTy::Bool]
        )),
        "CheckedBinaryOp should materialize the MIR (value, overflow) tuple"
    );
    assert!(
        bb0.body.iter().filter(|node| matches!(&node.inst, Inst::InsertField { .. })).count() >= 2,
        "CheckedBinaryOp should insert both tuple fields"
    );
}

#[test]
fn test_lower_checked_add_tuple_field_zero_projection() {
    let func = VerifiableFunction {
        name: "checked_add_value".to_string(),
        def_path: "test::checked_add_value".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|node| matches!(
            &node.inst,
            Inst::ExtractField { ty: TrustIrTy::U64, field: 0, .. }
        )),
        "reading checked_result.0 should extract the arithmetic value from the tuple"
    );
}

#[test]
fn test_lower_checked_add_tuple_field_one_assert() {
    use trust_types::AssertMessage;

    let func = VerifiableFunction {
        name: "checked_add_overflow_assert".to_string(),
        def_path: "test::checked_add_overflow_assert".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                TrustBlock {
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
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|node| matches!(
            &node.inst,
            Inst::ExtractField { ty: TrustIrTy::Bool, field: 1, .. }
        )),
        "reading checked_result.1 should extract the overflow flag from the tuple"
    );
}

#[test]
fn test_lower_guarded_checked_add_with_widthless_int_constants() {
    use trust_types::AssertMessage;

    // Mirrors tests/trust-falsification/proved/terminal_font_weight_bold.rs:
    //   if normalized >= 100 && normalized <= 900 { normalized + 200 } else { 700 }
    // The i32 literals arrive as width-less ConstValue::Int. CheckedBinaryOp
    // must let a fitting literal adopt the destination value type (i32) rather
    // than defaulting to i64 and failing the WHOLE function lowering — which
    // silently strands the native trust-mc route behind the ay bridge.
    let func = VerifiableFunction {
        name: "terminal_font_weight_bold".to_string(),
        def_path: "test::terminal_font_weight_bold".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("normalized".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: None },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
                LocalDecl { index: 4, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Ge,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(100)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(900)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(200)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(4, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(4, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                TrustBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(700))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                TrustBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect(
        "guarded checked add with width-less int literals must lower (native trust-mc route)",
    );
    assert_valid_module(&module);
    let f = &module.functions[0];

    // The checked add must be a real i32 Overflow instruction.
    let overflow_node = f
        .blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .find(|node| matches!(&node.inst, Inst::Overflow { .. }))
        .expect("CheckedBinaryOp should emit an Overflow instruction");
    assert!(
        matches!(
            &overflow_node.inst,
            Inst::Overflow { op: OverflowOp::AddOverflow, ty: TrustIrTy::I32, .. }
        ),
        "Overflow must carry the i32 operand type, got {:?}",
        overflow_node.inst
    );

    // The literal 200 must be emitted at the adopted i32 width, not i64.
    assert!(
        f.blocks.iter().flat_map(|b| b.body.iter()).any(|node| matches!(
            &node.inst,
            Inst::Const { ty: TrustIrTy::I32, value: TrustIrConstant::Int(200) }
        )),
        "the checked-add literal must adopt the destination i32 width"
    );

    // The Assert{Overflow} terminator must register the faithful panic-class
    // obligation. Item T1 (LANDED): an overflow assert now produces a per-site
    // `ArithmeticSafety` obligation (the function-level aggregate stays
    // `PanicFreedom`).
    assert!(
        module
            .proof_obligations
            .iter()
            .any(|o| matches!(o.kind, trust_ir::ObligationKind::ArithmeticSafety)),
        "the overflow assert must produce an ArithmeticSafety proof obligation"
    );
    // An `Assert`-bearing fn surfaces NO function-level PanicFreedom aggregate
    // (the lowering emits it only for diverging-panic `Call` terminators, not
    // for `Assert` sites — the w01/w13/w16/w19 completeness fix).
    assert!(
        !module
            .proof_obligations
            .iter()
            .any(|o| matches!(o.kind, trust_ir::ObligationKind::PanicFreedom)),
        "an Assert-bearing fn must surface no aggregate PanicFreedom obligation"
    );
}

#[test]
fn test_lower_checked_add_rejects_non_fitting_int_constant() {
    // A width-less literal that does NOT fit the destination type must keep
    // failing closed — adoption never truncates (i8 destination, literal 300).
    let func = VerifiableFunction {
        name: "checked_add_overflowing_literal".to_string(),
        def_path: "test::checked_add_overflowing_literal".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::i8(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::Tuple(vec![Ty::i8(), Ty::Bool]), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(300)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func)
        .expect_err("a literal that cannot fit the destination type must fail closed");
    assert!(
        matches!(&err, BridgeError::UnsupportedType(msg) if msg.contains("must match destination value type")),
        "expected the operand/destination mismatch error, got {err:?}"
    );
}

#[test]
fn test_lower_midpoint_function() {
    // fn get_midpoint(a: u64, b: u64) -> u64 { (a + b) / 2 }
    let func = VerifiableFunction {
        name: "get_midpoint".to_string(),
        def_path: "midpoint::get_midpoint".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::u64(), name: None },
                LocalDecl { index: 4, ty: Ty::u64(), name: None },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(3)),
                                Operand::Constant(ConstValue::Uint(2, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("midpoint should lower");
    assert_eq!(module.functions[0].blocks.len(), 2);

    let ft = &module.func_types[module.functions[0].ty.index() as usize];
    assert_eq!(ft.params, vec![TrustIrTy::U64, TrustIrTy::U64]);
    assert_eq!(ft.returns, vec![TrustIrTy::U64]);

    // bb0: Add + Br
    let bb0 = &module.functions[0].blocks[0];
    assert!(bb0.body.iter().any(|n| matches!(&n.inst, Inst::BinOp { op: TrustIrBinOp::Add, .. })));
    assert!(bb0.body.iter().any(|n| matches!(
        &n.inst,
        Inst::Br { target, .. } if target.index() == 1
    )));

    // bb1: Const(2) + UDiv + Copy + Return
    let bb1 = &module.functions[0].blocks[1];
    assert!(bb1.body.iter().any(|n| matches!(&n.inst, Inst::Const { .. })));
    assert!(bb1.body.iter().any(|n| matches!(&n.inst, Inst::BinOp { op: TrustIrBinOp::UDiv, .. })));
    assert!(bb1.body.iter().any(|n| matches!(&n.inst, Inst::Return { .. })));
}

#[test]
fn test_lower_nop_statement() {
    let func = VerifiableFunction {
        name: "nop_fn".to_string(),
        def_path: "test::nop_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Nop,
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("nop should not block lowering");
    // Should have instructions (at least Copy + Return), no errors.
    assert!(!module.functions[0].blocks[0].body.is_empty());
}

#[test]
fn test_metadata_statements_do_not_block_lowering() {
    let func = VerifiableFunction {
        name: "metadata_stmt_fn".to_string(),
        def_path: "test::metadata_stmt_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::StorageLive(1),
                    Statement::PlaceMention(Place::local(1)),
                    Statement::Retag { place: Place::local(1) },
                    Statement::Intrinsic {
                        name: "assume".into(),
                        args: vec![Operand::Constant(ConstValue::Bool(true))],
                    },
                    Statement::Coverage,
                    Statement::ConstEvalCounter,
                    Statement::StorageDead(1),
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("metadata statements should not block lowering");
    assert_valid_module(&module);
}

#[test]
fn test_unsupported_statement_reports_detail() {
    let func = VerifiableFunction {
        name: "unsupported_stmt_fn".to_string(),
        def_path: "test::unsupported_stmt_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Unsupported {
                    kind: "Foo".into(),
                    detail: "bar detail".into(),
                    operands: vec![],
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("unsupported statement must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(ref msg) if msg.contains("Foo") && msg.contains("bar detail")),
        "expected unsupported statement detail, got {err:?}"
    );
}

#[test]
fn test_deinit_and_unknown_intrinsic_fail_closed() {
    let deinit_func = VerifiableFunction {
        name: "deinit_stmt_fn".to_string(),
        def_path: "test::deinit_stmt_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Deinit { place: Place::local(1) }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let err = lower_to_trust_ir(&deinit_func).expect_err("Deinit must fail closed");
    assert!(matches!(err, BridgeError::UnsupportedOp(ref msg) if msg.contains("Deinit")));

    let intrinsic_func = VerifiableFunction {
        name: "intrinsic_stmt_fn".to_string(),
        def_path: "test::intrinsic_stmt_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Intrinsic {
                    name: "copy_nonoverlapping".into(),
                    args: vec![],
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let err = lower_to_trust_ir(&intrinsic_func).expect_err("unknown intrinsic must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(ref msg) if msg.contains("copy_nonoverlapping"))
    );
}

#[test]
fn test_unsupported_rvalue_and_operand_report_detail() {
    let unsupported_rvalue_func = VerifiableFunction {
        name: "unsupported_rvalue_fn".to_string(),
        def_path: "test::unsupported_rvalue_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Unsupported {
                        kind: "RKind".into(),
                        detail: "rvalue detail".into(),
                        operands: vec![],
                    },
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let err =
        lower_to_trust_ir(&unsupported_rvalue_func).expect_err("unsupported rvalue must fail");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(ref msg) if msg.contains("RKind") && msg.contains("rvalue detail")),
        "expected unsupported rvalue detail, got {err:?}"
    );

    let unsupported_operand_func = VerifiableFunction {
        name: "unsupported_operand_fn".to_string(),
        def_path: "test::unsupported_operand_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Unsupported {
                        kind: "OKind".into(),
                        detail: "operand detail".into(),
                    }),
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
    };
    let err =
        lower_to_trust_ir(&unsupported_operand_func).expect_err("unsupported operand must fail");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(ref msg) if msg.contains("OKind") && msg.contains("operand detail")),
        "expected unsupported operand detail, got {err:?}"
    );
}

#[test]
fn test_lower_contracts_to_obligations() {
    let func = VerifiableFunction {
        name: "contracted".to_string(),
        def_path: "test::contracted".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
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
        contracts: vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result > 0".to_string(),
            },
        ],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    assert!(
        module.proof_obligations.len() >= 2,
        "should have at least 2 proof obligations (requires + ensures)"
    );

    let has_pre = module.proof_obligations.iter().any(|po| {
        matches!(po.kind, trust_ir::proof::ObligationKind::Precondition)
            && po.description == "x > 0"
    });
    assert!(has_pre, "should have a precondition obligation");

    let has_post = module.proof_obligations.iter().any(|po| {
        matches!(po.kind, trust_ir::proof::ObligationKind::Postcondition)
            && po.description == "result > 0"
    });
    assert!(has_post, "should have a postcondition obligation");
}

#[test]
fn test_contract_obligations_carry_stable_source_metadata() {
    let contract_span = SourceSpan {
        file: "src/lib.rs".to_string(),
        line_start: 12,
        col_start: 4,
        line_end: 12,
        col_end: 22,
    };
    let contract =
        Contract { kind: ContractKind::Requires, span: contract_span, body: "x > 0".to_string() };
    let func = VerifiableFunction {
        name: "contracted".to_string(),
        def_path: "crate::contracted".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![contract.clone()],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    let obligation = module
        .proof_obligations
        .iter()
        .find(|obligation| matches!(obligation.kind, trust_ir::proof::ObligationKind::Precondition))
        .expect("precondition obligation");
    let formula = obligation.formula.as_ref().expect("source metadata formula");
    // The `x > 0` predicate parses, so the obligation now carries the
    // predicate-bearing `trust-types.Formula@1` payload (D2.1 enrichment). The
    // stable source metadata is PRESERVED under the nested `source` field — the
    // span is never lost.
    assert_eq!(formula.schema, TRUST_CONTRACT_PREDICATE_SCHEMA);
    let payload: serde_json::Value =
        serde_json::from_str(&formula.payload).expect("predicate-bearing json");
    let source = payload.get("source").expect("source metadata preserved under `source`");
    assert_eq!(source["source_id"], contract.stable_source_id(&func.def_path, 0));
    assert_eq!(source["assertion_id"], contract.stable_assertion_id(&func.def_path, 0));
    assert_eq!(
        source["native_assertion_id"],
        contract.stable_native_assertion_index(&func.def_path, 0)
    );
    assert_eq!(source["span"]["file"], "src/lib.rs");
    assert_eq!(source["span"]["line_start"], 12);
    let embedded_source = obligation
        .source
        .as_ref()
        .expect("proof authority must carry typed source identity outside the formula payload");
    assert_eq!(embedded_source.source_id, contract.stable_source_id(&func.def_path, 0));
    assert_eq!(embedded_source.assertion_id, contract.stable_assertion_id(&func.def_path, 0));
    assert_eq!(obligation.function, Some(trust_ir::FuncId::new(0)));
    let embedded_range = embedded_source.range.expect("typed source identity must preserve range");
    assert_eq!(module.file_name(embedded_range.file), Some("src/lib.rs"));
    assert_eq!(embedded_range.start_line, 12);
    assert_eq!(embedded_range.start_col, 4);
    assert_eq!(embedded_range.end_line, 12);
    assert_eq!(embedded_range.end_col, 22);
    assert!(
        embedded_source.public.is_none(),
        "generic lowering must not fabricate a public verifier obligation identity"
    );
    // The machine-readable predicate is now carried: JSON Formula AST + SMT-LIB +
    // sort, equal to `parse_spec_expr("x > 0")`.
    let emitted: trust_types::Formula =
        serde_json::from_value(payload.get("formula").expect("formula AST present").clone())
            .expect("deserializes to a trust_types::Formula");
    assert_eq!(emitted, trust_types::parse_spec_expr("x > 0").expect("parses"));
    assert_eq!(formula.smtlib.as_deref(), Some(emitted.to_smtlib().as_str()));
    assert_eq!(formula.sort.as_deref(), Some("Bool"));
}

#[test]
fn test_lower_drop_terminator() {
    let func = VerifiableFunction {
        name: "drop_fn".to_string(),
        def_path: "test::drop_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(0),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("drop should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_br =
        bb0.body.iter().any(|n| matches!(&n.inst, Inst::Br { target, .. } if target.index() == 1));
    assert!(has_br, "Drop should emit Br to target block");
}

#[test]
fn test_nontrivial_drop_fails_soft_with_honest_panic_obligation() {
    let drop_ty = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "NeedsDrop".to_string(),
        fields: vec![("x".to_string(), Ty::i64())],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "drop_nontrivial_fn".to_string(),
        def_path: "test::drop_nontrivial_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: drop_ty, name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(1),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // FAIL-SOFT (was fail-closed-by-Err): a Drop with unproven-panic-free glue
    // no longer fails the whole lowering — it lowers to the audited may-panic
    // encoding (Assert(false)+NoPanic marker + ONE marked PanicFreedom
    // obligation + the Br to the target). The fail-CLOSED property this test
    // protects is unchanged: the drop is never a silent no-op branch — its
    // possible panic stays reachable and carries an honest obligation.
    let module = lower_to_trust_ir(&func).expect("nontrivial Drop must lower fail-soft, not Err");
    assert_valid_module(&module);
    let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    assert_eq!(
        no_panic_false_assert_count(&module),
        1,
        "expected exactly one Assert(false)+NoPanic may-panic marker for the drop glue"
    );
    assert!(
        insts.iter().any(|n| matches!(n.inst, Inst::Br { .. })),
        "the drop must still branch to its target"
    );
    assert_eq!(
        module
            .proof_obligations
            .iter()
            .filter(|o| {
                o.kind == trust_ir::ObligationKind::PanicFreedom
                    && o.description
                        .starts_with(trust_types::assumption::DROP_GLUE_ASSUMPTION_PREFIX)
            })
            .count(),
        1,
        "expected exactly one marked drop-glue PanicFreedom obligation"
    );
    assert_eq!(
        module
            .proof_obligations
            .iter()
            .filter(|obligation| obligation.kind == trust_ir::ObligationKind::PanicFreedom)
            .count(),
        2,
        "an unknown Drop must emit exactly one site row plus one counted function carrier"
    );
    assert_eq!(
        module
            .proof_obligations
            .iter()
            .filter(|obligation| obligation.kind == trust_ir::ObligationKind::PanicFreedom)
            .filter_map(|obligation| obligation.source.as_ref())
            .filter(|source| source.source_id.starts_with("mir-assertions:"))
            .count(),
        1,
        "the fail-soft site must have exactly one counted whole-function carrier"
    );
}

// ---------------------------------------------------------------------------
// Drop-glue classifier: structural panic-free-drop proofs (vs. the honest
// fail-soft assumption row above). See `is_panic_free_drop_ext` in lower.rs.
// ---------------------------------------------------------------------------

/// Build a one-block `VerifiableFunction` that drops a single local of `drop_ty`
/// and returns. Shared by the drop-glue classifier tests below.
fn drop_glue_test_fn(drop_ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "drop_glue_fn".to_string(),
        def_path: "test::drop_glue_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: drop_ty, name: Some("v".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(1),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Count of `assumption:drop-glue` `PanicFreedom` obligations recorded on `module`.
fn drop_glue_assumption_count(module: &trust_ir::Module) -> usize {
    module
        .proof_obligations
        .iter()
        .filter(|o| {
            o.kind == trust_ir::ObligationKind::PanicFreedom
                && o.description.starts_with(trust_types::assumption::DROP_GLUE_ASSUMPTION_PREFIX)
        })
        .count()
}

/// Count generic-parameter drop boundaries reclassified as expected-absent. They retain the
/// reachable `Assert(false)+NoPanic` marker and remain unproved; only explicit advisory policy
/// may later record them as assumptions.
fn expected_absent_drop_count(module: &trust_ir::Module) -> usize {
    module
        .proof_obligations
        .iter()
        .filter(|obligation| {
            obligation.kind == trust_ir::ObligationKind::PanicFreedom
                && obligation
                    .description
                    .starts_with(trust_types::assumption::EXPECTED_ABSENT_CALLEE_ASSUMPTION_PREFIX)
                && obligation.description.contains("drop glue for generic parameter")
        })
        .count()
}

/// `true` if any instruction in `module`'s sole function is the drop-glue
/// `Assert(false)+NoPanic` may-panic marker.
///
/// Build-7 sharpening: the check resolves the asserted condition to its defining
/// `Const` and requires it to be the constant `false`. A PROVEN drop now records
/// its discharge as `Assert(true)+NoPanic` (a trivially-valid check paired with a
/// named, dischargeable obligation row — see the Drop arm in lower.rs), which is
/// NOT a may-panic marker; only the reachable-panic `Assert(false)` form is.
fn drop_glue_marker_count(module: &trust_ir::Module) -> usize {
    no_panic_false_assert_count(module)
}

fn has_drop_glue_marker(module: &trust_ir::Module) -> bool {
    drop_glue_marker_count(module) != 0
}

/// Count of the Build-7 DISCHARGED drop-glue rows on `module`: named `PanicFreedom`
/// obligations recording a classifier-proven panic-free drop. These carry the
/// human-readable justification and NO assumption prefix (they flow through normal
/// verdict discharge — never an unproved assumption-panic row).
fn drop_glue_discharged_count(module: &trust_ir::Module) -> usize {
    module
        .proof_obligations
        .iter()
        .filter(|o| {
            o.kind == trust_ir::ObligationKind::PanicFreedom
                && o.description.contains("drop glue for")
                && o.description.contains("— discharged: proven panic-free")
                && !o.description.starts_with(trust_types::assumption::DROP_GLUE_ASSUMPTION_PREFIX)
        })
        .count()
}

#[test]
fn test_drop_glue_proves_for_result_of_plain_struct_and_fieldless_enum() {
    // `Rat` — a plain-data struct with NO user `Drop` impl (as the compiler's
    // `collect_structural_drop_adts` would certify via `!has_dtor`).
    let rat_ty = Ty::adt(
        "myapp::Rat",
        vec![("numerator".to_string(), Ty::i64()), ("denominator".to_string(), Ty::i64())],
    );
    // `CheckError` — a FIELDLESS user enum, also compiler-certified no-`Drop`.
    let check_error_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "myapp::CheckError".to_string(),
        fields: vec![("__tag".to_string(), Ty::i64())],
        variants: vec![
            trust_types::VariantDef {
                name: "BadNumerator".to_string(),
                discriminant: 0,
                fields: vec![],
            },
            trust_types::VariantDef {
                name: "BadDenominator".to_string(),
                discriminant: 1,
                fields: vec![],
            },
        ],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    // `core::result::Result<Rat, CheckError>` — the vetted std payload enum,
    // flattened exactly as the real extractor's `lower_enum_adt` shapes it
    // (`__tag` + one `__v{idx}_{field}` entry per variant field).
    let result_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "core::result::Result".to_string(),
        fields: vec![
            ("__tag".to_string(), Ty::i64()),
            ("__v0_0".to_string(), rat_ty.clone()),
            ("__v1_0".to_string(), check_error_ty.clone()),
        ],
        variants: vec![
            trust_types::VariantDef {
                name: "Ok".to_string(),
                discriminant: 0,
                fields: vec![("0".to_string(), rat_ty)],
            },
            trust_types::VariantDef {
                name: "Err".to_string(),
                discriminant: 1,
                fields: vec![("0".to_string(), check_error_ty)],
            },
        ],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };

    let structural_drop: std::collections::HashSet<String> =
        ["myapp::Rat".to_string(), "myapp::CheckError".to_string()].into_iter().collect();
    let module = lower_to_trust_ir_functions_with_context(
        "test_mod",
        &[drop_glue_test_fn(result_ty)],
        &std::collections::HashSet::new(),
        &structural_drop,
    )
    .expect("Result<Rat, CheckError> drop must lower");
    assert_valid_module(&module);

    assert!(
        !has_drop_glue_marker(&module),
        "a provably panic-free drop must NOT emit the Assert(false)+NoPanic marker"
    );
    let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    assert!(
        insts.iter().any(|n| matches!(n.inst, Inst::Br { .. })),
        "the drop must still branch to its target"
    );
    assert_eq!(
        drop_glue_assumption_count(&module),
        0,
        "a provably panic-free drop must NOT record a drop-glue assumption row"
    );
    // Build-7 row-classification fix: the proof is RECORDED as one named,
    // dischargeable row (constant-false panic condition — flows through normal
    // verdict discharge), never left as an invisible bare `Br`.
    assert_eq!(drop_glue_discharged_count(&module), 1);
}

#[test]
fn test_drop_glue_kept_for_adt_with_user_drop_impl() {
    // `PanickyGuard` has a real user `Drop` impl. The compiler's
    // `collect_structural_drop_adts` would NOT include it (`has_dtor` is true), so
    // its name is deliberately ABSENT from `structural_drop` below even though the
    // set is non-empty (proving MEMBERSHIP — not merely "some set was passed" — is
    // what unlocks the proof).
    let guard_ty = Ty::adt("myapp::PanickyGuard", vec![("x".to_string(), Ty::i64())]);
    let structural_drop: std::collections::HashSet<String> =
        ["myapp::SomeOtherCertifiedType".to_string()].into_iter().collect();

    let module = lower_to_trust_ir_functions_with_context(
        "test_mod",
        &[drop_glue_test_fn(guard_ty)],
        &std::collections::HashSet::new(),
        &structural_drop,
    )
    .expect("uncertified Drop must lower fail-soft, not Err");
    assert_valid_module(&module);

    assert!(
        has_drop_glue_marker(&module),
        "a type with a possible user Drop impl must keep the Assert(false)+NoPanic marker"
    );
    assert_eq!(
        drop_glue_assumption_count(&module),
        1,
        "a type with a possible user Drop impl must keep exactly one drop-glue assumption row"
    );
}

#[test]
fn test_drop_glue_vec_of_plain_element_fails_closed_when_element_is_erased() {
    // A flattened `Vec` field tree does not authenticate its generic element or
    // allocator. A primitive-looking payload therefore cannot grant Drop authority.
    let vec_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "alloc::vec::Vec".to_string(),
        fields: vec![("elem".to_string(), Ty::i64())],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let module = lower_to_trust_ir_functions("test_mod", &[drop_glue_test_fn(vec_ty)])
        .expect("Vec<i64> drop must lower");
    assert_valid_module(&module);

    assert!(
        has_drop_glue_marker(&module),
        "Vec<i64>'s erased generic lanes must keep the drop obligation"
    );
    assert_eq!(drop_glue_assumption_count(&module), 1);
    assert_eq!(drop_glue_discharged_count(&module), 0);
}

#[test]
fn test_drop_glue_kept_for_vec_of_user_drop_element() {
    // `Vec<PanickyGuard>` — the container itself is trusted, but its ELEMENT
    // carries a possible user `Drop`, so the whole must decline (never a false
    // proof from trusting the container alone).
    let guard_ty = Ty::adt("myapp::PanickyGuard", vec![("x".to_string(), Ty::i64())]);
    let vec_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "alloc::vec::Vec".to_string(),
        fields: vec![("elem".to_string(), guard_ty)],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let module = lower_to_trust_ir_functions("test_mod", &[drop_glue_test_fn(vec_ty)])
        .expect("Vec<PanickyGuard> drop must lower fail-soft, not Err");
    assert_valid_module(&module);

    assert!(
        has_drop_glue_marker(&module),
        "Vec<PanickyGuard> must keep the Assert(false)+NoPanic marker (element may panic)"
    );
    assert_eq!(drop_glue_assumption_count(&module), 1);
}

#[test]
fn test_drop_glue_classifier_terminates_on_deep_recursive_type() {
    // Build a `Wrap0(Wrap1(Wrap2(...i64...)))` chain deeper than the classifier's
    // recursion fuel (`DROP_CLASSIFIER_FUEL` = 256 in `is_panic_free_drop_ext`),
    // simulating what a self-referential type would look like if the extractor's
    // Lever A (by-name `Ty::Datatype` back-reference) were somehow bypassed. The
    // classifier must TERMINATE — never stack-overflow or hang — and, since the
    // fuel runs out partway through, FAIL CLOSED rather than falsely prove.
    let mut inner = Ty::i64();
    let mut structural_drop = std::collections::HashSet::new();
    for depth in 0..300u32 {
        let name = format!("myapp::Wrap{depth}");
        structural_drop.insert(name.clone());
        inner = Ty::adt(name, vec![("0".to_string(), inner)]);
    }

    let module = lower_to_trust_ir_functions_with_context(
        "test_mod",
        &[drop_glue_test_fn(inner)],
        &std::collections::HashSet::new(),
        &structural_drop,
    )
    .expect("a deep (but finite) type chain must still lower — never hang");
    assert_valid_module(&module);

    assert_eq!(
        drop_glue_assumption_count(&module),
        1,
        "fuel-exhausted classification must fail closed to the drop-glue assumption row"
    );
}

#[test]
fn test_trait_object_drop_is_fatal_and_generic_param_drop_is_expected_absent() {
    // `Box<dyn MyTrait>` — a trait object's concrete drop glue is unknowable
    // (dynamic dispatch to whatever concrete type is behind the vtable).
    let boxed_dyn_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "alloc::boxed::Box".to_string(),
        fields: vec![("0".to_string(), Ty::Dynamic { trait_name: "myapp::MyTrait".to_string() })],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let module = lower_to_trust_ir_functions("test_mod", &[drop_glue_test_fn(boxed_dyn_ty)])
        .expect("Box<dyn Trait> drop must lower fail-soft, not Err");
    assert_valid_module(&module);
    assert!(has_drop_glue_marker(&module), "Box<dyn Trait> must keep the may-panic marker");
    assert_eq!(drop_glue_assumption_count(&module), 1);

    // An unresolved pre-monomorphization parameter is still opaque and therefore still
    // carries the reachable may-panic marker. Its boundary class is intentionally
    // EXPECTED-absent, however: the concrete Drop impl is selected and verified only at
    // monomorphization. This is an assumption, never a discharge or proof; strict policy
    // rejects it while explicit advisory policy may record it.
    let generic_ty = Ty::Unsupported {
        kind: "TyKind::Param".to_string(),
        detail: "generic type parameter T".to_string(),
    };
    let module2 = lower_to_trust_ir_functions("test_mod", &[drop_glue_test_fn(generic_ty)])
        .expect("generic-typed drop must lower fail-soft, not Err");
    assert_valid_module(&module2);
    assert!(has_drop_glue_marker(&module2), "an unresolved generic must keep the may-panic marker");
    assert_eq!(
        drop_glue_assumption_count(&module2),
        0,
        "a generic parameter is not a concrete user-Drop boundary"
    );
    assert_eq!(
        expected_absent_drop_count(&module2),
        1,
        "the generic parameter must remain visible as exactly one unproved expected-absent drop"
    );
}

// ---------------------------------------------------------------------------
// Build-5 drop-glue (Build-7 re-land): audited std-composed types (Ref/RefMut
// guards and num-bigint) prove panic-free; generic owning collections whose
// K/V types are erased from the compatibility IR and a user `Drop` anywhere in
// the visible field tree fail closed. Build-7 row-classification fix: a
// PROVEN drop records a named DISCHARGED row (never an unproved assumption
// row); a kept drop records the assumption row byte-identical to the base.
// See `is_total_drop_std_leaf` / `is_std_owning_or_scaffold`.
// ---------------------------------------------------------------------------

/// `std::ptr::NonNull<T>` — the pointer scaffold buried in owning containers.
fn ty_nonnull(pointee: Ty) -> Ty {
    Ty::adt(
        "std::ptr::NonNull",
        vec![("pointer".into(), Ty::RawPtr { mutable: false, pointee: Box::new(pointee) })],
    )
}
fn ty_phantomdata() -> Ty {
    Ty::adt("std::marker::PhantomData", vec![])
}
fn ty_global() -> Ty {
    Ty::adt("std::alloc::Global", vec![])
}

#[test]
fn test_build5_drop_glue_refmut_guard_is_leaf_and_proves() {
    // A `std::cell::RefMut` BORROW guard: it does NOT own/drop its referent — dropping it
    // only decrements a `Cell` borrow counter (the `BorrowRefMut` field's std `Drop`),
    // which is panic-free. To PROVE the classifier treats it as a non-owning LEAF (never
    // recursing into the referent), we give its `value` field a type that WOULD decline if
    // recursed — a user `PanickyGuard` with a possible panicking `Drop`. It must STILL
    // prove panic-free, because the guard genuinely never runs that `Drop`.
    let panicky = Ty::adt("my_crate::PanickyGuard", vec![("x".into(), Ty::i64())]);
    let refmut = Ty::adt(
        "std::cell::RefMut",
        vec![
            ("value".into(), ty_nonnull(panicky)),
            (
                "borrow".into(),
                Ty::adt(
                    "std::cell::BorrowRefMut",
                    vec![(
                        "borrow".into(),
                        Ty::Ref {
                            mutable: false,
                            inner: Box::new(Ty::adt(
                                "std::cell::Cell",
                                vec![("value".into(), Ty::i64())],
                            )),
                        },
                    )],
                ),
            ),
            ("marker".into(), ty_phantomdata()),
        ],
    );
    let module = lower_to_trust_ir_functions("test_mod", &[drop_glue_test_fn(refmut)])
        .expect("RefMut guard drop must lower");
    assert_valid_module(&module);
    assert!(
        !has_drop_glue_marker(&module),
        "a RefMut borrow guard never drops its referent — its drop is provably panic-free"
    );
    assert_eq!(drop_glue_assumption_count(&module), 0);
    assert_eq!(
        drop_glue_discharged_count(&module),
        1,
        "the proven drop must be recorded as ONE named discharged row"
    );
}

#[test]
fn test_build5_drop_glue_std_composed_arena_with_erased_maps_fails_closed() {
    // ny-cert's `Arena { values: Vec<BigRational>, dedup: HashMap<BigRational, u32> }` — a
    // user struct with NO `Drop` impl (in `structural_drop`) composed PURELY of std/num
    // fields. The `Vec` field is structurally visible, but the map K/V destructors are
    // not represented faithfully enough by the compatibility IR. The aggregate must
    // therefore fail closed even when its own no-`Drop` fact is certified.
    let arena = Ty::adt(
        "rational::Arena",
        vec![
            (
                "values".into(),
                // Vec<i64> stands in for Vec<BigRational> (element visible & panic-free).
                Ty::Adt { adt_kind: None, layout: None, 
                    name: "alloc::vec::Vec".to_string(),
                    fields: vec![("elem".into(), Ty::i64())],
                    variants: vec![],
                    disc_index_safe: false,
                    faithful_enum_repr: None, enum_layout: None, },
            ),
            // HashMap whose K/V hashbrown erases. A visible safe-looking scaffold must
            // not turn the absent K/V evidence into a vacuous proof.
            (
                "dedup".into(),
                Ty::adt(
                    "std::collections::HashMap",
                    vec![(
                        "base".into(),
                        Ty::adt("my_crate::PanickyGuard", vec![("x".into(), Ty::i64())]),
                    )],
                ),
            ),
            // BTreeMap with a COMPACTED `root: Ty::Datatype{Option}` (the real oversized
            // shape) likewise lacks usable element evidence.
            (
                "ordered".into(),
                Ty::adt(
                    "std::collections::BTreeMap",
                    vec![(
                        "root".into(),
                        Ty::Datatype { name: "std::option::Option".into(), variants: vec![] },
                    )],
                ),
            ),
        ],
    );
    let structural_drop: std::collections::HashSet<String> =
        ["rational::Arena".to_string()].into_iter().collect();
    let module = lower_to_trust_ir_functions_with_context(
        "test_mod",
        &[drop_glue_test_fn(arena)],
        &std::collections::HashSet::new(),
        &structural_drop,
    )
    .expect("std-composed Arena drop must lower fail-soft");
    assert_valid_module(&module);
    assert_eq!(
        drop_glue_marker_count(&module),
        1,
        "an Arena containing element-erased maps must keep one may-panic marker"
    );
    assert_eq!(drop_glue_assumption_count(&module), 1);
    assert_eq!(drop_glue_discharged_count(&module), 0);
}

#[test]
fn test_drop_glue_accepts_only_exact_pthread_mutex_and_condvar_leaves() {
    for name in
        ["std::sys::sync::mutex::pthread::Mutex", "std::sys::sync::condvar::pthread::Condvar"]
    {
        for (shape_name, shape) in [
            ("adt", Ty::adt(name, vec![])),
            ("datatype", Ty::Datatype { name: name.into(), variants: vec![] }),
        ] {
            let module = lower_to_trust_ir_functions("test_mod", &[drop_glue_test_fn(shape)])
                .unwrap_or_else(|error| {
                    panic!("exact pthread {shape_name} leaf `{name}` must lower: {error:?}")
                });
            assert_valid_module(&module);
            assert_eq!(
                drop_glue_marker_count(&module),
                0,
                "exact {shape_name} leaf `{name}` must prove"
            );
            assert_eq!(drop_glue_assumption_count(&module), 0);
            assert_eq!(drop_glue_discharged_count(&module), 1);
        }
    }

    for name in [
        "std::sys::sync::once_box::OnceBox",
        "std::sys::sync::mutex::futex::Mutex",
        "std::sys::sync::condvar::futex::Condvar",
        "std::sys::sync::lookalike::Mutex",
        "std::sys::sync::mutex::pthread::MutexGuard",
    ] {
        for (shape_name, shape) in [
            ("adt", Ty::adt(name, vec![])),
            ("datatype", Ty::Datatype { name: name.into(), variants: vec![] }),
        ] {
            let module = lower_to_trust_ir_functions("test_mod", &[drop_glue_test_fn(shape)])
                .unwrap_or_else(|error| {
                    panic!("near-miss {shape_name} sync type `{name}` must lower: {error:?}")
                });
            assert_valid_module(&module);
            assert_eq!(
                drop_glue_marker_count(&module),
                1,
                "near-miss {shape_name} sync type `{name}` must fail closed"
            );
            assert_eq!(drop_glue_assumption_count(&module), 1);
            assert_eq!(drop_glue_discharged_count(&module), 0);
        }
    }
}

#[test]
fn test_drop_glue_map_set_families_fail_closed_for_erased_compacted_and_forged_shapes() {
    let names = [
        "std::collections::hash::map::HashMap",
        "std::collections::hash::set::HashSet",
        "alloc::collections::btree::map::BTreeMap",
        "alloc::collections::btree::set::BTreeSet",
        "std::collections::HashMap",
        "std::collections::HashSet",
        "std::collections::BTreeMap",
        "std::collections::BTreeSet",
    ];

    for name in names {
        let shapes = [
            Ty::adt(name, vec![]),
            Ty::adt(
                name,
                vec![("ctrl".into(), Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) })],
            ),
            Ty::Datatype { name: name.into(), variants: vec![] },
        ];
        // Even a forged compiler context that claims the collection itself has no
        // explicit `Drop` impl cannot recover its erased K/V destructor evidence.
        let structural_drop = std::collections::HashSet::from([name.to_string()]);
        for shape in shapes {
            let module = lower_to_trust_ir_functions_with_context(
                "test_mod",
                &[drop_glue_test_fn(shape)],
                &std::collections::HashSet::new(),
                &structural_drop,
            )
            .unwrap_or_else(|error| panic!("map/set shape `{name}` must lower: {error:?}"));
            assert_valid_module(&module);
            assert_eq!(
                drop_glue_marker_count(&module),
                1,
                "map/set shape `{name}` must keep exactly one may-panic marker"
            );
            assert_eq!(drop_glue_assumption_count(&module), 1);
            assert_eq!(drop_glue_discharged_count(&module), 0);
        }
    }

    // `Box<T, A>` and `RawVec<T, A>` may likewise reach this compatibility
    // surface without their allocator parameter.  A primitive-looking pointer
    // field cannot prove that the erased allocator's destructor is panic-free.
    for (label, shape) in [
        (
            "Box with erased allocator",
            Ty::adt(
                "alloc::boxed::Box",
                vec![("ptr".into(), Ty::RawPtr { mutable: false, pointee: Box::new(Ty::i64()) })],
            ),
        ),
        (
            "RawVec with erased allocator",
            Ty::adt(
                "alloc::raw_vec::RawVec",
                vec![("ptr".into(), Ty::RawPtr { mutable: false, pointee: Box::new(Ty::i64()) })],
            ),
        ),
    ] {
        let module = lower_to_trust_ir_functions("test_mod", &[drop_glue_test_fn(shape)])
            .unwrap_or_else(|error| panic!("{label} must lower: {error:?}"));
        assert_valid_module(&module);
        assert_eq!(drop_glue_marker_count(&module), 1, "{label} must fail closed");
        assert_eq!(drop_glue_assumption_count(&module), 1);
        assert_eq!(drop_glue_discharged_count(&module), 0);
    }
}

#[test]
fn test_build5_drop_glue_vec_intoiter_fails_closed_and_bigint_proves() {
    // The compatibility type cannot authenticate every element/allocator lane of
    // `Vec::IntoIter<T>`. Even a primitive-looking field tree therefore keeps the
    // drop obligation.
    let into_iter = Ty::adt(
        "std::vec::IntoIter",
        vec![
            ("ptr".into(), ty_nonnull(Ty::i64())),
            ("end".into(), Ty::RawPtr { mutable: false, pointee: Box::new(Ty::i64()) }),
            ("cap".into(), Ty::u64()),
            ("alloc".into(), ty_global()),
            ("phantom".into(), ty_phantomdata()),
        ],
    );
    let module = lower_to_trust_ir_functions("test_mod", &[drop_glue_test_fn(into_iter)])
        .expect("Vec::IntoIter<i64> drop must lower");
    assert_valid_module(&module);
    assert!(has_drop_glue_marker(&module), "Vec::IntoIter<i64> drop must fail closed");
    assert_eq!(drop_glue_assumption_count(&module), 1);
    assert_eq!(drop_glue_discharged_count(&module), 0);

    // A printable third-party path is not authenticated crate/destructor
    // provenance; both full and compacted spellings fail closed.
    for bigint in [
        Ty::adt("num_bigint::BigInt", vec![("data".into(), Ty::u64())]),
        Ty::Datatype { name: "num_bigint::BigInt".into(), variants: vec![] },
    ] {
        let module = lower_to_trust_ir_functions("test_mod", &[drop_glue_test_fn(bigint)])
            .expect("BigInt drop must lower");
        assert_valid_module(&module);
        assert!(has_drop_glue_marker(&module), "unauthenticated BigInt drop must fail closed");
        assert_eq!(drop_glue_assumption_count(&module), 1);
        assert_eq!(drop_glue_discharged_count(&module), 0);
    }
}

#[test]
fn test_build5_drop_glue_fails_closed_on_user_drop_in_field_tree() {
    // SOUNDNESS: the Build-5 additions must NOT weaken the fail-closed default. A user
    // struct (no `Drop`, in `structural_drop`) that OWNS a field whose type carries a
    // possible user `Drop` (a `PanickyGuard`, NOT a leaf/scaffold, NOT in structural_drop)
    // must KEEP its drop-glue assumption row — the element recursion reaches the panicky
    // field and declines.
    let panicky = Ty::adt("my_crate::PanickyGuard", vec![("x".into(), Ty::i64())]);
    let composed = Ty::adt(
        "myapp::Composed",
        vec![
            ("values".into(), Ty::adt("alloc::vec::Vec", vec![("elem".into(), Ty::i64())])),
            // An OWNED user-Drop field (directly held, not behind a borrow guard).
            ("guard".into(), panicky.clone()),
        ],
    );
    let structural_drop: std::collections::HashSet<String> =
        ["myapp::Composed".to_string()].into_iter().collect();
    let module = lower_to_trust_ir_functions_with_context(
        "test_mod",
        &[drop_glue_test_fn(composed)],
        &std::collections::HashSet::new(),
        &structural_drop,
    )
    .expect("must lower fail-soft, not Err");
    assert_valid_module(&module);
    assert!(
        has_drop_glue_marker(&module),
        "a user Drop reachable in the owned field tree must keep the may-panic marker"
    );
    assert_eq!(drop_glue_assumption_count(&module), 1);
    assert_eq!(
        drop_glue_discharged_count(&module),
        0,
        "an UNPROVEN drop must never mint a discharged row"
    );

    // A directly-dropped `Vec<PanickyGuard>` via the new IntoIter path likewise declines
    // (element visible through the pointer scaffold).
    let into_iter_panicky = Ty::adt(
        "std::vec::IntoIter",
        vec![
            ("ptr".into(), ty_nonnull(panicky)),
            ("cap".into(), Ty::u64()),
            ("alloc".into(), ty_global()),
            ("phantom".into(), ty_phantomdata()),
        ],
    );
    let module2 = lower_to_trust_ir_functions("test_mod", &[drop_glue_test_fn(into_iter_panicky)])
        .expect("must lower fail-soft");
    assert_valid_module(&module2);
    assert!(
        has_drop_glue_marker(&module2),
        "Vec::IntoIter<PanickyGuard> must decline (element drop reachable via ptr)"
    );
    assert_eq!(drop_glue_assumption_count(&module2), 1);
    assert_eq!(drop_glue_discharged_count(&module2), 0);
}

// ---------------------------------------------------------------------------
// Round-5 gating extension: closure-environment drop glue (captures-only) and
// the element-gated `num_rational::Ratio` leaf. Clears the 27 assumption rows
// at rational.rs `intern::{closure#0}` (drop of the closure capturing a
// full-field `Ratio<BigInt>`). Fail-closed: `Ratio<UserAdt>` and an
// element-less compacted `Ratio` keep their rows.
// ---------------------------------------------------------------------------

/// A full-field `num_rational::Ratio<num_bigint::BigInt>` shaped exactly like the
/// real extractor output in the batch-49 census rows (`sign` enum + `data`
/// BigUint/Vec tree). The classifier accepts `BigInt` as a by-name LEAF, so the
/// foreign `Sign` enum inside (which would DECLINE if recursed) also proves the
/// leaf short-circuit is what fires.
fn ty_ratio_bigint_full() -> Ty {
    let sign = Ty::Adt { adt_kind: None, layout: None, 
        name: "num_bigint::Sign".to_string(),
        fields: vec![("__tag".to_string(), Ty::i64())],
        variants: vec![
            trust_types::VariantDef { name: "Minus".to_string(), discriminant: 0, fields: vec![] },
            trust_types::VariantDef { name: "NoSign".to_string(), discriminant: 1, fields: vec![] },
            trust_types::VariantDef { name: "Plus".to_string(), discriminant: 2, fields: vec![] },
        ],
        disc_index_safe: true,
        faithful_enum_repr: None, enum_layout: None, };
    let biguint = Ty::adt(
        "num_bigint::BigUint",
        vec![("data".to_string(), Ty::adt("std::vec::Vec", vec![("len".to_string(), Ty::u64())]))],
    );
    let bigint = Ty::adt(
        "num_bigint::BigInt",
        vec![("sign".to_string(), sign), ("data".to_string(), biguint)],
    );
    Ty::adt(
        "num_rational::Ratio",
        vec![("numer".to_string(), bigint.clone()), ("denom".to_string(), bigint)],
    )
}

/// The `intern::{closure#0}`-shaped closure environment: one capture of `upvar`.
fn ty_intern_closure(upvar: Ty) -> Ty {
    Ty::Closure {
        name: "rational::intern::{closure#0}".to_string(),
        upvars: vec![upvar],
        call: None,
    }
}

#[test]
fn test_round5_drop_glue_closure_capturing_ratio_bigint_proves() {
    // The exact census shape still lacks authenticated external destructor
    // identity, so structural_drop EMPTY means it must fail closed.
    let module = lower_to_trust_ir_functions(
        "test_mod",
        &[drop_glue_test_fn(ty_intern_closure(ty_ratio_bigint_full()))],
    )
    .expect("closure-capture Ratio<BigInt> drop must lower");
    assert_valid_module(&module);
    assert!(has_drop_glue_marker(&module), "unauthenticated Ratio<BigInt> drop fails closed");
    assert_eq!(drop_glue_assumption_count(&module), 1);
    assert_eq!(drop_glue_discharged_count(&module), 0);

    // The `Ty::Datatype` spelling of `Ratio` with VISIBLE, all-total element
    // fields likewise proves (same gate, other spelling).
    let bigint_leaf = Ty::Datatype { name: "num_bigint::BigInt".to_string(), variants: vec![] };
    let ratio_datatype = Ty::Datatype {
        name: "num_rational::Ratio".to_string(),
        variants: vec![(
            "Ratio".to_string(),
            vec![("numer".to_string(), bigint_leaf.clone()), ("denom".to_string(), bigint_leaf)],
        )],
    };
    let module2 = lower_to_trust_ir_functions(
        "test_mod",
        &[drop_glue_test_fn(ty_intern_closure(ratio_datatype))],
    )
    .expect("visible-field Ratio datatype drop must lower");
    assert_valid_module(&module2);
    assert!(has_drop_glue_marker(&module2));
    assert_eq!(drop_glue_assumption_count(&module2), 1);
    assert_eq!(drop_glue_discharged_count(&module2), 0);
}

#[test]
fn test_round5_drop_glue_closure_capturing_ratio_of_user_adt_fails_closed() {
    // SOUNDNESS KEYSTONE: `Ratio` is generic — `Ratio<UserType>` may own a
    // panicking user `Drop`, so the element gate must DECLINE it. The closure
    // arm's recursion reaches the user field and keeps the assumption row.
    let panicky = Ty::adt("my_crate::PanickyGuard", vec![("x".to_string(), Ty::i64())]);
    let ratio_user = Ty::adt(
        "num_rational::Ratio",
        vec![("numer".to_string(), panicky.clone()), ("denom".to_string(), panicky)],
    );
    let module = lower_to_trust_ir_functions(
        "test_mod",
        &[drop_glue_test_fn(ty_intern_closure(ratio_user))],
    )
    .expect("must lower fail-soft, not Err");
    assert_valid_module(&module);
    assert!(
        has_drop_glue_marker(&module),
        "Ratio<UserAdt> must keep the may-panic marker (user Drop reachable via element)"
    );
    assert_eq!(drop_glue_assumption_count(&module), 1);
    assert_eq!(drop_glue_discharged_count(&module), 0);
}

#[test]
fn test_round5_drop_glue_closure_capturing_compacted_ratio_fails_closed() {
    // A by-name COMPACTED `Ratio` back-reference (`variants: []` — the
    // `compact_oversized_field` shape) has NO visible element: it could be
    // `Ratio<UserPanickyDrop>`, so name-only trust is forbidden and the row is
    // KEPT. Same for a degenerate ctor list with zero visible fields, and for
    // an element-less `Ty::Adt` spelling.
    for compacted in [
        Ty::Datatype { name: "num_rational::Ratio".to_string(), variants: vec![] },
        Ty::Datatype {
            name: "num_rational::Ratio".to_string(),
            variants: vec![("Ratio".to_string(), vec![])],
        },
        Ty::adt("num_rational::Ratio", vec![]),
    ] {
        let module = lower_to_trust_ir_functions(
            "test_mod",
            &[drop_glue_test_fn(ty_intern_closure(compacted))],
        )
        .expect("must lower fail-soft, not Err");
        assert_valid_module(&module);
        assert!(
            has_drop_glue_marker(&module),
            "an element-less Ratio must keep the may-panic marker (never name-only trusted)"
        );
        assert_eq!(drop_glue_assumption_count(&module), 1);
        assert_eq!(drop_glue_discharged_count(&module), 0);
    }
}

#[test]
fn test_lower_unresolved_call_fails_soft_with_honest_panic_obligation() {
    let func = VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "callee".to_string(),
                        args: vec![Operand::Constant(ConstValue::Int(10))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // FAIL-SOFT (was fail-closed-by-Err): an unresolved call no longer fails
    // the whole lowering — it lowers to the audited may-panic encoding
    // (Assert(false)+NoPanic marker + havoc result + ONE marked PanicFreedom
    // obligation), so the function's OTHER obligations get real verdicts while
    // panic-freedom through this call site stays honestly unprovable. The
    // fail-CLOSED property this test protects is unchanged: the call can never
    // be silently treated as panic-free or lowered to a phantom Call.
    let module = lower_to_trust_ir(&func).expect("unresolved call must lower fail-soft, not Err");
    assert_valid_module(&module);
    let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    assert!(
        insts.iter().any(|n| {
            matches!(n.inst, Inst::Assert { .. })
                && n.proofs.contains(&trust_ir::ProofAnnotation::NoPanic)
        }),
        "expected the Assert(false)+NoPanic may-panic marker"
    );
    assert!(
        !insts.iter().any(|n| matches!(n.inst, Inst::Call { .. })),
        "an unresolved callee must not lower to a phantom Call"
    );
    assert_eq!(
        module
            .proof_obligations
            .iter()
            .filter(|o| {
                o.kind == trust_ir::ObligationKind::PanicFreedom
                    && o.description
                        .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
            })
            .count(),
        1,
        "expected exactly one marked PanicFreedom obligation"
    );
}

#[test]
fn test_panic_call_lowers_to_panic_freedom_obligation() {
    // A user `assert!`/`panic!` lowers to a diverging Call to a panic intrinsic
    // that is never part of the user crate's module. It must lower as a
    // panic-freedom obligation (prove the site unreachable), not fail closed.
    let func = VerifiableFunction {
        name: "panics".to_string(),
        def_path: "test::panics".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                    func: "core::panicking::panic".to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                },
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("panic call must lower, not fail closed");
    let has_panic_freedom = module.proof_obligations.iter().any(|po| {
        matches!(po.kind, trust_ir::proof::ObligationKind::PanicFreedom)
            && po.description.contains("must be unreachable")
    });
    assert!(has_panic_freedom, "panic call should yield a PanicFreedom obligation");
}

#[test]
fn str_pattern_method_with_panicking_closure_is_not_summarized_total() {
    // HOLE-6B differential / soundness regression. `s.find(|c| { …; assert!(…); … })`:
    // the str `Pattern` method drives the closure EAGERLY and it can panic, so the
    // call must NOT be lowered as a clean total `Undef` (which emits ZERO obligations
    // and PROVES the caller panic-free — the false proof). After the closure-pattern
    // gate on `total_no_panic_call_summary`, the call FAILS CLOSED: it either declines
    // (a `BridgeError`, leaving the whole function UNKNOWN) or carries a may-panic
    // `PanicFreedom` obligation. It is NEVER summarized total. If the gate ever
    // regresses, `str::find` matches the name-only TOTAL list again and this lowers to
    // a clean total with no obligation — which this test forbids.
    let func = VerifiableFunction {
        name: "boom".to_string(),
        def_path: "test::boom".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::Adt { adt_kind: None, layout: None, 
                        variants: Vec::new(),
                        name: "core::option::Option".into(),
                        fields: vec![],
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, },
                    name: None,
                },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Adt { adt_kind: None, layout: None, 
                            variants: Vec::new(),
                            name: "str".into(),
                            fields: vec![],
                            disc_index_safe: false,
                            faithful_enum_repr: None, enum_layout: None, }),
                    },
                    name: Some("s".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Closure {
                        name: "test::boom::{closure}".into(),
                        upvars: vec![],
                        call: None,
                    },
                    name: Some("pat".into()),
                },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false, is_foreign: false,
                        func: "core::str::<impl str>::find".to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Adt { adt_kind: None, layout: None, 
                variants: Vec::new(),
                name: "core::option::Option".into(),
                fields: vec![],
                disc_index_safe: false,
                faithful_enum_repr: None, enum_layout: None, },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    match lower_to_trust_ir(&func) {
        // Declined (fail closed) — sound: the caller's panic-freedom stays UNKNOWN.
        Err(_) => {}
        Ok(module) => {
            // If it lowered, the eager closure call MUST surface a may-panic
            // obligation — it must NOT be a clean total summary with zero panic
            // obligations.
            let has_may_panic = module
                .proof_obligations
                .iter()
                .any(|po| matches!(po.kind, trust_ir::proof::ObligationKind::PanicFreedom));
            assert!(
                has_may_panic,
                "str::find(panicking closure) was summarized as a clean total (no \
                 may-panic obligation) — HOLE-6B regression: the closure-pattern gate \
                 on total_no_panic_call_summary is gone",
            );
        }
    }
}

#[test]
fn test_lower_intra_module_call_terminator_validates() {
    let callee = VerifiableFunction {
        name: "callee".to_string(),
        def_path: "test::callee".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
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
    };

    let caller = VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "test::callee".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module =
        lower_to_trust_ir_functions("calls", &[callee, caller]).expect("module should lower");
    assert_valid_module(&module);
    let caller = &module.functions[1];
    let bb0 = &caller.blocks[0];
    assert!(
        bb0.body.iter().any(|n| matches!(&n.inst, Inst::Call { callee, args }
            if callee.index() == 0 && args.as_slice() == [ValueId::new(0)])),
        "caller should emit a resolved direct call to callee"
    );
    assert!(
        bb0.body.iter().any(|n| matches!(&n.inst, Inst::Br { target, .. } if target.index() == 1)),
        "call should branch to continuation block"
    );
}

#[test]
fn test_lower_cast_widening() {
    let func = VerifiableFunction {
        name: "widen".to_string(),
        def_path: "test::widen".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i8(), name: Some("a".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::i32()),
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
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_cast = bb0.body.iter().any(|n| matches!(&n.inst, Inst::Cast { .. }));
    assert!(has_cast, "should have a Cast instruction for widening");
}

#[test]
fn test_cast_constant_uses_constant_type_instead_of_i64_fallback() {
    let func = VerifiableFunction {
        name: "cast_const".to_string(),
        def_path: "test::cast_const".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::u32(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Constant(ConstValue::Uint(7, 8)), Ty::u32()),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("constant cast should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_u8_source_cast = bb0.body.iter().any(|n| {
        matches!(&n.inst, Inst::Cast { src_ty: TrustIrTy::U8, dst_ty: TrustIrTy::U32, .. })
    });
    assert!(has_u8_source_cast, "u8 constant cast should not default source type to I64");
}

#[test]
fn test_layout_sensitive_cast_without_tuple_layout_evidence_is_blocked() {
    let pair_ty = Ty::Tuple(vec![Ty::u64(), Ty::u64()]);
    let func = VerifiableFunction {
        name: "layout_cast".to_string(),
        def_path: "test::layout_cast".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: pair_ty, name: Some("pair".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u64()),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("diagnostic TrustIr should still lower");
    let blockers = collect_layout_sensitive_cast_blockers(&module);
    assert_eq!(blockers.len(), 1);
    assert_eq!(blockers[0].function, "layout_cast");
    assert_eq!(blockers[0].op, "bitcast");
    assert!(blockers[0].reason.contains("has no concrete memory layout evidence"));
    assert!(blockers[0].diagnostics().iter().any(|diagnostic| diagnostic
        == &format!("blocker-code={TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_FEATURE}")));
    assert!(ensure_layout_sensitive_cast_evidence(&module).is_err());
}

#[test]
fn test_layout_sensitive_pointer_cast_metadata_change_is_blocked() {
    let mut module = trust_ir::Module::new("bad_pointer_cast");
    let func_ty = module.add_func_type(trust_ir::FuncTy {
        params: vec![TrustIrTy::FatPtr(trust_ir::FatPtrKind::Str)],
        returns: vec![],
        is_vararg: false,
    });

    let mut func = trust_ir::Function::new(
        trust_ir::FuncId::new(0),
        "bad_pointer_cast",
        func_ty,
        trust_ir::BlockId::new(0),
    );
    let mut block = trust_ir::Block::new(trust_ir::BlockId::new(0));
    block.params.push((ValueId::new(0), TrustIrTy::FatPtr(trust_ir::FatPtrKind::Str)));
    block.body.push(
        trust_ir::InstrNode::new(Inst::Cast {
            op: TrustIrCastOp::PtrToPtr,
            src_ty: TrustIrTy::FatPtr(trust_ir::FatPtrKind::Str),
            dst_ty: TrustIrTy::FatPtr(trust_ir::FatPtrKind::TraitObject { trait_id: 7 }),
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    block.body.push(trust_ir::InstrNode::new(Inst::Return { values: vec![] }));
    func.blocks.push(block);
    module.add_function(func);

    let blockers = collect_layout_sensitive_cast_blockers(&module);
    assert_eq!(blockers.len(), 1);
    assert_eq!(blockers[0].op, "ptrtoptr");
    assert!(blockers[0].reason.contains("pointer cast changes metadata"));
}

#[test]
fn test_lower_f64_add_emits_fadd_and_validates() {
    let func = VerifiableFunction {
        name: "fadd".to_string(),
        def_path: "test::fadd".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::f64_ty(), name: None },
                LocalDecl { index: 1, ty: Ty::f64_ty(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::f64_ty(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
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

    let module = lower_to_trust_ir(&func).expect("f64 add should lower");
    assert_valid_module(&module);
    assert!(
        module.functions[0].blocks[0].body.iter().any(|node| matches!(
            &node.inst,
            Inst::BinOp { op: TrustIrBinOp::FAdd, ty: TrustIrTy::F64, .. }
        )),
        "f64 Add should emit TrustIr FAdd"
    );
}

#[test]
fn test_lower_f64_lt_emits_fcmp_not_icmp() {
    let func = VerifiableFunction {
        name: "flt".to_string(),
        def_path: "test::flt".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl { index: 1, ty: Ty::f64_ty(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::f64_ty(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("f64 comparison should lower");
    assert_valid_module(&module);
    let body = &module.functions[0].blocks[0].body;
    assert!(
        body.iter().any(|node| matches!(
            &node.inst,
            Inst::FCmp { op: TrustIrFCmpOp::OLt, ty: TrustIrTy::F64, .. }
        )),
        "f64 Lt should emit ordered TrustIr FCmp"
    );
    assert!(
        !body.iter().any(|node| matches!(&node.inst, Inst::ICmp { ty: TrustIrTy::F64, .. })),
        "float comparisons must not emit ICmp"
    );
}

#[test]
fn test_lower_f64_neg_emits_fneg() {
    let func = VerifiableFunction {
        name: "fneg".to_string(),
        def_path: "test::fneg".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::f64_ty(), name: None },
                LocalDecl { index: 1, ty: Ty::f64_ty(), name: Some("a".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::f64_ty(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("f64 neg should lower");
    assert_valid_module(&module);
    assert!(
        module.functions[0].blocks[0].body.iter().any(|node| matches!(
            &node.inst,
            Inst::UnOp { op: TrustIrUnOp::FNeg, ty: TrustIrTy::F64, .. }
        )),
        "f64 Neg should emit TrustIr FNeg"
    );
}

#[test]
fn test_cast_f64_to_int_uses_target_signedness() {
    let signed_func = VerifiableFunction {
        name: "f64_to_i32".to_string(),
        def_path: "test::f64_to_i32".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::f64_ty(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::i32()),
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
    };
    let unsigned_func = VerifiableFunction {
        name: "f64_to_u32".to_string(),
        def_path: "test::f64_to_u32".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::f64_ty(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u32()),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let signed = lower_to_trust_ir(&signed_func).expect("f64 to i32 should lower");
    assert_valid_module(&signed);
    assert!(
        signed.functions[0].blocks[0].body.iter().any(|node| matches!(
            &node.inst,
            Inst::Cast {
                op: TrustIrCastOp::FPToSISat,
                src_ty: TrustIrTy::F64,
                dst_ty: TrustIrTy::I32,
                ..
            }
        )),
        "f64 as i32 should emit FPToSISat (Rust's saturating float→int cast)"
    );

    let unsigned = lower_to_trust_ir(&unsigned_func).expect("f64 to u32 should lower");
    assert_valid_module(&unsigned);
    assert!(
        unsigned.functions[0].blocks[0].body.iter().any(|node| matches!(
            &node.inst,
            Inst::Cast {
                op: TrustIrCastOp::FPToUISat,
                src_ty: TrustIrTy::F64,
                dst_ty: TrustIrTy::U32,
                ..
            }
        )),
        "f64 as u32 should emit FPToUISat (Rust's saturating float→int cast)"
    );
}

#[test]
fn test_lower_floatbits64_constant_preserves_bits() {
    let bits = 0x7ff8_0000_0000_0001u128;
    let func = VerifiableFunction {
        name: "floatbits64".to_string(),
        def_path: "test::floatbits64".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::f64_ty(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::FloatBits {
                        bits,
                        width: 64,
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::f64_ty(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("f64 FloatBits should lower");
    assert_valid_module(&module);
    assert!(
        module.functions[0].blocks[0].body.iter().any(|node| matches!(
            &node.inst,
            Inst::Const { ty: TrustIrTy::F64, value: TrustIrConstant::Float(value) }
                if value.to_bits() == bits as u64
        )),
        "f64 FloatBits should preserve the exact IEEE-754 payload"
    );
}

#[test]
fn test_opaque_terminator_rejected_even_with_single_target() {
    let func = VerifiableFunction {
        name: "opaque_term".to_string(),
        def_path: "test::opaque_term".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Opaque {
                        kind: "Yield".to_string(),
                        targets: vec![BlockId(1)],
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("opaque terminator must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(msg) if msg.contains("opaque MIR terminator"))
    );
}

#[test]
fn test_field_projection_on_non_aggregate_rejected() {
    let func = VerifiableFunction {
        name: "bad_field".to_string(),
        def_path: "test::bad_field".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Field(0)],
                    })),
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
    };

    let err = lower_to_trust_ir(&func).expect_err("field projection on scalar must fail closed");
    assert!(matches!(err, BridgeError::UnsupportedOp(msg) if msg.contains("Field projection")));
}

#[test]
fn test_nested_field_projected_store_rebuilds_outer_aggregate() {
    let inner_ty = Ty::Tuple(vec![Ty::u64(), Ty::Bool]);
    let outer_ty = Ty::Tuple(vec![inner_ty.clone(), Ty::u64()]);
    let func = VerifiableFunction {
        name: "nested_field_store".to_string(),
        def_path: "test::nested_field_store".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: outer_ty.clone(), name: None },
                LocalDecl { index: 1, ty: outer_ty, name: Some("t".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("v".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place {
                            local: 1,
                            projections: vec![Projection::Field(0), Projection::Field(1)],
                        },
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Tuple(vec![inner_ty, Ty::u64()]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("nested projected store should lower");
    assert_valid_module(&module);
    let body = &module.functions[0].blocks[0].body;
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::ExtractField { field: 0, .. })),
        "nested field store should read the inner aggregate before rebuilding it"
    );
    assert!(
        body.iter().filter(|node| matches!(&node.inst, Inst::InsertField { .. })).count() >= 2,
        "nested field store should rebuild both inner and outer aggregates"
    );
}

fn multi_variant_projected_store_ty(faithful: bool) -> Ty {
    Ty::Adt { adt_kind: None, layout: None, 
        name: "test::MultiProjected".into(),
        fields: vec![
            ("__tag".into(), Ty::isize()),
            ("__v0_0".into(), Ty::i64()),
            ("__v1_0".into(), Ty::i64()),
            ("__v1_1".into(), Ty::i64()),
        ],
        variants: vec![
            VariantDef { name: "A".into(), discriminant: 3, fields: vec![("0".into(), Ty::i64())] },
            VariantDef {
                name: "B".into(),
                discriminant: 9,
                fields: vec![("0".into(), Ty::i64()), ("1".into(), Ty::i64())],
            },
        ],
        disc_index_safe: true,
        faithful_enum_repr: if faithful { Some(None) } else { None }, enum_layout: None, }
}

fn projected_store_through_pointer(
    name: &str,
    pointee: Ty,
    projections: Vec<Projection>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(pointee) },
                    name: Some("slot".into()),
                },
                LocalDecl { index: 2, ty: Ty::i64(), name: Some("value".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place { local: 1, projections },
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn assert_variant_interior_store_lowers_as_sound_havoc(func: &VerifiableFunction) {
    // SOUND HAVOC COMPLETION (was a hard fail-close): a DIRECT enum-interior
    // store lowers by replacing the whole enum-typed sub-value with a fresh
    // `Undef` — a strict over-approximation of the real post-state, so no
    // dependent obligation can falsely prove, and the B3-1b G1 silent-WRONG-
    // write hazard is structurally gone (no write is modeled at all). The
    // DEREF/address-walk path is unchanged and still fails closed (see the
    // `assert_variant_interior_address_walk_fails_closed` fixtures).
    let module = lower_to_trust_ir(func).expect("an enum-interior store now lowers (sound havoc)");
    let function = &module.functions[0];
    let mut saw_undef = false;
    for block in &function.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Undef { .. } => saw_undef = true,
                // No wrong write may be modeled: the havoc path emits neither a
                // flat-indexed InsertField into the enum nor a Store of the
                // copied value.
                Inst::InsertField { .. } => {
                    panic!("enum-interior store must not model a field write (wrong-write hazard)")
                }
                _ => {}
            }
        }
    }
    assert!(saw_undef, "the enum-interior store must havoc the enum-typed sub-value");
}

fn assert_variant_interior_address_walk_fails_closed(func: &VerifiableFunction) {
    let err = lower_to_trust_ir(func).expect_err("an enum-interior address walk must fail closed");
    assert!(
        matches!(
            err,
            BridgeError::UnsupportedOp(ref message)
                if message == "address walk into variant-bearing ADT interior"
        ),
        "unexpected enum-interior address-walk error: {err:?}"
    );
}

fn address_of_test_function(
    name: &str,
    base_ty: Ty,
    addressed_ty: Ty,
    place: Place,
    raw: bool,
    mutable: bool,
) -> VerifiableFunction {
    let result_ty = if raw {
        Ty::RawPtr { mutable, pointee: Box::new(addressed_ty) }
    } else {
        Ty::Ref { mutable, inner: Box::new(addressed_ty) }
    };
    let rvalue =
        if raw { Rvalue::AddressOf(mutable, place) } else { Rvalue::Ref { mutable, place } };

    VerifiableFunction {
        name: name.into(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: base_ty, name: Some("base".into()) },
                LocalDecl { index: 2, ty: result_ty, name: Some("address".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue,
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn enum_interior_address_cases() -> Vec<(&'static str, Ty, Place)> {
    let nested_enum = multi_variant_projected_store_ty(true);
    let nested_outer = Ty::adt("test::NestedEnumAddress", vec![("inner".into(), nested_enum)]);

    vec![
        (
            "flat",
            multi_variant_projected_store_ty(false),
            Place { local: 1, projections: vec![Projection::Downcast(1), Projection::Field(0)] },
        ),
        (
            "faithful",
            multi_variant_projected_store_ty(true),
            Place { local: 1, projections: vec![Projection::Downcast(1), Projection::Field(0)] },
        ),
        (
            "nested_faithful_deref",
            Ty::Ref { mutable: false, inner: Box::new(nested_outer) },
            Place {
                local: 1,
                projections: vec![
                    Projection::Deref,
                    Projection::Field(0),
                    Projection::Downcast(1),
                    Projection::Field(0),
                ],
            },
        ),
    ]
}

#[test]
fn test_ref_into_variant_bearing_adt_interior_fails_closed() {
    for (shape, base_ty, place) in enum_interior_address_cases() {
        let func = address_of_test_function(
            &format!("ref_into_{shape}_enum"),
            base_ty,
            Ty::i64(),
            place,
            false,
            false,
        );
        assert_variant_interior_address_walk_fails_closed(&func);
    }
}

#[test]
fn test_mutable_ref_into_variant_bearing_adt_interior_fails_closed() {
    for (shape, base_ty, place) in enum_interior_address_cases() {
        let func = address_of_test_function(
            &format!("mutable_ref_into_{shape}_enum"),
            base_ty,
            Ty::i64(),
            place,
            false,
            true,
        );
        assert_variant_interior_address_walk_fails_closed(&func);
    }
}

#[test]
fn test_address_of_variant_bearing_adt_interior_fails_closed() {
    for (shape, base_ty, place) in enum_interior_address_cases() {
        let func = address_of_test_function(
            &format!("address_of_{shape}_enum"),
            base_ty,
            Ty::i64(),
            place,
            true,
            false,
        );
        assert_variant_interior_address_walk_fails_closed(&func);
    }
}

#[test]
fn test_whole_variant_bearing_adt_ref_and_address_of_remain_supported() {
    for raw in [false, true] {
        let enum_ty = multi_variant_projected_store_ty(true);
        let func = address_of_test_function(
            if raw { "address_of_whole_enum" } else { "ref_whole_enum" },
            enum_ty.clone(),
            enum_ty,
            Place::local(1),
            raw,
            false,
        );
        let module = lower_to_trust_ir(&func).expect("a whole-enum address should lower");
        assert_valid_module(&module);
    }
}

#[test]
fn test_non_enum_interior_ref_and_address_of_remain_supported() {
    for raw in [false, true] {
        let tuple_ty = Ty::Tuple(vec![Ty::i64(), Ty::i64()]);
        let func = address_of_test_function(
            if raw { "address_of_tuple_field" } else { "ref_tuple_field" },
            tuple_ty,
            Ty::i64(),
            Place { local: 1, projections: vec![Projection::Field(1)] },
            raw,
            false,
        );
        let module = lower_to_trust_ir(&func).expect("a non-enum interior address should lower");
        assert_valid_module(&module);
        assert!(
            module.functions[0].blocks[0]
                .body
                .iter()
                .any(|node| matches!(&node.inst, Inst::GEP { pointee_ty: TrustIrTy::I64, .. }))
        );
    }
}

#[test]
fn test_deref_projected_store_into_flat_enum_fails_closed() {
    let func = projected_store_through_pointer(
        "flat_enum_deref_store",
        multi_variant_projected_store_ty(false),
        vec![Projection::Deref, Projection::Downcast(1), Projection::Field(0)],
    );
    assert_variant_interior_address_walk_fails_closed(&func);
}

#[test]
fn test_deref_projected_store_into_faithful_enum_fails_closed() {
    let func = projected_store_through_pointer(
        "faithful_enum_deref_store",
        multi_variant_projected_store_ty(true),
        vec![Projection::Deref, Projection::Downcast(1), Projection::Field(0)],
    );
    assert_variant_interior_address_walk_fails_closed(&func);
}

#[test]
fn test_deref_projected_store_into_nested_enum_fails_closed_before_enum_gep() {
    let outer = Ty::adt(
        "test::EnumCarrier",
        vec![("inner".into(), multi_variant_projected_store_ty(true))],
    );
    let func = projected_store_through_pointer(
        "nested_enum_deref_store",
        outer,
        vec![
            Projection::Deref,
            Projection::Field(0),
            Projection::Downcast(1),
            Projection::Field(0),
        ],
    );
    assert_variant_interior_address_walk_fails_closed(&func);
}

#[test]
fn test_direct_projected_store_into_flat_enum_lowers_as_sound_havoc() {
    let enum_ty = multi_variant_projected_store_ty(false);
    let func = VerifiableFunction {
        name: "flat_enum_direct_store".into(),
        def_path: "test::flat_enum_direct_store".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty, name: Some("slot".into()) },
                LocalDecl { index: 2, ty: Ty::i64(), name: Some("value".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place {
                        local: 1,
                        projections: vec![Projection::Downcast(1), Projection::Field(0)],
                    },
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    assert_variant_interior_store_lowers_as_sound_havoc(&func);
}

#[test]
fn test_whole_faithful_enum_store_through_reference_remains_supported() {
    let enum_ty = multi_variant_projected_store_ty(true);
    let func = VerifiableFunction {
        name: "whole_faithful_enum_store".into(),
        def_path: "test::whole_faithful_enum_store".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(enum_ty.clone()) },
                    name: Some("slot".into()),
                },
                LocalDecl { index: 2, ty: enum_ty, name: Some("value".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place { local: 1, projections: vec![Projection::Deref] },
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("a whole-enum store should lower");
    assert_valid_module(&module);
    assert!(
        module.functions[0].blocks[0]
            .body
            .iter()
            .any(|node| matches!(&node.inst, Inst::Store { ty: TrustIrTy::Enum(_), .. }))
    );
}

#[test]
fn test_non_enum_projected_store_through_reference_remains_supported() {
    let tuple_ty = Ty::Tuple(vec![Ty::i64(), Ty::i64()]);
    let func = projected_store_through_pointer(
        "tuple_deref_store",
        tuple_ty,
        vec![Projection::Deref, Projection::Field(1)],
    );

    let module = lower_to_trust_ir(&func).expect("a non-enum projected store should lower");
    assert_valid_module(&module);
    let body = &module.functions[0].blocks[0].body;
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::GEP { pointee_ty: TrustIrTy::I64, .. }))
    );
    assert!(body.iter().any(|node| matches!(&node.inst, Inst::Store { ty: TrustIrTy::I64, .. })));
}

fn faithful_enum_ty(name: &str, repr: Option<EnumReprHint>, variants: Vec<VariantDef>) -> Ty {
    let mut fields = vec![("__tag".into(), Ty::isize())];
    for (variant_index, variant) in variants.iter().enumerate() {
        for (field_index, (_, field_ty)) in variant.fields.iter().enumerate() {
            fields.push((format!("__v{variant_index}_{field_index}"), field_ty.clone()));
        }
    }
    Ty::Adt { adt_kind: None, layout: None, 
        name: name.into(),
        fields,
        variants,
        disc_index_safe: true,
        faithful_enum_repr: Some(repr), enum_layout: None, }
}

fn discriminant_read_function(name: &str, enum_ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::PtrSizedInt { signed: true }, name: None },
                LocalDecl { index: 1, ty: enum_ty, name: Some("value".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::PtrSizedInt { signed: true },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_faithful_discriminant_read_uses_exact_tag_width_and_repr_signedness() {
    let cases = [
        (
            "signed_disc",
            EnumReprHint::I16,
            0xfffbi128,
            -5i128,
            TrustIrTy::I16,
            trust_ir::EnumTagRepr::I16,
            TrustIrCastOp::SExt,
        ),
        (
            "unsigned_disc",
            EnumReprHint::U8,
            250i128,
            250i128,
            TrustIrTy::U8,
            trust_ir::EnumTagRepr::U8,
            TrustIrCastOp::ZExt,
        ),
    ];

    for (name, repr, raw_disc, effective_disc, tag_ty, tag_repr, expected_cast) in cases {
        let enum_ty = faithful_enum_ty(
            name,
            Some(repr),
            vec![
                VariantDef { name: "First".into(), discriminant: raw_disc, fields: vec![] },
                VariantDef { name: "Second".into(), discriminant: 7, fields: vec![] },
            ],
        );
        let module = lower_to_trust_ir(&discriminant_read_function(name, enum_ty))
            .expect("a faithful discriminant read should lower");
        assert_valid_module(&module);

        let enum_def = &module.enums[0];
        assert_eq!(enum_def.effective_discriminants(), Some(vec![effective_disc, 7]));
        assert_eq!(enum_def.canonical_tag_repr(), Some(tag_repr));
        let body = &module.functions[0].blocks[0].body;
        assert!(body.iter().any(|node| matches!(
            &node.inst,
            Inst::ExtractField { ty, field: 0, .. } if ty == &tag_ty
        )));
        assert!(body.iter().any(|node| matches!(
            &node.inst,
            Inst::Cast {
                op,
                src_ty,
                dst_ty: TrustIrTy::Isize,
                ..
            } if *op == expected_cast && src_ty == &tag_ty
        )));

        let tag = InterpretValue::int(tag_ty.clone(), effective_disc).unwrap();
        let input = InterpretValue {
            ty: TrustIrTy::Enum(enum_def.id),
            kind: trust_ir::interpret::InterpretValueKind::Aggregate(vec![tag]),
        };
        let outcome = Interpreter::with_module(&module)
            .execute_func(trust_ir::FuncId::new(0), vec![input])
            .expect("the faithful discriminant read should interpret");
        let expected = InterpretValue::int(TrustIrTy::Isize, effective_disc).unwrap();
        assert_eq!(outcome.returns[0].kind, expected.kind);
    }
}

fn pointer_width_switch_function(name: &str, discr_ty: Ty, case: u128) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: discr_ty, name: Some("discr".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(case, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                TrustBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_pointer_width_switch_cases_are_exactly_64_bit() {
    let signed_raw = u64::MAX as u128 - 4;
    let signed = lower_to_trust_ir(&pointer_width_switch_function(
        "isize_switch",
        Ty::PtrSizedInt { signed: true },
        signed_raw,
    ))
    .expect("a 64-bit isize case should lower");
    assert_valid_module(&signed);
    assert!(signed.functions[0].blocks[0].body.iter().any(|node| matches!(
        &node.inst,
        Inst::Const { ty: TrustIrTy::Isize, value: TrustIrConstant::Int(-5) }
    )));

    let unsigned = lower_to_trust_ir(&pointer_width_switch_function(
        "usize_switch",
        Ty::PtrSizedInt { signed: false },
        u64::MAX as u128,
    ))
    .expect("the largest 64-bit usize case should lower");
    assert_valid_module(&unsigned);
    assert!(unsigned.functions[0].blocks[0].body.iter().any(|node| matches!(
        &node.inst,
        Inst::Const {
            ty: TrustIrTy::Usize,
            value: TrustIrConstant::Int(value),
        } if *value == u64::MAX as i128
    )));

    let too_wide = pointer_width_switch_function(
        "usize_switch_too_wide",
        Ty::PtrSizedInt { signed: false },
        u64::MAX as u128 + 1,
    );
    let err = lower_to_trust_ir(&too_wide).expect_err("usize is pinned to 64 bits");
    assert!(matches!(
        err,
        BridgeError::UnsupportedOp(ref message)
            if message.contains("does not fit usize discriminator")
    ));
}

#[test]
fn test_faithful_downcast_field_reads_variant_local_payload_lane() {
    let enum_ty = faithful_enum_ty(
        "test::PayloadLanes",
        Some(EnumReprHint::U8),
        vec![
            VariantDef { name: "A".into(), discriminant: 3, fields: vec![("0".into(), Ty::i32())] },
            VariantDef {
                name: "B".into(),
                discriminant: 9,
                fields: vec![("0".into(), Ty::i64()), ("1".into(), Ty::Bool)],
            },
        ],
    );
    let func = VerifiableFunction {
        name: "payload_lane".into(),
        def_path: "test::payload_lane".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: enum_ty, name: Some("value".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Downcast(1), Projection::Field(0)],
                    })),
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
    };

    let module = lower_to_trust_ir(&func).expect("a faithful payload read should lower");
    assert_valid_module(&module);
    assert!(
        module.functions[0].blocks[0].body.iter().any(|node| matches!(
            &node.inst,
            Inst::ExtractField { ty: TrustIrTy::I64, field: 1, .. }
        ))
    );
    assert!(
        !module.functions[0].blocks[0]
            .body
            .iter()
            .any(|node| matches!(&node.inst, Inst::ExtractField { field: 2, .. }))
    );

    let enum_id = module.enums[0].id;
    let input = InterpretValue {
        ty: TrustIrTy::Enum(enum_id),
        kind: trust_ir::interpret::InterpretValueKind::Aggregate(vec![
            InterpretValue::int(TrustIrTy::U8, 9).unwrap(),
            InterpretValue::int(TrustIrTy::I64, 41).unwrap(),
            InterpretValue::bool(true),
        ]),
    };
    let outcome = Interpreter::with_module(&module)
        .execute_func(trust_ir::FuncId::new(0), vec![input])
        .expect("the faithful payload read should interpret");
    assert_eq!(outcome.returns[0].kind, InterpretValue::int(TrustIrTy::I64, 41).unwrap().kind);
}

fn mismatched_variant_operand_function(faithful: bool, op: BinOp) -> VerifiableFunction {
    let enum_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "test::MismatchedVariantOperands".into(),
        fields: vec![
            ("__tag".into(), Ty::PtrSizedInt { signed: true }),
            ("__v0_0".into(), Ty::i64()),
            ("__v1_0".into(), Ty::u8()),
        ],
        variants: vec![
            VariantDef {
                name: "Wide".into(),
                discriminant: 3,
                fields: vec![("0".into(), Ty::i64())],
            },
            VariantDef {
                name: "Byte".into(),
                discriminant: 9,
                fields: vec![("0".into(), Ty::u8())],
            },
        ],
        disc_index_safe: true,
        faithful_enum_repr: if faithful { Some(Some(EnumReprHint::U8)) } else { None }, enum_layout: None, };
    let return_ty = if op == BinOp::Eq { Ty::Bool } else { Ty::u8() };
    VerifiableFunction {
        name: format!("{}_variant_{op:?}", if faithful { "faithful" } else { "legacy" }),
        def_path: "test::mismatched_variant_operand".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: return_ty.clone(), name: None },
                LocalDecl { index: 1, ty: enum_ty, name: Some("value".into()) },
                LocalDecl { index: 2, ty: Ty::u8(), name: Some("rhs".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        op,
                        Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Downcast(1), Projection::Field(0)],
                        }),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_variant_qualified_operand_types_drive_division_and_comparison() {
    for faithful in [false, true] {
        let expected_lane = if faithful { 1 } else { 2 };
        let div = lower_to_trust_ir(&mismatched_variant_operand_function(faithful, BinOp::Div))
            .expect("a variant-local u8 division should lower");
        assert_valid_module(&div);
        let body = &div.functions[0].blocks[0].body;
        assert!(body.iter().any(|node| matches!(
            &node.inst,
            Inst::ExtractField { ty: TrustIrTy::U8, field, .. } if *field == expected_lane
        )));
        assert!(body.iter().any(|node| matches!(
            &node.inst,
            Inst::BinOp { op: TrustIrBinOp::UDiv, ty: TrustIrTy::U8, .. }
        )));

        let cmp = lower_to_trust_ir(&mismatched_variant_operand_function(faithful, BinOp::Eq))
            .expect("a variant-local u8 comparison should lower");
        assert_valid_module(&cmp);
        assert!(cmp.functions[0].blocks[0].body.iter().any(|node| matches!(
            &node.inst,
            Inst::ICmp { op: ICmpOp::Eq, ty: TrustIrTy::U8, .. }
        )));
    }
}

fn set_discriminant_function(enum_ty: Ty, variant_index: usize) -> VerifiableFunction {
    let return_ty = enum_ty.clone();
    VerifiableFunction {
        name: "set_faithful_discriminant".into(),
        def_path: "test::set_faithful_discriminant".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: enum_ty.clone(), name: None },
                LocalDecl { index: 1, ty: enum_ty, name: Some("value".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::SetDiscriminant { place: Place::local(1), variant_index },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_faithful_set_discriminant_replaces_the_whole_enum_value() {
    let enum_ty = faithful_enum_ty(
        "test::SetDisc",
        Some(EnumReprHint::U8),
        vec![
            VariantDef {
                name: "Payload".into(),
                discriminant: 11,
                fields: vec![("0".into(), Ty::i64())],
            },
            VariantDef { name: "Empty".into(), discriminant: 37, fields: vec![] },
        ],
    );
    let func = set_discriminant_function(enum_ty.clone(), 1);
    let module = lower_to_trust_ir(&func).expect("a fieldless variant change should lower");
    assert_valid_module(&module);
    let enum_id = module.enums[0].id;
    assert!(module.functions[0].blocks[0].body.iter().any(|node| matches!(
        &node.inst,
        Inst::Const {
            ty: TrustIrTy::Enum(id),
            value: TrustIrConstant::Aggregate(fields),
        } if *id == enum_id && fields.as_slice() == [TrustIrConstant::Int(37)]
    )));
    assert!(
        !module.functions[0].blocks[0]
            .body
            .iter()
            .any(|node| matches!(&node.inst, Inst::InsertField { ty: TrustIrTy::Enum(_), .. }))
    );

    let input = InterpretValue {
        ty: TrustIrTy::Enum(enum_id),
        kind: trust_ir::interpret::InterpretValueKind::Aggregate(vec![
            InterpretValue::int(TrustIrTy::U8, 11).unwrap(),
            InterpretValue::int(TrustIrTy::I64, 99).unwrap(),
        ]),
    };
    let outcome = Interpreter::with_module(&module)
        .execute_func(trust_ir::FuncId::new(0), vec![input])
        .expect("the whole-value variant change should interpret");
    assert_eq!(
        outcome.returns[0].kind,
        trust_ir::interpret::InterpretValueKind::Aggregate(vec![
            InterpretValue::int(TrustIrTy::U8, 37).unwrap()
        ])
    );

    let err = lower_to_trust_ir(&set_discriminant_function(enum_ty, 0))
        .expect_err("a payload-bearing target requires staging and must fail closed");
    assert!(matches!(
        err,
        BridgeError::UnsupportedOp(ref message)
            if message.contains("SetDiscriminant to payload-bearing variant 0")
    ));
}

fn i32_const_assign(local: usize, value: i128) -> Statement {
    Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(value))),
        span: SourceSpan::default(),
    }
}

fn local_copy_assign(dest: usize, source: usize) -> Statement {
    Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(source))),
        span: SourceSpan::default(),
    }
}

fn multi_block_local_function(early_read: bool) -> VerifiableFunction {
    VerifiableFunction {
        name: if early_read { "early_read".into() } else { "merged_local".into() },
        def_path: if early_read { "test::early_read".into() } else { "test::merged_local".into() },
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::u8(), name: Some("cond".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("tmp".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: if early_read { vec![local_copy_assign(0, 2)] } else { vec![] },
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![i32_const_assign(2, 10)],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![i32_const_assign(2, 20)],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: if early_read { vec![] } else { vec![local_copy_assign(0, 2)] },
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

fn fieldless_enum_reassignment_function(faithful: bool) -> VerifiableFunction {
    let enum_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "test::FieldlessReassignment".into(),
        fields: vec![("__tag".into(), Ty::i64())],
        variants: vec![
            VariantDef { name: "Initial".into(), discriminant: 0, fields: vec![] },
            VariantDef { name: "Reassigned".into(), discriminant: 1, fields: vec![] },
        ],
        disc_index_safe: true,
        faithful_enum_repr: if faithful { Some(None) } else { None }, enum_layout: None, };
    let variant = |local, index| Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Aggregate(
            AggregateKind::Adt {
                name: "test::FieldlessReassignment".into(),
                variant: index,
                active_field: None,
                args: None,
            },
            vec![],
        ),
        span: SourceSpan::default(),
    };

    VerifiableFunction {
        name: if faithful {
            "faithful_fieldless_reassignment".into()
        } else {
            "legacy_fieldless_reassignment".into()
        },
        def_path: "test::fieldless_reassignment".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: Ty::u8(), name: Some("reassign".into()) },
                LocalDecl { index: 2, ty: enum_ty.clone(), name: Some("value".into()) },
                LocalDecl { index: 3, ty: enum_ty, name: None },
                LocalDecl { index: 4, ty: Ty::i64(), name: None },
                LocalDecl { index: 5, ty: Ty::Unit, name: None },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![variant(2, 0)],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![
                        variant(3, 1),
                        local_copy_assign(2, 3),
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Unit)),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Unit)),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Discriminant(Place::local(2)),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(4)),
                        targets: vec![(0, BlockId(5)), (1, BlockId(4))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![i32_const_assign(0, 99)],
                    terminator: Terminator::Goto(BlockId(6)),
                },
                TrustBlock {
                    id: BlockId(4),
                    stmts: vec![i32_const_assign(0, 2)],
                    terminator: Terminator::Goto(BlockId(6)),
                },
                TrustBlock {
                    id: BlockId(5),
                    stmts: vec![i32_const_assign(0, 1)],
                    terminator: Terminator::Goto(BlockId(6)),
                },
                TrustBlock { id: BlockId(6), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::i64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_promoted_fieldless_enum_reassignment_stores_typed_enum_values() {
    let module = lower_to_trust_ir(&fieldless_enum_reassignment_function(true))
        .expect("a faithful fieldless enum reassignment should lower");
    for (reassign, expected) in [(0, 1), (1, 2)] {
        let outcome = Interpreter::with_module(&module)
            .execute_func(
                trust_ir::FuncId::new(0),
                vec![InterpretValue::int(TrustIrTy::U8, reassign).unwrap()],
            )
            .expect("fieldless enum and promoted-unit stores must remain interpretable");
        assert_eq!(
            outcome.returns[0].kind,
            InterpretValue::int(TrustIrTy::I64, expected).unwrap().kind
        );
    }
}

fn entry_i32_alloca(module: &trust_ir::Module) -> ValueId {
    module.functions[0].blocks[0]
        .body
        .iter()
        .find_map(|node| match (&node.inst, node.results.as_slice()) {
            (Inst::Alloca { ty: TrustIrTy::I32, .. }, [ptr]) => Some(*ptr),
            _ => None,
        })
        .expect("an i32 merge slot")
}

fn assert_no_i32_undef(module: &trust_ir::Module) {
    assert!(
        !module.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .any(|node| matches!(&node.inst, Inst::Undef { ty: TrustIrTy::I32 })),
        "a promoted local must not be initialized from undef"
    );
}

#[test]
fn test_promoted_nonargument_local_starts_uninitialized_and_merges_real_writes() {
    let module = lower_to_trust_ir(&multi_block_local_function(false))
        .expect("a valid multi-block local merge should lower");
    assert_valid_module(&module);
    let ptr = entry_i32_alloca(&module);
    let entry = &module.functions[0].blocks[0];
    assert_no_i32_undef(&module);
    assert!(
        !entry.body.iter().any(
            |node| matches!(&node.inst, Inst::Store { ptr: store_ptr, .. } if *store_ptr == ptr)
        ),
        "a nonargument merge slot must have no fabricated entry store"
    );

    for (cond, expected) in [(1, 10), (0, 20)] {
        let outcome = Interpreter::with_module(&module)
            .execute_func(
                trust_ir::FuncId::new(0),
                vec![InterpretValue::int(TrustIrTy::U8, cond).unwrap()],
            )
            .expect("each valid path stores before the merge load");
        assert_eq!(
            outcome.returns[0].kind,
            InterpretValue::int(TrustIrTy::I32, expected).unwrap().kind
        );
    }
}

#[test]
fn test_promoted_nonargument_early_read_remains_uninitialized_memory_ub() {
    let module = lower_to_trust_ir(&multi_block_local_function(true))
        .expect("the malformed early-read shape should lower without inventing a value");
    assert_valid_module(&module);
    let ptr = entry_i32_alloca(&module);
    let entry = &module.functions[0].blocks[0];
    assert_no_i32_undef(&module);
    assert!(entry.body.iter().any(|node| matches!(
        &node.inst,
        Inst::Load { ty: TrustIrTy::I32, ptr: load_ptr, .. } if *load_ptr == ptr
    )));
    assert!(
        !entry.body.iter().any(
            |node| matches!(&node.inst, Inst::Store { ptr: store_ptr, .. } if *store_ptr == ptr)
        )
    );

    let err = Interpreter::with_module(&module)
        .execute_func(
            trust_ir::FuncId::new(0),
            vec![InterpretValue::int(TrustIrTy::U8, 1).unwrap()],
        )
        .expect_err("loading the merge slot before a real write is UB");
    assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior);
    assert!(err.message.contains("uninitialized"), "unexpected interpreter error: {err:?}");
}

#[test]
fn test_promoted_argument_slot_preserves_the_entry_parameter() {
    let func = VerifiableFunction {
        name: "promoted_argument".into(),
        def_path: "test::promoted_argument".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("value".into()) },
                LocalDecl { index: 2, ty: Ty::u8(), name: Some("choice".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![i32_const_assign(1, 10)],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![i32_const_assign(1, 20)],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                TrustBlock {
                    id: BlockId(4),
                    stmts: vec![local_copy_assign(0, 1)],
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
    };
    let module = lower_to_trust_ir(&func).expect("a promoted argument should lower");
    assert_valid_module(&module);
    assert_no_i32_undef(&module);
    let ptr = entry_i32_alloca(&module);
    let entry = &module.functions[0].blocks[0];
    let entry_value = entry.params[0].0;
    assert!(entry.body.iter().any(|node| matches!(
        &node.inst,
        Inst::Store {
            ty: TrustIrTy::I32,
            ptr: store_ptr,
            value,
            ..
        } if *store_ptr == ptr && *value == entry_value
    )));

    let outcome = Interpreter::with_module(&module)
        .execute_func(
            trust_ir::FuncId::new(0),
            vec![
                InterpretValue::int(TrustIrTy::I32, 42).unwrap(),
                InterpretValue::int(TrustIrTy::U8, 2).unwrap(),
            ],
        )
        .expect("the no-overwrite path should observe the entry parameter");
    assert_eq!(outcome.returns[0].kind, InterpretValue::int(TrustIrTy::I32, 42).unwrap().kind);
}

#[test]
fn test_downcast_then_nested_aggregate_field_resets_active_variant() {
    // Trust (#46): a `Downcast(V)` records the active variant for ONLY the
    // immediately-following field lookup. Projecting a field of a variant payload
    // that is ITSELF an aggregate — e.g. `Some((a, b)).0.1`, the shape an
    // `enumerate`/`zip` desugar produces (`Option<(usize, &T)>`) — must reset the
    // active variant after that first field, or the inner tuple-field projection
    // fails with "Field projection on non-ADT with active variant N". Regression
    // for the stale-`active_variant` bug in `resolve_place`.
    let payload = Ty::Tuple(vec![Ty::u64(), Ty::u64()]);
    let option_ty = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "std::option::Option".into(),
        // ty_convert encodes a variant's field as `__v{variant}_{field}`; Some is
        // variant 1, its single payload field is `__v1_0` (here the (u64, u64) tuple).
        fields: vec![("__v1_0".into(), payload.clone())],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "downcast_nested_field".to_string(),
        def_path: "test::downcast_nested_field".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: option_ty, name: Some("o".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![
                            Projection::Downcast(1), // as Some
                            Projection::Field(0),    // the (u64, u64) tuple payload
                            Projection::Field(1),    // its second element — must NOT
                                                     // re-apply the `__v1_` prefix
                        ],
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func)
        .expect("nested aggregate field through a variant downcast should lower");
    assert_valid_module(&module);
    let body = &module.functions[0].blocks[0].body;
    let extracts = body.iter().filter(|n| matches!(&n.inst, Inst::ExtractField { .. })).count();
    assert!(
        extracts >= 2,
        "should ExtractField the payload tuple then its element (got {extracts})"
    );
}

#[test]
fn test_projected_binary_rvalue_store_rebuilds_aggregate() {
    let tuple_ty = Ty::Tuple(vec![Ty::i64(), Ty::i64()]);
    let func = VerifiableFunction {
        name: "projected_binary_store".to_string(),
        def_path: "test::projected_binary_store".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: tuple_ty.clone(), name: None },
                LocalDecl { index: 1, ty: tuple_ty.clone(), name: Some("t".into()) },
                LocalDecl { index: 2, ty: Ty::i64(), name: Some("a".into()) },
                LocalDecl { index: 3, ty: Ty::i64(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place { local: 1, projections: vec![Projection::Field(1)] },
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 3,
            return_ty: tuple_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("projected BinaryOp destination should lower");
    assert_valid_module(&module);
    let body = &module.functions[0].blocks[0].body;
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::BinOp { op: TrustIrBinOp::Add, .. })),
        "projected BinaryOp assignment should still compute the rvalue"
    );
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::InsertField { field: 1, .. })),
        "projected BinaryOp assignment should write the computed value into the aggregate"
    );
}

#[test]
fn test_array_index_projected_store_emits_insert_element() {
    let array_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 4 };
    let func = VerifiableFunction {
        name: "array_index_store".to_string(),
        def_path: "test::array_index_store".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: array_ty.clone(), name: None },
                LocalDecl { index: 1, ty: array_ty.clone(), name: Some("arr".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("v".into()) },
                LocalDecl { index: 3, ty: Ty::usize(), name: Some("idx".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place { local: 1, projections: vec![Projection::Index(3)] },
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 3,
            return_ty: array_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("array projected store should lower");
    assert_valid_module(&module);
    assert!(
        module.functions[0].blocks[0]
            .body
            .iter()
            .any(|node| matches!(&node.inst, Inst::InsertElement { .. })),
        "array projected store should rebuild the array with InsertElement"
    );
}

#[test]
fn test_fetch_nand_atomic_rejected() {
    let func = VerifiableFunction {
        name: "fetch_nand".to_string(),
        def_path: "test::fetch_nand".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u64()) },
                    name: Some("ptr".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                    func: "atomic_fetch_nand".to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: Some(AtomicOperation {
                        place: Place::local(1),
                        dest: Some(Place::local(0)),
                        op_kind: AtomicOpKind::FetchNand,
                        ordering: AtomicOrdering::SeqCst,
                        failure_ordering: None,
                        span: SourceSpan::default(),
                    }),
                },
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("string-derived atomic metadata is quarantined");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(msg) if msg.contains("compiler-authenticated"))
    );
}

#[test]
fn test_atomic_store_metadata_without_authenticated_evidence_rejected() {
    let func = VerifiableFunction {
        name: "atomic_store_operand".to_string(),
        def_path: "test::atomic_store_operand".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u64()) },
                    name: Some("ptr".into()),
                },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "atomic_store_release".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(5, 64)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: Some(AtomicOperation {
                            place: Place::local(1),
                            dest: None,
                            op_kind: AtomicOpKind::Store,
                            ordering: AtomicOrdering::Release,
                            failure_ordering: None,
                            span: SourceSpan::default(),
                        }),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("atomic store metadata must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(msg) if msg.contains("compiler-authenticated"))
    );
}

#[test]
fn test_atomic_load_metadata_without_authenticated_evidence_rejected() {
    let func = VerifiableFunction {
        name: "atomic_load_dest".to_string(),
        def_path: "test::atomic_load_dest".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
                    name: Some("ptr".into()),
                },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "atomic_load_acquire".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: Some(AtomicOperation {
                            place: Place::local(1),
                            dest: Some(Place::local(0)),
                            op_kind: AtomicOpKind::Load,
                            ordering: AtomicOrdering::Acquire,
                            failure_ordering: None,
                            span: SourceSpan::default(),
                        }),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("atomic load metadata must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(msg) if msg.contains("compiler-authenticated"))
    );
}

#[test]
fn test_atomic_fetch_add_metadata_without_authenticated_evidence_rejected() {
    let func = VerifiableFunction {
        name: "atomic_fetch_add_operand".to_string(),
        def_path: "test::atomic_fetch_add_operand".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u64()) },
                    name: Some("ptr".into()),
                },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "atomic_fetch_add".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(3, 64)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: Some(AtomicOperation {
                            place: Place::local(1),
                            dest: Some(Place::local(0)),
                            op_kind: AtomicOpKind::FetchAdd,
                            ordering: AtomicOrdering::SeqCst,
                            failure_ordering: None,
                            span: SourceSpan::default(),
                        }),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("atomic RMW metadata must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(msg) if msg.contains("compiler-authenticated"))
    );
}

#[test]
fn test_atomic_fetch_min_metadata_without_authenticated_evidence_rejected() {
    let func = VerifiableFunction {
        name: "atomic_fetch_min_unsigned".to_string(),
        def_path: "test::atomic_fetch_min_unsigned".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u64()) },
                    name: Some("ptr".into()),
                },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "atomic_fetch_min".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(2, 64)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: Some(AtomicOperation {
                            place: Place::local(1),
                            dest: Some(Place::local(0)),
                            op_kind: AtomicOpKind::FetchMin,
                            ordering: AtomicOrdering::SeqCst,
                            failure_ordering: None,
                            span: SourceSpan::default(),
                        }),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("atomic fetch_min metadata must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(msg) if msg.contains("compiler-authenticated"))
    );
}

#[test]
fn test_atomic_compare_exchange_metadata_without_authenticated_evidence_rejected() {
    let func = VerifiableFunction {
        name: "atomic_cxchg_tuple".to_string(),
        def_path: "test::atomic_cxchg_tuple".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u64()) },
                    name: Some("ptr".into()),
                },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "atomic_compare_exchange".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(10, 64)),
                            Operand::Constant(ConstValue::Uint(11, 64)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: Some(AtomicOperation {
                            place: Place::local(1),
                            dest: Some(Place::local(0)),
                            op_kind: AtomicOpKind::CompareExchange,
                            ordering: AtomicOrdering::AcqRel,
                            failure_ordering: Some(AtomicOrdering::Acquire),
                            span: SourceSpan::default(),
                        }),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("compare-exchange metadata must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(msg) if msg.contains("compiler-authenticated"))
    );
}

#[test]
fn test_error_display() {
    let e = BridgeError::UnsupportedType("Ref { .. }".to_string());
    assert_eq!(e.to_string(), "unsupported type: Ref { .. }");

    let e = BridgeError::UnsupportedOp("calls".to_string());
    assert_eq!(e.to_string(), "unsupported operation: calls");

    let e = BridgeError::MissingBlock(5);
    assert_eq!(e.to_string(), "missing block: bb5");

    let e = BridgeError::MissingLocal(3);
    assert_eq!(e.to_string(), "missing local: _3");
}

#[test]
fn test_lower_assert_terminator() {
    use trust_types::AssertMessage;

    let func = VerifiableFunction {
        name: "assert_fn".to_string(),
        def_path: "test::assert_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("cond".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::local(1)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];

    let has_assert = bb0.body.iter().any(|n| matches!(&n.inst, Inst::Assert { .. }));
    assert!(has_assert, "should have an Assert instruction");

    // Item T1 (LANDED): a `BoundsCheck` assert produces the faithful per-site
    // `BoundsCheck` obligation (NOT `PanicFreedom`).
    let has_bounds_check = module
        .proof_obligations
        .iter()
        .any(|po| matches!(po.kind, trust_ir::proof::ObligationKind::BoundsCheck));
    assert!(has_bounds_check, "bounds assert should generate a BoundsCheck obligation");

    // An `Assert`-bearing fn surfaces NO function-level PanicFreedom aggregate:
    // the lowering emits that aggregate only for diverging-panic `Call`
    // terminators, not for `Assert` sites (w01/w13/w16/w19 completeness fix).
    let has_panic_freedom = module
        .proof_obligations
        .iter()
        .any(|po| matches!(po.kind, trust_ir::proof::ObligationKind::PanicFreedom));
    assert!(!has_panic_freedom, "Assert-bearing fn must surface no aggregate PanicFreedom");
}

#[test]
fn test_lower_aggregate_construction() {
    let func = VerifiableFunction {
        name: "agg_fn".to_string(),
        def_path: "test::agg_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::i32(), Ty::i32()]), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        trust_types::AggregateKind::Tuple,
                        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Tuple(vec![Ty::i32(), Ty::i32()]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("aggregate should lower");
    let bb0 = &module.functions[0].blocks[0];

    // Should have Undef + InsertField + InsertField + Return.
    let has_undef = bb0.body.iter().any(|n| {
        matches!(
            &n.inst,
            Inst::Undef { ty: TrustIrTy::Tuple(fields) }
                if fields.as_slice() == [TrustIrTy::I32, TrustIrTy::I32]
        )
    });
    assert!(has_undef, "aggregate construction should start with Undef");

    let insert_count =
        bb0.body.iter().filter(|n| matches!(&n.inst, Inst::InsertField { .. })).count();
    assert_eq!(insert_count, 2, "should have 2 InsertField instructions for 2-element tuple");
}

#[test]
fn test_lower_fat_raw_ptr_aggregate_to_slice_fat_ptr() {
    let data_ptr_ty = Ty::RawPtr { pointee: Box::new(Ty::u8()), mutable: false };
    let slice_ptr_ty =
        Ty::RawPtr { pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }), mutable: false };
    let func = VerifiableFunction {
        name: "fat_raw_ptr_agg_fn".to_string(),
        def_path: "test::fat_raw_ptr_agg_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: data_ptr_ty, name: Some("data".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("len".into()) },
                LocalDecl { index: 3, ty: slice_ptr_ty, name: Some("out".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::RawPtr {
                            pointee_ty: Ty::Slice { elem: Box::new(Ty::u8()) },
                            mutable: false,
                        },
                        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("fat raw pointer aggregate should lower");
    let bb0 = &module.functions[0].blocks[0];
    // Trust (B2-1b): the aggregate assembles the FORMAT's first-class fat pointer
    // via PtrFromParts at FatPtr(Slice(elem TyId)) with the canonical U64 metadata
    // lane — the anonymous Undef+InsertField tuple lanes are retired.
    let u8_tid = module
        .types
        .iter()
        .position(|t| *t == TrustIrTy::U8)
        .expect("u8 slice element should be interned in the module types table");
    let fat_ty =
        TrustIrTy::FatPtr(trust_ir::FatPtrKind::Slice(trust_ir::value::TyId::new(u8_tid as u32)));
    assert!(
        bb0.body.iter().any(|n| matches!(
            &n.inst,
            Inst::PtrFromParts { ptr_ty, metadata_ty: TrustIrTy::U64, .. } if *ptr_ty == fat_ty
        )),
        "fat raw pointer aggregate should assemble data + usize metadata via PtrFromParts \
         at the first-class slice fat type"
    );
    assert!(
        !bb0.body.iter().any(|n| matches!(
            &n.inst,
            Inst::InsertField { .. } | Inst::Undef { ty: TrustIrTy::Tuple(_) }
        )),
        "the legacy anonymous tuple spelling (Undef + InsertField lanes) is retired"
    );
}

#[test]
fn test_lower_array_ref_to_slice_ref_cast_builds_fat_pointer() {
    let array_ref_ty =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Array { elem: Box::new(Ty::u8()), len: 4 }) };
    let slice_ref_ty =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
    let func = VerifiableFunction {
        name: "array_ref_to_slice_ref_cast_fn".to_string(),
        def_path: "test::array_ref_to_slice_ref_cast_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: slice_ref_ty.clone(), name: None },
                LocalDecl { index: 1, ty: array_ref_ty, name: Some("array".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), slice_ref_ty),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Ref {
                mutable: false,
                inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
            },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("array ref to slice ref cast should lower");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    // Trust (B2-1b): the length lane is the canonical U64 metadata, and the
    // coerced value is assembled via PtrFromParts at the TARGET's first-class
    // FatPtr(Slice(elem TyId)) spelling (InsertField tuple lanes retired).
    assert!(
        bb0.body.iter().any(|n| {
            matches!(&n.inst, Inst::Const { ty: TrustIrTy::U64, value: TrustIrConstant::Int(4) })
        }),
        "array-to-slice cast should materialize the array length metadata at U64"
    );
    let u8_tid = module
        .types
        .iter()
        .position(|t| *t == TrustIrTy::U8)
        .expect("u8 slice element should be interned in the module types table");
    let fat_ty =
        TrustIrTy::FatPtr(trust_ir::FatPtrKind::Slice(trust_ir::value::TyId::new(u8_tid as u32)));
    assert!(
        bb0.body.iter().any(|n| matches!(
            &n.inst,
            Inst::PtrFromParts { ptr_ty, metadata_ty: TrustIrTy::U64, .. } if *ptr_ty == fat_ty
        )),
        "array-to-slice cast should assemble data + length lanes via PtrFromParts \
         at the target's slice fat type"
    );
    assert!(
        !bb0.body.iter().any(|n| matches!(n.inst, Inst::Cast { .. })),
        "array-to-slice cast must not lower to a thin-pointer bitcast"
    );
}

#[test]
fn test_lower_array_raw_ptr_to_slice_raw_ptr_cast_builds_fat_pointer() {
    let array_ptr_ty = Ty::RawPtr {
        mutable: false,
        pointee: Box::new(Ty::Array { elem: Box::new(Ty::i32()), len: 3 }),
    };
    let slice_ptr_ty =
        Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Slice { elem: Box::new(Ty::i32()) }) };
    let func = VerifiableFunction {
        name: "array_raw_ptr_to_slice_raw_ptr_cast_fn".to_string(),
        def_path: "test::array_raw_ptr_to_slice_raw_ptr_cast_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: slice_ptr_ty.clone(), name: None },
                LocalDecl { index: 1, ty: array_ptr_ty, name: Some("array".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), slice_ptr_ty),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::RawPtr {
                mutable: false,
                pointee: Box::new(Ty::Slice { elem: Box::new(Ty::i32()) }),
            },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module =
        lower_to_trust_ir(&func).expect("array raw ptr to slice raw ptr cast should lower");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    // Trust (B2-1b): U64 length metadata + PtrFromParts at the target's
    // first-class FatPtr(Slice(i32 TyId)) spelling (InsertField lanes retired).
    assert!(
        bb0.body.iter().any(|n| {
            matches!(&n.inst, Inst::Const { ty: TrustIrTy::U64, value: TrustIrConstant::Int(3) })
        }),
        "array raw pointer to slice raw pointer cast should materialize array length metadata at U64"
    );
    let i32_tid = module
        .types
        .iter()
        .position(|t| *t == TrustIrTy::I32)
        .expect("i32 slice element should be interned in the module types table");
    let fat_ty =
        TrustIrTy::FatPtr(trust_ir::FatPtrKind::Slice(trust_ir::value::TyId::new(i32_tid as u32)));
    assert!(
        bb0.body.iter().any(|n| matches!(
            &n.inst,
            Inst::PtrFromParts { ptr_ty, metadata_ty: TrustIrTy::U64, .. } if *ptr_ty == fat_ty
        )),
        "raw pointer array-to-slice cast should construct the two-lane fat pointer via PtrFromParts"
    );
    assert!(
        !bb0.body.iter().any(|n| matches!(n.inst, Inst::Cast { .. })),
        "raw pointer array-to-slice cast must not lower to a thin-pointer bitcast"
    );
}

#[test]
fn test_lower_fat_raw_ptr_aggregate_rejects_dyn_vtable() {
    let data_ptr_ty = Ty::RawPtr { pointee: Box::new(Ty::u8()), mutable: false };
    let dyn_ptr_ty = Ty::RawPtr {
        pointee: Box::new(Ty::Dynamic { trait_name: "Debug".into() }),
        mutable: false,
    };
    let func = VerifiableFunction {
        name: "fat_raw_ptr_dyn_fn".to_string(),
        def_path: "test::fat_raw_ptr_dyn_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: data_ptr_ty, name: Some("data".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("vtable".into()) },
                LocalDecl { index: 3, ty: dyn_ptr_ty, name: Some("out".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::RawPtr {
                            pointee_ty: Ty::Dynamic { trait_name: "Debug".into() },
                            mutable: false,
                        },
                        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("dyn raw pointer metadata must fail closed");
    assert!(matches!(
        err,
        BridgeError::UnsupportedOp(msg) if msg.contains("vtable metadata lane")
    ));
}

#[test]
fn test_lower_address_of_slice_subslice_preserves_metadata() {
    let slice_ptr_ty =
        Ty::RawPtr { pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }), mutable: false };
    let func = VerifiableFunction {
        name: "addr_of_slice_subslice_fn".to_string(),
        def_path: "test::addr_of_slice_subslice_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: slice_ptr_ty.clone(), name: None },
                LocalDecl { index: 1, ty: slice_ptr_ty, name: Some("slice".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::AddressOf(
                        false,
                        Place {
                            local: 1,
                            projections: vec![
                                Projection::Deref,
                                Projection::Subslice { from: 1, to: 1, from_end: true },
                            ],
                        },
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::RawPtr {
                pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                mutable: false,
            },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("address-of slice subslice should lower");
    let bb0 = &module.functions[0].blocks[0];
    // Trust (B2-1b): the source length is read via PtrMetadata at the canonical
    // U64 lane, trimmed with U64 arithmetic, and the subslice is reassembled via
    // PtrFromParts (the InsertField metadata lane retired with the tuple model).
    assert!(
        bb0.body
            .iter()
            .any(|n| matches!(n.inst, Inst::PtrMetadata { metadata_ty: TrustIrTy::U64, .. })),
        "from_end address subslice should read the source fat-pointer metadata lane"
    );
    assert!(
        bb0.body.iter().any(|n| matches!(
            n.inst,
            Inst::BinOp { op: TrustIrBinOp::Sub, ty: TrustIrTy::U64, .. }
        )),
        "from_end address subslice should derive length from source metadata at U64"
    );
    let ptr_ty = bb0
        .body
        .iter()
        .find_map(|n| match &n.inst {
            Inst::PtrFromParts { ptr_ty, metadata_ty: TrustIrTy::U64, .. } => Some(ptr_ty),
            _ => None,
        })
        .expect("address-of slice subslice should preserve a U64 metadata lane");
    assert_slice_fat_ptr_element(&module, ptr_ty, &TrustIrTy::U8);
}

#[test]
fn test_lower_ref_direct_local_materializes_borrow() {
    let ref_ty = Ty::Ref { mutable: false, inner: Box::new(Ty::i64()) };
    let func = VerifiableFunction {
        name: "ref_direct_local".to_string(),
        def_path: "test::ref_direct_local".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ref_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: ref_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("direct local ref should lower");
    assert_valid_module(&module);
    let body = &module.functions[0].blocks[0].body;
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::Alloca { ty: TrustIrTy::I64, .. })),
        "taking a local reference should materialize addressable storage"
    );
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::Borrow { .. })),
        "shared Ref should emit a TrustIr Borrow"
    );
    assert!(
        body.iter()
            .any(|node| node.proofs.contains(&trust_ir::proof::ProofAnnotation::SharedBorrow)),
        "shared Ref should carry a SharedBorrow proof annotation"
    );
}

#[test]
fn test_address_taken_local_assignment_updates_storage_and_reads_load() {
    let ref_ty = Ty::Ref { mutable: false, inner: Box::new(Ty::i64()) };
    let func = VerifiableFunction {
        name: "address_taken_local_coherence".to_string(),
        def_path: "test::address_taken_local_coherence".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: ref_ty, name: Some("r".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(99))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("address-taken local should stay coherent");
    assert_valid_module(&module);
    let body = &module.functions[0].blocks[0].body;
    let slot = body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::Alloca { ty: TrustIrTy::I64, .. } => node.results.first().copied(),
            _ => None,
        })
        .expect("taking &x should allocate storage for x");
    let stores_to_slot = body
        .iter()
        .filter(
            |node| matches!(&node.inst, Inst::Store { ty: TrustIrTy::I64, ptr, .. } if *ptr == slot),
        )
        .count();
    assert!(
        stores_to_slot >= 2,
        "initial materialization and later x assignment should both store into x storage"
    );
    assert!(
        body.iter().any(
            |node| matches!(&node.inst, Inst::Load { ty: TrustIrTy::I64, ptr, .. } if *ptr == slot)
        ),
        "reading x after its address is taken should load from authoritative storage"
    );
}

#[test]
fn test_lower_array_subslice_value_is_fixed_array() {
    let array_ty = Ty::Array { elem: Box::new(Ty::i32()), len: 5 };
    let subslice_ty = Ty::Array { elem: Box::new(Ty::i32()), len: 2 };
    let func = VerifiableFunction {
        name: "array_subslice_value_fn".to_string(),
        def_path: "test::array_subslice_value_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: subslice_ty, name: Some("out".into()) },
                LocalDecl { index: 2, ty: array_ty, name: Some("arr".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 2,
                        projections: vec![Projection::Subslice { from: 1, to: 3, from_end: false }],
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("array subslice value should lower");
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|n| matches!(&n.inst, Inst::Undef { ty: TrustIrTy::Array(_, 2) })),
        "array subslice should build a fixed-size array"
    );
    assert_eq!(
        bb0.body.iter().filter(|n| matches!(n.inst, Inst::InsertElement { .. })).count(),
        2,
        "array subslice 1..3 should insert two elements"
    );
    assert!(
        !bb0.body.iter().any(|n| matches!(n.inst, Inst::InsertField { field: 1, .. })),
        "array subslice value must not synthesize slice metadata"
    );
}

#[test]
fn test_lower_address_of_array_subslice_is_thin_array_pointer() {
    let array_ty = Ty::Array { elem: Box::new(Ty::i32()), len: 5 };
    let ptr_ty = Ty::RawPtr {
        pointee: Box::new(Ty::Array { elem: Box::new(Ty::i32()), len: 2 }),
        mutable: false,
    };
    let func = VerifiableFunction {
        name: "addr_of_array_subslice_fn".to_string(),
        def_path: "test::addr_of_array_subslice_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ptr_ty.clone(), name: None },
                LocalDecl { index: 1, ty: array_ty, name: Some("arr".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::AddressOf(
                        false,
                        Place {
                            local: 1,
                            projections: vec![Projection::Subslice {
                                from: 1,
                                to: 3,
                                from_end: false,
                            }],
                        },
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: ptr_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("address-of array subslice should lower");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|n| matches!(&n.inst, Inst::Alloca { ty: TrustIrTy::Array(_, 5), .. })),
        "address-of array subslice should materialize addressable array storage"
    );
    assert!(
        bb0.body.iter().any(|n| matches!(n.inst, Inst::GEP { .. })),
        "address-of array subslice should lower to pointer arithmetic, not a copied array value"
    );
    assert!(
        !bb0.body.iter().any(|n| matches!(&n.inst, Inst::Undef { ty: TrustIrTy::Array(_, 2) })),
        "address-of array subslice must not construct a temporary array value"
    );
    assert!(
        !bb0.body.iter().any(|n| matches!(n.inst, Inst::InsertField { field: 1, .. })),
        "address-of array subslice must not synthesize slice metadata"
    );
}

#[test]
fn test_lower_discriminant_rvalue() {
    let func = VerifiableFunction {
        name: "discr_fn".to_string(),
        def_path: "test::discr_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Adt { adt_kind: None, layout: None, 
                        variants: Vec::new(),
                        name: "MyEnum".to_string(),
                        fields: vec![
                            ("payload".to_string(), Ty::i32()),
                            ("tag".to_string(), Ty::u64()),
                        ],
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, },
                    name: Some("e".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("discriminant should lower");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    let has_extract = bb0
        .body
        .iter()
        .any(|n| matches!(&n.inst, Inst::ExtractField { field: 1, ty: TrustIrTy::U64, .. }));
    assert!(has_extract, "Discriminant should extract the explicit tag field");
}

#[test]
fn test_lower_discriminant_rvalue_untagged_adt_fails_closed() {
    let func = VerifiableFunction {
        name: "discr_untagged_fn".to_string(),
        def_path: "test::discr_untagged_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Adt { adt_kind: None, layout: None, 
                        variants: Vec::new(),
                        name: "Untagged".to_string(),
                        fields: vec![("payload".to_string(), Ty::i32())],
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, },
                    name: Some("e".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("untagged discriminant read must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(ref msg) if msg.contains("no explicit discriminant/tag field")),
        "expected explicit tag diagnostic, got {err:?}"
    );
}

#[test]
fn test_lower_discriminant_rvalue_result_type_mismatch_fails_closed() {
    let func = VerifiableFunction {
        name: "discr_mismatch_fn".to_string(),
        def_path: "test::discr_mismatch_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Adt { adt_kind: None, layout: None, 
                        variants: Vec::new(),
                        name: "Tagged".to_string(),
                        fields: vec![("tag".to_string(), Ty::u8())],
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, },
                    name: Some("e".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("mismatched discriminant type must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(ref msg) if msg.contains("does not match explicit discriminant/tag field type")),
        "expected discriminant type mismatch diagnostic, got {err:?}"
    );
}

/// Trust (disc-read, READ-side mirror of the write-side bare-Int arm in
/// `lower_set_discriminant`): a `Discriminant` READ on a place whose LOWERED
/// type is a bare `Ty::Int` — an enum the extractor erased to just its tag
/// scalar, so there is no `Ty::Adt` wrapper and no explicit `__tag` field to
/// extract — must lower as a FRESH UNCONSTRAINED value of the dest type
/// (havoc), never the old hard `Err` that aborted the WHOLE function's
/// lowering (live victim: `proof_carrying::classify` in ny-cert). No Const
/// and no Assume may be emitted: the havoc'd value carries no fact, so it can
/// never discharge a bound (no false proof); precision-only loss.
#[test]
fn test_lower_discriminant_read_bare_int_havocs_dest() {
    let func = VerifiableFunction {
        name: "discr_bare_int".to_string(),
        def_path: "test::discr_bare_int".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::isize(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 64, signed: true },
                    name: Some("e".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::isize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func)
        .expect("bare-Int Discriminant read must lower (fresh unconstrained dest), not Err");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|n| matches!(&n.inst, Inst::Undef { ty } if *ty == TrustIrTy::I64)),
        "expected a fresh unconstrained I64 (Undef) discriminant value"
    );
    assert!(
        !bb0.body.iter().any(|n| matches!(&n.inst, Inst::Const { .. })),
        "bare-Int Discriminant read must not materialize any constant"
    );
    assert!(
        !bb0.body.iter().any(|n| matches!(&n.inst, Inst::Assume { .. })),
        "bare-Int Discriminant read must not emit any Assume (no synthesized range fact)"
    );
}

/// Fail-closed pin for the carve-out above: the bare-Int arm matches EXACTLY
/// `Ty::Int` — a `Discriminant` read on any other non-enum scalar (here
/// `Ty::Bool`) must still hard-error.
#[test]
fn test_lower_discriminant_read_bare_bool_still_fails_closed() {
    let func = VerifiableFunction {
        name: "discr_bare_bool".to_string(),
        def_path: "test::discr_bare_bool".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::isize(), name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("e".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::isize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err =
        lower_to_trust_ir(&func).expect_err("non-Int non-Adt Discriminant read must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(ref msg) if msg.contains("SetDiscriminant is modeled only")),
        "expected the fail-closed UnsupportedOp diagnostic, got {err:?}"
    );
}

// Trust: enum-disc-full-native — the `Discriminant` read emits the
// `Assume(min_disc <= tag <= max_disc)` range fact ONLY when the enum is
// classified `disc_index_safe` AND its discriminants are non-negative.

/// Build a one-statement `tag = Discriminant(e)` function over an enum local
/// whose `__tag` is isize, with the given variant discriminants and
/// `disc_index_safe` flag.
fn discriminant_range_fixture(discs: &[i128], disc_index_safe: bool) -> VerifiableFunction {
    let variants: Vec<trust_types::VariantDef> = discs
        .iter()
        .enumerate()
        .map(|(i, d)| trust_types::VariantDef {
            name: format!("V{i}"),
            discriminant: *d,
            fields: vec![],
        })
        .collect();
    let enum_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "DiscEnum".to_string(),
        // `__tag` is the signed pointer-width int the extractor synthesizes.
        fields: vec![("__tag".to_string(), Ty::isize())],
        variants,
        disc_index_safe,
        faithful_enum_repr: None, enum_layout: None, };
    VerifiableFunction {
        name: "disc_range".to_string(),
        def_path: "test::disc_range".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::isize(), name: None },
                LocalDecl { index: 1, ty: enum_ty, name: Some("e".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::isize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn count_assumes(module: &trust_ir::Module) -> usize {
    module.functions[0].blocks[0]
        .body
        .iter()
        .filter(|n| matches!(&n.inst, Inst::Assume { .. }))
        .count()
}

#[test]
fn test_discriminant_emits_range_assumes_when_safe_and_nonneg() {
    // Direct-tag-encoded, non-negative discriminants 0..=3, classified safe.
    let func = discriminant_range_fixture(&[0, 1, 2, 3], true);
    let module = lower_to_trust_ir(&func).expect("safe discriminant should lower");
    assert_valid_module(&module);
    // Exactly two Assume facts: `0 <= tag` and `tag <= 3`.
    assert_eq!(
        count_assumes(&module),
        2,
        "a safe, non-negative enum should emit both discriminant range bounds"
    );
    // Both bounds use signed comparison (Sle) on the isize tag.
    let sle_cmps = module.functions[0].blocks[0]
        .body
        .iter()
        .filter(|n| matches!(&n.inst, Inst::ICmp { op: ICmpOp::Sle, .. }))
        .count();
    assert_eq!(sle_cmps, 2, "both range bounds compare with signed Sle");
}

#[test]
fn test_discriminant_no_assume_when_not_disc_index_safe() {
    // Same shape, but NOT classified safe (the niche/fail-closed case) — no Assume.
    let func = discriminant_range_fixture(&[0, 1, 2, 3], false);
    let module =
        lower_to_trust_ir(&func).expect("unsafe-classified discriminant should still lower");
    assert_valid_module(&module);
    assert_eq!(
        count_assumes(&module),
        0,
        "a non-disc_index_safe enum must NOT emit a discriminant range fact (fail-closed)"
    );
}

#[test]
fn test_discriminant_no_assume_when_negative_discriminant() {
    // Classified safe, but a NEGATIVE discriminant: the later `as usize` Bitcast
    // reinterprets the negative tag as ~2^64, so a signed lower bound does not
    // bound the unsigned index — GATE-NONNEG must suppress the fact.
    let func = discriminant_range_fixture(&[-1, 0, 1], true);
    let module = lower_to_trust_ir(&func).expect("negative-disc discriminant should still lower");
    assert_valid_module(&module);
    assert_eq!(
        count_assumes(&module),
        0,
        "a negative-discriminant enum must NOT emit the range fact (bitcast unsoundness)"
    );
}

#[test]
fn test_discriminant_cross_width_u8_dest_isize_tag_bounds_and_assigns() {
    // The REAL `#[repr(u8)]` MIR shape: `__tag` is isize but the `Discriminant`
    // dest local is `u8` (rustc types the discriminant read at the repr type).
    // The gated path must produce a well-typed `u8` dest constrained to the
    // discriminant range — NOT fail closed on the isize/u8 width mismatch.
    let variants: Vec<trust_types::VariantDef> = (0..4i128)
        .map(|d| trust_types::VariantDef { name: format!("V{d}"), discriminant: d, fields: vec![] })
        .collect();
    let enum_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "ReprU8".to_string(),
        fields: vec![("__tag".to_string(), Ty::isize())],
        variants,
        disc_index_safe: true,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "disc_u8".to_string(),
        def_path: "test::disc_u8".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                // dest is u8 — the repr discriminant type, NOT isize.
                LocalDecl { index: 0, ty: Ty::u8(), name: None },
                LocalDecl { index: 1, ty: enum_ty, name: Some("e".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u8(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let module =
        lower_to_trust_ir(&func).expect("cross-width u8 discriminant must lower (not fail closed)");
    assert_valid_module(&module);
    // Two range Assumes, in UNSIGNED u8 comparison (Ule) since dest is u8.
    assert_eq!(count_assumes(&module), 2, "u8-dest safe enum should emit both range bounds");
    let ule_cmps = module.functions[0].blocks[0]
        .body
        .iter()
        .filter(|n| matches!(&n.inst, Inst::ICmp { op: ICmpOp::Ule, .. }))
        .count();
    assert_eq!(ule_cmps, 2, "u8 dest uses unsigned Ule comparison for both bounds");
}

#[test]
fn test_discriminant_range_assume_uses_true_min_max() {
    // Explicit discriminants 0, 5, 10 — the bound must use min=0, max=10
    // (not variant count), so an `arr[e as usize]` over a [T; 11] proves while
    // [T; 10] would not. We check the emitted constants include 10 and 0.
    let func = discriminant_range_fixture(&[0, 5, 10], true);
    let module = lower_to_trust_ir(&func).expect("explicit-disc enum should lower");
    assert_valid_module(&module);
    let consts: Vec<i128> = module.functions[0].blocks[0]
        .body
        .iter()
        .filter_map(|n| match &n.inst {
            Inst::Const { value: TrustIrConstant::Int(v), .. } => Some(*v),
            _ => None,
        })
        .collect();
    assert!(consts.contains(&10), "upper bound must be the max discriminant 10, got {consts:?}");
    assert!(consts.contains(&0), "lower bound must be the min discriminant 0, got {consts:?}");
    assert_eq!(count_assumes(&module), 2);
}

#[test]
fn test_lower_set_discriminant_explicit_tag_inserts_tag_field() {
    let enum_ty = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "Tagged".into(),
        fields: vec![("payload".into(), Ty::i32()), ("__tag".into(), Ty::Bool)],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "set_discr".to_string(),
        def_path: "test::set_discr".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty, name: Some("e".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::SetDiscriminant {
                    place: Place::local(1),
                    variant_index: 1,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("explicit-tag SetDiscriminant should lower");
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|n| {
            matches!(
                &n.inst,
                Inst::Const { ty: TrustIrTy::Bool, value: TrustIrConstant::Bool(true) }
            )
        }),
        "SetDiscriminant should materialize the bool tag value"
    );
    assert!(
        bb0.body.iter().any(|n| matches!(&n.inst, Inst::InsertField { field: 1, .. })),
        "SetDiscriminant should update the explicit tag field"
    );
}

#[test]
fn test_lower_set_discriminant_untagged_adt_fails_closed() {
    let enum_ty = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "Untagged".into(),
        fields: vec![("payload".into(), Ty::i32())],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "set_discr_untagged".to_string(),
        def_path: "test::set_discr_untagged".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty, name: Some("e".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::SetDiscriminant {
                    place: Place::local(1),
                    variant_index: 1,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func).expect_err("untagged SetDiscriminant must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(msg) if msg.contains("no explicit discriminant/tag field"))
    );
}

/// Trust (T4, aterm-scrollback): a `SetDiscriminant` on a place whose lowered
/// type is a BARE `Ty::Int` (an enum the extractor lowered to just its tag
/// scalar — no `Ty::Adt` wrapper, so no explicit tag FIELD exists) must lower
/// as a store of a FRESH UNCONSTRAINED Int to the place — the standard sound
/// over-approximation — instead of the old hard `Err` that ABORTED the whole
/// function lowering. Precision-only loss: the written tag value is not
/// tracked (a downstream read stays unknown, never falsely proved).
#[test]
fn test_lower_set_discriminant_bare_int_stores_fresh_unconstrained_tag() {
    let func = VerifiableFunction {
        name: "set_discr_bare_int".to_string(),
        def_path: "test::set_discr_bare_int".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 32, signed: true },
                    name: Some("tag".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::SetDiscriminant {
                    place: Place::local(1),
                    variant_index: 1,
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func)
        .expect("bare-Int SetDiscriminant must lower (fresh unconstrained store), not Err");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    // The written tag is a FRESH UNCONSTRAINED Int (Undef), never a Const of the
    // variant index: with the ADT metadata erased there is no sound
    // variant-index -> discriminant-value mapping.
    assert!(
        bb0.body.iter().any(|n| matches!(&n.inst, Inst::Undef { ty } if *ty == TrustIrTy::I32)),
        "expected a fresh unconstrained I32 (Undef) tag value"
    );
    assert!(
        !bb0.body
            .iter()
            .any(|n| matches!(&n.inst, Inst::Const { value: TrustIrConstant::Int(1), .. })),
        "the variant INDEX must not be asserted as the discriminant VALUE"
    );
}

#[test]
fn test_lower_tagged_option_none_aggregate_sets_false_tag() {
    let option_ty = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "std::option::Option".into(),
        fields: vec![("__payload".into(), Ty::i32()), ("__tag".into(), Ty::isize())],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "option_none".to_string(),
        def_path: "test::option_none".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: option_ty, name: Some("out".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "std::option::Option".into(),
                            variant: 0,
                            active_field: None,
                            args: None,
                        },
                        vec![],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("tagged Option::None aggregate should lower");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|node| {
            matches!(&node.inst, Inst::Const { ty: TrustIrTy::I64, value: TrustIrConstant::Int(0) })
        }),
        "Option::None aggregate should materialize the zero tag"
    );
    assert!(
        bb0.body.iter().any(|node| matches!(&node.inst, Inst::InsertField { field: 1, .. })),
        "Option::None aggregate should write the tag field"
    );
}

#[test]
fn test_lower_tagged_option_some_aggregate_sets_payload_and_true_tag() {
    let option_ty = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "std::option::Option".into(),
        fields: vec![("__payload".into(), Ty::i32()), ("__tag".into(), Ty::isize())],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "option_some".to_string(),
        def_path: "test::option_some".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: option_ty, name: Some("out".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "std::option::Option".into(),
                            variant: 1,
                            active_field: None,
                            args: None,
                        },
                        vec![Operand::Constant(ConstValue::Int(7))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("tagged Option::Some aggregate should lower");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|node| {
            matches!(&node.inst, Inst::Const { ty: TrustIrTy::I64, value: TrustIrConstant::Int(1) })
        }),
        "Option::Some aggregate should materialize the one tag"
    );
    assert!(
        bb0.body.iter().any(|node| matches!(&node.inst, Inst::InsertField { field: 0, .. })),
        "Option::Some aggregate should write the payload field"
    );
    assert!(
        bb0.body.iter().any(|node| matches!(&node.inst, Inst::InsertField { field: 1, .. })),
        "Option::Some aggregate should write the tag field"
    );
}

#[test]
fn test_lower_tagged_option_some_symbolic_payload_sets_tag() {
    let option_ty = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "std::option::Option".into(),
        fields: vec![("__payload".into(), Ty::i32()), ("__tag".into(), Ty::isize())],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "option_some_symbolic".to_string(),
        def_path: "test::option_some_symbolic".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: option_ty, name: Some("out".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "std::option::Option".into(),
                            variant: 1,
                            active_field: None,
                            args: None,
                        },
                        vec![Operand::Symbolic(Formula::Var("payload".into(), Sort::BitVec(32)))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module =
        lower_to_trust_ir(&func).expect("tagged Option::Some symbolic aggregate should lower");
    assert_valid_module(&module);
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|node| {
            matches!(&node.inst, Inst::Const { ty: TrustIrTy::I64, value: TrustIrConstant::Int(1) })
        }),
        "Option::Some symbolic aggregate should still materialize the one tag"
    );
    assert!(
        bb0.body.iter().any(|node| matches!(&node.inst, Inst::InsertField { field: 0, .. })),
        "Option::Some symbolic aggregate should write the payload field"
    );
    assert!(
        bb0.body.iter().any(|node| matches!(&node.inst, Inst::InsertField { field: 1, .. })),
        "Option::Some symbolic aggregate should write the tag field"
    );
}

// ---------------------------------------------------------------------------
// Lever A native lane: `Ty::Datatype` → opaque zero-field struct
// ---------------------------------------------------------------------------

/// A by-name datatype reference (empty `variants`) — the shape the extractor
/// emits for a recursive back-edge or a compacted oversized field.
fn datatype_ref_ty(name: &str) -> Ty {
    Ty::Datatype { name: name.to_string(), variants: Vec::new() }
}

#[test]
fn test_map_type_datatype_stateless_fails_with_ctx_hint() {
    let err = map_type(&datatype_ref_ty("selfcheck::CheckError"))
        .expect_err("stateless map_type must not map Datatype");
    assert!(
        matches!(err, BridgeError::UnsupportedType(ref msg) if msg.contains("context-aware")),
        "expected context-aware-lowering hint, got {err:?}"
    );
}

#[test]
fn test_lower_datatype_local_move_through() {
    // Whole-value flow of an opaque datatype value (arg -> return) must lower:
    // this is exactly what a fact-free sort marker must support, and what the
    // pre-fix catch-all rejected (failing the WHOLE function to Unknown).
    let dt = datatype_ref_ty("selfcheck::CheckError");
    let func = VerifiableFunction {
        name: "dt_move".to_string(),
        def_path: "test::dt_move".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: dt.clone(), name: None },
                LocalDecl { index: 1, ty: dt.clone(), name: Some("e".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Move(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: dt,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("whole-value datatype move should lower");
    assert_valid_module(&module);
    let opaque = module
        .structs
        .iter()
        .find(|s| s.name == "datatype::selfcheck::CheckError")
        .expect("opaque datatype struct should be registered");
    assert!(opaque.fields.is_empty(), "datatype struct must be a zero-field havoc slot");
    // The identical `Ty` value is cached, so exactly one registration.
    assert_eq!(
        module.structs.iter().filter(|s| s.name.starts_with("datatype::")).count(),
        1,
        "same datatype Ty must map to one registered struct"
    );
}

#[test]
fn test_lower_datatype_field_projection_fail_softs_to_dest_typed_havoc() {
    // A Field READ out of the opaque marker with a KNOWN consumer type (the
    // Assign destination's declared type) fail-softs to ONE fresh `Undef` of
    // that type instead of dropping the whole function (the pre-fix behavior:
    // hard `Err` in `field_type`, the largest native-lane unsupported source).
    // SOUNDNESS: the havoc is unconstrained and fact-free — no `Assume`, no
    // fabricated constant, no `ExtractField` pretending structure exists.
    let dt = datatype_ref_ty("serde_json::Value");
    let func = VerifiableFunction {
        name: "dt_field".to_string(),
        def_path: "test::dt_field".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: dt, name: Some("v".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Field(0)],
                    })),
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
    };

    let module = lower_to_trust_ir(&func)
        .expect("field read out of an opaque datatype should fail-soft to a typed havoc");
    assert_valid_module(&module);
    let body: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::Undef { ty: TrustIrTy::I32 })),
        "the projected value must be modeled as a dest-typed Undef havoc"
    );
    assert!(
        !body.iter().any(|node| matches!(&node.inst, Inst::ExtractField { .. })),
        "no structural extraction may be fabricated from the opaque datatype"
    );
    assert!(
        !body.iter().any(|node| matches!(&node.inst, Inst::Assume { .. })),
        "no fact may be emitted about the compacted contents"
    );
}

#[test]
fn test_lower_nested_compacted_field_read_keeps_unrelated_obligations() {
    use trust_types::AssertMessage;
    // The ny-cert `certz::qpair_json` shape: an ADT whose field 0 was
    // compacted by the extractor's Lever-A 64-node cap (nested types still
    // compact under the `cap_fields = !ctx.adt_stack.is_empty()` gate), and
    // MIR reads `.0` OUT of the compacted value. The read fail-softs to a
    // dest-typed havoc, so the function still lowers and its UNRELATED
    // obligation (a checked add on a different local) keeps a native verdict
    // instead of the whole function collapsing to one Unsupported note.
    let marker = datatype_ref_ty("__trust_compacted_aggregate");
    let outer = Ty::Adt { adt_kind: None, layout: None, 
        name: "certz::Compacted".to_string(),
        fields: vec![("payload".to_string(), marker), ("len".to_string(), Ty::u64())],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "qpair_like".to_string(),
        def_path: "test::qpair_like".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: outer, name: Some("c".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 3, ty: Ty::u64(), name: Some("hidden".into()) },
                LocalDecl {
                    index: 4,
                    ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]),
                    name: Some("checked".into()),
                },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // `_3 = copy ((_1.0).0)` — a `.0` READ out of the
                        // NESTED compacted field (`_1.0` resolves to the
                        // marker, then `.0` reads out of it) → typed havoc.
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Field(0), Projection::Field(0)],
                            })),
                            span: SourceSpan::default(),
                        },
                        // Unrelated, obligation-bearing work on `_2`.
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Int(200)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(4, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(4, 0))),
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
    };

    let module = lower_to_trust_ir(&func)
        .expect("a nested-compacted `.0` read must not drop the whole function");
    assert_valid_module(&module);
    let body: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    // The compacted read is a u64-typed havoc (the dest local's declared type).
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::Undef { ty: TrustIrTy::U64 })),
        "the compacted `.0` read must lower to a u64 Undef havoc"
    );
    assert!(
        !body.iter().any(|node| matches!(&node.inst, Inst::Assume { .. })),
        "no fact may be emitted about the compacted contents"
    );
    // The UNRELATED checked add still produces its real overflow instruction
    // and its per-site ArithmeticSafety obligation — a native verdict target.
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::Overflow { .. })),
        "the unrelated checked add must still lower to a real Overflow instruction"
    );
    assert!(
        module
            .proof_obligations
            .iter()
            .any(|o| matches!(o.kind, trust_ir::ObligationKind::ArithmeticSafety)),
        "the unrelated overflow obligation must survive the fail-soft havoc"
    );
}

#[test]
fn test_lower_compacted_field_read_without_expected_type_still_fails_closed() {
    // A compacted-field read whose consuming context carries NO declared type
    // (a BinaryOp operand types the place BEFORE resolution) keeps the
    // original hard fail — we never fabricate an untyped value.
    let marker = datatype_ref_ty("__trust_compacted_aggregate");
    let outer = Ty::Adt { adt_kind: None, layout: None, 
        name: "certz::Compacted".to_string(),
        fields: vec![("payload".to_string(), marker), ("len".to_string(), Ty::u64())],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "compacted_binop".to_string(),
        def_path: "test::compacted_binop".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl { index: 1, ty: outer, name: Some("c".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Eq,
                        Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Field(0), Projection::Field(0)],
                        }),
                        Operand::Constant(ConstValue::Int(3)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func)
        .expect_err("an expectation-less compacted-field read must keep failing closed");
    // The exact ny-cert diagnostic note shape (348 notes pre-fix).
    assert!(
        matches!(
            err,
            BridgeError::UnsupportedOp(ref msg)
                if msg.contains("Field projection .0 on non-aggregate type Datatype")
                    && msg.contains("__trust_compacted_aggregate")
        ),
        "expected the fail-closed Field-projection error, got {err:?}"
    );
}

#[test]
fn test_lower_projected_store_into_compacted_field_still_fails_closed() {
    // The WRITE direction is untouched: storing INTO a compacted field would
    // need the read-modify-write chain to walk structure the marker does not
    // carry, so it keeps the fail-closed refusal.
    let marker = datatype_ref_ty("__trust_compacted_aggregate");
    let outer = Ty::Adt { adt_kind: None, layout: None, 
        name: "certz::Compacted".to_string(),
        fields: vec![("payload".to_string(), marker), ("len".to_string(), Ty::u64())],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "compacted_store".to_string(),
        def_path: "test::compacted_store".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: outer, name: Some("c".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place {
                        local: 1,
                        projections: vec![Projection::Field(0), Projection::Field(0)],
                    },
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(3, 64))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func)
        .expect_err("a store into a compacted field must keep failing closed");
    assert!(matches!(err, BridgeError::UnsupportedOp(_)), "expected UnsupportedOp, got {err:?}");
}

#[test]
fn test_lower_compacted_field_read_as_known_call_arg_fail_softs() {
    // A compacted-field read passed AS an argument to an IN-MODULE callee
    // fail-softs to a havoc typed from the callee's declared param type, so
    // the caller still lowers and the call edge stays a real `Inst::Call`
    // (the callee's own obligations keep propagating to the caller).
    let marker = datatype_ref_ty("__trust_compacted_aggregate");
    let outer = Ty::Adt { adt_kind: None, layout: None, 
        name: "certz::Compacted".to_string(),
        fields: vec![("payload".to_string(), marker), ("len".to_string(), Ty::u64())],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let callee = VerifiableFunction {
        name: "test::sink".to_string(),
        def_path: "test::sink".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let caller = VerifiableFunction {
        name: "test::caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: outer, name: Some("c".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "test::sink".to_string(),
                        args: vec![Operand::Move(Place {
                            local: 1,
                            projections: vec![Projection::Field(0), Projection::Field(0)],
                        })],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir_functions("call_arg_havoc", &[callee, caller])
        .expect("a compacted-field call arg to a known callee must fail-soft");
    assert_valid_module(&module);
    let caller_fn =
        module.functions.iter().find(|f| f.name == "test::caller").expect("caller must be lowered");
    let body: Vec<_> = caller_fn.blocks.iter().flat_map(|b| b.body.iter()).collect();
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::Undef { ty: TrustIrTy::U64 })),
        "the compacted-field arg must lower to a param-typed Undef havoc"
    );
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::Call { .. })),
        "the call edge must remain a real Inst::Call to the in-module callee"
    );
}

#[test]
fn test_lower_aggregate_from_compacted_field_read_fail_softs() {
    // A tuple aggregate built FROM a compacted-field read: the aggregate's
    // declared field type supplies the havoc's type, so construction still
    // lowers as the canonical Undef + InsertField chain.
    let marker = datatype_ref_ty("__trust_compacted_aggregate");
    let outer = Ty::Adt { adt_kind: None, layout: None, 
        name: "certz::Compacted".to_string(),
        fields: vec![("payload".to_string(), marker), ("len".to_string(), Ty::u64())],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "compacted_aggregate".to_string(),
        def_path: "test::compacted_aggregate".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::u64(), Ty::u64()]), name: None },
                LocalDecl { index: 1, ty: outer, name: Some("c".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Tuple,
                        vec![
                            Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Field(0), Projection::Field(0)],
                            }),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Tuple(vec![Ty::u64(), Ty::u64()]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func)
        .expect("a tuple aggregate over a compacted-field read must fail-soft");
    assert_valid_module(&module);
    let body: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::Undef { ty: TrustIrTy::U64 })),
        "the compacted-field operand must lower to a field-typed Undef havoc"
    );
    assert!(
        body.iter().filter(|node| matches!(&node.inst, Inst::InsertField { .. })).count() >= 2,
        "the tuple must still be built with the canonical InsertField chain"
    );
}

#[test]
fn test_lower_borrow_of_compacted_field_fail_softs_to_dest_typed_gep() {
    // Task #56: a BORROW of a `.0` INTO the compacted marker — `&(c.0).0` —
    // routes through `address_of_place` / `address_from_pointer` (the GEP
    // path), NOT `resolve_place_expecting`, so the Lever-A read fail-soft
    // does not apply. Pre-fix this hard-failed in `field_type`
    // (`UnsupportedOp("Field projection .0 on non-aggregate type Datatype {
    // name: \"__trust_compacted_aggregate\", variants: [] }")`), dropping the
    // whole function. Now the dest's declared `&u64` pointee types ONE
    // fail-soft GEP (havoc'd by the trust-mc consumer — fact-free).
    let marker = datatype_ref_ty("__trust_compacted_aggregate");
    let outer = Ty::Adt { adt_kind: None, layout: None, 
        name: "certz::Compacted".to_string(),
        fields: vec![("payload".to_string(), marker), ("len".to_string(), Ty::u64())],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "compacted_borrow".to_string(),
        def_path: "test::compacted_borrow".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: outer, name: Some("c".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u64()) },
                    name: Some("r".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref {
                        mutable: false,
                        place: Place {
                            local: 1,
                            projections: vec![Projection::Field(0), Projection::Field(0)],
                        },
                    },
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func)
        .expect("a borrow of a compacted `.0` must fail-soft to a dest-typed GEP");
    assert_valid_module(&module);
    let body: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    // The compacted `.0` address is ONE GEP typed at the dest's pointee
    // (`u64`) — the same result shape as the precise field-address arm.
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::GEP { pointee_ty: TrustIrTy::U64, .. })),
        "the compacted `.0` address must lower to a dest-pointee-typed GEP"
    );
    // The borrow itself still lowers as a real shared borrow.
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::Borrow { .. })),
        "the borrow must still lower to a real Inst::Borrow"
    );
    assert!(
        !body.iter().any(|node| matches!(&node.inst, Inst::Assume { .. })),
        "no fact may be emitted about the compacted contents"
    );
}

#[test]
fn test_lower_borrow_through_ref_of_compacted_datatype_field_fail_softs() {
    // Task #56: the exact `certz::qpair_json` shape — `Ratio::numer` inlines
    // to `&(*r).0` where `r: &Ratio<BigInt>` and the Ratio type was compacted
    // to a by-name `Ty::Datatype` marker. The Deref-first arm of
    // `address_of_place` hands the opaque pointee to `address_from_pointer`,
    // whose `Field` arm pre-fix hard-failed in `field_type` — the lowering
    // failure then cascaded transitively as ~136 absent-callee unknowns in
    // ny-cert. The dest's declared `&BigInt` pointee (itself an opaque
    // datatype) types the fail-soft GEP.
    let ratio = datatype_ref_ty("num_rational::Ratio<num_bigint::BigInt>");
    let func = VerifiableFunction {
        name: "qpair_numer".to_string(),
        def_path: "test::qpair_numer".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(ratio) },
                    name: Some("r".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(datatype_ref_ty("num_bigint::BigInt")),
                    },
                    name: Some("numer".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref {
                        mutable: false,
                        place: Place {
                            local: 1,
                            projections: vec![Projection::Deref, Projection::Field(0)],
                        },
                    },
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func)
        .expect("the qpair `&(*r).0` borrow must fail-soft to a dest-typed GEP");
    assert_valid_module(&module);
    // The dest pointee is itself an opaque datatype: its zero-field struct
    // must be registered and type the fail-soft GEP.
    let opaque = module
        .structs
        .iter()
        .find(|s| s.name == "datatype::num_bigint::BigInt")
        .expect("the dest-pointee datatype struct must be registered");
    assert!(opaque.fields.is_empty(), "datatype struct must be a zero-field havoc slot");
    let body: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    assert!(
        body.iter().any(|node| matches!(&node.inst,
            Inst::GEP { pointee_ty: TrustIrTy::Struct(id), .. } if *id == opaque.id)),
        "the compacted `.0` address must lower to a GEP typed at the dest pointee"
    );
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::Borrow { .. })),
        "the borrow must still lower to a real Inst::Borrow"
    );
    assert!(
        !body.iter().any(|node| matches!(&node.inst, Inst::Assume { .. })),
        "no fact may be emitted about the compacted contents"
    );
}

#[test]
fn test_lower_borrow_of_compacted_field_with_unmappable_dest_still_fails_closed() {
    // Task #56 pin: the borrow/GEP fail-soft is EXPECTATION-GATED. When the
    // dest's pointee type is itself unmappable (`Ty::Unsupported`), no typed
    // havoc can be fabricated, so the borrow keeps the ORIGINAL fail-closed
    // `field_type` error — never an untyped value.
    let marker = datatype_ref_ty("__trust_compacted_aggregate");
    let outer = Ty::Adt { adt_kind: None, layout: None, 
        name: "certz::Compacted".to_string(),
        fields: vec![("payload".to_string(), marker), ("len".to_string(), Ty::u64())],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "compacted_borrow_unmappable".to_string(),
        def_path: "test::compacted_borrow_unmappable".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: outer, name: Some("c".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Unsupported {
                            kind: "TyKind::Foreign".to_string(),
                            detail: "extern type".to_string(),
                        }),
                    },
                    name: Some("r".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref {
                        mutable: false,
                        place: Place {
                            local: 1,
                            projections: vec![Projection::Field(0), Projection::Field(0)],
                        },
                    },
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func)
        .expect_err("an unmappable-dest compacted borrow must keep failing closed");
    assert!(
        matches!(
            err,
            BridgeError::UnsupportedOp(ref msg)
                if msg.contains("Field projection .0 on non-aggregate type Datatype")
                    && msg.contains("__trust_compacted_aggregate")
        ),
        "expected the ORIGINAL fail-closed Field-projection error, got {err:?}"
    );
}

/// The REAL dumped `certz::qpair_json` failure shape (task #56, verified by
/// `TRUST_DUMP_MIR` real-MIR dump from a stage2 repro crate): the `vec![a, b]`
/// box write `(*_13).1.0.0 = [move _5, move _9]` (span alloc/src/macros.rs),
/// where `_13: *const MaybeUninit<..>` whose pointee chain is
/// `MaybeUninit { uninit: (), value: ManuallyDrop { value: MaybeDangling {
/// 0: __trust_compacted_aggregate } } }` — the boxed `[serde_json::Value; 2]`
/// subtree compacted to the GENERIC marker. `place_type` walks the dest chain
/// successfully and yields the MARKER as the aggregate's destination type;
/// pre-fix the per-operand `aggregate_operand_type(marker, i)` then
/// hard-failed with "Field projection .0 on non-aggregate type Datatype
/// { name: \"__trust_compacted_aggregate\", variants: [] }", dropping
/// `certz::qpair_json` / `certz::lincon_json::{closure#0}` whole (and
/// cascading as absent-callee unknowns in ny-cert).
fn compacted_vec_box_write_func(operands: Vec<Operand>) -> VerifiableFunction {
    let marker = datatype_ref_ty("__trust_compacted_aggregate");
    let value_enum = Ty::Adt { adt_kind: None, layout: None, 
        name: "serde_json::Value".into(),
        fields: vec![("__v3_0".into(), marker.clone()), ("__tag".into(), Ty::isize())],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let pointee = Ty::Adt { adt_kind: None, layout: None,
        name: "std::mem::MaybeUninit".to_string(),
        fields: vec![
            ("uninit".to_string(), Ty::Unit),
            (
                "value".to_string(),
                Ty::Adt { adt_kind: None, layout: None, 
                    name: "std::mem::ManuallyDrop".to_string(),
                    fields: vec![(
                        "value".to_string(),
                        Ty::Adt { adt_kind: None, layout: None, 
                            name: "std::mem::MaybeDangling".to_string(),
                            fields: vec![("0".to_string(), marker)],
                            variants: Vec::new(),
                            disc_index_safe: false,
                            faithful_enum_repr: None, enum_layout: None, },
                    )],
                    variants: Vec::new(),
                    disc_index_safe: false,
                    faithful_enum_repr: None, enum_layout: None, },
            ),
        ],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    VerifiableFunction {
        name: "compacted_box_write".to_string(),
        def_path: "test::compacted_box_write".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(pointee) },
                    name: Some("p".into()),
                },
                LocalDecl { index: 2, ty: value_enum.clone(), name: None },
                LocalDecl { index: 3, ty: value_enum, name: None },
                LocalDecl {
                    index: 4,
                    ty: Ty::Adt { adt_kind: None, layout: None, 
                        name: "certz::Compacted".to_string(),
                        fields: vec![(
                            "payload".to_string(),
                            datatype_ref_ty("__trust_compacted_aggregate"),
                        )],
                        variants: Vec::new(),
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, },
                    name: Some("c".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    // `(*_1).1.0.0 = [ ...operands ]` — the dumped dest chain.
                    place: Place {
                        local: 1,
                        projections: vec![
                            Projection::Deref,
                            Projection::Field(1),
                            Projection::Field(0),
                            Projection::Field(0),
                        ],
                    },
                    rvalue: Rvalue::Aggregate(AggregateKind::Array, operands),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 4,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_lower_array_aggregate_into_compacted_slot_fail_softs_to_opaque_havoc() {
    // The real qpair_json shape: two whole-value element moves into the
    // compacted slot. The aggregate fail-softs to ONE fresh `Inst::Undef` of
    // the marker's mapped opaque zero-field struct (Coroutine-frame
    // precedent); the projected store through the raw pointer still lowers
    // (GEP chain + Store). SOUNDNESS: the stored value carries NO facts — no
    // fabricated `InsertField` structure, no `Assume`; every later read of
    // the slot stays havoc/fail-closed.
    let func = compacted_vec_box_write_func(vec![
        Operand::Move(Place::local(2)),
        Operand::Move(Place::local(3)),
    ]);
    let module =
        lower_to_trust_ir(&func).expect("an array aggregate into a compacted slot must fail-soft");
    assert_valid_module(&module);
    let opaque = module
        .structs
        .iter()
        .find(|s| s.name == "datatype::__trust_compacted_aggregate")
        .expect("the marker's opaque struct must be registered");
    assert!(opaque.fields.is_empty(), "marker struct must be a zero-field havoc slot");
    let body: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    assert!(
        body.iter().any(|node| matches!(&node.inst,
            Inst::Undef { ty: TrustIrTy::Struct(id) } if *id == opaque.id)),
        "the aggregate must lower to ONE opaque marker-typed Undef havoc"
    );
    assert!(
        body.iter().any(|node| matches!(&node.inst, Inst::Store { .. })),
        "the projected store through the raw pointer must still lower"
    );
    assert!(
        !body.iter().any(|node| matches!(&node.inst, Inst::InsertField { .. })),
        "no structural InsertField may be fabricated into the opaque slot"
    );
    assert!(
        !body.iter().any(|node| matches!(&node.inst, Inst::Assume { .. })),
        "no fact may be emitted about the compacted contents"
    );
}

#[test]
fn test_lower_aggregate_into_compacted_slot_with_unlowerable_operand_still_fails_closed() {
    // Pin: the aggregate fail-soft still RESOLVES every operand (their reads
    // may carry obligations), so an operand that itself cannot lower — a
    // `.0` READ out of a compacted marker with no expectation — keeps the
    // original fail-closed error.
    let func = compacted_vec_box_write_func(vec![Operand::Copy(Place {
        local: 4,
        projections: vec![Projection::Field(0), Projection::Field(0)],
    })]);
    let err = lower_to_trust_ir(&func)
        .expect_err("an unlowerable aggregate operand must keep failing closed");
    assert!(
        matches!(
            err,
            BridgeError::UnsupportedOp(ref msg)
                if msg.contains("Field projection .0 on non-aggregate type Datatype")
                    && msg.contains("__trust_compacted_aggregate")
        ),
        "expected the fail-closed Field-projection error, got {err:?}"
    );
}

#[test]
fn test_lower_datatype_discriminant_fails_closed() {
    // Discriminant reads need the flat `Ty::Adt` `__tag` machinery; an opaque
    // datatype value carries no tag, so the read must fail closed (never an
    // assumed range fact, never a fabricated tag).
    let dt = datatype_ref_ty("selfcheck::CheckError");
    let func = VerifiableFunction {
        name: "dt_discr".to_string(),
        def_path: "test::dt_discr".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: dt, name: Some("e".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_trust_ir(&func)
        .expect_err("discriminant read on an opaque datatype must fail closed");
    assert!(matches!(err, BridgeError::UnsupportedOp(_)), "expected UnsupportedOp, got {err:?}");
}

#[test]
fn test_lower_enum_aggregate_with_datatype_payload_field() {
    // The `Err(e)` shape that regressed ny-cert: a flat tagged enum whose
    // payload field was compacted to a by-name datatype reference. The
    // aggregate must lower (tag write + opaque payload write); the payload
    // value is havoc downstream, which is sound (never a false proof).
    let dt = datatype_ref_ty("selfcheck::CheckError");
    let result_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "std::result::Result".into(),
        fields: vec![("__v1_0".into(), dt.clone()), ("__tag".into(), Ty::isize())],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "result_err".to_string(),
        def_path: "test::result_err".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: dt, name: Some("e".into()) },
                LocalDecl { index: 2, ty: result_ty, name: Some("out".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "std::result::Result".into(),
                            variant: 1,
                            active_field: None,
                            args: None,
                        },
                        vec![Operand::Move(Place::local(1))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func)
        .expect("enum aggregate with an opaque datatype payload should lower");
    assert_valid_module(&module);
    assert!(
        module.structs.iter().any(|s| s.name == "datatype::selfcheck::CheckError"),
        "payload datatype struct should be registered"
    );
    let bb0 = &module.functions[0].blocks[0];
    assert!(
        bb0.body.iter().any(|node| matches!(&node.inst, Inst::InsertField { field: 1, .. })),
        "Err aggregate should write the tag field"
    );
}

// ---------------------------------------------------------------------------
// Fail-soft absent-callee lowering
// ---------------------------------------------------------------------------

fn typed_absent_call(func: &str, arg_tys: Vec<Ty>, dest_ty: Ty) -> VerifiableFunction {
    typed_absent_call_with_metadata(
        func,
        arg_tys,
        dest_ty,
        false,
        false,
        Some(BlockId(1)),
        None,
    )
}

fn typed_absent_call_with_metadata(
    func: &str,
    arg_tys: Vec<Ty>,
    dest_ty: Ty,
    is_unsafe_sig: bool,
    is_foreign: bool,
    target: Option<BlockId>,
    atomic: Option<AtomicOperation>,
) -> VerifiableFunction {
    let mut locals = vec![LocalDecl { index: 0, ty: dest_ty.clone(), name: None }];
    let mut args = Vec::with_capacity(arg_tys.len());
    for (offset, ty) in arg_tys.into_iter().enumerate() {
        let index = offset + 1;
        locals.push(LocalDecl { index, ty, name: Some(format!("arg{index}")) });
        args.push(Operand::Copy(Place::local(index)));
    }
    VerifiableFunction {
        name: "typed_absent_call".into(),
        def_path: "test::typed_absent_call".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            arg_count: args.len(),
            locals,
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig,
                        is_foreign,
                        func: func.into(),
                        args,
                        dest: Place::local(0),
                        target,
                        span: SourceSpan::default(),
                        atomic,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            return_ty: dest_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn has_absent_callee_panic_obligation(module: &trust_ir::Module) -> bool {
    module.proof_obligations.iter().any(|obligation| {
        obligation.kind == trust_ir::ObligationKind::PanicFreedom
            && obligation
                .description
                .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
    })
}

#[test]
fn test_primitive_ord_gate_requires_canonical_trait_and_primitive_types() {
    let primitive = lower_to_trust_ir(&typed_absent_call(
        "core::cmp::Ord::min",
        vec![Ty::u64(), Ty::u64()],
        Ty::u64(),
    ))
    .expect("primitive Ord::min lowers through its typed gate");
    assert!(!has_absent_callee_panic_obligation(&primitive));

    let user = Ty::adt("my_crate::PanickyOrd", vec![("value".into(), Ty::u64())]);
    let user_call = lower_to_trust_ir(&typed_absent_call(
        "core::cmp::Ord::min",
        vec![user.clone(), user.clone()],
        user,
    ))
    .expect("user Ord lowers fail-soft");
    assert!(has_absent_callee_panic_obligation(&user_call));

    let forged_path = lower_to_trust_ir(&typed_absent_call(
        "my_crate::core::cmp::Ord::min",
        vec![Ty::u64(), Ty::u64()],
        Ty::u64(),
    ))
    .expect("same-tail user function lowers fail-soft");
    assert!(has_absent_callee_panic_obligation(&forged_path));

    let clamp = lower_to_trust_ir(&typed_absent_call(
        "core::cmp::Ord::clamp",
        vec![Ty::u64(), Ty::u64(), Ty::u64()],
        Ty::u64(),
    ))
    .expect("primitive clamp lowers fail-soft");
    assert!(
        has_absent_callee_panic_obligation(&clamp),
        "primitive clamp must keep its lo <= hi panic precondition"
    );
}

#[test]
fn test_iterator_gate_authenticates_trait_path_and_receiver() {
    let iter = Ty::Ref { mutable: true, inner: Box::new(Ty::adt("core::slice::Iter", vec![])) };
    let canonical = lower_to_trust_ir(&typed_absent_call(
        "core::iter::Iterator::next",
        vec![iter.clone()],
        Ty::u64(),
    ))
    .expect("canonical slice iterator next lowers");
    assert!(!has_absent_callee_panic_obligation(&canonical));

    for hostile in ["my_crate::Iterator::next", "my_crate::core::iter::Iterator::next"] {
        let module = lower_to_trust_ir(&typed_absent_call(hostile, vec![iter.clone()], Ty::u64()))
            .expect("same-tail hostile iterator call lowers fail-soft");
        assert!(
            has_absent_callee_panic_obligation(&module),
            "receiver type alone must not authenticate `{hostile}`"
        );
    }
}

#[test]
fn test_string_markers_and_capacity_growth_never_grant_totality() {
    let vec_ty = Ty::adt("alloc::vec::Vec", vec![("len".into(), Ty::usize())]);
    let cases = [
        typed_absent_call(
            "alloc::vec::Vec::<u8>::with_capacity",
            vec![Ty::usize()],
            vec_ty.clone(),
        ),
        typed_absent_call(
            "alloc::vec::Vec::<u8>::push",
            vec![Ty::Ref { mutable: true, inner: Box::new(vec_ty) }, Ty::u8()],
            Ty::Unit,
        ),
        typed_absent_call(
            "core::ops::FromResidual::from_residual::<__trust_try_total>",
            vec![Ty::u64()],
            Ty::u64(),
        ),
    ];
    for function in cases {
        let callee = match &function.body.blocks[0].terminator {
            Terminator::Call { func, .. } => func.clone(),
            _ => unreachable!(),
        };
        let module = lower_to_trust_ir(&function)
            .unwrap_or_else(|error| panic!("`{callee}` must lower fail-soft: {error:?}"));
        assert!(
            has_absent_callee_panic_obligation(&module),
            "`{callee}` must retain panic authority"
        );
    }
}

#[test]
fn test_primitive_num_gates_require_exact_library_paths() {
    for (callee, args, dest) in [
        ("core::num::<impl u64>::count_ones", vec![Ty::u64()], Ty::u32()),
        (
            "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add",
            vec![Ty::u64(), Ty::u64()],
            Ty::u64(),
        ),
    ] {
        let module = lower_to_trust_ir(&typed_absent_call(callee, args, dest))
            .unwrap_or_else(|error| panic!("exact primitive method must lower: {error:?}"));
        assert!(
            !has_absent_callee_panic_obligation(&module),
            "exact primitive method should retain its typed summary: {callee}"
        );
    }

    for (callee, args, dest) in [
        ("my_crate::core::num::count_ones", vec![Ty::u64()], Ty::u32()),
        ("core::hostile::num::count_ones", vec![Ty::u64()], Ty::u32()),
        ("core::num::<impl u64>::wrapping_add", vec![Ty::u64(), Ty::u64()], Ty::u64()),
        ("core::hostile::num::wrapping_add", vec![Ty::u64(), Ty::u64()], Ty::u64()),
        (
            "@trust-rustc-total-primitive-method::core::num::<impl u32>::wrapping_add",
            vec![Ty::u64(), Ty::u64()],
            Ty::u64(),
        ),
        (
            "@trust-rustc-total-primitive-method::core::num::<impl u128>::wrapping_add",
            vec![Ty::u128(), Ty::u128()],
            Ty::u128(),
        ),
    ] {
        let module =
            lower_to_trust_ir(&typed_absent_call(callee, args, dest)).unwrap_or_else(|error| {
                panic!("hostile primitive tail must lower fail-soft: {error:?}")
            });
        assert!(
            has_absent_callee_panic_obligation(&module),
            "same-tail path must not gain primitive summary authority: {callee}"
        );
    }
}

fn assert_single_wrapping_binop(
    module: &trust_ir::Module,
    expected_op: TrustIrBinOp,
    expected_ty: TrustIrTy,
) {
    assert_valid_module(module);
    let wrapping: Vec<_> = module
        .functions
        .iter()
        .flat_map(|function| function.blocks.iter())
        .flat_map(|block| block.body.iter())
        .filter(|node| node.proofs.contains(&trust_ir::ProofAnnotation::Wrapping))
        .collect();
    assert_eq!(wrapping.len(), 1, "expected exactly one wrapping-certified instruction");
    assert!(
        matches!(
            &wrapping[0].inst,
            Inst::BinOp { op, ty, .. } if op == &expected_op && ty == &expected_ty
        ),
        "wrapping certificate must decorate the expected modular BinOp: {:?}",
        wrapping[0]
    );
    assert!(
        !has_absent_callee_panic_obligation(module),
        "an authenticated wrapping call must not retain an absent-callee panic obligation"
    );
}

fn wrapping_call_with_int_rhs(callee: &str, ty: Ty, rhs: i128) -> VerifiableFunction {
    let mut function = typed_absent_call(callee, vec![ty.clone()], ty);
    let Terminator::Call { args, .. } = &mut function.body.blocks[0].terminator else {
        unreachable!("typed_absent_call always constructs a call terminator");
    };
    args.push(Operand::Constant(ConstValue::Int(rhs)));
    function
}

fn wrapping_call_with_uint_rhs(
    callee: &str,
    ty: Ty,
    rhs: u128,
    encoded_width: u32,
) -> VerifiableFunction {
    let mut function = typed_absent_call(callee, vec![ty.clone()], ty);
    let Terminator::Call { args, .. } = &mut function.body.blocks[0].terminator else {
        unreachable!("typed_absent_call always constructs a call terminator");
    };
    args.push(Operand::Constant(ConstValue::Uint(rhs, encoded_width)));
    function
}

#[test]
fn test_wrapping_refutation_markers_lower_signed_and_pointer_sized_binops() {
    let signed = lower_to_trust_ir(&typed_absent_call(
        "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_sub",
        vec![Ty::i32(), Ty::i32()],
        Ty::i32(),
    ))
    .expect("authenticated i32 wrapping_sub must lower");
    assert_single_wrapping_binop(&signed, TrustIrBinOp::Sub, TrustIrTy::I32);

    let signed_literal = lower_to_trust_ir(&wrapping_call_with_int_rhs(
        "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_add",
        Ty::i32(),
        1,
    ))
    .expect("authenticated i32 wrapping_add with a representable literal must lower");
    assert_single_wrapping_binop(&signed_literal, TrustIrBinOp::Add, TrustIrTy::I32);

    let faithful_usize = Ty::PtrSizedInt { signed: false };
    let pointer_sized = lower_to_trust_ir(&typed_absent_call(
        "@trust-rustc-wrapping-refutation-method::core::num::<impl usize>::wrapping_add",
        vec![faithful_usize.clone(), faithful_usize.clone()],
        faithful_usize,
    ))
    .expect("authenticated faithful usize wrapping_add must lower");
    assert_single_wrapping_binop(&pointer_sized, TrustIrBinOp::Add, TrustIrTy::Usize);

    let legacy_pointer_sized = lower_to_trust_ir(&typed_absent_call(
        "@trust-rustc-wrapping-refutation-method::core::num::<impl usize>::wrapping_add",
        vec![Ty::usize(), Ty::usize()],
        Ty::usize(),
    ))
    .expect("authenticated legacy usize wrapping_add must lower");
    assert_single_wrapping_binop(&legacy_pointer_sized, TrustIrBinOp::Add, TrustIrTy::U64);
}

fn assert_wrapping_call_fails_closed(function: VerifiableFunction, label: &str) {
    match lower_to_trust_ir(&function) {
        Ok(module) => {
            assert!(
                module
                    .functions
                    .iter()
                    .flat_map(|function| function.blocks.iter())
                    .flat_map(|block| block.body.iter())
                    .all(|node| {
                        !matches!(&node.inst, Inst::BinOp { .. })
                            && !node.proofs.contains(&trust_ir::ProofAnnotation::Wrapping)
                    }),
                "{label} must not inherit modular BinOp authority"
            );
            assert!(
                has_absent_callee_panic_obligation(&module),
                "{label} must retain the fail-closed absent-callee panic obligation"
            );
        }
        Err(_) => {
            // A hard lowering refusal is also fail-closed. Atomic metadata uses
            // this lane because its source-string reconstruction is quarantined.
        }
    }
}

#[test]
fn test_wrapping_refutation_marker_metadata_and_shape_fail_closed() {
    const I32_ADD: &str =
        "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_add";
    const U64_ADD: &str =
        "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add";
    let i32_args = || vec![Ty::i32(), Ty::i32()];

    assert_wrapping_call_fails_closed(
        typed_absent_call(
            "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_add::suffix",
            i32_args(),
            Ty::i32(),
        ),
        "malformed marker",
    );
    assert_wrapping_call_fails_closed(
        typed_absent_call(I32_ADD, vec![Ty::u32(), Ty::u32()], Ty::u32()),
        "carrier-mismatched marker",
    );
    assert_wrapping_call_fails_closed(
        wrapping_call_with_int_rhs(
            "@trust-rustc-wrapping-refutation-method::core::num::<impl i8>::wrapping_add",
            Ty::i8(),
            128,
        ),
        "unrepresentable narrow literal",
    );
    assert_wrapping_call_fails_closed(
        wrapping_call_with_uint_rhs(U64_ADD, Ty::u64(), 1, 32),
        "unsigned literal whose encoded width disagrees with the marker",
    );
    assert_wrapping_call_fails_closed(
        wrapping_call_with_int_rhs(U64_ADD, Ty::u64(), 1),
        "signed literal spelling under an unsigned marker",
    );
    assert_wrapping_call_fails_closed(
        wrapping_call_with_uint_rhs(I32_ADD, Ty::i32(), 1, 32),
        "unsigned literal spelling under a signed marker",
    );
    assert_wrapping_call_fails_closed(
        typed_absent_call_with_metadata(
            I32_ADD,
            i32_args(),
            Ty::i32(),
            true,
            false,
            Some(BlockId(1)),
            None,
        ),
        "unsafe call metadata",
    );
    assert_wrapping_call_fails_closed(
        typed_absent_call_with_metadata(
            I32_ADD,
            i32_args(),
            Ty::i32(),
            false,
            true,
            Some(BlockId(1)),
            None,
        ),
        "foreign call metadata",
    );
    assert_wrapping_call_fails_closed(
        typed_absent_call_with_metadata(
            I32_ADD,
            i32_args(),
            Ty::i32(),
            false,
            false,
            None,
            None,
        ),
        "missing normal-return target",
    );
    assert_wrapping_call_fails_closed(
        typed_absent_call_with_metadata(
            I32_ADD,
            i32_args(),
            Ty::i32(),
            false,
            false,
            Some(BlockId(1)),
            Some(AtomicOperation {
                place: Place::local(1),
                dest: Some(Place::local(0)),
                op_kind: AtomicOpKind::FetchAdd,
                ordering: AtomicOrdering::SeqCst,
                failure_ordering: None,
                span: SourceSpan::default(),
            }),
        ),
        "atomic call metadata",
    );
}

/// `u32::try_from(u64)` via the type-erased trait spelling: the TYPED gate
/// (int arg + `Result<_, num::TryFromIntError>` dest) pins it to the std
/// int→int blanket impl — total, so NO PanicFreedom obligation and a havoc
/// result. A same-named call whose Err payload is a user type keeps the
/// fail-soft may-panic encoding (a user `TryFrom` impl can panic).
#[test]
fn test_int_try_from_lowered_total_no_panic_obligation() {
    let mk = |ok_ty: Ty, err_ty_name: &str, label: &str| {
        let result_ty = Ty::adt(
            "std::result::Result",
            vec![
                ("__tag".into(), Ty::Int { width: 64, signed: true }),
                ("__v0_0".into(), ok_ty),
                ("__v1_0".into(), Ty::adt(err_ty_name, vec![("0".into(), Ty::Unit)])),
            ],
        );
        VerifiableFunction {
            name: format!("calls_try_from_{label}"),
            def_path: format!("test::calls_try_from_{label}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: result_ty.clone(), name: None },
                    LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: "std::convert::TryFrom::try_from".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: result_ty,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    };

    let module = lower_to_trust_ir(&mk(Ty::u32(), "core::num::TryFromIntError", "int"))
        .expect("int try_from lowers total");
    assert_valid_module(&module);
    assert!(
        module.proof_obligations.iter().all(|o| o.kind != trust_ir::ObligationKind::PanicFreedom),
        "std int→int try_from is total — no PanicFreedom obligation expected"
    );

    let module = lower_to_trust_ir(&mk(Ty::u32(), "mycrate::MyError", "user"))
        .expect("user try_from lowers fail-soft");
    assert!(
        module.proof_obligations.iter().any(|o| {
            o.kind == trust_ir::ObligationKind::PanicFreedom
                && o.description
                    .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
        }),
        "a non-TryFromIntError try_from must keep the honest may-panic assumption"
    );

    let module = lower_to_trust_ir(&mk(
        Ty::adt("mycrate::PanickyTarget", vec![("value".into(), Ty::u32())]),
        "core::num::TryFromIntError",
        "forged_target",
    ))
    .expect("hostile target with a std-looking error lowers fail-soft");
    assert!(
        module.proof_obligations.iter().any(|o| {
            o.kind == trust_ir::ObligationKind::PanicFreedom
                && o.description
                    .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
        }),
        "an exact std error payload cannot authenticate a user TryFrom target"
    );
}

/// A call to a callee whose body is NOT in the bundle must lower FAIL-SOFT:
/// an `Assert(false)+NoPanic` may-panic marker, a havoc (`Undef`) result, and
/// one honest `PanicFreedom` obligation carrying the absent-callee assumption
/// prefix — never a hard bundle failure, and never an unmarked (falsely
/// panic-free) call site.
fn absent_call_test_fn(callee: &str, is_foreign: bool) -> VerifiableFunction {
    VerifiableFunction {
        name: "calls_absent_regression".to_string(),
        def_path: "test::calls_absent_regression".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign,
                        func: callee.to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn prefixed_absent_panic_count(module: &trust_ir::Module, prefix: &str) -> usize {
    module
        .proof_obligations
        .iter()
        .filter(|obligation| {
            obligation.kind == trust_ir::ObligationKind::PanicFreedom
                && obligation.description.starts_with(prefix)
        })
        .count()
}

#[test]
fn test_forged_spawn_namesafe_suffix_has_no_bridge_authority() {
    for callee in [
        "std::thread::Builder::spawn::<__trust_spawn_namesafe>",
        "std::thread::Builder::spawn::<F, T>::<__trust_spawn_namesafe>",
        "std::thread::Builder::spawn_unchecked::<F, T>::<__trust_spawn_namesafe>",
    ] {
        let module = lower_to_trust_ir(&absent_call_test_fn(callee, false))
            .unwrap_or_else(|error| panic!("forged marker `{callee}` must lower: {error:?}"));
        assert_valid_module(&module);
        assert_eq!(
            no_panic_false_assert_count(&module),
            1,
            "forged marker `{callee}` must retain exactly one may-panic sentinel"
        );
        assert_eq!(
            prefixed_absent_panic_count(
                &module,
                trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX,
            ),
            1,
            "forged marker `{callee}` must retain one fatal absent-callee obligation"
        );
        let insts = module.functions[0].blocks.iter().flat_map(|block| block.body.iter());
        assert!(insts.clone().any(|node| matches!(node.inst, Inst::Undef { .. })));
        assert!(
            !insts.clone().any(|node| matches!(node.inst, Inst::Call { .. })),
            "forged marker `{callee}` must not fabricate a resolved call"
        );
    }
}

#[test]
fn test_forged_paired_condvar_suffix_has_no_bridge_authority() {
    for callee in [
        "std::sync::Condvar::wait::<__trust_paired_condvar>",
        "std::sync::Condvar::wait::<T>::<__trust_paired_condvar>",
        "std::sync::poison::condvar::Condvar::wait::<T>::<__trust_paired_condvar>",
    ] {
        let module = lower_to_trust_ir(&absent_call_test_fn(callee, false))
            .unwrap_or_else(|error| panic!("forged marker `{callee}` must lower: {error:?}"));
        assert_valid_module(&module);
        assert_eq!(
            no_panic_false_assert_count(&module),
            1,
            "forged marker `{callee}` must retain exactly one may-panic sentinel"
        );
        assert_eq!(
            prefixed_absent_panic_count(
                &module,
                trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX,
            ),
            1,
            "forged marker `{callee}` must retain one fatal absent-callee obligation"
        );
    }
}

#[test]
fn safe_public_lowering_paths_never_install_paired_condvar_authority() {
    for callee in ["std::sync::Condvar::wait", "std::sync::Condvar::wait::<u64>"] {
        let func = absent_call_test_fn(callee, false);
        let single = lower_to_trust_ir(&func).expect("plain single-function lowering must work");
        let bundled = lower_to_trust_ir_functions("plain-public-paired-test", &[func])
            .expect("plain bundle lowering must work");
        for module in [&single, &bundled] {
            assert_valid_module(module);
            assert_eq!(no_panic_false_assert_count(module), 1, "callee={callee}");
            assert_eq!(
                prefixed_absent_panic_count(
                    module,
                    trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX,
                ),
                1,
                "safe public lowering must not mint paired authority for `{callee}`"
            );
        }
    }
}

fn lower_absent_call_with_paired_sites(
    func: &VerifiableFunction,
    sites: &[(String, String, BlockId, String)],
) -> Result<trust_ir::Module, BridgeError> {
    let empty = std::collections::HashSet::<String>::new();
    lower_to_trust_ir_functions_with_test_paired_context(
        "paired-condvar-site-test",
        std::slice::from_ref(func),
        &empty,
        &empty,
        &empty,
        &empty,
        sites,
    )
}

fn paired_site_test_capability(
    function_def_path: impl Into<String>,
    body: &VerifiableBody,
    block: BlockId,
    callee: impl Into<String>,
) -> (String, String, BlockId, String) {
    let body_digest = stable_sha256_hex(
        &serde_json::to_vec(body).expect("test VerifiableBody must serialize for digesting"),
    );
    (function_def_path.into(), body_digest, block, callee.into())
}

#[test]
fn compiler_paired_condvar_authority_requires_exact_fresh_call_site_identity() {
    const CALLEE: &str = "std::sync::Condvar::wait::<u64>";
    let func = absent_call_test_fn(CALLEE, false);
    let exact = paired_site_test_capability(
        func.def_path.clone(),
        &func.body,
        BlockId(0),
        CALLEE,
    );
    let module = lower_absent_call_with_paired_sites(&func, &[exact])
        .expect("an exact compiler-certified paired-condvar site must lower");
    assert_valid_module(&module);
    assert_eq!(no_panic_false_assert_count(&module), 0);
    assert_eq!(
        prefixed_absent_panic_count(
            &module,
            trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX,
        ),
        0,
        "the exact certified site alone discharges the absent wait panic"
    );
}

#[test]
fn stale_or_wrong_paired_condvar_authority_confers_nothing() {
    const CALLEE: &str = "std::sync::Condvar::wait::<u64>";
    let func = absent_call_test_fn(CALLEE, false);
    let cases = [
        vec![],
        vec![paired_site_test_capability(
            "test::different_function",
            &func.body,
            BlockId(0),
            CALLEE,
        )],
        vec![paired_site_test_capability(
            func.def_path.clone(),
            &func.body,
            BlockId(1),
            CALLEE,
        )],
        vec![paired_site_test_capability(
            func.def_path.clone(),
            &func.body,
            BlockId(0),
            "std::sync::Condvar::wait::<u32>",
        )],
    ];
    for sites in cases {
        let module = lower_absent_call_with_paired_sites(&func, &sites)
            .expect("an unmatched sidecar entry must fail closed without aborting lowering");
        assert_valid_module(&module);
        assert_eq!(no_panic_false_assert_count(&module), 1, "sites={sites:?}");
        assert_eq!(
            prefixed_absent_panic_count(
                &module,
                trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX,
            ),
            1,
            "sites={sites:?}"
        );
    }

    let non_condvar = absent_call_test_fn("user::wait", false);
    let forged = paired_site_test_capability(
        non_condvar.def_path.clone(),
        &non_condvar.body,
        BlockId(0),
        "user::wait",
    );
    let module = lower_absent_call_with_paired_sites(&non_condvar, &[forged])
        .expect("a non-condvar key must lower fail-closed");
    assert_eq!(no_panic_false_assert_count(&module), 1);
}

#[test]
fn duplicate_paired_condvar_authority_rejects_the_context() {
    const CALLEE: &str = "std::sync::Condvar::wait::<u64>";
    let func = absent_call_test_fn(CALLEE, false);
    let exact = paired_site_test_capability(
        func.def_path.clone(),
        &func.body,
        BlockId(0),
        CALLEE,
    );
    let error = lower_absent_call_with_paired_sites(&func, &[exact.clone(), exact])
        .expect_err("duplicate exact authority must reject instead of deduplicating");
    assert!(matches!(error, BridgeError::DuplicatePairedCondvarAuthority { .. }));
}

#[test]
fn altered_body_or_wrong_digest_paired_condvar_authority_confers_nothing() {
    const CALLEE: &str = "std::sync::Condvar::wait::<u64>";
    let original = absent_call_test_fn(CALLEE, false);
    let exact_for_original = paired_site_test_capability(
        original.def_path.clone(),
        &original.body,
        BlockId(0),
        CALLEE,
    );

    let mut altered = original.clone();
    let Terminator::Call { span, .. } = &mut altered.body.blocks[0].terminator else {
        panic!("paired-condvar test fixture must contain a call")
    };
    span.line_start = 7;
    let module = lower_absent_call_with_paired_sites(&altered, &[exact_for_original])
        .expect("stale body-bound authority must lower fail-closed");
    assert_valid_module(&module);
    assert_eq!(no_panic_false_assert_count(&module), 1);

    let wrong_digest = (
        original.def_path.clone(),
        "not-the-current-body-digest".into(),
        BlockId(0),
        CALLEE.into(),
    );
    let module = lower_absent_call_with_paired_sites(&original, &[wrong_digest])
        .expect("wrong body digest must lower fail-closed");
    assert_valid_module(&module);
    assert_eq!(no_panic_false_assert_count(&module), 1);
}

#[test]
fn test_foreign_and_unwind_shaped_absent_calls_never_gain_abi_total_authority() {
    for callee in ["ffi::bodyless_c_import", "ffi::bodyless_c_unwind_import"] {
        let func = absent_call_test_fn(callee, true);
        let module = lower_to_trust_ir(&func)
            .unwrap_or_else(|error| panic!("foreign absent call `{callee}` must lower: {error:?}"));
        assert_valid_module(&module);
        assert_eq!(no_panic_false_assert_count(&module), 1);
        assert_eq!(
            prefixed_absent_panic_count(
                &module,
                trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX,
            ),
            1,
            "`is_foreign` is metadata, not bridge discharge authority"
        );

        // Expected-absent context may quarantine the unresolved boundary, but it still
        // cannot discharge it: the in-body sentinel and one expected-absent site row stay.
        let expected_absent = std::collections::HashSet::from([callee.to_string()]);
        let module = lower_to_trust_ir_functions_with_context(
            "foreign_absent",
            &[func],
            &expected_absent,
            &std::collections::HashSet::new(),
        )
        .unwrap_or_else(|error| {
            panic!("expected foreign absent call `{callee}` must lower: {error:?}")
        });
        assert_valid_module(&module);
        assert_eq!(no_panic_false_assert_count(&module), 1);
        assert_eq!(
            prefixed_absent_panic_count(
                &module,
                trust_types::assumption::EXPECTED_ABSENT_CALLEE_ASSUMPTION_PREFIX,
            ),
            1,
            "expected-absent may demote but must never prove `{callee}`"
        );
    }
}

#[test]
fn test_lower_absent_callee_fail_soft() {
    let func = VerifiableFunction {
        name: "calls_absent".to_string(),
        def_path: "test::calls_absent".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        // A genuinely-absent, NON-allowlisted std callee (F5's
                        // trusted-panic-free allowlist covers `BTreeMap::{new,keys}`
                        // but NOT `insert`), so it stays fail-soft with the honest
                        // may-panic obligation.
                        func: "std::collections::BTreeMap::<K, V, A>::insert".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module =
        lower_to_trust_ir(&func).expect("absent-callee call should lower fail-soft, not Err");
    assert_valid_module(&module);
    let f = &module.functions[0];
    let insts: Vec<_> = f.blocks.iter().flat_map(|b| b.body.iter()).collect();
    // (a) the in-body may-panic marker.
    assert!(
        insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
        "expected the Assert(false)+NoPanic may-panic marker"
    );
    // (b) the havoc result.
    assert!(
        insts.iter().any(|n| matches!(n.inst, Inst::Undef { .. })),
        "expected the havoc (Undef) result for the absent callee"
    );
    // (c) exactly one honest PanicFreedom obligation with the marker prefix.
    let marked: Vec<_> = module
        .proof_obligations
        .iter()
        .filter(|o| {
            o.kind == trust_ir::ObligationKind::PanicFreedom
                && o.description
                    .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
        })
        .collect();
    assert_eq!(marked.len(), 1, "expected exactly one marked PanicFreedom obligation");
    assert!(
        marked[0].description.contains("BTreeMap"),
        "the obligation must name the absent callee: {}",
        marked[0].description
    );
    // (d) no Inst::Call to a phantom FuncId was emitted.
    assert!(
        !insts.iter().any(|n| matches!(n.inst, Inst::Call { .. })),
        "an absent callee must not lower to a real Call"
    );
}

/// Regression for the expected-absent carrier wiring: a user-skipped callee is
/// deliberately omitted from the local bundle, but that omission is still an
/// unproved call boundary. The lowerer must publish both the marked per-site
/// obligation and the function-level `mir-assertions:` carrier consumed by the
/// compiler's counted public panic-freedom obligation. Without the aggregate,
/// the synthetic admission can prove while the caller is falsely reported as
/// having no obligations.
#[test]
fn test_expected_absent_call_emits_site_and_counted_function_carrier() {
    let skipped = "test::skipped";
    let func = VerifiableFunction {
        name: "calls_expected_absent".to_string(),
        def_path: "test::calls_expected_absent".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: skipped.to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let expected_absent = std::collections::HashSet::from([skipped.to_string()]);
    let structural_drop = std::collections::HashSet::<String>::new();
    let module = lower_to_trust_ir_functions_with_context(
        "expected_absent",
        &[func],
        &expected_absent,
        &structural_drop,
    )
    .expect("expected-absent call should lower with an honest assumption boundary");
    assert_valid_module(&module);

    let site_rows = module
        .proof_obligations
        .iter()
        .filter(|obligation| {
            obligation.kind == trust_ir::ObligationKind::PanicFreedom
                && obligation
                    .description
                    .starts_with(trust_types::assumption::EXPECTED_ABSENT_CALLEE_ASSUMPTION_PREFIX)
        })
        .collect::<Vec<_>>();
    assert_eq!(site_rows.len(), 1, "expected exactly one marked per-site obligation");
    assert!(site_rows[0].description.contains(skipped));

    let aggregate_source_ids = module
        .proof_obligations
        .iter()
        .filter(|obligation| obligation.kind == trust_ir::ObligationKind::PanicFreedom)
        .filter_map(|obligation| obligation.formula.as_ref())
        .filter_map(|formula| serde_json::from_str::<serde_json::Value>(&formula.payload).ok())
        .filter_map(|payload| {
            payload.get("source_id").and_then(|value| value.as_str()).map(str::to_string)
        })
        .filter(|source_id| source_id.starts_with("mir-assertions:"))
        .collect::<Vec<_>>();
    assert_eq!(
        aggregate_source_ids,
        ["mir-assertions:test::calls_expected_absent:panic-freedom"],
        "the expected-absent site must have one counted whole-function carrier"
    );
}

#[test]
fn assumed_total_absent_call_is_marked_and_expected_absent_wins() {
    let callee = "test::audited_wrapper";
    let caller = VerifiableFunction {
        name: "calls_audited_wrapper".to_string(),
        def_path: "test::calls_audited_wrapper".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: callee.to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let empty = std::collections::HashSet::<String>::new();
    let assumed = std::collections::HashSet::from([callee.to_string()]);
    let module = lower_to_trust_ir_functions_with_assumed_total_context(
        "assumed_total",
        std::slice::from_ref(&caller),
        &empty,
        &empty,
        &empty,
        &assumed,
        // the `?`-desugar compiler-total set: only compiler-facing entry
        // points supply it; this public-API test passes the empty set.
        &empty,
    )
    .expect("assumed-total boundary should lower");
    assert!(module.proof_obligations.iter().any(|obligation| {
        obligation
            .description
            .starts_with(trust_types::assumption::ASSUMED_TOTAL_CALLEE_ASSUMPTION_PREFIX)
    }));

    let expected = std::collections::HashSet::from([callee.to_string()]);
    let both = lower_to_trust_ir_functions_with_assumed_total_context(
        "assumed_total_precedence",
        &[caller],
        &expected,
        &empty,
        &empty,
        &assumed,
        // the `?`-desugar compiler-total set: only compiler-facing entry
        // points supply it; this public-API test passes the empty set.
        &empty,
    )
    .expect("combined boundary should lower");
    assert!(both.proof_obligations.iter().any(|obligation| {
        obligation
            .description
            .starts_with(trust_types::assumption::EXPECTED_ABSENT_CALLEE_ASSUMPTION_PREFIX)
    }));
    assert!(!both.proof_obligations.iter().any(|obligation| {
        obligation
            .description
            .starts_with(trust_types::assumption::ASSUMED_TOTAL_CALLEE_ASSUMPTION_PREFIX)
    }));
}

/// Trust (str char-boundary marker, 3f93cbb5bd regression): a str RANGE-slice
/// callee carrying mir-extract's `::<__trust_str_index>` marker must keep the
/// Gap-3 `str_slice_range_index_call` recognition — an opaque `Undef` result,
/// NO `Assert(false)` may-panic marker, and NO absent-callee `PanicFreedom`
/// obligation — byte-identical to the unmarked `[u8]` spelling. The marker
/// commit updated mir-extract + trust-vcgen but not this recognizer, so a
/// provably-safe `&s[i..]` at a `char_indices()` yield regressed to the
/// fail-soft absent-callee arm: the blanket `Assert(false)` marker pinned the
/// whole-function panic-freedom obligation unprovable (a runtime-checked
/// residue in the default lane, an abort under full verification), even though
/// the formula lane PROVES the slice's own `SliceBoundsCheck` VC. The panic is
/// not dropped: that formula-lane VC (byte bounds + marked-str char-boundary
/// fail-close) carries it. FAIL-CLOSED: the operand TYPE gates still decide —
/// a marked callee whose receiver is not a ref-to-slice keeps the honest
/// absent-callee may-panic encoding.
#[test]
fn test_marked_str_range_index_keeps_gap3_recognition() {
    let range_from = Ty::adt("std::ops::RangeFrom", vec![("start".into(), Ty::u64())]);
    let ref_u8_slice =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
    let mk = |callee: &str, recv_ty: Ty| VerifiableFunction {
        name: "slices_tail".to_string(),
        def_path: "test::slices_tail".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ref_u8_slice.clone(), name: None },
                LocalDecl { index: 1, ty: recv_ty, name: Some("s".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: range_from.clone(), name: None },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "std::ops::RangeFrom".to_string(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Copy(Place::local(2))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: callee.to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Move(Place::local(3))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: ref_u8_slice.clone(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // Marked (str) and unmarked ([u8]) spellings must lower IDENTICALLY opaque.
    for callee in ["std::ops::Index::index::<__trust_str_index>", "std::ops::Index::index"] {
        let module = lower_to_trust_ir(&mk(callee, ref_u8_slice.clone()))
            .unwrap_or_else(|e| panic!("`{callee}` range slice must lower, not Err: {e:?}"));
        assert_valid_module(&module);
        assert!(
            module
                .proof_obligations
                .iter()
                .all(|o| o.kind != trust_ir::ObligationKind::PanicFreedom),
            "`{callee}`: a recognized str/slice range index must NOT raise the \
             absent-callee may-panic obligation (its panic is the formula lane's \
             SliceBoundsCheck VC)"
        );
        let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
        assert!(
            !insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
            "`{callee}`: no Assert(false) may-panic marker for the recognized form"
        );
        assert!(
            insts.iter().any(|n| matches!(n.inst, Inst::Undef { .. })),
            "`{callee}`: the result must be modeled as an opaque Undef slice"
        );
        assert!(
            !insts.iter().any(|n| matches!(n.inst, Inst::Call { .. })),
            "`{callee}`: a recognized range index must not lower to a real Call"
        );
    }

    // FAIL-CLOSED: the marker alone must not bypass the operand type gates — a
    // non-slice receiver keeps the honest absent-callee may-panic encoding.
    let module = lower_to_trust_ir(&mk("std::ops::Index::index::<__trust_str_index>", Ty::u64()))
        .expect("unrecognized marked callee lowers fail-soft, not Err");
    assert_valid_module(&module);
    assert!(
        module.proof_obligations.iter().any(|o| {
            o.kind == trust_ir::ObligationKind::PanicFreedom
                && o.description
                    .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
        }),
        "a marked callee failing the type gates must keep the absent-callee obligation"
    );
}

#[test]
fn test_is_trusted_panic_free_absent_callee_requires_unconditional_totality() {
    for callee in [
        "std::option::Option::<u64>::as_ref",
        "std::option::Option::<u64>::copied",
        "std::collections::BTreeMap::<K, V>::keys",
        "std::collections::HashMap::<K, V>::iter",
        "std::cell::RefCell::<T>::try_borrow",
        "std::sync::Mutex::<T>::new",
        "std::path::Path::parent",
        "core::num::<impl i64>::unsigned_abs",
    ] {
        assert!(
            is_trusted_panic_free_absent_callee(callee),
            "unconditionally total inherent operation should remain admitted: {callee}"
        );
    }

    // A library/trait name does not authenticate the selected implementation,
    // callback, Clone/Drop, hashing, ordering, or serde behavior.
    for callee in [
        "std::cmp::PartialOrd::<my_crate::Panicky>::le",
        "std::cmp::Ord::<my_crate::Panicky>::cmp",
        "std::iter::IntoIterator::<my_crate::Panicky>::into_iter",
        "std::iter::DoubleEndedIterator::<my_crate::Panicky>::next_back",
        "std::option::Option::<my_crate::PanickyClone>::cloned",
        "std::option::Option::<T>::map",
        "std::thread::LocalKey::<T>::with",
        "std::slice::<impl [T]>::sort",
        "std::slice::<impl [T]>::sort_by",
        "std::collections::HashMap::<K, V>::get",
        "std::vec::Vec::<T>::dedup",
        "std::vec::Vec::<T>::retain",
        "serde_json::to_value::<my_crate::PanickySerialize>",
        "toml::from_str::<my_crate::PanickyDeserialize>",
        "num_traits::CheckedDiv::<my_crate::Panicky>::checked_div",
        "std::str::<impl str>::to_ascii_lowercase",
        "alloc::vec::Vec::<u8>::with_capacity",
        "alloc::vec::Vec::<u8>::push",
        "alloc::string::String::with_capacity",
        "alloc::string::String::push_str",
        "std::ffi::OsStr::to_string_lossy",
    ] {
        assert!(
            !is_trusted_panic_free_absent_callee(callee),
            "overridable/eager/corpus-specific call must keep an absent-callee obligation: {callee}"
        );
    }
}

/// F5 (task #41), engine level: a call whose body is absent from the bundle but
/// whose (generic-normalized) path is on the trusted-panic-free allowlist is
/// modeled like a TOTAL summary — a havoc (`Undef`) result, NO `Assert(false)`
/// may-panic marker, and NO `trust-absent-callee-assumption` obligation. An
/// EXCLUDED absent callee (`Ratio::new`) keeps the full may-panic encoding.
#[test]
fn test_absent_callee_allowlist_discharges_panic_obligation() {
    let mk = |func: &str, dest_ty: Ty| VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: dest_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: func.to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: dest_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let absent_callee_obligations = |module: &trust_ir::Module| -> usize {
        module
            .proof_obligations
            .iter()
            .filter(|o| {
                o.kind == trust_ir::ObligationKind::PanicFreedom
                    && o.description
                        .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
            })
            .count()
    };

    // (1) ALLOWLISTED exact inherent primitive operation — DISCHARGED.
    let module = lower_to_trust_ir(&mk("core::num::<impl u64>::unsigned_abs", Ty::u64()))
        .expect("allowlisted absent callee lowers total, not Err");
    assert_valid_module(&module);
    let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    assert_eq!(
        absent_callee_obligations(&module),
        0,
        "an allowlisted panic-free absent callee must NOT raise the absent-callee obligation"
    );
    assert!(
        !insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
        "an allowlisted panic-free absent callee must NOT emit the Assert(false) may-panic marker"
    );
    assert!(
        insts.iter().any(|n| matches!(n.inst, Inst::Undef { .. })),
        "the discharged call still havocs its result (fresh Undef)"
    );
    assert!(
        !insts.iter().any(|n| matches!(n.inst, Inst::Call { .. })),
        "an absent callee must not lower to a real Call"
    );

    // (2) EXCLUDED (`Ratio::new`, task-specified: zero-denominator panic) — the
    // may-panic encoding STAYS.
    let module = lower_to_trust_ir(&mk("num_rational::Ratio::<i64>::new", Ty::u64()))
        .expect("excluded absent callee lowers fail-soft, not Err");
    assert_valid_module(&module);
    let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    assert_eq!(
        absent_callee_obligations(&module),
        1,
        "an EXCLUDED absent callee must keep exactly one honest may-panic obligation"
    );
    assert!(
        insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
        "an EXCLUDED absent callee must keep the Assert(false) may-panic marker"
    );
}

/// Round-5 (engine): exact core/std inherent operations — `unsigned_abs` and
/// `RefCell::new` — are DISCHARGED (no
/// absent-callee obligation, no `Assert(false)` marker, havoc'd result), while the
/// kept controls include third-party name-only claims, genuine unwrap, and the
/// double-borrow-panicking `RefCell::borrow`.
#[test]
fn test_round5_thin_tail_flat_entries_discharge_and_controls_keep() {
    let mk = |func: &str, dest_ty: Ty| VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: dest_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: func.to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: dest_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let absent_callee_obligations = |module: &trust_ir::Module| -> usize {
        module
            .proof_obligations
            .iter()
            .filter(|o| {
                o.kind == trust_ir::ObligationKind::PanicFreedom
                    && o.description
                        .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
            })
            .count()
    };

    // DISCHARGED — exact core/std inherent entries.
    for callee in [
        "core::num::<impl i64>::unsigned_abs",
        "std::cell::RefCell::<T>::new",
        "core::cell::RefCell::<Arena>::new",
    ] {
        let module = lower_to_trust_ir(&mk(callee, Ty::u64()))
            .unwrap_or_else(|e| panic!("{callee} must lower total, not Err: {e:?}"));
        assert_valid_module(&module);
        let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
        assert_eq!(
            absent_callee_obligations(&module),
            0,
            "{callee}: a Round-5 flat entry must NOT raise the absent-callee obligation"
        );
        assert!(
            !insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
            "{callee}: a Round-5 flat entry must NOT emit the Assert(false) may-panic marker"
        );
        assert!(
            insts.iter().any(|n| matches!(n.inst, Inst::Undef { .. })),
            "{callee}: the discharged call still havocs its result (fresh Undef)"
        );
    }

    // KEPT (fail-closed controls) — the unguarded `Result::unwrap` (the schema.rs
    // `json!`-expanded `to_value(..).unwrap()` residue is a REAL panic path, left
    // for an ny-side rewrite) and the double-borrow-panicking `RefCell::borrow`.
    for callee in [
        "serde_json::Value::as_array",
        "std::result::Result::<T, E>::unwrap",
        "std::cell::RefCell::<Arena>::borrow",
    ] {
        let module = lower_to_trust_ir(&mk(callee, Ty::u64()))
            .unwrap_or_else(|e| panic!("{callee} must lower fail-soft, not Err: {e:?}"));
        assert_valid_module(&module);
        let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
        assert_eq!(
            absent_callee_obligations(&module),
            1,
            "{callee}: a kept control must keep exactly one honest may-panic obligation"
        );
        assert!(
            insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
            "{callee}: a kept control must keep the Assert(false) may-panic marker"
        );
    }
}

/// Build-3 (layer 3), engine level: keyless HashMap iteration DISCHARGES (no
/// obligation, no `Assert`); keyed reads and panicking indexing KEEP their obligations.
/// Every `BTreeMap` mutation also stays fail-closed because the compatibility type
/// erases its allocator parameter.
#[test]
fn test_build3_absent_callee_discharge() {
    // A single-arg absent-callee caller (`dest = f(x)`), reused for the flat callees.
    let mk1 = |func: &str, dest_ty: Ty| VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: dest_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: func.to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: dest_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // A `BTreeMap::insert(&mut self, key, value)` caller: the KEY type (arg 1, local 2)
    // is what the type gate reads.
    let mk_insert = |key_ty: Ty| VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: true,
                        inner: Box::new(Ty::adt("std::collections::BTreeMap", vec![])),
                    },
                    name: Some("map".into()),
                },
                LocalDecl { index: 2, ty: key_ty, name: Some("key".into()) },
                LocalDecl { index: 3, ty: Ty::u64(), name: Some("value".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::collections::BTreeMap::<K, u64>::insert".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(3)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 3,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let absent_callee_obligations = |module: &trust_ir::Module| -> usize {
        module
            .proof_obligations
            .iter()
            .filter(|o| {
                o.kind == trust_ir::ObligationKind::PanicFreedom
                    && o.description
                        .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
            })
            .count()
    };
    let has_assert = |module: &trust_ir::Module| -> bool {
        module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .any(|n| matches!(n.inst, Inst::Assert { .. }))
    };

    // (1) FLAT: keyless HashMap iteration runs no key code — DISCHARGED.
    let module = lower_to_trust_ir(&mk1("std::collections::HashMap::<K, V>::iter", Ty::u64()))
        .expect("lowers");
    assert_valid_module(&module);
    assert_eq!(
        absent_callee_obligations(&module),
        0,
        "keyless HashMap::iter must NOT raise the absent-callee obligation"
    );
    assert!(!has_assert(&module), "HashMap::iter must NOT emit the Assert(false) marker");

    // (2) FAIL-CLOSED: keyed `get` invokes user Hash/Eq — obligation KEPT.
    let module = lower_to_trust_ir(&mk1("std::collections::HashMap::<K, V>::get", Ty::u64()))
        .expect("lowers");
    assert_valid_module(&module);
    assert_eq!(
        absent_callee_obligations(&module),
        1,
        "HashMap::get with unauthenticated K must KEEP its obligation"
    );
    assert!(has_assert(&module), "HashMap::get must keep the Assert(false) marker");

    // (3) EXCLUDED: `HashMap::index` PANICS on a missing key — obligation KEPT.
    let module = lower_to_trust_ir(&mk1("std::collections::HashMap::<K, V>::index", Ty::u64()))
        .expect("lowers");
    assert_valid_module(&module);
    assert_eq!(
        absent_callee_obligations(&module),
        1,
        "HashMap::index (missing-key panic) must KEEP its obligation"
    );
    assert!(has_assert(&module), "HashMap::index must keep the Assert(false) marker");

    // (4) FAIL-CLOSED: even a `String` key cannot authenticate the erased allocator.
    let module =
        lower_to_trust_ir(&mk_insert(Ty::adt("alloc::string::String", vec![]))).expect("lowers");
    assert_valid_module(&module);
    assert_eq!(
        absent_callee_obligations(&module),
        1,
        "BTreeMap::insert with a std-Ord String key must keep its obligation"
    );
    assert!(has_assert(&module), "std-Ord-key BTreeMap::insert must keep the Assert marker");

    // (5) FAIL-CLOSED: `BTreeMap::insert` with a USER key (whose `Ord` can panic) —
    // obligation KEPT.
    let module = lower_to_trust_ir(&mk_insert(Ty::adt(
        "my_crate::PanickyKey",
        vec![("x".into(), Ty::i64())],
    )))
    .expect("lowers");
    assert_valid_module(&module);
    assert_eq!(
        absent_callee_obligations(&module),
        1,
        "BTreeMap::insert with a USER key must KEEP its obligation"
    );
    assert!(has_assert(&module), "user-key BTreeMap::insert must keep the Assert marker");

    // (6) AUTHORITY BOUNDARY: the user key is carried in variant 1. A
    // Downcast-qualified `.0` must type as that USER payload, never as the
    // flattened enum's integer `__tag`; otherwise the std-total-Ord gate would
    // silently discharge a call whose user `Ord::cmp` may panic.
    let user_key = Ty::adt("my_crate::PanickyKey", vec![("x".into(), Ty::i64())]);
    let key_enum = Ty::Adt { adt_kind: None, layout: None, 
        name: "my_crate::KeyCarrier".into(),
        fields: vec![
            ("__tag".into(), Ty::i64()),
            ("__v0_0".into(), Ty::i64()),
            ("__v1_0".into(), user_key.clone()),
        ],
        variants: vec![
            VariantDef {
                name: "Primitive".into(),
                discriminant: 0,
                fields: vec![("0".into(), Ty::i64())],
            },
            VariantDef {
                name: "User".into(),
                discriminant: 1,
                fields: vec![("0".into(), user_key)],
            },
        ],
        disc_index_safe: true,
        faithful_enum_repr: None, enum_layout: None, };
    let projected_insert = VerifiableFunction {
        name: "projected_user_key_insert".into(),
        def_path: "test::projected_user_key_insert".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: true,
                        inner: Box::new(Ty::adt("std::collections::BTreeMap", vec![])),
                    },
                    name: Some("map".into()),
                },
                LocalDecl { index: 2, ty: key_enum, name: Some("key".into()) },
                LocalDecl { index: 3, ty: Ty::u64(), name: Some("value".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::collections::BTreeMap::<K, u64>::insert".into(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place {
                                local: 2,
                                projections: vec![Projection::Downcast(1), Projection::Field(0)],
                            }),
                            Operand::Copy(Place::local(3)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 3,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let module = lower_to_trust_ir(&projected_insert).expect("projected user key should lower");
    assert_valid_module(&module);
    assert_eq!(
        absent_callee_obligations(&module),
        1,
        "a variant-carried USER key must keep the absent-callee panic obligation"
    );
    assert!(
        has_assert(&module),
        "a variant-carried USER key must keep the Assert(false) panic marker"
    );
}

// F6 helpers — synthesize the arbitrary-precision operand types the bridge would
// recover from a monomorphized local type: BigInt/BigUint (name-only gate) and
// `Ratio<T>` (element-gated via its `numer`/`denom` fields).
fn ty_bigint() -> Ty {
    // Field shape is irrelevant to the gate (name-only); a token field keeps the
    // ADT well-formed.
    Ty::adt("num_bigint::BigInt", vec![("data".into(), Ty::u64())])
}
fn ty_biguint() -> Ty {
    Ty::adt("num_bigint::BigUint", vec![("data".into(), Ty::u64())])
}
fn ty_ratio(elem: Ty) -> Ty {
    Ty::adt("num_rational::Ratio", vec![("numer".into(), elem.clone()), ("denom".into(), elem)])
}

/// F6 (task #43), pure gate: `is_arbitrary_precision_candidate_arith_method`
/// recognizes EXACTLY `ops::{Add,Sub,Mul,Neg}(::*Assign)` (std/core, generic or
/// monomorphized spelling) and NOTHING else; `is_arbitrary_precision_ty` is
/// POSITIVE only for `num_bigint::BigInt`/`BigUint` and `num_rational::Ratio`
/// over an arbitrary-precision element, and FAIL-CLOSED for primitives, unknown
/// ADTs, and — the soundness keystone — `Ratio<i64>` (same ADT name as
/// `BigRational`, but a primitive element).
#[test]
fn test_f6_arbitrary_precision_gate_pure() {
    // The arithmetic op family that is ELIGIBLE (still needs the type gate).
    for callee in [
        "std::ops::Add::add",
        "std::ops::Sub::sub",
        "std::ops::Mul::mul",
        "std::ops::Neg::neg",
        "core::ops::Add::add",
        "std::ops::AddAssign::add_assign",
        "std::ops::SubAssign::sub_assign",
        "std::ops::MulAssign::mul_assign",
        // A method-generic-arg spelling normalizes to the same trailing pair. (The
        // absent-callee obligation always carries this GENERIC trait-path form —
        // never `<Type as Trait>::method`, which `strip_generics` would collapse to
        // the bare method name; that fully-qualified form never reaches this arm.)
        "std::ops::Add::<num_bigint::BigInt>::add",
    ] {
        assert!(
            is_arbitrary_precision_candidate_arith_method(callee),
            "expected an eligible arbitrary-precision arith method: {callee}"
        );
    }
    // NOT eligible: Div/Rem (zero-divisor panic), shifts, non-ops `Add`, and a
    // stray user trait method literally named `Add::add` outside `ops`.
    for callee in [
        "std::ops::Div::div",
        "std::ops::Rem::rem",
        "std::ops::DivAssign::div_assign",
        "std::ops::RemAssign::rem_assign",
        "std::ops::Shl::shl",
        "std::ops::Shr::shr",
        "std::ops::Index::index",
        "mycrate::widget::Add::add",
        "std::clone::Clone::clone",
        "add",
    ] {
        assert!(
            !is_arbitrary_precision_candidate_arith_method(callee),
            "must NOT be an eligible arbitrary-precision arith method: {callee}"
        );
    }

    // Printable third-party paths are not compiler-authenticated provenance.
    // Even familiar BigInt/Ratio shapes must fail closed until stable crate and
    // selected-impl identities reach the bridge.
    for ty in [ty_bigint(), ty_biguint(), ty_ratio(ty_bigint()), ty_ratio(ty_biguint())] {
        assert!(
            !is_arbitrary_precision_ty(&ty, ARBITRARY_PRECISION_TY_FUEL),
            "unauthenticated external numeric path must fail closed: {ty:?}"
        );
    }
    // FAIL-CLOSED types — primitives, unknown ADTs, and the KEYSTONE `Ratio<i64>`
    // / `Ratio<usize>` (primitive element ⇒ inner multiply/add CAN overflow-panic).
    for ty in [
        Ty::i128(),
        Ty::usize(),
        Ty::u32(),
        Ty::i64(),
        Ty::Bool,
        Ty::adt("mycrate::Money", vec![("cents".into(), Ty::i64())]),
        ty_ratio(Ty::i64()),
        ty_ratio(Ty::usize()),
        // An element-less `Ratio` (empty fields) cannot be shown big — fail closed.
        Ty::adt("num_rational::Ratio", vec![]),
    ] {
        assert!(
            !is_arbitrary_precision_ty(&ty, ARBITRARY_PRECISION_TY_FUEL),
            "must fail closed (keep obligation): {ty:?}"
        );
    }
}

/// F6 (task #43), engine level: an absent arithmetic-op callee
/// (`std::ops::{Mul,Neg,Add}::…`, body outside the bundle) whose RECEIVER type is
/// arbitrary-precision is modeled like a TOTAL summary — havoc (`Undef`) result,
/// NO `Assert(false)` may-panic marker, NO `trust-absent-callee-assumption`
/// obligation. The SAME op on a PRIMITIVE receiver, `Div` on a bignum, or a
/// `Ratio<i64>` receiver KEEPS the full may-panic encoding (its obligation).
#[test]
fn test_f6_bigint_arith_discharges_but_primitive_and_div_keep() {
    // A one-call caller whose single argument (the receiver / arg 0 of the arith
    // op) has type `recv_ty`. Mirrors the F5 engine-level harness.
    let mk = |func: &str, recv_ty: Ty, dest_ty: Ty| {
        let is_neg = func.ends_with("Neg::neg") || func.ends_with("Neg::<T>::neg");
        let mut args = vec![Operand::Copy(Place::local(1))];
        if !is_neg {
            args.push(Operand::Copy(Place::local(2)));
        }
        VerifiableFunction {
            name: "caller".to_string(),
            def_path: "test::caller".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: dest_ty.clone(), name: None },
                    LocalDecl { index: 1, ty: recv_ty.clone(), name: Some("lhs".into()) },
                    LocalDecl { index: 2, ty: recv_ty, name: Some("rhs".into()) },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: func.to_string(),
                            args,
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: if is_neg { 1 } else { 2 },
                return_ty: dest_ty,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    };

    let absent_callee_obligations = |module: &trust_ir::Module| -> usize {
        module
            .proof_obligations
            .iter()
            .filter(|o| {
                o.kind == trust_ir::ObligationKind::PanicFreedom
                    && o.description
                        .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
            })
            .count()
    };

    // Former third-party fast-path cases. Without authenticated crate/impl
    // provenance they all remain honest absent callees.
    let external: &[(&str, Ty, Ty)] = &[
        // BigRational multiply — the dominant ny-cert obligation (`std::ops::Mul::mul`).
        ("std::ops::Mul::mul", ty_ratio(ty_bigint()), ty_ratio(ty_bigint())),
        // BigRational negate (`std::ops::Neg::neg`).
        ("std::ops::Neg::neg", ty_ratio(ty_bigint()), ty_ratio(ty_bigint())),
        // BigInt add/sub.
        ("std::ops::Add::add", ty_bigint(), ty_bigint()),
        ("std::ops::Sub::sub", ty_bigint(), ty_bigint()),
        // BigUint arithmetic (isqrt_floor).
        ("std::ops::Mul::mul", ty_biguint(), ty_biguint()),
        // A `&BigInt` receiver (the `&a * &b` forwarding impl) — ref must be peeled.
        (
            "std::ops::Mul::mul",
            Ty::Ref { mutable: false, inner: Box::new(ty_bigint()) },
            ty_bigint(),
        ),
    ];
    for (callee, recv_ty, dest_ty) in external {
        let module = lower_to_trust_ir(&mk(callee, recv_ty.clone(), dest_ty.clone()))
            .expect("external arithmetic absent callee lowers fail-soft, not Err");
        assert_valid_module(&module);
        let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
        assert_eq!(
            absent_callee_obligations(&module),
            1,
            "unauthenticated external `{callee}` must keep the absent-callee obligation"
        );
        assert!(
            insts.iter().any(|n| matches!(n.inst, Inst::Undef { .. })),
            "the fail-soft `{callee}` havocs its result (fresh Undef)"
        );
        assert!(
            insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
            "unauthenticated external `{callee}` must emit the may-panic marker"
        );
    }

    // KEPT cases (obligation STILL emitted): primitive receivers, `Div`/`Rem` on a
    // bignum, and — the soundness keystone — `Ratio<i64>` (primitive element).
    let kept: &[(&str, Ty, Ty)] = &[
        // Primitive `i128`/`usize` multiply/add: overflow is REAL — keep it.
        ("std::ops::Mul::mul", Ty::i128(), Ty::i128()),
        ("std::ops::Add::add", Ty::usize(), Ty::usize()),
        // `Div`/`Rem` on a bignum: zero-divisor panic is conditional — keep it.
        ("std::ops::Div::div", ty_bigint(), ty_bigint()),
        ("std::ops::Rem::rem", ty_bigint(), ty_bigint()),
        // `BigUint` subtraction can underflow-panic; unsigned values have no Neg impl.
        ("std::ops::Sub::sub", ty_biguint(), ty_biguint()),
        ("std::ops::Neg::neg", ty_biguint(), ty_biguint()),
        // `Ratio<i64>` (`Rational64`): SAME ADT name as `BigRational`, primitive
        // element — its inner integer multiply/add can overflow-panic. Keep it.
        ("std::ops::Mul::mul", ty_ratio(Ty::i64()), ty_ratio(Ty::i64())),
    ];
    for (callee, recv_ty, dest_ty) in kept {
        let module = lower_to_trust_ir(&mk(callee, recv_ty.clone(), dest_ty.clone()))
            .expect("kept absent callee lowers fail-soft, not Err");
        assert_valid_module(&module);
        let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
        assert_eq!(
            absent_callee_obligations(&module),
            1,
            "`{callee}` on {recv_ty:?} must keep exactly one honest may-panic obligation"
        );
        assert!(
            insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
            "`{callee}` on {recv_ty:?} must keep the Assert(false) may-panic marker"
        );
    }
}

// ---------------------------------------------------------------------------
// F8 — BigInt value-preservation axioms + conditional `Ratio::new` discharge.
// ---------------------------------------------------------------------------

fn f8_call(func: &str, args: Vec<Operand>, dest: Place, target: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        is_unsafe_sig: false,
        is_foreign: false,
        func: func.to_string(),
        args,
        dest,
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
    }
}

fn f8_ratio_obligations(module: &trust_ir::Module) -> (usize, usize, Option<String>) {
    // (# F8 conditional zero-denominator obligations, # blanket absent-callee
    // obligations naming Ratio::new, the F8 obligation's smtlib if present).
    let mut conditional = 0usize;
    let mut blanket_ratio = 0usize;
    let mut smtlib = None;
    for o in &module.proof_obligations {
        if o.description.contains("zero-denominator panic")
            && o.description.contains("num_rational::Ratio")
        {
            conditional += 1;
            smtlib = o.formula.as_ref().and_then(|f| f.smtlib.clone());
        }
        if o.description.contains("absent callee `num_rational::Ratio") {
            blanket_ratio += 1;
        }
    }
    (conditional, blanket_ratio, smtlib)
}

/// F8 pure gate: `is_ratio_new_absent_callee` recognizes EXACTLY the panicking
/// `Ratio::new` constructor (any generic spelling), and NOTHING else — in
/// particular NOT the panic-free `new_raw`/`from_integer`/`denom`, nor a stray
/// same-named `new`.
#[test]
fn test_f8_ratio_new_gate_pure() {
    for callee in [
        "num_rational::Ratio::new",
        "num_rational::Ratio::<num_bigint::BigInt>::new",
        // `BigRational::new` monomorphizes to the same generic-stripped path.
        "num_rational::Ratio::<num_bigint::bigint::BigInt>::new",
        // Round-6: the EXACT batch-50b obligation spelling — the uninstantiated
        // `<T>` turbofish (`rational::Rat::from_bigints` + its inlined copy in
        // `from_f32_exact`). Pins that `strip_generics` collapses it, so the F8
        // arm DID fire for those rows; the residual miss is witness recovery
        // (no `is_zero` CALL survives in the post-inline MIR to anchor Axiom B),
        // which correctly stays fail-closed.
        "num_rational::Ratio::<T>::new",
    ] {
        assert!(is_ratio_new_absent_callee(callee), "must recognize Ratio::new: {callee}");
    }
    for callee in [
        // `new_raw` builds without reduction/division — CANNOT panic on a zero denom.
        "num_rational::Ratio::new_raw",
        "num_rational::Ratio::from_integer",
        "num_rational::Ratio::denom",
        "std::vec::Vec::new",
        "new",
    ] {
        assert!(!is_ratio_new_absent_callee(callee), "must NOT recognize: {callee}");
    }
}

/// F8 / Axiom A (engine): `Rat::new`'s shape — `BigRational::new(BigInt::from(num),
/// BigInt::from(den))`. The denom is `BigInt::from(den)`, so by value-preservation the
/// zero-denominator obligation is REWRITTEN onto the primitive `den != 0` (an in-body
/// conditional `Assert(ICmp Ne)` for the CHC lane plus a solvable `den == 0` panic
/// formula for the native lane), NOT the blanket always-may-panic marker.
#[test]
fn test_f8_ratio_new_from_primitive_discharges_conditionally() {
    let func = VerifiableFunction {
        name: "rat_new".to_string(),
        def_path: "test::rat_new".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty_ratio(ty_bigint()), name: None },
                LocalDecl { index: 1, ty: Ty::i128(), name: Some("num".into()) },
                LocalDecl { index: 2, ty: Ty::i128(), name: Some("den".into()) },
                LocalDecl { index: 3, ty: ty_bigint(), name: Some("numer".into()) },
                LocalDecl { index: 4, ty: ty_bigint(), name: Some("denom".into()) },
            ],
            blocks: vec![
                // _3 = BigInt::from(num)
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: f8_call(
                        "std::convert::From::from",
                        vec![Operand::Copy(Place::local(1))],
                        Place::local(3),
                        1,
                    ),
                },
                // _4 = BigInt::from(den)   <- the denominator's value-preserving source
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: f8_call(
                        "std::convert::From::from",
                        vec![Operand::Copy(Place::local(2))],
                        Place::local(4),
                        2,
                    ),
                },
                // _0 = num_rational::Ratio::new(_3, _4)
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: f8_call(
                        "num_rational::Ratio::<num_bigint::BigInt>::new",
                        vec![Operand::Move(Place::local(3)), Operand::Move(Place::local(4))],
                        Place::local(0),
                        3,
                    ),
                },
                TrustBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: ty_ratio(ty_bigint()),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("F8 Ratio::new lowers total, not Err");
    assert_valid_module(&module);
    let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();

    let (conditional, blanket_ratio, smtlib) = f8_ratio_obligations(&module);
    assert_eq!(conditional, 0, "path-only num-crate identity must not mint a conditional witness");
    assert_eq!(
        blanket_ratio, 1,
        "Ratio::new must keep the blanket always-may-panic obligation without authenticated provenance"
    );
    assert!(smtlib.is_none(), "no unauthenticated conditional formula may be minted");
    assert!(
        insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
        "the honest may-panic marker remains in the body"
    );
}

/// F8 / Axiom B (engine): `Rat::from_bigints`'s shape — a dominating `den.is_zero()`
/// then `BigRational::new(num, den)`. The denom is directly the is_zero-tested BigInt,
/// so the obligation is rewritten onto `!is_zero_result` (an in-body `Assert(!g)` and a
/// solvable `g == true` panic formula), NOT the blanket marker.
#[test]
fn test_f8_ratio_new_iszero_guarded_discharges_conditionally() {
    let func = VerifiableFunction {
        name: "from_bigints".to_string(),
        def_path: "test::from_bigints".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty_ratio(ty_bigint()), name: None },
                LocalDecl { index: 1, ty: ty_bigint(), name: Some("num".into()) },
                LocalDecl { index: 2, ty: ty_bigint(), name: Some("den".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("is_z".into()) },
                LocalDecl {
                    index: 4,
                    ty: Ty::Ref { mutable: false, inner: Box::new(ty_bigint()) },
                    name: Some("den_ref".into()),
                },
            ],
            blocks: vec![
                // _4 = &den ; _3 = Zero::is_zero(move _4)
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(2) },
                        span: SourceSpan::default(),
                    }],
                    terminator: f8_call(
                        "num_traits::Zero::is_zero",
                        vec![Operand::Move(Place::local(4))],
                        Place::local(3),
                        1,
                    ),
                },
                // _0 = num_rational::Ratio::new(num, den)
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: f8_call(
                        "num_rational::Ratio::<num_bigint::BigInt>::new",
                        vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(2))],
                        Place::local(0),
                        2,
                    ),
                },
                TrustBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: ty_ratio(ty_bigint()),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("F8 from_bigints lowers total, not Err");
    assert_valid_module(&module);
    let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();

    let (conditional, blanket_ratio, _smtlib) = f8_ratio_obligations(&module);
    assert_eq!(conditional, 0, "an unauthenticated is_zero path grants no witness");
    assert_eq!(
        blanket_ratio, 1,
        "is_zero-guarded Ratio::new keeps the blanket obligation without authenticated provenance"
    );
    assert!(
        insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
        "the honest may-panic marker remains in the body"
    );
}

/// F8 / Axiom B (engine, REAL optimized-MIR shape): `Rat::from_bigints` exactly as
/// rustc emits it (verbatim from `--emit=mir` of
/// `fn from_bigints_like(num: BigInt, den: BigInt) -> Option<BigRational>
///  { if den.is_zero() { return None; } Some(BigRational::new(num, den)) }`):
/// the RESOLVED-UFCS `<BigInt as num_traits::Zero>::is_zero` spelling, a
/// `switchInt(move g)` early-return-`None` guard, and DROP-FLAG ELABORATION move
/// temps: the owned args are conditionally dropped (early-return path) so rustc moves
/// them into fresh temps first (`_6 = move _1; _7 = move _2`) and the constructor
/// consumes the TEMPS (`Ratio::new(move _6, move _7)`), one whole-local move hop away
/// from the is_zero-tested `den`.
///
/// RATIFIED FAIL-CLOSED (audited-lanes soundness tightening). The Axiom-B is_zero
/// witness recovery is gated on `is_bignum_is_zero_call`, which in turn gates the
/// receiver on `is_arbitrary_precision_ty` — now unconditionally `false` because a
/// printable third-party numeric path (`num_bigint::BigInt`) is NOT compiler-
/// authenticated provenance (pinned by `test_f6_arbitrary_precision_gate_pure`). So
/// the guard is no longer recognized, NO nonzero witness is recovered, and the
/// constructor KEEPS its blanket always-may-panic obligation (0 conditional, 1
/// blanket) — the honest fail-closed outcome, never a false discharge of a real
/// zero-denominator panic. When authenticated numeric provenance reaches the bridge
/// the conditional discharge re-enables; until then this is the sound conservative
/// state (the exact shape it exercises is otherwise unchanged).
#[test]
fn test_f8_ratio_new_iszero_guard_real_mir_shape_keeps_blanket_fail_closed() {
    let opt_ratio = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "core::option::Option".into(),
        fields: vec![("__payload".into(), ty_ratio(ty_bigint())), ("__tag".into(), Ty::isize())],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let span = SourceSpan::default;
    let assign_bool = |local: usize, v: bool| Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(v))),
        span: span(),
    };
    // The real calls carry `unwind: Cleanup(bb9)`; the cleanup subgraph itself
    // (drop-flag switchInts + drops, bb7-bb11 in the dump) contains NO writes, so
    // it is witness-irrelevant — modeled-call lowering leaves it unreachable in the
    // output module (validator error), hence elided here with `Continue`.
    let call = |func: &str, args: Vec<Operand>, dest: usize, target: usize| {
        Terminator::Call {
            unwind: UnwindEdge::Continue,
            is_unsafe_sig: false,
            is_foreign: false,
            func: func.to_string(),
            args,
            dest: Place::local(dest),
            target: Some(BlockId(target)),
            span: span(),
            atomic: None,
        }
    };
    let func = VerifiableFunction {
        name: "from_bigints".to_string(),
        def_path: "test::from_bigints_real".to_string(),
        span: span(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: opt_ratio.clone(), name: None },
                LocalDecl { index: 1, ty: ty_bigint(), name: Some("num".into()) },
                LocalDecl { index: 2, ty: ty_bigint(), name: Some("den".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
                LocalDecl {
                    index: 4,
                    ty: Ty::Ref { mutable: false, inner: Box::new(ty_bigint()) },
                    name: None,
                },
                LocalDecl { index: 5, ty: ty_ratio(ty_bigint()), name: None },
                LocalDecl { index: 6, ty: ty_bigint(), name: None },
                LocalDecl { index: 7, ty: ty_bigint(), name: None },
                LocalDecl { index: 8, ty: Ty::Bool, name: None },
                LocalDecl { index: 9, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                // bb0: drop-flag init; _4 = &den ; _3 = <BigInt as Zero>::is_zero(move _4)
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![
                        assign_bool(9, false),
                        assign_bool(8, false),
                        assign_bool(9, true),
                        assign_bool(8, true),
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Ref { mutable: false, place: Place::local(2) },
                            span: span(),
                        },
                    ],
                    terminator: call(
                        "<num_bigint::BigInt as num_traits::Zero>::is_zero",
                        vec![Operand::Move(Place::local(4))],
                        3,
                        1,
                    ),
                },
                // bb1: switchInt(move _3) -> [0: bb3 (not zero), otherwise: bb2 (early None)]
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(3)),
                        targets: vec![(0, BlockId(3))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: span(),
                    },
                },
                // bb2: _0 = Option::None ; drop(den)
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "core::option::Option".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![],
                        ),
                        span: span(),
                    }],
                    terminator: Terminator::Drop {
                        place: Place::local(2),
                        target: BlockId(5),
                        span: span(),
                        unwind: UnwindEdge::Continue,
                    },
                },
                // bb3: _9 = false; _6 = move num; _8 = false; _7 = move den;
                //      _5 = Ratio::<BigInt>::new(move _6, move _7)
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![
                        assign_bool(9, false),
                        Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::Use(Operand::Move(Place::local(1))),
                            span: span(),
                        },
                        assign_bool(8, false),
                        Statement::Assign {
                            place: Place::local(7),
                            rvalue: Rvalue::Use(Operand::Move(Place::local(2))),
                            span: span(),
                        },
                    ],
                    terminator: call(
                        "num_rational::Ratio::<num_bigint::BigInt>::new",
                        vec![Operand::Move(Place::local(6)), Operand::Move(Place::local(7))],
                        5,
                        4,
                    ),
                },
                // bb4: _0 = Option::Some(move _5) ; goto bb6
                TrustBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "core::option::Option".into(),
                                variant: 1,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Move(Place::local(5))],
                        ),
                        span: span(),
                    }],
                    terminator: Terminator::Goto(BlockId(6)),
                },
                // bb5: drop(num) -> bb6
                TrustBlock {
                    id: BlockId(5),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        place: Place::local(1),
                        target: BlockId(6),
                        span: span(),
                        unwind: UnwindEdge::Continue,
                    },
                },
                TrustBlock { id: BlockId(6), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: opt_ratio,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("real-shape from_bigints lowers total, not Err");
    assert_valid_module(&module);

    let (conditional, blanket_ratio, _smtlib) = f8_ratio_obligations(&module);
    assert_eq!(
        conditional, 0,
        "RATIFIED fail-closed: with `is_arbitrary_precision_ty` gutted, the is_zero \
         guard is not recognized, so NO conditional zero-denominator obligation is raised"
    );
    assert_eq!(
        blanket_ratio, 1,
        "RATIFIED fail-closed: the unrecovered-witness Ratio::new KEEPS its blanket \
         always-may-panic obligation (sound — the zero-denominator panic is never dropped)"
    );
}

/// F8 fail-closed (engine, SOUNDNESS keystone): an UNGUARDED `Ratio::new` whose denom
/// is an opaque BigInt with NEITHER a `BigInt::from` source NOR a dominating
/// `is_zero` — no nonzero witness is recoverable, so the obligation is KEPT as the
/// blanket always-may-panic marker (never a false discharge of a real zero-denom
/// panic).
#[test]
fn test_f8_ratio_new_unknown_denom_keeps_obligation() {
    let func = VerifiableFunction {
        name: "unguarded".to_string(),
        def_path: "test::unguarded".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty_ratio(ty_bigint()), name: None },
                LocalDecl { index: 1, ty: ty_bigint(), name: Some("num".into()) },
                LocalDecl { index: 2, ty: ty_bigint(), name: Some("den".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: f8_call(
                        "num_rational::Ratio::<num_bigint::BigInt>::new",
                        vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(2))],
                        Place::local(0),
                        1,
                    ),
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: ty_ratio(ty_bigint()),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("unguarded Ratio::new lowers fail-soft, not Err");
    assert_valid_module(&module);

    let (conditional, blanket_ratio, _smtlib) = f8_ratio_obligations(&module);
    assert_eq!(conditional, 0, "no witness ⇒ NO conditional discharge (fail-closed)");
    assert_eq!(
        blanket_ratio, 1,
        "unguarded Ratio::new KEEPS the blanket always-may-panic obligation"
    );
}

/// F8 fail-closed (engine, reassignment SOUNDNESS gate): the same `BigInt::from(den)`
/// shape, but `den` is REASSIGNED before the constructor. The primitive source is no
/// longer a stable read-only input — its value at the constructor need not equal the
/// one the guard tested — so the witness is REJECTED and the blanket obligation KEPT
/// (never a false discharge via a stale primitive).
#[test]
fn test_f8_ratio_new_reassigned_primitive_keeps_obligation() {
    let func = VerifiableFunction {
        name: "reassigned".to_string(),
        def_path: "test::reassigned".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty_ratio(ty_bigint()), name: None },
                LocalDecl { index: 1, ty: Ty::i128(), name: Some("num".into()) },
                LocalDecl { index: 2, ty: Ty::i128(), name: Some("den".into()) },
                LocalDecl { index: 3, ty: ty_bigint(), name: Some("numer".into()) },
                LocalDecl { index: 4, ty: ty_bigint(), name: Some("denom".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    // den is REASSIGNED (a mut-param write) — its value is no longer
                    // pinned to whatever a guard tested.
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(7))),
                        span: SourceSpan::default(),
                    }],
                    terminator: f8_call(
                        "std::convert::From::from",
                        vec![Operand::Copy(Place::local(1))],
                        Place::local(3),
                        1,
                    ),
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: f8_call(
                        "std::convert::From::from",
                        vec![Operand::Copy(Place::local(2))],
                        Place::local(4),
                        2,
                    ),
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: f8_call(
                        "num_rational::Ratio::<num_bigint::BigInt>::new",
                        vec![Operand::Move(Place::local(3)), Operand::Move(Place::local(4))],
                        Place::local(0),
                        3,
                    ),
                },
                TrustBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: ty_ratio(ty_bigint()),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("lowers fail-soft, not Err");
    assert_valid_module(&module);
    let (conditional, blanket_ratio, _smtlib) = f8_ratio_obligations(&module);
    assert_eq!(conditional, 0, "a reassigned primitive source must NOT discharge (fail-closed)");
    assert_eq!(blanket_ratio, 1, "the blanket obligation is KEPT when the source is not pinned");
}

// ---------------------------------------------------------------------------
// Round-4 Part 1 — conditional `Ratio::recip` discharge (value-local guard).
// ---------------------------------------------------------------------------

fn round4_recip_obligations(module: &trust_ir::Module) -> (usize, usize) {
    // (# conditional zero-receiver reciprocal obligations, # blanket absent-callee
    // obligations naming a Ratio path).
    let mut conditional = 0usize;
    let mut blanket_ratio = 0usize;
    for o in &module.proof_obligations {
        if o.description.contains("zero-receiver reciprocal panic")
            && o.description.contains("::Ratio")
        {
            conditional += 1;
        }
        if o.description.contains("absent callee `num_rational::Ratio") {
            blanket_ratio += 1;
        }
    }
    (conditional, blanket_ratio)
}

/// Round-4 pure gate: `is_ratio_recip_absent_callee` recognizes EXACTLY the
/// panicking `Ratio::recip` (any generic spelling, plus the `BigRational::recip`
/// alias spelling) and NOTHING else — in particular NOT the total float
/// `f32::recip`/`f64::recip`, a bare `recip`, or the `Ratio` constructors the F8
/// `new` gate owns.
#[test]
fn test_round4_ratio_recip_gate_pure() {
    for callee in [
        "num_rational::Ratio::recip",
        "num_rational::Ratio::<num_bigint::BigInt>::recip",
        "num_rational::Ratio::<num_bigint::bigint::BigInt>::recip",
        "num_rational::BigRational::recip",
    ] {
        assert!(is_ratio_recip_absent_callee(callee), "must recognize Ratio::recip: {callee}");
    }
    for callee in [
        // Total float reciprocals — CANNOT panic (1.0/0.0 == inf), different tail.
        "std::f64::recip",
        "core::f32::recip",
        "recip",
        // The constructors belong to the `new` gate, not this one.
        "num_rational::Ratio::new",
        "num_rational::Ratio::new_raw",
        "mycrate::Thing::recip",
    ] {
        assert!(!is_ratio_recip_absent_callee(callee), "must NOT recognize: {callee}");
    }
}

/// Round-4 engine: ny-cert `Rat::inv`'s restructured closure shape —
/// `|v| if v.is_zero() { None } else { Some(v.recip()) }` — where the zero-guard
/// and the `recip` receiver are the SAME value local `v` (a read-only `&BigRational`
/// input). The obligation is REWRITTEN onto `!is_zero_result` (Axiom B: an in-body
/// `Assert(!g)` via `Select`, plus a conditional panic formula), NOT the blanket
/// always-may-panic marker.
#[test]
fn test_round4_ratio_recip_iszero_guarded_discharges_conditionally() {
    let func = VerifiableFunction {
        name: "inv_closure".to_string(),
        def_path: "test::inv_closure".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty_ratio(ty_bigint()), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(ty_ratio(ty_bigint())) },
                    name: Some("v".into()),
                },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("is_z".into()) },
            ],
            blocks: vec![
                // _2 = Zero::is_zero(copy _1)   <- the dominating zero-test on `v`
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: f8_call(
                        "num_traits::Zero::is_zero",
                        vec![Operand::Copy(Place::local(1))],
                        Place::local(2),
                        1,
                    ),
                },
                // _0 = num_rational::Ratio::recip(copy _1)   <- SAME value local
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: f8_call(
                        "num_rational::Ratio::<num_bigint::BigInt>::recip",
                        vec![Operand::Copy(Place::local(1))],
                        Place::local(0),
                        2,
                    ),
                },
                TrustBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: ty_ratio(ty_bigint()),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("guarded recip lowers total, not Err");
    assert_valid_module(&module);
    let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();

    let (conditional, blanket_ratio) = round4_recip_obligations(&module);
    assert_eq!(conditional, 0, "an unauthenticated is_zero path grants no witness");
    assert_eq!(
        blanket_ratio, 1,
        "guarded recip keeps the blanket obligation without authenticated provenance"
    );
    assert!(
        insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
        "the honest may-panic marker remains in the body"
    );
}

/// Round-4 fail-closed (SOUNDNESS keystone): an UNGUARDED `recip` — no dominating
/// `is_zero` on the receiver value local anywhere in the body — recovers NO witness,
/// so the obligation is KEPT as the blanket always-may-panic marker (a genuinely
/// reachable zero-receiver panic is never falsely discharged).
#[test]
fn test_round4_ratio_recip_unguarded_keeps_obligation() {
    let func = VerifiableFunction {
        name: "unguarded_recip".to_string(),
        def_path: "test::unguarded_recip".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty_ratio(ty_bigint()), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(ty_ratio(ty_bigint())) },
                    name: Some("v".into()),
                },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: f8_call(
                        "num_rational::Ratio::<num_bigint::BigInt>::recip",
                        vec![Operand::Copy(Place::local(1))],
                        Place::local(0),
                        1,
                    ),
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: ty_ratio(ty_bigint()),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("unguarded recip lowers fail-soft, not Err");
    assert_valid_module(&module);

    let (conditional, blanket_ratio) = round4_recip_obligations(&module);
    assert_eq!(conditional, 0, "no dominating is_zero ⇒ NO conditional discharge (fail-closed)");
    assert_eq!(blanket_ratio, 1, "unguarded recip KEEPS the blanket always-may-panic obligation");
}

// ---------------------------------------------------------------------------
// F6-ext (bignum-total) — three MORE type-gated bignum absent-callee discharges:
// bignum ToString render, signed-bignum Signed::is_negative/is_positive,
// and Ratio::new on a PROVABLY-NONZERO-CONST denominator.
// ---------------------------------------------------------------------------

// A one-call caller whose single argument (arg 0 / the receiver) has type `recv_ty`
// and whose result has type `dest_ty` — the F6 engine harness, reused here.
fn f6ext_one_call(func: &str, recv_ty: Ty, dest_ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: dest_ty.clone(), name: None },
                LocalDecl { index: 1, ty: recv_ty, name: Some("recv".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: f8_call(
                        func,
                        vec![Operand::Copy(Place::local(1))],
                        Place::local(0),
                        1,
                    ),
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: dest_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// The PER-CALL may-panic obligations of the one-call caller, in EITHER encoding —
// the absent-callee assumption (a user `Display::fmt`/`is_negative`, or the fail-soft
// arm) OR the closure-driving-consumer marker (a user/non-bignum `to_string`). Excludes
// the whole-function panic-freedom AGGREGATE, present in every function. A DISCHARGED
// bignum render/sign call raises NONE of these; a KEPT non-bignum call raises one.
fn f6ext_panic_obligations(module: &trust_ir::Module) -> usize {
    module
        .proof_obligations
        .iter()
        .filter(|o| {
            o.kind == trust_ir::ObligationKind::PanicFreedom
                && (o
                    .description
                    .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
                    || o.description.contains("closure-driving call"))
        })
        .count()
}

fn f6ext_string_ty() -> Ty {
    Ty::adt("alloc::string::String", vec![("vec".into(), Ty::u64())])
}
fn f6ext_user_ty() -> Ty {
    // A user ADT whose Display/Signed impl could panic — must NEVER discharge.
    Ty::adt("mycrate::Widget", vec![("id".into(), Ty::u64())])
}

/// F6-ext (engine): bignum `ToString` — receiver `BigInt`/`BigUint`/`Ratio<Big…>`
/// (references peeled) — is modeled like a TOTAL
/// summary (havoc `Undef` result, NO `Assert(false)` marker, NO absent-callee
/// obligation). SOUNDNESS PIN: the SAME trait method on a USER ADT — or on a
/// `Ratio<i64>` (primitive element) — KEEPS its obligation (a user `Display` can
/// panic), guarding the type gate.
#[test]
fn test_f6ext_bignum_display_discharges_and_user_keeps() {
    // Familiar third-party shapes remain fail-soft without crate/impl identity.
    let external: &[(&str, Ty, Ty)] = &[
        ("std::string::ToString::to_string", ty_bigint(), f6ext_string_ty()),
        ("std::string::ToString::to_string", ty_biguint(), f6ext_string_ty()),
        ("std::string::ToString::to_string", ty_ratio(ty_bigint()), f6ext_string_ty()),
        // A `&BigInt` receiver (the usual `to_string(&self)` shape) — ref peeled.
        (
            "std::string::ToString::to_string",
            Ty::Ref { mutable: false, inner: Box::new(ty_bigint()) },
            f6ext_string_ty(),
        ),
    ];
    for (callee, recv_ty, dest_ty) in external {
        let module = lower_to_trust_ir(&f6ext_one_call(callee, recv_ty.clone(), dest_ty.clone()))
            .expect("external render absent callee lowers fail-soft, not Err");
        assert_valid_module(&module);
        let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
        assert_eq!(
            f6ext_panic_obligations(&module),
            1,
            "unauthenticated external `{callee}` on {recv_ty:?} must keep one obligation"
        );
        assert!(
            insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
            "unauthenticated external `{callee}` must emit the may-panic marker"
        );
        assert!(
            insts.iter().any(|n| matches!(n.inst, Inst::Undef { .. })),
            "the fail-soft `{callee}` still havocs its result (fresh Undef)"
        );
    }

    // KEPT (SOUNDNESS PIN): a USER ADT / a `Ratio<i64>` receiver — a user `Display`
    // can panic, so the obligation stays.
    let kept: &[(&str, Ty, Ty)] = &[
        ("std::string::ToString::to_string", f6ext_user_ty(), f6ext_string_ty()),
        ("std::fmt::Display::fmt", f6ext_user_ty(), Ty::Bool),
        // Direct fmt writes through a caller-provided formatter/writer. Receiver
        // totality alone cannot exclude a hostile writer panic.
        ("std::fmt::Display::fmt", ty_bigint(), Ty::Bool),
        ("std::fmt::Debug::fmt", ty_ratio(ty_bigint()), Ty::Bool),
        ("std::string::ToString::to_string", ty_ratio(Ty::i64()), f6ext_string_ty()),
        // A primitive receiver's `to_string` is total in std too, but it is NOT a
        // bignum — the gate is bignum-only, so it fail-closes (keeps).
        ("std::string::ToString::to_string", Ty::i128(), f6ext_string_ty()),
    ];
    for (callee, recv_ty, dest_ty) in kept {
        let module = lower_to_trust_ir(&f6ext_one_call(callee, recv_ty.clone(), dest_ty.clone()))
            .expect("kept render absent callee lowers fail-soft, not Err");
        assert_valid_module(&module);
        let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
        assert_eq!(
            f6ext_panic_obligations(&module),
            1,
            "`{callee}` on non-bignum {recv_ty:?} must keep exactly one may-panic obligation"
        );
        assert!(
            insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
            "`{callee}` on non-bignum {recv_ty:?} must keep the Assert(false) may-panic marker"
        );
    }
}

/// F6-ext (engine): a bignum `Signed::is_negative`/`is_positive` — receiver a
/// bignum — is modeled TOTAL (no obligation, no Assert). SOUNDNESS PIN: the same
/// predicate on a USER ADT (whose `Signed` impl could panic) KEEPS its obligation.
#[test]
fn test_f6ext_bignum_sign_predicate_discharges_and_user_keeps() {
    let external: &[(&str, Ty)] = &[
        ("num_traits::sign::Signed::is_negative", ty_bigint()),
        ("num_traits::sign::Signed::is_positive", ty_bigint()),
        ("num_traits::sign::Signed::is_negative", ty_ratio(ty_bigint())),
        // The `Sign` enum's inherent-method spelling (its production def-path names
        // the defining crate, `num_bigint`), still type-gated — the namespace sweep
        // anchors the `Sign` arm on `num_bigint`/`bigint` so a user `my::Sign`
        // cannot ride it.
        ("num_bigint::Sign::is_negative", ty_biguint()),
        // A `&Ratio<BigInt>` receiver — ref peeled.
        (
            "num_traits::sign::Signed::is_positive",
            Ty::Ref { mutable: false, inner: Box::new(ty_ratio(ty_bigint())) },
        ),
    ];
    for (callee, recv_ty) in external {
        let module = lower_to_trust_ir(&f6ext_one_call(callee, recv_ty.clone(), Ty::Bool))
            .expect("external sign predicate lowers fail-soft, not Err");
        assert_valid_module(&module);
        let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
        assert_eq!(
            f6ext_panic_obligations(&module),
            1,
            "unauthenticated external `{callee}` on {recv_ty:?} must keep one obligation"
        );
        assert!(
            insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })),
            "unauthenticated external `{callee}` must emit the may-panic marker"
        );
    }

    // KEPT (SOUNDNESS PIN): a USER `Signed` impl / a `Ratio<i64>` receiver.
    let kept: &[(&str, Ty)] = &[
        ("num_traits::sign::Signed::is_negative", f6ext_user_ty()),
        ("num_traits::sign::Signed::is_positive", ty_ratio(Ty::i64())),
        ("num_traits::Sign::is_negative", ty_biguint()),
        ("num_traits::Signed::is_negative", ty_biguint()),
    ];
    for (callee, recv_ty) in kept {
        let module = lower_to_trust_ir(&f6ext_one_call(callee, recv_ty.clone(), Ty::Bool))
            .expect("kept sign predicate lowers fail-soft, not Err");
        assert_valid_module(&module);
        assert_eq!(
            f6ext_panic_obligations(&module),
            1,
            "`{callee}` on non-bignum {recv_ty:?} must keep exactly one may-panic obligation"
        );
    }
}

/// F6-ext (engine): a `Ratio::new` whose DENOMINATOR is a PROVABLY-NONZERO CONSTANT
/// (`BigInt::from(1) << k`) has NO panic condition at all, so it FULLY discharges —
/// NEITHER a conditional zero-denominator obligation NOR a blanket one (the F5/F6
/// total path, distinct from the F8 conditional rewrite). The `Shl::shl` is separately
/// discharged; the `BigInt::from(1)` conversion is an ordinary absent callee (its
/// obligation is unrelated to the Ratio and not counted here).
#[test]
fn test_f6ext_ratio_new_const_nonzero_denom_fully_discharges() {
    // _3 = BigInt::from(1);  _4 = Shl::shl(_3, k);  _0 = Ratio::new(_1, _4)
    let mk = |from_const: u128, ratio_ty: Ty, bignum_denom: bool| {
        // For the bignum path, denom (_4) is a BigInt built by `from(const) << k`.
        // For the type-gate PIN, the denom is a primitive local instead.
        let denom_ty = if bignum_denom { ty_bigint() } else { Ty::i64() };
        let locals = vec![
            LocalDecl { index: 0, ty: ratio_ty.clone(), name: None },
            LocalDecl { index: 1, ty: ty_bigint(), name: Some("numer".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("k".into()) },
            LocalDecl { index: 3, ty: ty_bigint(), name: Some("base".into()) },
            LocalDecl { index: 4, ty: denom_ty, name: Some("denom".into()) },
        ];
        let blocks = if bignum_denom {
            vec![
                // _3 = BigInt::from(<from_const>)
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: f8_call(
                        "std::convert::From::from",
                        vec![Operand::Constant(ConstValue::Uint(from_const, 128))],
                        Place::local(3),
                        1,
                    ),
                },
                // _4 = Shl::shl(move _3, copy _2)   (BigInt << u32)
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: f8_call(
                        "std::ops::Shl::<u32>::shl",
                        vec![Operand::Move(Place::local(3)), Operand::Copy(Place::local(2))],
                        Place::local(4),
                        2,
                    ),
                },
                // _0 = Ratio::new(move _1, move _4)
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: f8_call(
                        "num_rational::Ratio::<num_bigint::BigInt>::new",
                        vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(4))],
                        Place::local(0),
                        3,
                    ),
                },
                TrustBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ]
        } else {
            // Type-gate PIN: `Ratio<i64>::new`, denom a primitive i64 const `1`.
            vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: f8_call(
                        "num_rational::Ratio::<i64>::new",
                        vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(4))],
                        Place::local(0),
                        1,
                    ),
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ]
        };
        VerifiableFunction {
            name: "rat".to_string(),
            def_path: "test::rat".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody { locals, blocks, arg_count: 2, return_ty: ratio_ty },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    };

    // Even a mathematically nonzero shape cannot grant authority from printable
    // third-party paths alone: it keeps the blanket obligation.
    let module = lower_to_trust_ir(&mk(1, ty_ratio(ty_bigint()), true))
        .expect("const-nonzero-denom Ratio::new lowers total, not Err");
    assert_valid_module(&module);
    let (conditional, blanket_ratio, _smt) = f8_ratio_obligations(&module);
    assert_eq!(
        conditional, 0,
        "a provably-nonzero-const denom has NO panic condition — no conditional obligation"
    );
    assert_eq!(
        blanket_ratio, 1,
        "an unauthenticated Ratio::new path must keep the blanket obligation"
    );

    // SOUNDNESS PIN (nonzero required): `BigInt::from(0) << k` denom — the shift of a
    // ZERO base is zero, so the constructor's zero-denominator panic is REAL. The base's
    // const `0` fails the `>= 1` nonzero gate, so it does NOT full-discharge; and because
    // the denom is produced by `Shl` (not a direct `BigInt::from`), the F8 Axiom-A shape
    // does not apply either, so the real panic is KEPT as the blanket obligation.
    let module0 = lower_to_trust_ir(&mk(0, ty_ratio(ty_bigint()), true))
        .expect("zero-const-denom Ratio::new lowers total, not Err");
    assert_valid_module(&module0);
    let (conditional0, blanket0, _s0) = f8_ratio_obligations(&module0);
    assert_eq!(
        conditional0, 0,
        "a ZERO base is not provably nonzero AND not directly Axiom-A shaped — no conditional discharge"
    );
    assert_eq!(
        blanket0, 1,
        "a ZERO-const denom must NOT full-discharge — the real zero-denominator panic is KEPT (blanket)"
    );

    // SOUNDNESS PIN (type gate): `Ratio<i64>::new` with a nonzero-const denom — the
    // denom is a PRIMITIVE, not a bignum, so the type gate fails and the const-nonzero
    // full-discharge does NOT fire; no bignum witness exists either, so it KEEPS the
    // blanket obligation.
    let module_i64 = lower_to_trust_ir(&mk(1, ty_ratio(Ty::i64()), false))
        .expect("Ratio<i64>::new lowers fail-soft, not Err");
    assert_valid_module(&module_i64);
    let (conditional_i64, blanket_i64, _si) = f8_ratio_obligations(&module_i64);
    assert_eq!(
        conditional_i64, 0,
        "Ratio<i64>::new has no bignum witness — no conditional discharge"
    );
    assert_eq!(
        blanket_i64, 1,
        "Ratio<i64>::new (primitive denom) fails the type gate and KEEPS the blanket obligation"
    );
}

// ---------------------------------------------------------------------------
// Round-4 Part 2 — literal-shift-in-range overflow discharge.
// ---------------------------------------------------------------------------

/// Round-4 / Part 2: an `Overflow(Shl|Shr)` assert whose shift AMOUNT is an integer
/// literal STRICTLY below the shiftee's bit width is DISCHARGED (the assert is
/// vacuously true — `x << k` panics iff `k >= bits(x)`): no refutable `Inst::Assert`,
/// no `ArithmeticSafety` obligation — while the `Shl`/`Shr` RVALUE still lowers
/// (byte-identical `Inst::BinOp`, obligation-gating only). A literal amount >= the
/// width, and a SYMBOLIC amount, KEEP the real per-site obligation (fail-closed).
#[test]
fn test_round4_literal_shift_in_range_discharges_and_fail_closed_keeps() {
    use trust_types::AssertMessage;

    // rustc's checked-shift shape: `assert(cond, Overflow(op)) -> bb1;
    // bb1: _0 = op(value, amount)` — the shift runs on the assert's SUCCESS edge
    // (the TARGET block, where `reconstruct_shift_violation` also looks).
    let mk = |op: BinOp, value: Operand, amount: Operand, dest_ty: Ty| VerifiableFunction {
        name: "shifter".to_string(),
        def_path: "test::shifter".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: dest_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("k".into()) },
                LocalDecl { index: 3, ty: Ty::u64(), name: Some("s".into()) },
                LocalDecl { index: 4, ty: Ty::i128(), name: Some("w".into()) },
                LocalDecl { index: 5, ty: Ty::i64(), name: Some("n".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Constant(ConstValue::Bool(true)),
                        expected: true,
                        msg: AssertMessage::Overflow(op),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(op, value, amount),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 5,
            return_ty: dest_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let arith_safety_count = |module: &trust_ir::Module| -> usize {
        module
            .proof_obligations
            .iter()
            .filter(|o| o.kind == trust_ir::ObligationKind::ArithmeticSafety)
            .count()
    };
    let insts_of = |module: &trust_ir::Module| -> Vec<Inst> {
        module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| b.body.iter().map(|n| n.inst.clone()))
            .collect()
    };

    // DISCHARGED: literal amount strictly below the shiftee width.
    for (label, op, value, amount, dest_ty) in [
        // ny-cert rational.rs:231 `bits >> 31` on u32.
        (
            "u32 >> 31",
            BinOp::Shr,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Int(31)),
            Ty::u32(),
        ),
        // i128 << 23 with a TYPED i128 shiftee local — width from the place type.
        (
            "i128 << 23",
            BinOp::Shl,
            Operand::Copy(Place::local(4)),
            Operand::Constant(ConstValue::Int(23)),
            Ty::i128(),
        ),
        // ny-cert generate.rs:39 `state >> 33` on u64.
        (
            "u64 >> 33",
            BinOp::Shr,
            Operand::Copy(Place::local(3)),
            Operand::Constant(ConstValue::Int(33)),
            Ty::u64(),
        ),
        // ny-cert exact.rs:71 `1 << 20` on usize — width-carrying Uint shiftee.
        (
            "1usize << 20",
            BinOp::Shl,
            Operand::Constant(ConstValue::Uint(1, 64)),
            Operand::Constant(ConstValue::Int(20)),
            Ty::usize(),
        ),
        // A width-carrying Uint AMOUNT (a named const evaluated to `Uint(31, 32)`).
        (
            "u32 << const 31u32",
            BinOp::Shl,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(31, 32)),
            Ty::u32(),
        ),
    ] {
        let module = lower_to_trust_ir(&mk(op, value, amount, dest_ty))
            .expect("literal in-range shift must lower total, not Err");
        assert_valid_module(&module);
        assert_eq!(
            arith_safety_count(&module),
            0,
            "literal in-range shift `{label}` must NOT raise an ArithmeticSafety obligation"
        );
        let insts = insts_of(&module);
        assert!(
            !insts.iter().any(|i| matches!(i, Inst::Assert { .. })),
            "literal in-range shift `{label}` must NOT emit a refutable Assert"
        );
        assert!(
            insts.iter().any(|i| matches!(i, Inst::BinOp { .. })),
            "the `{label}` shift RVALUE must still lower to its BinOp (gating only)"
        );
    }

    // DISCHARGED — ny-cert rational.rs:243 `1i128 << 23`: a WIDTH-LESS `Int`
    // shiftee, whose width the gate recovers from the assignment DESTINATION's
    // declared type (i128), exactly where trust-vcgen reads it. NOTE: no
    // `assert_valid_module` here — the width-less-literal RVALUE lowering itself
    // (untouched by this round: both operands keep their contextless i64 const
    // type under an i128-typed BinOp) trips the validator's OperandTypeMismatch
    // with or without the discharge; this test pins ONLY the obligation gating.
    {
        let module = lower_to_trust_ir(&mk(
            BinOp::Shl,
            Operand::Constant(ConstValue::Int(1)),
            Operand::Constant(ConstValue::Int(23)),
            Ty::i128(),
        ))
        .expect("const-shiftee literal shift must lower total, not Err");
        assert_eq!(
            arith_safety_count(&module),
            0,
            "`1i128 << 23` (dest-recovered width) must NOT raise an ArithmeticSafety obligation"
        );
        let insts = insts_of(&module);
        assert!(
            !insts.iter().any(|i| matches!(i, Inst::Assert { .. })),
            "`1i128 << 23` must NOT emit a refutable Assert"
        );
        assert!(
            insts.iter().any(|i| matches!(i, Inst::BinOp { .. })),
            "the `1i128 << 23` shift RVALUE must still lower to its BinOp (gating only)"
        );
    }

    // KEPT (fail-closed): out-of-range literal, symbolic amount, negative literal.
    for (label, op, value, amount, dest_ty) in [
        // Hypothetical `u32 << 32` — amount == width is a REAL panic.
        (
            "u32 << 32",
            BinOp::Shl,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Int(32)),
            Ty::u32(),
        ),
        // ny-cert crown_deep.rs:652 `1u32 << shift` — SYMBOLIC amount (no dominating
        // guard consulted this round).
        (
            "u32 << k",
            BinOp::Shl,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
            Ty::u32(),
        ),
        // Negative literal amount — a real panic (an i64 shiftee so the literal
        // adopts a valid operand type; the gate rejects it on sign alone).
        (
            "i64 << -1",
            BinOp::Shl,
            Operand::Copy(Place::local(5)),
            Operand::Constant(ConstValue::Int(-1)),
            Ty::i64(),
        ),
    ] {
        let module = lower_to_trust_ir(&mk(op, value, amount, dest_ty))
            .expect("kept shift assert must still lower");
        assert_valid_module(&module);
        assert!(
            arith_safety_count(&module) >= 1,
            "shift `{label}` must KEEP its real ArithmeticSafety obligation"
        );
        let insts = insts_of(&module);
        assert!(
            insts.iter().any(|i| matches!(i, Inst::Assert { .. })),
            "shift `{label}` must KEEP its refutable in-body Assert"
        );
    }
}

/// Build-4 / Part A: an `Overflow(Add|Sub|Mul)` assert whose `CheckedBinaryOp`
/// operates on ARBITRARY-PRECISION operands (`BigInt`/`BigUint`/`BigRational`) is
/// DISCHARGED — no refutable `Inst::Assert`, no `ArithmeticSafety` obligation (a
/// bignum add/sub/mul grows instead of overflowing, so the assert is vacuous and
/// would otherwise strand as an unsolvable `FullVerification::ArithmeticSafety` →
/// strict FAILED). The SAME shape on a PRIMITIVE operand (`i128`/`usize`) KEEPS its
/// real per-site `ArithmeticSafety` obligation — primitive overflow is genuine.
#[test]
fn test_build4_bigint_overflow_assert_discharges_but_primitive_keeps() {
    use trust_types::AssertMessage;

    // A `_r = CheckedOp(a, b); assert(!_r.1, Overflow(op)) -> bb1` caller whose
    // operand locals have type `op_ty`. Mirrors the checked-overflow harness above.
    let mk = |op: BinOp, op_ty: Ty| VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: op_ty.clone(), name: None },
                LocalDecl { index: 1, ty: op_ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: op_ty.clone(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![op_ty.clone(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            op,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(op),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
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
            return_ty: op_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let arith_safety_count = |module: &trust_ir::Module| -> usize {
        module
            .proof_obligations
            .iter()
            .filter(|o| o.kind == trust_ir::ObligationKind::ArithmeticSafety)
            .count()
    };

    // `CheckedBinaryOp` is a compiler builtin-integer construct. A synthetic
    // third-party ADT spelling must be rejected before invalid TrustIr is built.
    for (op, op_ty) in [
        (BinOp::Sub, ty_bigint()), // the recip `T::zero() - self.denom` shape
        (BinOp::Add, ty_bigint()),
        (BinOp::Mul, ty_bigint()),
        (BinOp::Mul, ty_ratio(ty_bigint())), // BigRational multiply
    ] {
        let err = lower_to_trust_ir(&mk(op, op_ty.clone()))
            .expect_err("non-integer CheckedBinaryOp must fail closed");
        assert!(
            matches!(&err, BridgeError::UnsupportedType(msg) if msg.contains("compiler builtin integer")),
            "unexpected error for external CheckedBinaryOp({op:?}) on {op_ty:?}: {err:?}"
        );
    }

    // KEPT: primitive operands — real overflow, per-site ArithmeticSafety obligation.
    // (The `Ratio<i64>` / `Rational64` soundness keystone — same ADT name as
    // BigRational but a PRIMITIVE element, so `is_arbitrary_precision_ty` must return
    // false — is a CALL/operator-overload shape, never a `CheckedBinaryOp`, and is
    // asserted at the pure-gate level in `test_f6_arbitrary_precision_gate_pure`.)
    for (op, op_ty) in
        [(BinOp::Sub, Ty::i128()), (BinOp::Add, Ty::usize()), (BinOp::Mul, Ty::i128())]
    {
        let module = lower_to_trust_ir(&mk(op, op_ty.clone()))
            .expect("primitive overflow assert must lower");
        assert_valid_module(&module);
        assert!(
            arith_safety_count(&module) >= 1,
            "primitive `Overflow({op:?})` on {op_ty:?} must KEEP its real \
             ArithmeticSafety obligation"
        );
    }
}

/// Third-party printable paths are not compiler-authenticated type identities and
/// therefore never enter the element-free std leaf set.
#[test]
fn test_build1_bigint_element_free_leaf() {
    for name in [
        "num_bigint::BigInt",
        "num_bigint::BigUint",
        "num_bigint::bigint::BigInt",
        "num_bigint::biguint::BigUint",
    ] {
        assert!(
            !is_element_free_total_std_type(name),
            "unauthenticated external path must fail closed: {name}"
        );
    }
    for name in [
        // Generic — element erased from the name; fail closed here (handled soundly
        // by the field-aware `is_arbitrary_precision_ty`).
        "num_rational::Ratio",
        // num_bigint types that are NOT the bignum integers — the `ends_with` gate
        // must keep them out.
        "num_bigint::Sign",
        "num_bigint::ParseBigIntError",
        // K-parameterized containers whose element could be a panicking user type.
        "alloc::vec::Vec",
        "std::collections::BTreeMap",
        "mycrate::money::Money",
    ] {
        assert!(
            !is_element_free_total_std_type(name),
            "must fail closed (keep obligation): {name}"
        );
    }
}

/// Build-1 engine level (Spec 3 F5-completeness + Spec 1 RefCell): a sequence
/// `collect` (dest `Vec`/`VecDeque`/`String`), a `Clone::clone` on an
/// arbitrary-precision type (`BigInt`/`BigUint`/`BigRational`), and the TOTAL
/// `RefCell::try_borrow{,_mut}` are modeled like a TOTAL summary — a havoc
/// (`Undef`) result, NO `Assert(false)` may-panic marker, NO
/// `trust-absent-callee-assumption` obligation. A KEYED `collect` (dest
/// `BTreeMap`), a USER-type `Clone` (and `Ratio<i64>`, primitive element), and the
/// panicking `RefCell::borrow` KEEP the full may-panic encoding (fail-closed).
#[test]
fn test_build1_collect_clone_refcell_discharge_and_keep() {
    fn ty_vec() -> Ty {
        Ty::adt("alloc::vec::Vec", vec![("buf".into(), Ty::u64()), ("len".into(), Ty::usize())])
    }
    fn ty_btreemap() -> Ty {
        Ty::adt("std::collections::BTreeMap", vec![("root".into(), Ty::u64())])
    }
    fn ty_money() -> Ty {
        Ty::adt("mycrate::money::Money", vec![("cents".into(), Ty::i64())])
    }
    fn ty_box_with_panicking_zst_allocator() -> Ty {
        let pointee = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::i64()) };
        let nonnull = Ty::adt("core::ptr::NonNull", vec![("pointer".into(), pointee)]);
        let unique = Ty::adt(
            "core::ptr::Unique",
            vec![
                ("pointer".into(), nonnull),
                ("marker".into(), Ty::adt("core::marker::PhantomData", vec![])),
            ],
        );
        Ty::adt(
            "alloc::boxed::Box",
            vec![
                ("ptr".into(), unique),
                ("alloc".into(), Ty::adt("mycrate::PanickingZstAlloc", vec![])),
            ],
        )
    }

    // One-call caller whose single argument (arg 0 = the receiver) has type
    // `recv_ty` and whose dest has type `dest_ty`. Mirrors the F5/F6 harness.
    let mk = |func: &str, recv_ty: Ty, dest_ty: Ty| VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: dest_ty.clone(), name: None },
                LocalDecl { index: 1, ty: recv_ty, name: Some("recv".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: func.to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: dest_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let absent_callee_obligations = |module: &trust_ir::Module| -> usize {
        module
            .proof_obligations
            .iter()
            .filter(|o| {
                o.kind == trust_ir::ObligationKind::PanicFreedom
                    && o.description
                        .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
            })
            .count()
    };
    let has_may_panic_marker = |module: &trust_ir::Module| -> bool {
        module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .any(|n| matches!(n.inst, Inst::Assert { .. }))
    };

    // (callee, receiver/arg0 type, dest type, expect_discharged, label).
    let cases: &[(&str, Ty, Ty, bool, &str)] = &[
        // `collect` drives producer `next` and partial-result cleanup. A destination
        // spelling alone proves neither total, even for `Vec`.
        ("std::iter::Iterator::collect", Ty::u64(), ty_vec(), false, "collect into Vec"),
        // Keyed collect — KEEPS the marker (BTreeMap dest fails the sequence gate,
        // falls through to the closure-driving arm).
        (
            "std::iter::Iterator::collect",
            Ty::u64(),
            ty_btreemap(),
            false,
            "keyed collect into BTreeMap",
        ),
        // Third-party Clone paths lack authenticated crate/impl identity.
        (
            "std::clone::Clone::clone",
            ty_ratio(ty_bigint()),
            ty_ratio(ty_bigint()),
            false,
            "Clone BigRational",
        ),
        ("std::clone::Clone::clone", ty_bigint(), ty_bigint(), false, "Clone BigInt"),
        (
            "std::clone::Clone::clone",
            ty_box_with_panicking_zst_allocator(),
            ty_box_with_panicking_zst_allocator(),
            false,
            "Clone Box with panicking ZST allocator",
        ),
        // Clone type-gate — KEPT for a user ADT and for Ratio<i64> (primitive
        // element — a user/inner Clone could panic).
        ("std::clone::Clone::clone", ty_money(), ty_money(), false, "Clone user ADT"),
        (
            "std::clone::Clone::clone",
            ty_ratio(Ty::i64()),
            ty_ratio(Ty::i64()),
            false,
            "Clone Ratio<i64>",
        ),
        // RefCell — DISCHARGED for the total try_borrow{,_mut}.
        ("std::cell::RefCell::try_borrow", Ty::u64(), Ty::u64(), true, "RefCell::try_borrow"),
        (
            "core::cell::RefCell::try_borrow_mut",
            Ty::u64(),
            Ty::u64(),
            true,
            "RefCell::try_borrow_mut",
        ),
        // RefCell — KEPT for the panicking borrow.
        ("core::cell::RefCell::borrow", Ty::u64(), Ty::u64(), false, "RefCell::borrow"),
    ];

    for (callee, recv_ty, dest_ty, discharged, label) in cases {
        let module = lower_to_trust_ir(&mk(callee, recv_ty.clone(), dest_ty.clone()))
            .unwrap_or_else(|e| panic!("`{label}` (`{callee}`) must lower, not Err: {e:?}"));
        assert_valid_module(&module);
        if *discharged {
            assert_eq!(
                absent_callee_obligations(&module),
                0,
                "{label}: a discharged callee must NOT raise the absent-callee obligation"
            );
            assert!(
                !has_may_panic_marker(&module),
                "{label}: a discharged callee must NOT emit the Assert(false) may-panic marker"
            );
        } else {
            assert!(
                has_may_panic_marker(&module),
                "{label}: a fail-closed callee must KEEP the Assert(false) may-panic marker"
            );
        }
    }
}

/// Round-6 (batch-50b): the `clone_is_total` type gate must ALSO discharge the
/// two receiver spellings that survived rounds 1-5:
///   * a name-preserving COMPACTED `Ty::Datatype` leaf — the spelling an
///     oversized `num_bigint::BigInt` operand takes (`compact_oversized_field`),
///     which the `Ty::Adt`-only arm missed (the batch-50b rows inside the
///     MIR-inlined derived `<Ratio<BigInt> as Clone>::clone`);
///   * a `Ty::Closure` receiver whose upvars all clone totally — the
///     `#[trust::ensures]` contract closures (`[i128, i128]` captures) the
///     contract instrumentation clones (the batch-50b `generate::Lcg` rows).
/// FAIL-CLOSED controls: a compacted `Ratio` Datatype (element unrecoverable), a
/// user-named Datatype, and a closure capturing a user ADT all KEEP the
/// obligation.
#[test]
fn test_round6_clone_datatype_and_closure_receivers() {
    fn ty_money() -> Ty {
        Ty::adt("mycrate::money::Money", vec![("cents".into(), Ty::i64())])
    }
    let dt = |name: &str| Ty::Datatype { name: name.to_string(), variants: vec![] };
    let closure = |upvars: Vec<Ty>| Ty::Closure {
        name: "generate::Lcg::range_i128::{closure#0}".to_string(),
        upvars,
        call: None,
    };

    // One-call caller whose single argument (arg 0 = the receiver) has type
    // `recv_ty` and whose dest has type `dest_ty` — the F5/F6/Build-1 harness.
    let mk = |func: &str, recv_ty: Ty, dest_ty: Ty| VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: dest_ty.clone(), name: None },
                LocalDecl { index: 1, ty: recv_ty, name: Some("recv".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: func.to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: dest_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let has_may_panic_marker = |module: &trust_ir::Module| -> bool {
        module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .any(|n| matches!(n.inst, Inst::Assert { .. }))
    };

    // (receiver type, dest type, expect_discharged, label).
    let cases: &[(Ty, Ty, bool, &str)] = &[
        // Compacted third-party paths carry no authenticated crate/impl identity.
        (dt("num_bigint::BigInt"), dt("num_bigint::BigInt"), false, "Clone Datatype BigInt"),
        (dt("num_bigint::BigUint"), dt("num_bigint::BigUint"), false, "Clone Datatype BigUint"),
        (dt("std::string::String"), dt("std::string::String"), true, "Clone Datatype String"),
        // Ref-wrapped compacted receiver — peeled by `trait_method_governing_ty`,
        // then DISCHARGED (the derived-impl `&self.numer` shape).
        (
            Ty::Ref { mutable: false, inner: Box::new(dt("num_bigint::BigInt")) },
            dt("num_bigint::BigInt"),
            false,
            "Clone &Datatype BigInt",
        ),
        // Compacted `Ratio` — element UNRECOVERABLE from a by-name Datatype, so
        // the arbitrary-precision gate fails and the obligation is KEPT (a
        // `Ratio<i64>`/`Ratio<UserType>` must never ride the compacted spelling).
        (dt("num_rational::Ratio"), dt("num_rational::Ratio"), false, "Clone Datatype Ratio"),
        // A user-named Datatype — KEPT (fail-closed).
        (dt("mycrate::money::Money"), dt("mycrate::money::Money"), false, "Clone Datatype user"),
        // Contract-closure receivers — DISCHARGED for primitive/total captures
        // (the compiler-built closure Clone clones each upvar and nothing else).
        (closure(vec![Ty::i128(), Ty::i128()]), Ty::Unit, true, "Clone closure [i128, i128]"),
        (closure(vec![Ty::usize(), Ty::usize()]), Ty::Unit, true, "Clone closure [usize, usize]"),
        (closure(vec![]), Ty::Unit, true, "Clone capture-free closure"),
        // A by-REF capture of a user ADT clones the POINTER only — DISCHARGED.
        (
            closure(vec![Ty::Ref { mutable: false, inner: Box::new(ty_money()) }]),
            Ty::Unit,
            true,
            "Clone closure [&UserAdt]",
        ),
        // A by-VALUE captured user ADT — its Clone could panic; KEPT (fail-closed).
        (closure(vec![Ty::i128(), ty_money()]), Ty::Unit, false, "Clone closure [i128, UserAdt]"),
    ];

    for (recv_ty, dest_ty, discharged, label) in cases {
        let module =
            lower_to_trust_ir(&mk("std::clone::Clone::clone", recv_ty.clone(), dest_ty.clone()))
                .unwrap_or_else(|e| panic!("`{label}` must lower, not Err: {e:?}"));
        assert_valid_module(&module);
        if *discharged {
            assert!(
                !has_may_panic_marker(&module),
                "{label}: a discharged Clone receiver must NOT emit the Assert(false) marker"
            );
            assert!(
                !module.proof_obligations.iter().any(|o| {
                    o.kind == trust_ir::ObligationKind::PanicFreedom
                        && o.description.contains("absent callee")
                }),
                "{label}: a discharged Clone receiver must NOT raise the absent-callee obligation"
            );
        } else {
            assert!(
                has_may_panic_marker(&module),
                "{label}: a fail-closed Clone receiver must KEEP the Assert(false) marker"
            );
        }
    }
}

/// Round-6 (batch-50b, FnOnce census): a `FnOnce::call_once` whose receiver is
/// a LEGACY identity-less zero-sized callable constant. Historical JSON dumps
/// encoded non-capturing closures/function items as
/// `Operand::Constant(ConstValue::Unit)`; those dumps remain readable and must
/// lower FAIL-SOFT via the audited untypeable-receiver may-panic encoding
/// (marker + havoc + ONE prefixed PanicFreedom obligation), never a phantom
/// Call and never a false total summary. This pins the post-`#[inline(always)]`
/// ny shape (the 45 batch-50b rows at `rational::with_val`'s span): the
/// receiver was a concrete ZST callable at the Rust level, but a legacy dump's
/// identity is gone. New extraction uses `CallableItem`; this regression pins
/// conservative compatibility for old `Unit` payloads.
#[test]
fn test_round6_fnonce_erased_zst_receiver_fail_soft() {
    let func = VerifiableFunction {
        name: "calls_erased_zst".to_string(),
        def_path: "test::calls_erased_zst".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i64(), name: None }],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::ops::FnOnce::call_once".to_string(),
                        args: vec![
                            // The erased ZST callable (was `Clone::clone` / a
                            // non-capturing closure before extraction).
                            Operand::Constant(ConstValue::Unit),
                            // The rust-call args tuple (empty).
                            Operand::Constant(ConstValue::Unit),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::i64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func)
        .expect("erased-ZST-receiver callable shim should lower fail-soft, not Err");
    assert_valid_module(&module);
    let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    // (a) the in-body may-panic marker.
    assert!(
        insts.iter().any(|n| {
            matches!(n.inst, Inst::Assert { .. })
                && n.proofs.contains(&trust_ir::ProofAnnotation::NoPanic)
        }),
        "expected the Assert(false)+NoPanic may-panic marker"
    );
    // (b) exactly one honest marked PanicFreedom obligation naming the shim's
    //     untypeable-receiver encoding.
    let marked: Vec<_> = module
        .proof_obligations
        .iter()
        .filter(|o| {
            o.kind == trust_ir::ObligationKind::PanicFreedom
                && o.description
                    .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
        })
        .collect();
    assert_eq!(marked.len(), 1, "expected exactly one marked PanicFreedom obligation");
    assert!(
        marked[0].description.contains("untypeable callable receiver"),
        "the obligation must carry the untypeable-receiver encoding: {}",
        marked[0].description
    );
    // (c) no phantom direct or indirect call was fabricated.
    assert!(
        !insts.iter().any(|n| {
            matches!(n.inst, Inst::Call { .. }) || matches!(n.inst, Inst::CallIndirect { .. })
        }),
        "an erased-ZST callable receiver must not lower to a phantom Call/CallIndirect"
    );
}

/// Trust (T4, aterm-scrollback): a `FnMut::call_mut` shim whose receiver is a
/// `dyn FnMut` trait object (untypeable — no closure name, no FnDef, no fn-ptr
/// sig) must lower FAIL-SOFT via the audited may-panic encoding — the
/// `Assert(false)+NoPanic` marker, a havoc result, and ONE `PanicFreedom`
/// obligation carrying the absent-callee assumption prefix — instead of the old
/// hard `Err("requires a typed closure receiver")` that ABORTED the whole
/// function lowering. Fail-CLOSED is preserved: the site is never treated as
/// panic-free and never lowers to a phantom Call.
#[test]
fn test_lower_dyn_callable_receiver_fail_soft() {
    let dyn_recv_ty = Ty::Ref {
        mutable: true,
        inner: Box::new(Ty::Dynamic { trait_name: "core::ops::function::FnMut".into() }),
    };
    let func = VerifiableFunction {
        name: "calls_dyn".to_string(),
        def_path: "test::calls_dyn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: dyn_recv_ty, name: Some("f".into()) },
                LocalDecl { index: 2, ty: Ty::Unit, name: Some("args".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "core::ops::function::FnMut::call_mut".to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::i64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func)
        .expect("dyn-receiver callable shim should lower fail-soft, not Err");
    assert_valid_module(&module);
    let insts: Vec<_> = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    // (a) the in-body may-panic marker.
    assert!(
        insts.iter().any(|n| {
            matches!(n.inst, Inst::Assert { .. })
                && n.proofs.contains(&trust_ir::ProofAnnotation::NoPanic)
        }),
        "expected the Assert(false)+NoPanic may-panic marker"
    );
    // (b) the havoc result.
    assert!(
        insts.iter().any(|n| matches!(n.inst, Inst::Undef { .. })),
        "expected the havoc (Undef) result for the unknown dyn callee"
    );
    // (c) exactly one honest marked PanicFreedom obligation naming the shim.
    let marked: Vec<_> = module
        .proof_obligations
        .iter()
        .filter(|o| {
            o.kind == trust_ir::ObligationKind::PanicFreedom
                && o.description
                    .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
        })
        .collect();
    assert_eq!(marked.len(), 1, "expected exactly one marked PanicFreedom obligation");
    assert!(
        marked[0].description.contains("call_mut"),
        "the obligation must name the callable shim: {}",
        marked[0].description
    );
    // (d) no phantom direct or indirect call was fabricated.
    assert!(
        !insts.iter().any(|n| {
            matches!(n.inst, Inst::Call { .. }) || matches!(n.inst, Inst::CallIndirect { .. })
        }),
        "an untypeable callable receiver must not lower to a phantom Call/CallIndirect"
    );
}

/// Trust (T4, aterm-scrollback): an `OpaqueConst` operand (`&[&str]`/`&[T]`
/// static lookup table) passed as a CALL ARGUMENT must TYPE as the slice
/// fat pointer (the variant's prescribed lowering) instead of hitting the
/// "unknown const"/"unknown operand variant" catch-alls, which ABORTED the
/// whole-function lowering. The call here is a closure-driving consumer
/// (`Iterator::fold`), whose arm types every argument via
/// `operand_trust_type` (`try_resolve_hof_closure`) before falling to the
/// conservative may-panic lowering — so lowering SUCCEEDS with the honest
/// obligation, and the OpaqueConst carries no asserted value (fail-closed
/// precision, never a false prove).
#[test]
fn test_opaque_const_call_arg_types_as_slice_fat_pointer() {
    let func = VerifiableFunction {
        name: "folds_registry".to_string(),
        def_path: "test::folds_registry".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i64(), name: None }],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "core::iter::Iterator::fold".to_string(),
                        args: vec![
                            Operand::Constant(ConstValue::OpaqueConst),
                            Operand::Constant(ConstValue::Int(0)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::i64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // Before the OpaqueConst operand-typing arms, this Err'd with "unknown
    // operand variant" (whole function poisoned). Now it lowers, keeping the
    // closure-driving consumer's honest PanicFreedom obligation.
    let module =
        lower_to_trust_ir(&func).expect("an OpaqueConst call argument must not abort the lowering");
    assert_valid_module(&module);
    assert!(
        module.proof_obligations.iter().any(|o| o.kind == trust_ir::ObligationKind::PanicFreedom),
        "the closure-driving consumer must keep its honest PanicFreedom obligation"
    );
}

// ---------------------------------------------------------------------------
// f32 FloatBits constant lowering
// ---------------------------------------------------------------------------

/// Non-NaN f32 constants lower bit-exactly through the f64 `Constant::Float`
/// carrier (the f32 values are a strict subset of f64; the widen is injective
/// and the demote round-trips). NaN payloads stay fail-closed (a hardware
/// widen can quiet a signaling NaN — a wrong-bits constant fold hazard).
#[test]
fn test_lower_f32_floatbits_constant_bit_exact_non_nan() {
    for (bits, label) in [
        (0f32.to_bits(), "zero"),
        ((-0f32).to_bits(), "neg-zero"),
        (1.5f32.to_bits(), "finite"),
        (f32::MIN_POSITIVE.to_bits() >> 1, "subnormal"),
        (f32::INFINITY.to_bits(), "inf"),
        (f32::NEG_INFINITY.to_bits(), "neg-inf"),
    ] {
        let func = VerifiableFunction {
            name: "f32_const".to_string(),
            def_path: "test::f32_const".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Float { width: 32 }, name: None }],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::FloatBits {
                            bits: u128::from(bits),
                            width: 32,
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Float { width: 32 },
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let module = lower_to_trust_ir(&func)
            .unwrap_or_else(|e| panic!("[{label}] non-NaN f32 const should lower: {e:?}"));
        assert_valid_module(&module);
        let expected = f64::from(f32::from_bits(bits));
        let found = module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).any(|n| {
            matches!(&n.inst, Inst::Const { ty: TrustIrTy::F32, value: TrustIrConstant::Float(v) }
                if v.to_bits() == expected.to_bits())
        });
        assert!(found, "[{label}] expected an F32-typed bit-exact Float constant");
    }

    // NaN payloads stay fail-closed.
    let func = VerifiableFunction {
        name: "f32_nan".to_string(),
        def_path: "test::f32_nan".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Float { width: 32 }, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::FloatBits {
                        bits: u128::from(f32::NAN.to_bits()),
                        width: 32,
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Float { width: 32 },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let err = lower_to_trust_ir(&func).expect_err("f32 NaN constant must stay fail-closed");
    assert!(matches!(err, BridgeError::UnsupportedOp(ref m) if m.contains("NaN")));
}

// ---------------------------------------------------------------------------
// FnDef callable receiver resolution
// ---------------------------------------------------------------------------

/// `FnOnce::call_once(f, (x,))` where `f` is a FUNCTION ITEM (`Ty::FnDef`)
/// must resolve DIRECTLY to the named function when its body is bundled:
/// the dataless ZST receiver is dropped, the tuple is flattened, and the
/// callee's own obligations join the bundle — the class that poisoned whole
/// modules ("requires a typed closure receiver, got FnDef { ... }").
#[test]
fn test_fn_def_callable_receiver_resolves_direct_call() {
    let fn_def_ty = Ty::FnDef {
        name: "test::mapper".to_string(),
        sig: Box::new(trust_types::FnSig { params: vec![Ty::u32()], ret: Box::new(Ty::u32()) }),
    };
    let caller = VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: fn_def_ty, name: Some("f".into()) },
                LocalDecl { index: 2, ty: Ty::Tuple(vec![Ty::u32()]), name: Some("args".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("out".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Tuple,
                            vec![Operand::Constant(ConstValue::Uint(7, 32))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "core::ops::function::FnOnce::call_once".to_string(),
                        args: vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(2))],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let mapper = VerifiableFunction {
        name: "test::mapper".to_string(),
        def_path: "test::mapper".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir_functions("fndef_call", &[caller, mapper])
        .expect("FnDef receiver call should lower to a direct bundled call");
    assert_valid_module(&module);
    let mapper_id = module
        .functions
        .iter()
        .find(|f| f.name == "test::mapper")
        .map(|f| f.id)
        .expect("mapper bundled");
    let caller_fn = module.functions.iter().find(|f| f.name == "caller").expect("caller present");
    let call = caller_fn
        .blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .find_map(|n| match &n.inst {
            Inst::Call { callee, args } if *callee == mapper_id => Some(args.clone()),
            _ => None,
        })
        .expect("expected a DIRECT call to test::mapper");
    assert_eq!(call.len(), 1, "receiver dropped, tuple flattened to the single param");
}

// ---------------------------------------------------------------------------
// B61: `FnOnce::call_once` through a `ConstValue::CallableItem` receiver
// ---------------------------------------------------------------------------
//
// Extraction (schema v5) PRESERVES a fn-item / non-capturing-closure receiver's
// identity as `Operand::Constant(ConstValue::CallableItem { def_path, kind, .. })`
// (a ZST). `operand_trust_type` erases it to `Ty::Unit`, so the `Ty::FnDef` /
// `Ty::Closure` arms cannot see it — pre-B61 EVERY such shim took the untypeable
// may-panic UNKNOWN arm. These pin: a CallableItem whose `def_path` IS bundled
// resolves to a real `Inst::Call` into the actual body (typeable — its OWN guarded
// obligation propagates); a CallableItem whose `def_path` is NOT bundled stays
// FAIL-CLOSED on the untypeable may-panic encoding (no fabricated proof). Both
// `FnDef` and `Closure` kinds are covered.

/// Deterministic non-zero `DefPathHash` for CallableItem test operands (the value
/// is irrelevant to resolution, which keys on `def_path` presence in the bundle).
fn callable_item_test_hash() -> CallableDefPathHash {
    CallableDefPathHash::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210)
}

/// FnDef-kind CallableItem receiver whose `def_path` IS bundled resolves to a
/// DIRECT `Inst::Call` — the ZST receiver dropped, the rust-call tuple flattened —
/// NOT the untypeable may-panic arm.
#[test]
fn test_fn_def_callable_item_const_receiver_resolves_direct_call() {
    let caller = VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::Tuple(vec![Ty::u32()]), name: Some("args".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("out".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Tuple,
                            vec![Operand::Constant(ConstValue::Uint(7, 32))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "core::ops::function::FnOnce::call_once".to_string(),
                        // The receiver is the fn item's IDENTITY as a ZST const, NOT
                        // a `Ty::FnDef` local — this is the shape extraction produces.
                        args: vec![
                            Operand::Constant(ConstValue::CallableItem {
                                def_path: "test::mapper".to_string(),
                                kind: CallableKind::FnDef,
                                def_path_hash: callable_item_test_hash(),
                            }),
                            Operand::Move(Place::local(1)),
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let mapper = VerifiableFunction {
        name: "test::mapper".to_string(),
        def_path: "test::mapper".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir_functions("fndef_callable_item", &[caller, mapper])
        .expect("bundled FnDef CallableItem receiver must resolve, not fail closed");
    assert_valid_module(&module);
    let mapper_id = module
        .functions
        .iter()
        .find(|f| f.name == "test::mapper")
        .map(|f| f.id)
        .expect("mapper bundled");
    let caller_fn =
        module.functions.iter().find(|f| f.name == "caller").expect("caller present");
    let call = caller_fn
        .blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .find_map(|n| match &n.inst {
            Inst::Call { callee, args } if *callee == mapper_id => Some(args.clone()),
            _ => None,
        })
        .expect("expected a DIRECT call to test::mapper");
    assert_eq!(call.len(), 1, "receiver dropped, tuple flattened to the single param");
    // It resolved — so it did NOT take the untypeable may-panic arm.
    assert!(
        !module.proof_obligations.iter().any(|o| o
            .description
            .contains("untypeable callable receiver")),
        "a bundled CallableItem receiver must not emit the untypeable may-panic obligation"
    );
}

/// FnDef-kind CallableItem receiver whose `def_path` is NOT bundled stays
/// FAIL-CLOSED: the audited untypeable may-panic encoding (marker + one prefixed
/// PanicFreedom obligation + havoc), never a fabricated/phantom Call.
#[test]
fn test_fn_def_callable_item_const_receiver_unbundled_fail_closed() {
    let caller = VerifiableFunction {
        name: "calls_unbundled_fn".to_string(),
        def_path: "test::calls_unbundled_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::Tuple(vec![Ty::u32()]), name: Some("args".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("out".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Tuple,
                            vec![Operand::Constant(ConstValue::Uint(7, 32))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "core::ops::function::FnOnce::call_once".to_string(),
                        args: vec![
                            Operand::Constant(ConstValue::CallableItem {
                                def_path: "other_crate::absent_mapper".to_string(),
                                kind: CallableKind::FnDef,
                                def_path_hash: callable_item_test_hash(),
                            }),
                            Operand::Move(Place::local(1)),
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // The unbundled CallableItem body is absent, so the shim lowers FAIL-SOFT (not
    // Err) via the untypeable may-panic encoding.
    let module = lower_to_trust_ir(&caller)
        .expect("unbundled FnDef CallableItem receiver must lower fail-soft, not Err");
    assert_valid_module(&module);
    let insts: Vec<_> =
        module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    assert!(
        insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })
            && n.proofs.contains(&trust_ir::ProofAnnotation::NoPanic)),
        "expected the Assert(false)+NoPanic may-panic marker"
    );
    let marked: Vec<_> = module
        .proof_obligations
        .iter()
        .filter(|o| o.kind == trust_ir::ObligationKind::PanicFreedom
            && o.description
                .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
            && o.description.contains("untypeable callable receiver"))
        .collect();
    assert_eq!(marked.len(), 1, "expected exactly one marked untypeable PanicFreedom obligation");
    assert!(
        !insts.iter().any(|n| matches!(n.inst, Inst::Call { .. })
            || matches!(n.inst, Inst::CallIndirect { .. })),
        "an UNBUNDLED CallableItem receiver must not fabricate a phantom Call"
    );
}

/// Closure-kind CallableItem receiver (a non-capturing closure const) whose
/// `def_path` IS bundled resolves to a DIRECT `Inst::Call` into the closure body —
/// the receiver lowered as the (empty-upvar → Unit) env, the rust-call tuple
/// flattened — NOT the untypeable may-panic arm.
#[test]
fn test_closure_callable_item_const_receiver_resolves_direct_call() {
    let closure_name = "test::make::{closure#0}".to_string();
    // A non-capturing closure: its env (param 0) has EMPTY upvars → `TrustIrTy::Unit`.
    let env_ty = Ty::Closure { name: closure_name.clone(), upvars: vec![], call: None };
    let caller = VerifiableFunction {
        name: "closure_caller".to_string(),
        def_path: "test::closure_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::Tuple(vec![Ty::u32()]), name: Some("args".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("out".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Tuple,
                            vec![Operand::Constant(ConstValue::Uint(7, 32))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "core::ops::function::FnOnce::call_once".to_string(),
                        args: vec![
                            Operand::Constant(ConstValue::CallableItem {
                                def_path: closure_name.clone(),
                                kind: CallableKind::Closure,
                                def_path_hash: callable_item_test_hash(),
                            }),
                            Operand::Move(Place::local(1)),
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    // Closure body params are `[env, input]`; it just returns its input (total).
    let closure_body = VerifiableFunction {
        name: closure_name.clone(),
        def_path: closure_name.clone(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: env_ty, name: Some("self".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("arg".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module =
        lower_to_trust_ir_functions("closure_callable_item", &[caller, closure_body])
            .expect("bundled Closure CallableItem receiver must resolve, not fail closed");
    assert_valid_module(&module);
    let closure_id = module
        .functions
        .iter()
        .find(|f| f.name == closure_name)
        .map(|f| f.id)
        .expect("closure body bundled");
    let caller_fn = module
        .functions
        .iter()
        .find(|f| f.name == "closure_caller")
        .expect("caller present");
    let call = caller_fn
        .blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .find_map(|n| match &n.inst {
            Inst::Call { callee, args } if *callee == closure_id => Some(args.clone()),
            _ => None,
        })
        .expect("expected a DIRECT call to the closure body");
    assert_eq!(call.len(), 2, "env receiver kept, tuple flattened to the single input");
    assert!(
        !module.proof_obligations.iter().any(|o| o
            .description
            .contains("untypeable callable receiver")),
        "a bundled CallableItem closure receiver must not emit the untypeable may-panic obligation"
    );
}

/// Closure-kind CallableItem receiver whose `def_path` is NOT bundled stays
/// FAIL-CLOSED on the untypeable may-panic encoding — never a fabricated Call.
#[test]
fn test_closure_callable_item_const_receiver_unbundled_fail_closed() {
    let caller = VerifiableFunction {
        name: "calls_unbundled_closure".to_string(),
        def_path: "test::calls_unbundled_closure".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::Tuple(vec![Ty::u32()]), name: Some("args".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("out".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Tuple,
                            vec![Operand::Constant(ConstValue::Uint(7, 32))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "core::ops::function::FnOnce::call_once".to_string(),
                        args: vec![
                            Operand::Constant(ConstValue::CallableItem {
                                def_path: "other_crate::absent::{closure#0}".to_string(),
                                kind: CallableKind::Closure,
                                def_path_hash: callable_item_test_hash(),
                            }),
                            Operand::Move(Place::local(1)),
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&caller)
        .expect("unbundled Closure CallableItem receiver must lower fail-soft, not Err");
    assert_valid_module(&module);
    let insts: Vec<_> =
        module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect();
    assert!(
        insts.iter().any(|n| matches!(n.inst, Inst::Assert { .. })
            && n.proofs.contains(&trust_ir::ProofAnnotation::NoPanic)),
        "expected the Assert(false)+NoPanic may-panic marker"
    );
    let marked: Vec<_> = module
        .proof_obligations
        .iter()
        .filter(|o| o.kind == trust_ir::ObligationKind::PanicFreedom
            && o.description
                .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
            && o.description.contains("untypeable callable receiver"))
        .collect();
    assert_eq!(marked.len(), 1, "expected exactly one marked untypeable PanicFreedom obligation");
    assert!(
        !insts.iter().any(|n| matches!(n.inst, Inst::Call { .. })
            || matches!(n.inst, Inst::CallIndirect { .. })),
        "an UNBUNDLED CallableItem closure receiver must not fabricate a phantom Call"
    );
}

// ---------------------------------------------------------------------------
// Trust (R3, generics): pre-monomorphization alias marker lowering
// ---------------------------------------------------------------------------

/// The identity-erased marker `trust-mir-extract` stamps on a param-bearing
/// projection alias (`<S as Serializer>::Ok`).
fn pre_mono_alias_marker_ty() -> Ty {
    Ty::Unsupported {
        kind: trust_types::PRE_MONO_ALIAS_KIND.to_string(),
        detail: trust_types::PRE_MONO_ALIAS_DETAIL.to_string(),
    }
}

#[test]
fn test_pre_mono_alias_marker_lowers_to_opaque_zero_field_struct() {
    // R3: a param-typed value slot lowers to a REGISTERED zero-field struct
    // (the Datatype/Coroutine precedent — an opaque per-binding symbol with no
    // interpreted equality and no arithmetic sort), NOT `Unit` (which trust-mc
    // concretizes to 0) and NOT a whole-function lowering error.
    let func = VerifiableFunction {
        name: "alias_param".to_string(),
        def_path: "test::alias_param".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: pre_mono_alias_marker_ty(), name: Some("opaque".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_trust_ir(&func).expect("pre-mono alias param must lower");
    let opaque = module
        .structs
        .iter()
        .find(|s| s.name == "opaque_alias::pre_monomorphization")
        .expect("marker must register the opaque struct");
    assert!(opaque.fields.is_empty(), "the opaque alias struct must have ZERO fields");
    assert_valid_module(&module);
}

#[test]
fn test_pre_mono_alias_marker_feeding_arith_fails_closed() {
    // SOUNDNESS (the no-arith invariant): a value of the marker type feeding a
    // primitive binary op must FAIL lowering/validation — never a silent 0
    // (the documented `Param -> Unit` fragility this arm deliberately avoids).
    let func = VerifiableFunction {
        name: "alias_arith".to_string(),
        def_path: "test::alias_arith".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: pre_mono_alias_marker_ty(), name: Some("opaque".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(1)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    match lower_to_trust_ir(&func) {
        Err(_) => {} // fail-closed at lowering — good
        Ok(module) => {
            let errors = validate_module(&module);
            assert!(
                !errors.is_empty(),
                "an Add over the opaque alias struct must fail lowering or validation; \
                 got a valid module: {module:?}"
            );
        }
    }
}

#[test]
fn test_monomorphic_alias_details_still_fail_type_mapping() {
    // SOUNDNESS (exact-scope regression): only the pre-monomorphization detail
    // gets the opaque-struct lowering; every other `TyKind::Alias` detail keeps
    // failing the whole-function lowering (fail-closed).
    let mut func = VerifiableFunction {
        name: "alias_mono".to_string(),
        def_path: "test::alias_mono".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Unsupported {
                        kind: trust_types::PRE_MONO_ALIAS_KIND.to_string(),
                        detail: "alias args nest ADTs too deep (9) to normalize safely".into(),
                    },
                    name: Some("opaque".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    lower_to_trust_ir(&func).expect_err("nest-too-deep alias must keep failing lowering");

    func.body.locals[1].ty = Ty::Unsupported {
        kind: trust_types::PRE_MONO_ALIAS_KIND.to_string(),
        detail: "opaque alias has no typing env to reveal against".into(),
    };
    lower_to_trust_ir(&func).expect_err("env-less opaque alias must keep failing lowering");
}

// ---------------------------------------------------------------------------
// Round-3 — keyed/Result collect dest gate, HashMap::insert key gate, bignum
// Shl, unsigned div_ceil, serde_json::Value indexing, Display local-impl
// resolution, and the first-party bundle context probe.
// ---------------------------------------------------------------------------

/// Round-3, engine level: the four new TYPE-/ARG-GATED absent-callee discharges
/// (bignum Shl, unsigned div_ceil, serde_json::Value index) DISCHARGE exactly
/// their gated shapes — havoc result,
/// NO `Assert(false)` marker, NO absent-callee obligation — while every
/// primitive/user/symbolic sibling KEEPS the full may-panic encoding. Collect and
/// map mutation always stay closed because producer/cleanup, hasher, and allocator
/// authority is erased.
#[test]
fn test_round3_absent_callee_gates_engine() {
    // A caller with an explicit local per argument. `arg_locals` are (ty, operand
    // constructor uses Copy); a `None` local slot means the argument is the given
    // constant operand instead.
    #[allow(clippy::type_complexity)]
    let mk = |func: &str, arg_tys: Vec<Ty>, const_args: Vec<Option<Operand>>, dest_ty: Ty| {
        let mut locals = vec![LocalDecl { index: 0, ty: dest_ty.clone(), name: None }];
        let mut args: Vec<Operand> = Vec::new();
        let mut next_local = 1usize;
        for (i, ty) in arg_tys.iter().enumerate() {
            match const_args.get(i).cloned().flatten() {
                Some(op) => args.push(op),
                None => {
                    locals.push(LocalDecl {
                        index: next_local,
                        ty: ty.clone(),
                        name: Some(format!("a{next_local}")),
                    });
                    args.push(Operand::Copy(Place::local(next_local)));
                    next_local += 1;
                }
            }
        }
        let arg_count = next_local - 1;
        VerifiableFunction {
            name: "caller".to_string(),
            def_path: "test::caller".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals,
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: func.to_string(),
                            args,
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count,
                return_ty: dest_ty,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    };
    let absent_callee_obligations = |module: &trust_ir::Module| -> usize {
        module
            .proof_obligations
            .iter()
            .filter(|o| {
                o.kind == trust_ir::ObligationKind::PanicFreedom
                    && o.description
                        .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
            })
            .count()
    };
    let has_may_panic_marker = |module: &trust_ir::Module| -> bool {
        module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .any(|n| matches!(n.inst, Inst::Assert { .. }))
    };

    let r = |inner: Ty| Ty::Ref { mutable: false, inner: Box::new(inner) };
    let rm = |inner: Ty| Ty::Ref { mutable: true, inner: Box::new(inner) };
    let ty_string = || Ty::adt("std::string::String", vec![]);
    let ty_user_key = || Ty::adt("my_crate::PanickyKey", vec![("x".into(), Ty::i64())]);
    let ty_hashmap = || Ty::adt("std::collections::HashMap", vec![]);
    let ty_btreemap = || Ty::adt("std::collections::BTreeMap", vec![("root".into(), Ty::u64())]);
    let ty_result = || {
        Ty::adt("std::result::Result", vec![("ok".into(), Ty::u64()), ("err".into(), Ty::u64())])
    };
    let ty_value = || Ty::adt("serde_json::Value", vec![]);
    let ty_map_iter = || Ty::adt("std::iter::Map", vec![]);
    let ty_str = || Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) };
    let u128_uns = || Ty::Int { width: 128, signed: false };

    const KEYED_COLLECT: &str = "<std::iter::Map<std::collections::btree_map::Iter<'_, std::string::String, rational::Rat>, {closure@crates/ny-cert/src/selfcheck.rs:99:57: 99:65}> as std::iter::Iterator>::collect::<std::collections::BTreeMap<std::string::String, rational::Rat>>::<__trust_elem_bytes_72>";
    const KEYED_COLLECT_USER_KEY: &str = "<It as std::iter::Iterator>::collect::<std::collections::BTreeMap<my_crate::PanickyKey, u64>>::<__trust_elem_bytes_8>";
    const RESULT_VEC_COLLECT: &str = "<std::iter::Map<std::slice::Iter<'_, rational::Rat>, {closure@crates/ny-cert/src/schema.rs:200:14: 200:17}> as std::iter::Iterator>::collect::<std::result::Result<std::vec::Vec<std::string::String>, rational::RatError>>::<__trust_elem_bytes_16>";
    const RESULT_BTREE_COLLECT: &str = "<It as std::iter::Iterator>::collect::<std::result::Result<std::collections::BTreeMap<std::string::String, rational::Rat>, rational::RatError>>::<__trust_elem_bytes_72>";
    const RESULT_BTREE_COLLECT_USER_KEY: &str = "<It as std::iter::Iterator>::collect::<std::result::Result<std::collections::BTreeMap<my_crate::PanickyKey, rational::Rat>, rational::RatError>>::<__trust_elem_bytes_72>";

    // (callee, arg types, const-arg overrides, dest, expect_discharged, label)
    #[allow(clippy::type_complexity)]
    let cases: Vec<(&str, Vec<Ty>, Vec<Option<Operand>>, Ty, bool, &str)> = vec![
        // --- keyed/Result collect (dest place type + callee turbofish) ---
        (
            KEYED_COLLECT,
            vec![ty_map_iter()],
            vec![None],
            ty_btreemap(),
            false,
            "collect into BTreeMap<String, Rat>",
        ),
        (
            KEYED_COLLECT_USER_KEY,
            vec![ty_map_iter()],
            vec![None],
            ty_btreemap(),
            false,
            "collect into BTreeMap<UserKey, _>",
        ),
        (
            RESULT_VEC_COLLECT,
            vec![ty_map_iter()],
            vec![None],
            ty_result(),
            false,
            "collect into Result<Vec<String>, RatError>",
        ),
        (
            RESULT_BTREE_COLLECT,
            vec![ty_map_iter()],
            vec![None],
            ty_result(),
            false,
            "collect into Result<BTreeMap<String, Rat>, RatError>",
        ),
        (
            RESULT_BTREE_COLLECT_USER_KEY,
            vec![ty_map_iter()],
            vec![None],
            ty_result(),
            false,
            "collect into Result<BTreeMap<UserKey, _>, _>",
        ),
        // --- HashMap::insert key gate ---
        (
            "std::collections::HashMap::<K, V, S, A>::insert",
            vec![rm(ty_hashmap()), ty_string(), Ty::u64()],
            vec![None, None, None],
            Ty::u64(),
            false,
            "HashMap::insert String key",
        ),
        (
            "std::collections::HashMap::<K, V, S, A>::insert",
            vec![rm(ty_hashmap()), ty_ratio(ty_bigint()), Ty::u32()],
            vec![None, None, None],
            Ty::u64(),
            false,
            "HashMap::insert BigRational key",
        ),
        (
            "std::collections::HashMap::<K, V, S, A>::insert",
            vec![rm(ty_hashmap()), ty_user_key(), Ty::u64()],
            vec![None, None, None],
            Ty::u64(),
            false,
            "HashMap::insert user key",
        ),
        // --- bignum Shl ---
        (
            "std::ops::Shl::shl",
            vec![r(ty_bigint()), Ty::u32()],
            vec![None, None],
            ty_bigint(),
            false,
            "BigInt << u32",
        ),
        (
            "std::ops::Shl::shl",
            vec![r(ty_biguint()), Ty::usize()],
            vec![None, None],
            ty_biguint(),
            false,
            "BigUint << usize",
        ),
        (
            "std::ops::Shl::shl",
            vec![r(ty_bigint()), Ty::i64()],
            vec![None, None],
            ty_bigint(),
            false,
            "BigInt << i64 (signed rhs panics on negative)",
        ),
        (
            "std::ops::Shl::shl",
            vec![r(ty_bigint()), u128_uns()],
            vec![None, None],
            ty_bigint(),
            false,
            "BigInt << u128 (width > 64)",
        ),
        (
            "std::ops::Shl::shl",
            vec![Ty::u64(), Ty::u32()],
            vec![None, None],
            Ty::u64(),
            false,
            "u64 << u32 (primitive shift-overflow)",
        ),
        // --- unsigned div_ceil with literal nonzero divisor ---
        (
            "core::num::<impl u64>::div_ceil",
            vec![Ty::u64(), Ty::u64()],
            vec![None, Some(Operand::Constant(ConstValue::Uint(2, 64)))],
            Ty::u64(),
            true,
            "u64::div_ceil(2)",
        ),
        (
            "core::num::<impl u64>::div_ceil",
            vec![Ty::u64(), Ty::u64()],
            vec![None, None],
            Ty::u64(),
            false,
            "u64::div_ceil(symbolic)",
        ),
        (
            "core::num::<impl u64>::div_ceil",
            vec![Ty::u64(), Ty::u64()],
            vec![None, Some(Operand::Constant(ConstValue::Uint(0, 64)))],
            Ty::u64(),
            false,
            "u64::div_ceil(0) (division by zero)",
        ),
        (
            "core::num::<impl i64>::div_ceil",
            vec![Ty::i64(), Ty::i64()],
            vec![None, Some(Operand::Constant(ConstValue::Int(2)))],
            Ty::i64(),
            false,
            "i64::div_ceil (signed MIN/-1 overflow)",
        ),
        // --- serde_json::Value Index ---
        (
            "std::ops::Index::index",
            vec![r(ty_value()), r(ty_str())],
            vec![None, None],
            r(ty_value()),
            false,
            "serde_json::Value[..] read",
        ),
        (
            "std::ops::Index::index",
            vec![r(ty_hashmap()), r(ty_str())],
            vec![None, None],
            Ty::u64(),
            false,
            "HashMap[..] (missing-key panic)",
        ),
    ];

    for (callee, arg_tys, const_args, dest_ty, discharged, label) in cases {
        let module = lower_to_trust_ir(&mk(callee, arg_tys, const_args, dest_ty))
            .unwrap_or_else(|e| panic!("`{label}` (`{callee}`) must lower, not Err: {e:?}"));
        assert_valid_module(&module);
        if discharged {
            assert_eq!(
                absent_callee_obligations(&module),
                0,
                "{label}: a discharged callee must NOT raise the absent-callee obligation"
            );
            assert!(
                !has_may_panic_marker(&module),
                "{label}: a discharged callee must NOT emit the Assert(false) may-panic marker"
            );
        } else {
            assert!(
                has_may_panic_marker(&module),
                "{label}: a fail-closed callee must KEEP the Assert(false) may-panic marker"
            );
        }
    }
}

/// Round-3: `Display::fmt` on a LOCAL ADT receiver resolves to the ADT's bundled
/// in-module impl (the thiserror `#[error(transparent)]` shape —
/// `Display::fmt(&self.0, f)`) and is emitted as a REAL call into the impl body,
/// with NO absent-callee obligation; an UNBUNDLED receiver keeps the fail-closed
/// absent-callee encoding.
#[test]
fn test_round3_display_fmt_resolves_local_impl() {
    let ty_err = || Ty::adt("test::MyErr", vec![("code".into(), Ty::u64())]);
    let ty_fmt = || Ty::adt("std::fmt::Formatter", vec![]);
    let r = |inner: Ty| Ty::Ref { mutable: false, inner: Box::new(inner) };
    let rm = |inner: Ty| Ty::Ref { mutable: true, inner: Box::new(inner) };

    let mk_caller = |recv_ty: Ty| VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: recv_ty, name: Some("inner".into()) },
                LocalDecl { index: 2, ty: rm(ty_fmt()), name: Some("f".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::fmt::Display::fmt".to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let impl_fn = VerifiableFunction {
        name: "<test::MyErr as std::fmt::Display>::fmt".to_string(),
        def_path: "<test::MyErr as std::fmt::Display>::fmt".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: r(ty_err()), name: Some("self".into()) },
                LocalDecl { index: 2, ty: rm(ty_fmt()), name: Some("f".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let absent_callee_obligations = |module: &trust_ir::Module| -> usize {
        module
            .proof_obligations
            .iter()
            .filter(|o| {
                o.kind == trust_ir::ObligationKind::PanicFreedom
                    && o.description
                        .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
            })
            .count()
    };

    // BUNDLED impl: the call resolves to a REAL Inst::Call into functions[1].
    let module = lower_to_trust_ir_functions("display_resolve", &[mk_caller(r(ty_err())), impl_fn])
        .expect("Display::fmt with a bundled local impl must lower");
    assert_valid_module(&module);
    assert!(
        module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .any(|n| matches!(&n.inst, Inst::Call { callee, .. } if callee.index() == 1)),
        "Display::fmt on a bundled local ADT must emit a real call into the impl body"
    );
    assert_eq!(
        absent_callee_obligations(&module),
        0,
        "a locally-resolved Display::fmt must not raise the absent-callee obligation"
    );

    // UNBUNDLED receiver: stays on the fail-closed absent-callee arm.
    let module = lower_to_trust_ir(&mk_caller(r(Ty::adt("test::OtherErr", vec![]))))
        .expect("unbundled Display::fmt receiver must still lower fail-soft");
    assert_valid_module(&module);
    assert_eq!(
        absent_callee_obligations(&module),
        1,
        "an unbundled Display::fmt receiver must KEEP the absent-callee obligation"
    );
}

/// Round-3 (first-party bundling gap): the CONTEXT-AWARE survivor probe. A
/// function whose body invokes a closure through the `FnOnce::call_once` shim
/// hard-fails ALONE (the closure body is not in the module), but the probe —
/// which registers every candidate's name/signature — correctly reports it
/// lowers IN CONTEXT; with the closure missing from the candidate set the probe
/// stays fail-closed.
#[test]
fn test_round3_bundle_context_probe() {
    let closure_name = "test::probe::{closure#0}".to_string();
    let closure_ty =
        Ty::Closure { name: closure_name.clone(), upvars: vec![Ty::u32()], call: None };

    let caller = VerifiableFunction {
        name: "probe_caller".to_string(),
        def_path: "test::probe_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("captured".into()) },
                LocalDecl { index: 2, ty: closure_ty.clone(), name: Some("closure".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32()]), name: Some("args".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("result".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Aggregate(
                                AggregateKind::Closure {
                                    name: closure_name.clone(),
                                    captures: vec![],
                                    call_kind: ClosureCallKind::FnOnce,
                                },
                                vec![Operand::Copy(Place::local(1))],
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Aggregate(
                                AggregateKind::Tuple,
                                vec![Operand::Constant(ConstValue::Uint(7, 32))],
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::ops::function::FnOnce::call_once".to_string(),
                        args: vec![Operand::Move(Place::local(2)), Operand::Move(Place::local(3))],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let closure_body = VerifiableFunction {
        name: closure_name.clone(),
        def_path: closure_name.clone(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: closure_ty, name: Some("self".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("arg".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let empty: std::collections::HashSet<String> = std::collections::HashSet::new();
    // ALONE the caller hard-fails (the shim's closure body is not in the module) —
    // this is exactly the alone-probe misverdict the context probe fixes.
    assert!(
        lower_to_trust_ir(&caller).is_err(),
        "caller with a closure shim must fail to lower ALONE"
    );
    // IN CONTEXT (closure body registered) it lowers.
    assert!(
        verifiable_function_lowers_in_module_context(
            &[caller.clone(), closure_body.clone()],
            0,
            &empty,
            &empty
        ),
        "caller must lower in the candidate set's context"
    );
    // And the closure body itself probes fine at its own index.
    assert!(
        verifiable_function_lowers_in_module_context(
            &[caller.clone(), closure_body],
            1,
            &empty,
            &empty
        ),
        "closure body must lower in context"
    );
    // With the closure missing from the candidate set the probe FAILS CLOSED.
    assert!(
        !verifiable_function_lowers_in_module_context(&[caller], 0, &empty, &empty),
        "probe must fail closed when the shim's closure body is not a candidate"
    );
    // Out-of-range index fails closed.
    assert!(!verifiable_function_lowers_in_module_context(&[], 0, &empty, &empty));
}

/// Round-3: `Rev<Range<usize>>` / bare `Range<int>` receivers are recognized
/// TOTAL for `Iterator::next` (the batch-44 `exact::solve_system` reversed
/// elimination loop), while `Range<UserStep>` stays fail-closed.
///
/// Round-5: `RangeInclusive<int>` (extracted shape: `start`/`end` ints + the
/// `exhausted` Bool) joins the total bases — batch-49's residual
/// `exact::solve_system` `for c in col..=n` loops — while
/// `RangeInclusive<UserStep>` (ADT bounds driving a user `Step`) stays
/// fail-closed.
#[test]
fn test_round3_range_iterator_next_discharges() {
    let ty_range = || {
        Ty::adt("std::ops::Range", vec![("start".into(), Ty::usize()), ("end".into(), Ty::usize())])
    };
    let ty_rev_range = || Ty::adt("std::iter::Rev", vec![("iter".into(), ty_range())]);
    let ty_user_range = || {
        Ty::adt(
            "std::ops::Range",
            vec![
                ("start".into(), Ty::adt("my_crate::Step", vec![])),
                ("end".into(), Ty::adt("my_crate::Step", vec![])),
            ],
        )
    };
    let rm = |inner: Ty| Ty::Ref { mutable: true, inner: Box::new(inner) };

    let mk = |recv_ty: Ty| VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: recv_ty, name: Some("it".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::iter::Iterator::next".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let absent_callee_obligations = |module: &trust_ir::Module| -> usize {
        module
            .proof_obligations
            .iter()
            .filter(|o| {
                o.kind == trust_ir::ObligationKind::PanicFreedom
                    && o.description
                        .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
            })
            .count()
    };

    for (recv, discharged, label) in [
        (rm(ty_range()), true, "Range<usize>::next"),
        (rm(ty_rev_range()), true, "Rev<Range<usize>>::next"),
        (rm(ty_user_range()), false, "Range<UserStep>::next"),
        // Round-5 — the REAL extracted `RangeInclusive<usize>` shape (`start`/`end`
        // ints + the `exhausted` Bool the exclusive-Range all-Int gate could not
        // cover) now DISCHARGES.
        (
            rm(Ty::adt(
                "std::ops::RangeInclusive",
                vec![
                    ("start".into(), Ty::usize()),
                    ("end".into(), Ty::usize()),
                    ("exhausted".into(), Ty::Bool),
                ],
            )),
            true,
            "RangeInclusive<usize>::next (Round-5)",
        ),
        // Round-5 fail-closed control — ADT bounds drive a user `Step` whose
        // `forward`/`backward` may panic; and a Bool-only lookalike carries no
        // integer cursor at all. Both must KEEP the obligation.
        (
            rm(Ty::adt(
                "std::ops::RangeInclusive",
                vec![
                    ("start".into(), Ty::adt("my_crate::Step", vec![])),
                    ("end".into(), Ty::adt("my_crate::Step", vec![])),
                    ("exhausted".into(), Ty::Bool),
                ],
            )),
            false,
            "RangeInclusive<UserStep>::next",
        ),
        (
            rm(Ty::adt("std::ops::RangeInclusive", vec![("exhausted".into(), Ty::Bool)])),
            false,
            "RangeInclusive with no integer cursor",
        ),
    ] {
        let module = lower_to_trust_ir(&mk(recv))
            .unwrap_or_else(|e| panic!("{label} must lower, not Err: {e:?}"));
        assert_valid_module(&module);
        assert_eq!(
            absent_callee_obligations(&module) == 0,
            discharged,
            "{label}: discharge expectation mismatch"
        );
    }
}
