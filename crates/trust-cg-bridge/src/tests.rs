//! Tests for trust-cg-bridge.

use trust_types::UnwindEdge;
use trust_cg_lower::instructions::{
    AtomicOrdering as LirAtomicOrdering, AtomicRmwOp, Block, FloatCC, IntCC, Opcode, Value,
};
use trust_cg_lower::types::Type as LirType;
use trust_types::{
    AggregateKind, AtomicOpKind, AtomicOperation, AtomicOrdering, BasicBlock as TrustBlock, BinOp,
    BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnOp, VerifiableBody, VerifiableFunction,
};

use super::*;

// -- Type mapping tests --

#[test]
fn test_map_type_bool() {
    assert_eq!(map_type(&Ty::Bool).unwrap(), LirType::B1);
}

#[test]
fn test_map_type_integers() {
    assert_eq!(map_type(&Ty::i8()).unwrap(), LirType::I8);
    assert_eq!(map_type(&Ty::u8()).unwrap(), LirType::I8);
    assert_eq!(map_type(&Ty::i16()).unwrap(), LirType::I16);
    assert_eq!(map_type(&Ty::u16()).unwrap(), LirType::I16);
    assert_eq!(map_type(&Ty::i32()).unwrap(), LirType::I32);
    assert_eq!(map_type(&Ty::u32()).unwrap(), LirType::I32);
    assert_eq!(map_type(&Ty::i64()).unwrap(), LirType::I64);
    assert_eq!(map_type(&Ty::u64()).unwrap(), LirType::I64);
    assert_eq!(map_type(&Ty::i128()).unwrap(), LirType::I128);
    assert_eq!(map_type(&Ty::u128()).unwrap(), LirType::I128);
}

#[test]
fn test_map_type_floats() {
    assert_eq!(map_type(&Ty::f32_ty()).unwrap(), LirType::F32);
    assert_eq!(map_type(&Ty::f64_ty()).unwrap(), LirType::F64);
}

#[test]
fn test_map_type_unit() {
    assert!(matches!(map_type(&Ty::Unit), Err(BridgeError::UnsupportedType(_))));
    assert!(matches!(map_type(&Ty::Never), Err(BridgeError::UnsupportedType(_))));
}

#[test]
fn test_map_type_fieldless_adt_fails_closed() {
    let ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "core::option::Option<i32>".into(),
        fields: vec![],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    assert!(matches!(map_type(&ty), Err(BridgeError::UnsupportedType(_))));
}

#[test]
fn test_map_type_bv() {
    assert_eq!(map_type(&Ty::Bv(32)).unwrap(), LirType::I32);
    assert_eq!(map_type(&Ty::Bv(64)).unwrap(), LirType::I64);
}

#[test]
fn test_map_type_ref_and_slice() {
    // References map to I64 (pointer-sized)
    assert_eq!(
        map_type(&Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) }).unwrap(),
        LirType::I64
    );
    // Slices map to fat pointer struct { ptr: I64, len: I64 }
    assert_eq!(
        map_type(&Ty::Slice { elem: Box::new(Ty::i32()) }).unwrap(),
        LirType::Struct(vec![LirType::I64, LirType::I64])
    );
}

#[test]
fn test_map_type_unsupported_bv() {
    // Odd bitvector widths are unsupported
    assert!(map_type(&Ty::Bv(7)).is_err());
}

// -- BinOp mapping tests --

#[test]
fn test_map_binop_arithmetic() {
    assert_eq!(map_binop(BinOp::Add, false).unwrap(), Opcode::Iadd);
    assert_eq!(map_binop(BinOp::Sub, false).unwrap(), Opcode::Isub);
    assert_eq!(map_binop(BinOp::Mul, false).unwrap(), Opcode::Imul);
    assert_eq!(map_binop(BinOp::Div, false).unwrap(), Opcode::Udiv);
    assert_eq!(map_binop(BinOp::Div, true).unwrap(), Opcode::Sdiv);
    assert_eq!(map_binop(BinOp::Rem, false).unwrap(), Opcode::Urem);
    assert_eq!(map_binop(BinOp::Rem, true).unwrap(), Opcode::Srem);
}

#[test]
fn test_map_binop_comparison() {
    assert_eq!(map_binop(BinOp::Eq, false).unwrap(), Opcode::Icmp { cond: IntCC::Equal });
    assert_eq!(map_binop(BinOp::Ne, false).unwrap(), Opcode::Icmp { cond: IntCC::NotEqual });
    assert_eq!(map_binop(BinOp::Lt, true).unwrap(), Opcode::Icmp { cond: IntCC::SignedLessThan });
    assert_eq!(
        map_binop(BinOp::Lt, false).unwrap(),
        Opcode::Icmp { cond: IntCC::UnsignedLessThan }
    );
}

#[test]
fn test_map_binop_bitwise() {
    assert_eq!(map_binop(BinOp::BitAnd, false).unwrap(), Opcode::Band);
    assert_eq!(map_binop(BinOp::BitOr, false).unwrap(), Opcode::Bor);
    assert_eq!(map_binop(BinOp::BitXor, false).unwrap(), Opcode::Bxor);
    assert_eq!(map_binop(BinOp::Shl, false).unwrap(), Opcode::Ishl);
    assert_eq!(map_binop(BinOp::Shr, false).unwrap(), Opcode::Ushr);
    assert_eq!(map_binop(BinOp::Shr, true).unwrap(), Opcode::Sshr);
}

#[test]
fn test_map_binop_cmp_unsupported() {
    assert!(map_binop(BinOp::Cmp, false).is_err());
}

#[test]
fn test_map_float_binop() {
    assert_eq!(map_float_binop(BinOp::Add).unwrap(), Opcode::Fadd);
    assert_eq!(map_float_binop(BinOp::Sub).unwrap(), Opcode::Fsub);
    assert_eq!(map_float_binop(BinOp::Mul).unwrap(), Opcode::Fmul);
    assert_eq!(map_float_binop(BinOp::Div).unwrap(), Opcode::Fdiv);
    assert_eq!(map_float_binop(BinOp::Lt).unwrap(), Opcode::Fcmp { cond: FloatCC::LessThan });
    assert_eq!(
        map_float_binop(BinOp::Ge).unwrap(),
        Opcode::Fcmp { cond: FloatCC::GreaterThanOrEqual }
    );
    assert!(map_float_binop(BinOp::BitAnd).is_err());
}

// -- UnOp mapping tests --

#[test]
fn test_map_unop() {
    assert_eq!(map_unop(UnOp::Not).unwrap(), Opcode::Bnot);
    assert_eq!(map_unop(UnOp::Neg).unwrap(), Opcode::Ineg);
    assert!(map_unop(UnOp::PtrMetadata).is_err());
}

// -- Full function lowering tests --

/// Helper: build the MIR for `fn add(a: i32, b: i32) -> i32 { a + b }`
fn make_add_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "add".to_string(),
        def_path: "test::add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None }, // return
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
    let lir = lower_to_lir(&func).expect("should lower successfully");

    assert_eq!(lir.name, "add");
    assert_eq!(lir.signature.params.len(), 2);
    assert_eq!(lir.signature.params[0], LirType::I32);
    assert_eq!(lir.signature.params[1], LirType::I32);
    assert_eq!(lir.signature.returns.len(), 1);
    assert_eq!(lir.signature.returns[0], LirType::I32);
    assert_eq!(lir.blocks.len(), 1);
    assert_eq!(lir.entry_block, Block(0));

    let bb0 = &lir.blocks[&Block(0)];
    // Should have: iadd instruction + return
    assert!(bb0.instructions.len() >= 2);
    assert!(matches!(bb0.instructions.last().unwrap().opcode, Opcode::Return));
    // The add instruction should be an Iadd.
    let add_inst = bb0
        .instructions
        .iter()
        .find(|i| matches!(i.opcode, Opcode::Iadd))
        .expect("should have Iadd instruction");
    assert_eq!(add_inst.args.len(), 2);
    assert_eq!(add_inst.results.len(), 1);

    // Return instruction must carry the return value.
    let ret_inst = bb0.instructions.last().unwrap();
    assert_eq!(ret_inst.args.len(), 1, "Return must include return value in args for ISel");
    assert_eq!(
        ret_inst.args[0], add_inst.results[0],
        "Return arg must be the value assigned to local 0"
    );
}

#[test]
fn test_lower_float_add_function() {
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

    let lir = lower_to_lir(&func).expect("float add should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert_eq!(lir.signature.params, vec![LirType::F64, LirType::F64]);
    assert_eq!(lir.signature.returns, vec![LirType::F64]);
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Fadd)));
}

#[test]
fn test_lower_float_comparison_function() {
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

    let lir = lower_to_lir(&func).expect("float comparison should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Fcmp { cond: FloatCC::LessThan }))
    );
}

#[test]
fn test_lower_unit_return_function() {
    // fn noop() -> ()
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

    let lir = lower_to_lir(&func).expect("should lower successfully");
    assert_eq!(lir.signature.params.len(), 0);
    assert!(lir.signature.returns.is_empty()); // Unit returns nothing

    // Unit return: Return should have empty args.
    let bb0 = &lir.blocks[&Block(0)];
    let ret_inst = bb0.instructions.last().unwrap();
    assert!(matches!(ret_inst.opcode, Opcode::Return));
    assert!(ret_inst.args.is_empty(), "Unit return should have empty args");
}

#[test]
fn test_lower_constant_use() {
    // fn const_fn() -> i32 { 42 }
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

    let lir = lower_to_lir(&func).expect("should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should have Iconst + Return
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Iconst { .. })));
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

    let lir = lower_to_lir(&func).expect("should lower");
    assert_eq!(lir.blocks.len(), 2);
    let bb0 = &lir.blocks[&Block(0)];
    assert!(matches!(bb0.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(1) }));
}

#[test]
fn test_lower_switch_int_binary() {
    // SwitchInt with one target = Brif
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

    let lir = lower_to_lir(&func).expect("should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(bb0.instructions.iter().any(|i| matches!(
        i.opcode,
        Opcode::Brif { then_dest: Block(1), else_dest: Block(2), .. }
    )));
}

#[test]
fn test_lower_call_basic() {
    // Basic call lowering: call with no args and a continuation block.
    let func = VerifiableFunction {
        name: "call_fn".to_string(),
        def_path: "test::call_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "other_fn".to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let result = lower_to_lir(&func);
    assert!(result.is_ok(), "call lowering should succeed");
    let lir = result.unwrap();
    let bb0 = &lir.blocks[&Block(0)];
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Call { .. })));
}

#[test]
fn test_lower_atomic_fetch_add_call() {
    let func = VerifiableFunction {
        name: "atomic_fetch_add".to_string(),
        def_path: "test::atomic_fetch_add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { pointee: Box::new(Ty::u64()), mutable: true },
                    name: Some("ptr".into()),
                },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("delta".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::intrinsics::atomic_xadd_seqcst".to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
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
            arg_count: 2,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("atomic fetch_add should lower");
    let bb0 = &lir.blocks[&Block(0)];

    assert!(bb0.instructions.iter().any(|i| matches!(
        i.opcode,
        Opcode::AtomicRmw {
            op: AtomicRmwOp::Add,
            ty: LirType::I64,
            ordering: LirAtomicOrdering::SeqCst
        }
    )));
    assert!(matches!(bb0.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(1) }));
}

#[test]
fn test_lower_midpoint_function() {
    // The standard midpoint test: fn get_midpoint(a: u64, b: u64) -> u64 { (a + b) / 2 }
    // Uses CheckedBinaryOp for the add, and BinaryOp for the div.
    let func = VerifiableFunction {
        name: "get_midpoint".to_string(),
        def_path: "midpoint::get_midpoint".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::u64(), name: None }, // add result
                LocalDecl { index: 4, ty: Ty::u64(), name: None }, // div result
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

    let lir = lower_to_lir(&func).expect("midpoint should lower");

    assert_eq!(lir.name, "get_midpoint");
    assert_eq!(lir.blocks.len(), 2);
    assert_eq!(lir.signature.params, vec![LirType::I64, LirType::I64]);
    assert_eq!(lir.signature.returns, vec![LirType::I64]);

    // bb0 should have Iadd + Jump
    let bb0 = &lir.blocks[&Block(0)];
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Iadd)));
    assert!(matches!(bb0.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(1) }));

    // bb1 should have Iconst(2) + Udiv + Return
    let bb1 = &lir.blocks[&Block(1)];
    assert!(bb1.instructions.iter().any(|i| matches!(i.opcode, Opcode::Udiv)));
    let ret_inst = bb1.instructions.last().unwrap();
    assert!(matches!(ret_inst.opcode, Opcode::Return));
    // Return must carry the return value in multi-block functions.
    assert_eq!(ret_inst.args.len(), 1, "Return in midpoint bb1 must include return value");
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

    let lir = lower_to_lir(&func).expect("should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Bnot)));
}

#[test]
fn test_lower_nop_statement() {
    // fn nop_fn(a: i32) -> i32 { a } with a Nop before the return assign
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

    let lir = lower_to_lir(&func).expect("Nop should not block lowering");
    let bb0 = &lir.blocks[&Block(0)];
    // Nop produces no instructions; only the Return instruction.
    assert!(matches!(bb0.instructions.last().unwrap().opcode, Opcode::Return));
}

#[test]
fn test_lower_use_copy() {
    // fn copy_fn(a: i32) -> i32 { let x = a; x }
    let func = VerifiableFunction {
        name: "copy_fn".to_string(),
        def_path: "test::copy_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
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

    let lir = lower_to_lir(&func).expect("Use copy should lower");
    // Use is a value alias — should produce only the Return instruction.
    let bb0 = &lir.blocks[&Block(0)];
    assert!(matches!(bb0.instructions.last().unwrap().opcode, Opcode::Return));
}

#[test]
fn test_lower_const_bool_and_uint_variants() {
    // Test Bool and Uint(val, width) constant variants.
    let func = VerifiableFunction {
        name: "const_variety".to_string(),
        def_path: "test::const_variety".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: None },
                LocalDecl { index: 2, ty: Ty::u8(), name: None },
                LocalDecl { index: 3, ty: Ty::u16(), name: None },
                LocalDecl { index: 4, ty: Ty::u64(), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(255, 8))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1000, 16))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(
                            42_000_000_000,
                            64,
                        ))),
                        span: SourceSpan::default(),
                    },
                ],
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

    let lir = lower_to_lir(&func).expect("constants should lower");
    let bb0 = &lir.blocks[&Block(0)];

    // Should have 4 Iconst instructions + Return.
    let iconst_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Iconst { .. })).count();
    assert_eq!(iconst_count, 4, "expected 4 Iconst instructions");

    // Check the Bool const emits B1.
    let bool_inst = bb0
        .instructions
        .iter()
        .find(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::B1, imm: 1 }))
        .expect("should have Iconst B1 for true");
    assert_eq!(bool_inst.results.len(), 1);

    // Check the u8 const emits I8.
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::I8, .. }))
    );

    // Check the u16 const emits I16.
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::I16, .. }))
    );
}

/// Regression test for #826: ConstValue::Int should infer the narrowest
/// signed LIR type from the value range, not always emit I64.
#[test]
fn test_lower_const_int_width_inference() {
    let func = VerifiableFunction {
        name: "int_widths".to_string(),
        def_path: "test::int_widths".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None }, // return
                LocalDecl { index: 1, ty: Ty::i8(), name: None },  // i8 range
                LocalDecl { index: 2, ty: Ty::i16(), name: None }, // i16 range
                LocalDecl { index: 3, ty: Ty::i32(), name: None }, // i32 range
                LocalDecl { index: 4, ty: Ty::i64(), name: None }, // i64 range
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    // 42 fits in i8 (-128..=127)
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
                        span: SourceSpan::default(),
                    },
                    // 1000 fits in i16 (-32768..=32767)
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1000))),
                        span: SourceSpan::default(),
                    },
                    // 100_000 fits in i32
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(100_000))),
                        span: SourceSpan::default(),
                    },
                    // 5_000_000_000 exceeds i32, needs i64
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(5_000_000_000))),
                        span: SourceSpan::default(),
                    },
                ],
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

    let lir = lower_to_lir(&func).expect("signed int constants should lower");
    let bb0 = &lir.blocks[&Block(0)];

    // Collect Iconst types in order.
    let types: Vec<LirType> = bb0
        .instructions
        .iter()
        .filter_map(|i| match &i.opcode {
            Opcode::Iconst { ty, .. } => Some(ty.clone()),
            _ => None,
        })
        .collect();

    assert_eq!(types.len(), 4, "expected 4 Iconst instructions, got {}", types.len());
    assert_eq!(types[0], LirType::I8, "42 should emit I8");
    assert_eq!(types[1], LirType::I16, "1000 should emit I16");
    assert_eq!(types[2], LirType::I32, "100_000 should emit I32");
    assert_eq!(types[3], LirType::I64, "5_000_000_000 should emit I64");
}

/// Negative signed constants should also infer the narrowest type.
#[test]
fn test_lower_const_int_negative_width_inference() {
    let func = VerifiableFunction {
        name: "neg_int_widths".to_string(),
        def_path: "test::neg_int_widths".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i8(), name: None },
                LocalDecl { index: 2, ty: Ty::i16(), name: None },
                LocalDecl { index: 3, ty: Ty::i32(), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    // -1 fits in i8
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(-1))),
                        span: SourceSpan::default(),
                    },
                    // -200 fits in i16 but not i8
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(-200))),
                        span: SourceSpan::default(),
                    },
                    // -100_000 fits in i32 but not i16
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(-100_000))),
                        span: SourceSpan::default(),
                    },
                ],
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

    let lir = lower_to_lir(&func).expect("negative int constants should lower");
    let bb0 = &lir.blocks[&Block(0)];

    let types: Vec<LirType> = bb0
        .instructions
        .iter()
        .filter_map(|i| match &i.opcode {
            Opcode::Iconst { ty, .. } => Some(ty.clone()),
            _ => None,
        })
        .collect();

    assert_eq!(types.len(), 3, "expected 3 Iconst instructions");
    assert_eq!(types[0], LirType::I8, "-1 should emit I8");
    assert_eq!(types[1], LirType::I16, "-200 should emit I16");
    assert_eq!(types[2], LirType::I32, "-100_000 should emit I32");
}

#[test]
fn test_lower_cast_widening_unsigned() {
    // fn widen(a: u8) -> u32 { a as u32 }
    let func = VerifiableFunction {
        name: "widen".to_string(),
        def_path: "test::widen".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u8(), name: Some("a".into()) },
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

    let lir = lower_to_lir(&func).expect("widening cast should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should have Uextend instruction (unsigned source).
    assert!(
        bb0.instructions.iter().any(|i| matches!(
            i.opcode,
            Opcode::Uextend { from_ty: LirType::I8, to_ty: LirType::I32 }
        )),
        "expected Uextend from I8 to I32"
    );
}

#[test]
fn test_lower_cast_widening_signed() {
    // fn widen_signed(a: i8) -> i32 { a as i32 }
    let func = VerifiableFunction {
        name: "widen_signed".to_string(),
        def_path: "test::widen_signed".to_string(),
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

    let lir = lower_to_lir(&func).expect("signed widening cast should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should have Sextend instruction (signed source).
    assert!(
        bb0.instructions.iter().any(|i| matches!(
            i.opcode,
            Opcode::Sextend { from_ty: LirType::I8, to_ty: LirType::I32 }
        )),
        "expected Sextend from I8 to I32"
    );
}

#[test]
fn test_lower_cast_narrowing() {
    // fn narrow(a: i64) -> i16 { a as i16 }
    let func = VerifiableFunction {
        name: "narrow".to_string(),
        def_path: "test::narrow".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i16(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("a".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::i16()),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i16(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("narrowing cast should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should have Trunc instruction.
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Trunc { to_ty: LirType::I16 })),
        "expected Trunc to I16"
    );
}

#[test]
fn test_lower_cast_same_width() {
    // fn same(a: i32) -> u32 { a as u32 } (same width, no instruction)
    let func = VerifiableFunction {
        name: "same_width".to_string(),
        def_path: "test::same_width".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
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

    let lir = lower_to_lir(&func).expect("same-width cast should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Same width produces no Trunc/Sextend/Uextend — just a Return.
    assert!(!bb0.instructions.iter().any(|i| matches!(
        i.opcode,
        Opcode::Trunc { .. } | Opcode::Sextend { .. } | Opcode::Uextend { .. }
    )));
}

#[test]
fn test_lower_call_terminator() {
    // fn caller() -> i32 { callee(10) }
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
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
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

    let lir = lower_to_lir(&func).expect("call should lower");
    let bb0 = &lir.blocks[&Block(0)];

    // Should have: Iconst (for arg 10) + Call + Jump to bb1.
    let call_inst = bb0
        .instructions
        .iter()
        .find(|i| matches!(i.opcode, Opcode::Call { .. }))
        .expect("should have Call instruction");
    match &call_inst.opcode {
        Opcode::Call { name } => assert_eq!(name, "callee"),
        _ => panic!("expected Call opcode"),
    }
    assert_eq!(call_inst.args.len(), 1, "call should have 1 argument");
    assert_eq!(call_inst.results.len(), 1, "call should have 1 result");
    assert_eq!(
        lir.value_types.get(&call_inst.results[0]),
        Some(&LirType::I32),
        "call result should preserve its lowered return type for ISel"
    );

    // Should jump to bb1 after call.
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Jump { dest: Block(1) })));
}

#[test]
fn test_emit_object_scalar_call_result_return_uses_value_types() {
    let callee = VerifiableFunction {
        name: "callee_i32".to_string(),
        def_path: "test::callee_i32".to_string(),
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
        name: "caller_i32".to_string(),
        def_path: "test::caller_i32".to_string(),
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
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "callee_i32".to_string(),
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

    let callee_lir = lower_to_lir(&callee).expect("callee should lower");
    let caller_lir = lower_to_lir(&caller).expect("caller should lower");
    let backend = crate::codegen_backend::TrustCgCodegenBackend::host();
    let objects = backend.emit_objects(&[callee_lir, caller_lir]);

    assert!(
        objects.is_ok(),
        "per-function object emission should succeed for a direct call whose result is returned: {objects:?}"
    );

    let objects = objects.unwrap();
    assert_eq!(objects.len(), 2, "callee and caller should each emit one object");
    assert!(
        objects.iter().any(|(name, bytes)| name == "caller_i32" && !bytes.is_empty()),
        "caller object should be present and non-empty"
    );
}

#[test]
fn test_lower_aggregate_call_result_populates_value_types() {
    let pair_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "Pair".into(),
        fields: vec![("left".into(), Ty::i64()), ("right".into(), Ty::i32())],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "call_pair".to_string(),
        def_path: "test::call_pair".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: pair_ty.clone(), name: None }],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "make_pair".to_string(),
                        args: vec![],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: pair_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("aggregate call should lower");
    let bb0 = &lir.blocks[&Block(0)];
    let call_inst = bb0
        .instructions
        .iter()
        .find(|i| matches!(i.opcode, Opcode::Call { .. }))
        .expect("should have Call instruction");

    assert_eq!(
        lir.value_types.get(&call_inst.results[0]),
        Some(&LirType::Struct(vec![LirType::I64, LirType::I32])),
        "aggregate call result should preserve its full lowered type for ISel"
    );
}

#[test]
fn test_lower_call_no_continuation() {
    // Call with no continuation (diverging function).
    let func = VerifiableFunction {
        name: "diverge".to_string(),
        def_path: "test::diverge".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "abort".to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                },
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("diverging call should lower");
    let bb0 = &lir.blocks[&Block(0)];

    // Should have Call but no Jump (no continuation).
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Call { .. })));
    assert!(!bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Jump { .. })));
}

// -- #828: Cast operation tests --

#[test]
fn test_lower_cast_float_to_signed_int() {
    // fn f2i(a: f64) -> i32 { a as i32 }
    let func = VerifiableFunction {
        name: "f2i".to_string(),
        def_path: "test::f2i".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::f64_ty(), name: Some("a".into()) },
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

    let lir = lower_to_lir(&func).expect("float-to-int cast should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::FcvtToInt { dst_ty: LirType::I32 })),
        "expected FcvtToInt for signed target"
    );
}

#[test]
fn test_lower_cast_float_to_unsigned_int() {
    // fn f2u(a: f64) -> u32 { a as u32 }
    let func = VerifiableFunction {
        name: "f2u".to_string(),
        def_path: "test::f2u".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::f64_ty(), name: Some("a".into()) },
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

    let lir = lower_to_lir(&func).expect("float-to-uint cast should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::FcvtToUint { dst_ty: LirType::I32 })),
        "expected FcvtToUint for unsigned target"
    );
}

#[test]
fn test_lower_cast_signed_int_to_float() {
    // fn i2f(a: i32) -> f64 { a as f64 }
    let func = VerifiableFunction {
        name: "i2f".to_string(),
        def_path: "test::i2f".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::f64_ty(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::f64_ty()),
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

    let lir = lower_to_lir(&func).expect("int-to-float cast should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::FcvtFromInt { src_ty: LirType::I32 })),
        "expected FcvtFromInt for signed source"
    );
}

#[test]
fn test_lower_cast_unsigned_int_to_float() {
    // fn u2f(a: u32) -> f64 { a as f64 }
    let func = VerifiableFunction {
        name: "u2f".to_string(),
        def_path: "test::u2f".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::f64_ty(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::f64_ty()),
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

    let lir = lower_to_lir(&func).expect("uint-to-float cast should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::FcvtFromUint { src_ty: LirType::I32 })),
        "expected FcvtFromUint for unsigned source"
    );
}

#[test]
fn test_lower_cast_float_widen() {
    // fn fext(a: f32) -> f64 { a as f64 }
    let func = VerifiableFunction {
        name: "fext".to_string(),
        def_path: "test::fext".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::f64_ty(), name: None },
                LocalDecl { index: 1, ty: Ty::f32_ty(), name: Some("a".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::f64_ty()),
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

    let lir = lower_to_lir(&func).expect("float widen should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::FPExt)),
        "expected FPExt for f32 -> f64"
    );
}

#[test]
fn test_lower_cast_float_narrow() {
    // fn ftrunc(a: f64) -> f32 { a as f32 }
    let func = VerifiableFunction {
        name: "ftrunc".to_string(),
        def_path: "test::ftrunc".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::f32_ty(), name: None },
                LocalDecl { index: 1, ty: Ty::f64_ty(), name: Some("a".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::f32_ty()),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::f32_ty(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("float narrow should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::FPTrunc)),
        "expected FPTrunc for f64 -> f32"
    );
}

#[test]
fn test_lower_cast_ptr_to_ptr() {
    // Ptr-to-ptr cast: *const i32 -> *const u8
    let func = VerifiableFunction {
        name: "ptr_cast".to_string(),
        def_path: "test::ptr_cast".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::RawPtr { pointee: Box::new(Ty::u8()), mutable: false },
                    name: None,
                },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { pointee: Box::new(Ty::i32()), mutable: false },
                    name: Some("p".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(
                        Operand::Copy(Place::local(1)),
                        Ty::RawPtr { pointee: Box::new(Ty::u8()), mutable: false },
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::RawPtr { pointee: Box::new(Ty::u8()), mutable: false },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("ptr-to-ptr cast should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Ptr-to-ptr is a no-op: no Trunc/Extend/FcvtTo*/FcvtFrom* instructions.
    assert!(
        !bb0.instructions.iter().any(|i| matches!(
            i.opcode,
            Opcode::Trunc { .. }
                | Opcode::Sextend { .. }
                | Opcode::Uextend { .. }
                | Opcode::FcvtToInt { .. }
                | Opcode::FcvtToUint { .. }
                | Opcode::FcvtFromInt { .. }
                | Opcode::FcvtFromUint { .. }
                | Opcode::FPExt
                | Opcode::FPTrunc
        )),
        "ptr-to-ptr cast should produce no conversion instructions"
    );
}

// -- #828: Checked arithmetic tests --

#[test]
fn test_lower_checked_add_uses_signed_overflow_formula() {
    let func = VerifiableFunction {
        name: "checked_add".to_string(),
        def_path: "test::checked_add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
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
            return_ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("checked add should lower");
    let bb0 = &lir.blocks[&Block(0)];

    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Iadd)),
        "should have Iadd for the addition"
    );
    assert!(
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Bxor)).count() >= 2,
        "signed checked add should xor both operands against the wrapped result"
    );
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Band)),
        "signed checked add should intersect the xor sign-change masks"
    );
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Icmp { cond: IntCC::SignedLessThan })),
        "signed checked add should detect overflow via a signed-less-than sign-bit test"
    );
    assert!(
        !bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Isub)),
        "signed checked add must not use the old inverse-sub overflow check"
    );
    let gep_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::StructGep { .. })).count();
    assert!(gep_count >= 2, "should have >= 2 StructGep for tuple fields, got {gep_count}");
    let store_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Store { .. })).count();
    assert!(store_count >= 2, "should have >= 2 Store for tuple fields, got {store_count}");
    assert!(
        bb0.instructions.iter().any(|i| matches!(
            i.opcode,
            Opcode::Load {
                ty: LirType::Struct(ref fields), ..
            } if fields == &vec![LirType::I32, LirType::B1]
        )),
        "checked binary op tuple should load the materialized tuple value for by-value uses"
    );
}

#[test]
fn test_lower_checked_sub_uses_unsigned_underflow_compare() {
    let func = VerifiableFunction {
        name: "checked_sub".to_string(),
        def_path: "test::checked_sub".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Sub,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("checked sub should lower");
    let bb0 = &lir.blocks[&Block(0)];

    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Isub)), "should have Isub");
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Icmp { cond: IntCC::UnsignedLessThan })),
        "unsigned checked sub should detect underflow with lhs < rhs"
    );
    assert!(
        !bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Iadd)),
        "unsigned checked sub must not use the old inverse-add overflow check"
    );
}

#[test]
fn test_lower_checked_mul_uses_widened_compare() {
    let func = VerifiableFunction {
        name: "checked_mul".to_string(),
        def_path: "test::checked_mul".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("checked mul should lower");
    let bb0 = &lir.blocks[&Block(0)];

    assert!(
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Imul)).count() >= 2,
        "checked mul should compute both the wrapped narrow product and a widened product"
    );
    assert!(
        bb0.instructions
            .iter()
            .filter(|i| matches!(
                i.opcode,
                Opcode::Uextend { from_ty: LirType::I32, to_ty: LirType::I64 }
            ))
            .count()
            >= 3,
        "checked mul should widen lhs, rhs, and the wrapped result before comparison"
    );
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Icmp { cond: IntCC::NotEqual })),
        "checked mul should compare the widened wrapped result against the full widened product"
    );
    assert!(
        !bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Udiv)),
        "checked mul must not use the old inverse-division overflow check"
    );
}

#[test]
fn test_lower_checked_bitand_is_unsupported() {
    let func = VerifiableFunction {
        name: "checked_band".to_string(),
        def_path: "test::checked_band".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::BitAnd,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_lir(&func).expect_err("checked bitand must not synthesize false overflow");
    assert!(matches!(err, BridgeError::UnsupportedOp(_)));
    assert!(
        err.to_string().contains("checked BitAnd overflow flag lowering not supported"),
        "unexpected error: {err}"
    );
}

#[test]
fn test_lower_checked_shr_uses_signed_shift_and_range_check() {
    let func = VerifiableFunction {
        name: "checked_shr".to_string(),
        def_path: "test::checked_shr".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("value".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("shift".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Shr,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("checked shr should lower");
    let bb0 = &lir.blocks[&Block(0)];

    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Sshr)),
        "checked signed shr should preserve arithmetic shift semantics from the tuple payload type"
    );
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Icmp { cond: IntCC::UnsignedGreaterThanOrEqual })),
        "checked shift should detect overflow with shift >= bitwidth"
    );
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::I32, imm: 32 })),
        "checked i32 shift should compare against the payload bitwidth"
    );
    assert!(
        !bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Ushr)),
        "checked signed shr must not use the tuple local's unsigned default"
    );
}

#[test]
fn test_lower_checked_i128_mul_is_unsupported() {
    let func = VerifiableFunction {
        name: "checked_mul_i128".to_string(),
        def_path: "test::checked_mul_i128".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::i128(), Ty::Bool]), name: None },
                LocalDecl { index: 1, ty: Ty::i128(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i128(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Tuple(vec![Ty::i128(), Ty::Bool]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_lir(&func).expect_err("checked i128 mul should not silently miscompile");
    assert!(matches!(err, BridgeError::UnsupportedOp(_)));
}

// -- #828: Memory operation tests (Ref, AddressOf, Len) --

#[test]
fn test_lower_ref_produces_stack_addr() {
    // Rvalue::Ref { place, .. } -> StackAddr
    let func = VerifiableFunction {
        name: "take_ref".to_string(),
        def_path: "test::take_ref".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) },
                    name: None,
                },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) },
                    name: None,
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("Ref rvalue should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::StackAddr { .. })),
        "Ref should produce StackAddr"
    );
}

#[test]
fn test_lower_address_of_produces_stack_addr() {
    // Rvalue::AddressOf(mutable, place) -> StackAddr
    let func = VerifiableFunction {
        name: "addr_of".to_string(),
        def_path: "test::addr_of".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::RawPtr { pointee: Box::new(Ty::i32()), mutable: true },
                    name: None,
                },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { pointee: Box::new(Ty::i32()), mutable: true },
                    name: None,
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::AddressOf(true, Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::RawPtr { pointee: Box::new(Ty::i32()), mutable: true },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("AddressOf should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::StackAddr { .. })),
        "AddressOf should produce StackAddr"
    );
}

#[test]
fn test_lower_len_array_produces_iconst() {
    // Rvalue::Len on [i32; 5] -> Iconst(5)
    let func = VerifiableFunction {
        name: "arr_len".to_string(),
        def_path: "test::arr_len".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::i32()), len: 5 },
                    name: Some("arr".into()),
                },
                LocalDecl { index: 2, ty: Ty::u64(), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Len(Place::local(1)),
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

    let lir = lower_to_lir(&func).expect("Len on array should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::I64, imm: 5 })),
        "Len on [_; 5] should emit Iconst(I64, 5)"
    );
}

// -- #828: Aggregate construction tests --

#[test]
fn test_lower_aggregate_tuple() {
    // Aggregate::Tuple with two fields.
    let func = VerifiableFunction {
        name: "make_tuple".to_string(),
        def_path: "test::make_tuple".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Tuple,
                        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("tuple aggregate should lower");
    let bb0 = &lir.blocks[&Block(0)];

    // Should have StackAddr + 2 StructGep + 2 Store.
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::StackAddr { .. })),
        "tuple should allocate stack slot"
    );
    let gep_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::StructGep { .. })).count();
    assert_eq!(gep_count, 2, "expected 2 StructGep for 2-field tuple");
    let store_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Store { .. })).count();
    assert_eq!(store_count, 2, "expected 2 Store for 2-field tuple");
    assert!(
        bb0.instructions.iter().any(|i| matches!(
            i.opcode,
            Opcode::Load {
                ty: LirType::Struct(ref fields), ..
            } if fields == &vec![LirType::I32, LirType::B1]
        )),
        "tuple aggregate should load the materialized tuple value for later by-value uses"
    );
}

#[test]
fn test_lower_aggregate_adt() {
    // Aggregate::Adt with named fields.
    let func = VerifiableFunction {
        name: "make_struct".to_string(),
        def_path: "test::make_struct".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::Adt { adt_kind: None, layout: None,
                        variants: Vec::new(),
                        name: "Point".into(),
                        fields: vec![("x".into(), Ty::i32()), ("y".into(), Ty::i32())],
                        disc_index_safe: false,
                     faithful_enum_repr: None, enum_layout: None, },
                    name: None,
                },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("y".into()) },
                LocalDecl {
                    index: 3,
                    ty: Ty::Adt { adt_kind: None, layout: None,
                        variants: Vec::new(),
                        name: "Point".into(),
                        fields: vec![("x".into(), Ty::i32()), ("y".into(), Ty::i32())],
                        disc_index_safe: false,
                     faithful_enum_repr: None, enum_layout: None, },
                    name: None,
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt { name: "Point".into(), variant: 0, active_field: None },
                        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Adt { adt_kind: None, layout: None,
                variants: Vec::new(),
                name: "Point".into(),
                fields: vec![("x".into(), Ty::i32()), ("y".into(), Ty::i32())],
                disc_index_safe: false,
             faithful_enum_repr: None, enum_layout: None, },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("ADT aggregate should lower");
    let bb0 = &lir.blocks[&Block(0)];

    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::StackAddr { .. })),
        "ADT should allocate stack slot"
    );
    let gep_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::StructGep { .. })).count();
    assert_eq!(gep_count, 2, "expected 2 StructGep for 2-field ADT");
}

#[test]
fn test_lower_aggregate_adt_enum_variant_writes_discriminant() {
    // Trust: #828 — constructing an enum variant (e.g., Some(42)) must
    // write the discriminant tag at field 0 and data at field 1+.
    let option_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "Option".into(),
        fields: vec![("tag".into(), Ty::i64()), ("value".into(), Ty::i32())],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "make_some".to_string(),
        def_path: "test::make_some".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: option_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("val".into()) },
                LocalDecl { index: 2, ty: option_ty.clone(), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "Option".into(),
                            variant: 1, // Some
                            active_field: None,
                        },
                        vec![Operand::Copy(Place::local(1))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: option_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("enum variant aggregate should lower");
    let bb0 = &lir.blocks[&Block(0)];

    // Should have: StackAddr, StructGep(0) for tag, Iconst(1) for variant,
    // Store for tag, StructGep(1) for data, Store for data.
    let gep_indices: Vec<u32> = bb0
        .instructions
        .iter()
        .filter_map(|i| match &i.opcode {
            Opcode::StructGep { field_index, .. } => Some(*field_index),
            _ => None,
        })
        .collect();
    assert_eq!(gep_indices, vec![0, 1], "expected StructGep(0) for tag and StructGep(1) for data");

    // Check that the discriminant value (variant=1) is emitted as Iconst.
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::I64, imm: 1 })),
        "should emit Iconst(I64, 1) for variant discriminant"
    );

    // Should have 2 stores: one for tag, one for data.
    let store_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Store { .. })).count();
    assert_eq!(store_count, 2, "expected 2 Store: 1 tag + 1 data field");
}

#[test]
fn test_lower_aggregate_adt_none_variant_no_data() {
    // Trust: #828 — constructing None (variant 0, no data fields).
    let option_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "Option".into(),
        fields: vec![("tag".into(), Ty::i64()), ("value".into(), Ty::i32())],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "make_none".to_string(),
        def_path: "test::make_none".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: option_ty.clone(), name: None },
                LocalDecl { index: 1, ty: option_ty.clone(), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "Option".into(),
                            variant: 0, // None
                            active_field: None,
                        },
                        vec![], // no data fields
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: option_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("None variant should lower");
    let bb0 = &lir.blocks[&Block(0)];

    // Should have StructGep(0) for tag + Iconst(0) + Store.
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::I64, imm: 0 })),
        "should emit Iconst(I64, 0) for None discriminant"
    );
    let store_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Store { .. })).count();
    assert_eq!(store_count, 1, "expected 1 Store for tag only (no data fields)");
}

#[test]
fn test_lower_fieldless_option_some_fails_closed() {
    let option_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "core::option::Option<i32>".into(),
        fields: vec![],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "make_some_fieldless".to_string(),
        def_path: "test::make_some_fieldless".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: option_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("val".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "core::option::Option".into(),
                            variant: 1,
                            active_field: None,
                        },
                        vec![Operand::Copy(Place::local(1))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: option_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_lir(&func).expect_err("fieldless Option layout must fail closed");
    assert!(matches!(err, BridgeError::UnsupportedType(msg) if msg.contains("fieldless ADT")));
}

#[test]
fn test_lower_checked_div_like_fieldless_option_fails_closed() {
    let option_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "core::option::Option<i32>".into(),
        fields: vec![],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "checked_div_like".to_string(),
        def_path: "test::checked_div_like".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: option_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![
                TrustBlock {
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
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "core::option::Option".into(),
                                variant: 0,
                                active_field: None,
                            },
                            vec![],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "core::option::Option".into(),
                                variant: 1,
                                active_field: None,
                            },
                            vec![Operand::Copy(Place::local(1))],
                        ),
                        span: SourceSpan::default(),
                    }],
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
    };

    let err = lower_to_lir(&func).expect_err("fieldless Option layout must fail closed");
    assert!(matches!(err, BridgeError::UnsupportedType(msg) if msg.contains("fieldless ADT")));
}

#[test]
fn test_emit_object_struct_return_after_aggregate_construction() {
    let pair_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "Pair".into(),
        fields: vec![("left".into(), Ty::i64()), ("right".into(), Ty::i32())],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "make_pair".to_string(),
        def_path: "test::make_pair".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: pair_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("left".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("right".into()) },
            ],
            blocks: vec![TrustBlock {
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
    };

    let lir = lower_to_lir(&func).expect("struct aggregate return should lower");
    let backend = crate::codegen_backend::TrustCgCodegenBackend::host();
    let object = backend.emit_object(&[lir]);
    assert!(
        object.is_ok(),
        "object emission should succeed for struct aggregate return: {object:?}"
    );
}

#[test]
fn test_emit_object_checked_add_overflow_flag_return() {
    let checked_ty = Ty::Tuple(vec![Ty::i32(), Ty::Bool]);
    let func = VerifiableFunction {
        name: "checked_add_overflow_flag".to_string(),
        def_path: "test::checked_add_overflow_flag".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: checked_ty, name: Some("checked".into()) },
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
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 3,
                            projections: vec![Projection::Field(1)],
                        })),
                        span: SourceSpan::default(),
                    },
                ],
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

    let lir = lower_to_lir(&func).expect("checked add overflow flag should lower");
    let backend = crate::codegen_backend::TrustCgCodegenBackend::host();
    let object = backend.emit_object(&[lir]);
    assert!(
        object.is_ok(),
        "object emission should succeed when returning a checked-add overflow flag: {object:?}"
    );
}

#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
fn make_checked_add_overflowing_function() -> VerifiableFunction {
    use trust_types::AssertMessage;

    VerifiableFunction {
        name: "checked_add_overflowing".to_string(),
        def_path: "test::checked_add_overflowing".to_string(),
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
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
fn make_checked_add_overflow_main_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "main".to_string(),
        def_path: "test::main".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("result".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
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
                    },
                },
                TrustBlock {
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

#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
fn parse_hex_address(token: &str) -> Option<u64> {
    let trimmed = token.trim_end_matches(':');
    let trimmed = trimmed.strip_prefix("0x").unwrap_or(trimmed);
    u64::from_str_radix(trimmed, 16).ok()
}

#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
fn main_disassembly_block(disassembly: &str) -> String {
    let mut lines = Vec::new();
    let mut in_main = false;

    for line in disassembly.lines() {
        let trimmed = line.trim();
        if !in_main {
            if trimmed == "_main:" {
                in_main = true;
                lines.push(line.to_string());
            }
            continue;
        }

        if trimmed.ends_with(':') && !trimmed.starts_with("0x") && trimmed != "_main:" {
            break;
        }

        if !trimmed.is_empty() {
            lines.push(line.to_string());
        }
    }

    lines.join("\n")
}

#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
fn aarch64_self_branch_in_main(disassembly: &str) -> Option<String> {
    for line in main_disassembly_block(disassembly).lines() {
        let columns: Vec<_> = line.split_whitespace().collect();
        if columns.len() < 3 || !matches!(columns[1], "b" | "bl") {
            continue;
        }

        if let (Some(site), Some(target)) =
            (parse_hex_address(columns[0]), parse_hex_address(columns[2]))
            && site == target
        {
            return Some(line.to_string());
        }
    }

    None
}

#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
#[test]
fn test_emit_object_checked_add_overflow_linked_main_does_not_self_call() {
    let callee = make_checked_add_overflowing_function();
    let caller = make_checked_add_overflow_main_function();

    let callee_lir = lower_to_lir(&callee).expect("checked-add overflow callee should lower");
    let caller_lir = lower_to_lir(&caller).expect("overflow caller should lower");

    let caller_block = &caller_lir.blocks[&Block(0)];
    let caller_call = caller_block
        .instructions
        .iter()
        .find(
            |inst| matches!(inst.opcode, Opcode::Call { ref name } if name == "checked_add_overflowing"),
        )
        .expect("caller LIR should contain a direct checked_add_overflowing call");
    assert_eq!(
        caller_lir.value_types.get(&caller_call.results[0]),
        Some(&LirType::I32),
        "overflow caller should preserve the checked_add_overflowing result type"
    );

    let panic_block = callee_lir
        .blocks
        .iter()
        .find(|(block, _)| **block != Block(0) && **block != Block(1))
        .map(|(_, block)| block)
        .expect("checked-add overflow callee should synthesize a panic block");
    assert!(
        panic_block
            .instructions
            .iter()
            .any(|inst| matches!(&inst.opcode, Opcode::Call { name } if name == "abort")),
        "checked-add overflow panic block should terminate via abort"
    );

    let backend = crate::codegen_backend::TrustCgCodegenBackend::host();
    let objects =
        backend.emit_objects(&[callee_lir, caller_lir]).expect("overflow objects should emit");

    let temp_dir = tempfile::tempdir().expect("tempdir should succeed");
    let callee_object = temp_dir.path().join("checked_add_overflowing.o");
    let caller_object = temp_dir.path().join("main.o");
    let executable = temp_dir.path().join("overflow-self-call-check");

    for (name, bytes) in objects {
        match name.as_str() {
            "checked_add_overflowing" => {
                std::fs::write(&callee_object, &bytes).expect("callee object write should succeed");
            }
            "main" => {
                std::fs::write(&caller_object, &bytes).expect("caller object write should succeed");
            }
            other => panic!("unexpected emitted object `{other}`"),
        }
    }
    assert!(
        callee_object.is_file() && caller_object.is_file(),
        "checked_add_overflowing and main objects should both materialize before linking"
    );

    let link = std::process::Command::new("cc")
        .arg(&caller_object)
        .arg(&callee_object)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("native linker should run");
    assert!(
        link.status.success(),
        "native link should succeed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&link.stdout),
        String::from_utf8_lossy(&link.stderr)
    );

    let disassembly = std::process::Command::new("otool")
        .arg("-tvV")
        .arg(&executable)
        .output()
        .expect("otool should run on linked executable");
    assert!(
        disassembly.status.success(),
        "otool should succeed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&disassembly.stdout),
        String::from_utf8_lossy(&disassembly.stderr)
    );

    let disassembly_stdout = String::from_utf8_lossy(&disassembly.stdout);
    let main_disassembly = main_disassembly_block(&disassembly_stdout);
    assert!(
        !main_disassembly.is_empty(),
        "linked executable should contain _main disassembly\n{}",
        disassembly_stdout
    );

    let self_branch = aarch64_self_branch_in_main(&disassembly_stdout);
    assert!(
        self_branch.is_none(),
        "bridge lowering kept a direct checked_add_overflowing call and an abort panic block, but linked _main still self-branches: {self_branch:?}\n_main disassembly:\n{main_disassembly}"
    );
}

#[test]
fn test_lower_drop_non_copy_adt_requires_resolved_drop_glue() {
    let string_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "String".into(),
        fields: vec![
            ("ptr".into(), Ty::i64()),
            ("len".into(), Ty::i64()),
            ("cap".into(), Ty::i64()),
        ],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "drop_string".to_string(),
        def_path: "test::drop_string".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: string_ty, name: Some("s".into()) },
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
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let error = lower_to_lir(&func)
        .expect_err("non-Copy drop must not use a fabricated debug-formatted symbol");
    assert!(matches!(
        error,
        BridgeError::UnsupportedOp(message)
            if message.contains("exact monomorphized drop-glue symbol")
                && message.contains("TrustIr carries neither")
    ));
}

#[test]
fn test_lower_drop_copy_type_no_call() {
    // Trust: #828 — dropping a Copy type should NOT emit drop_in_place.
    let func = VerifiableFunction {
        name: "drop_int".to_string(),
        def_path: "test::drop_int".to_string(),
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
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(1),
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

    let lir = lower_to_lir(&func).expect("drop of Copy type should lower");
    let bb0 = &lir.blocks[&Block(0)];

    // Should NOT emit a Call instruction — Copy types have no drop glue.
    let has_call = bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Call { .. }));
    assert!(!has_call, "Copy type should not emit drop_in_place");

    // Should still jump to continuation.
    let has_jump =
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Jump { dest: Block(1) }));
    assert!(has_jump, "should jump to target block even for Copy drop");
}

#[test]
fn test_lower_drop_immutable_ref_no_call() {
    // Trust: #828 — immutable references are Copy, so no drop_in_place.
    let func = VerifiableFunction {
        name: "drop_ref".to_string(),
        def_path: "test::drop_ref".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) },
                    name: Some("r".into()),
                },
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
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("drop of &T should lower");
    let bb0 = &lir.blocks[&Block(0)];

    let has_call = bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Call { .. }));
    assert!(!has_call, "&T is Copy — should not emit drop_in_place");
}

// -- Binary round-trip tests (lower_to_lir -> lift_from_lir) --

#[test]
fn test_binary_roundtrip_simple_return() {
    // fn const_fn() -> i32 { 42 }
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

    let lir = lower_to_lir(&func).expect("should lower");
    let lifted = lift_from_lir(&lir).expect("should lift back");

    assert_eq!(lifted.body.return_ty, Ty::i32());
    assert_eq!(lifted.body.arg_count, 0);
    assert_eq!(lifted.body.blocks.len(), 1);
    assert!(
        matches!(lifted.body.blocks[0].terminator, Terminator::Return),
        "expected Return terminator after round-trip"
    );
}

#[test]
fn test_binary_roundtrip_arithmetic() {
    let func = make_add_function();
    let lir = lower_to_lir(&func).expect("should lower");
    let lifted = lift_from_lir(&lir).expect("should lift back");

    assert_eq!(lifted.body.return_ty, Ty::i32());
    assert_eq!(lifted.body.arg_count, 2);
    assert_eq!(lifted.body.blocks.len(), 1);
    // The lifted body should contain a BinaryOp(Add, ..) assignment.
    let has_add = lifted.body.blocks[0]
        .stmts
        .iter()
        .any(|s| matches!(s, Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Add, ..), .. }));
    assert!(has_add, "round-trip should preserve Add binary op");
}

#[test]
fn test_binary_roundtrip_float_comparison() {
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

    let lir = lower_to_lir(&func).expect("should lower");
    let lifted = lift_from_lir(&lir).expect("should lift back");

    let has_lt = lifted.body.blocks[0]
        .stmts
        .iter()
        .any(|s| matches!(s, Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Lt, ..), .. }));
    assert!(has_lt, "round-trip should preserve float Lt binary op");
}

#[test]
fn test_binary_roundtrip_branch() {
    // fn branch_fn(cond: bool) -> () { if cond { } else { } }
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

    let lir = lower_to_lir(&func).expect("should lower");
    let lifted = lift_from_lir(&lir).expect("should lift back");

    // May have extra panic block from lowering.
    assert!(
        lifted.body.blocks.len() >= 3,
        "expected at least 3 blocks, got {}",
        lifted.body.blocks.len()
    );
    assert_eq!(lifted.body.arg_count, 1);
    // At least one block should have a SwitchInt terminator.
    let has_switch =
        lifted.body.blocks.iter().any(|bb| matches!(bb.terminator, Terminator::SwitchInt { .. }));
    assert!(has_switch, "round-trip should preserve SwitchInt terminator");
}

#[test]
fn test_binary_roundtrip_preserves_types() {
    // fn sum64(a: i64, b: i64) -> i64 { a + b }
    let func = VerifiableFunction {
        name: "sum64".to_string(),
        def_path: "test::sum64".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i64(), name: Some("b".into()) },
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
            return_ty: Ty::i64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("should lower");
    let lifted = lift_from_lir(&lir).expect("should lift back");

    assert!(
        matches!(lifted.body.return_ty, Ty::Int { width: 64, .. }),
        "return type should be i64, got {:?}",
        lifted.body.return_ty
    );
    assert_eq!(lifted.body.arg_count, 2);
    // Args (locals[1] and locals[2]) should have width-64 integer types.
    assert!(
        matches!(lifted.body.locals[1].ty, Ty::Int { width: 64, .. }),
        "arg1 type should be i64, got {:?}",
        lifted.body.locals[1].ty
    );
    assert!(
        matches!(lifted.body.locals[2].ty, Ty::Int { width: 64, .. }),
        "arg2 type should be i64, got {:?}",
        lifted.body.locals[2].ty
    );
}

#[test]
fn test_binary_roundtrip_multi_block() {
    // fn multi(a: i64, b: i64) -> i64 { let sum = a + b; sum / 2 }
    // bb0: sum = a + b; goto bb1
    // bb1: _0 = sum / 2; return
    let func = VerifiableFunction {
        name: "multi".to_string(),
        def_path: "test::multi".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::i64(), name: None },
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
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(3)),
                            Operand::Constant(ConstValue::Int(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::i64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("should lower");
    let lifted = lift_from_lir(&lir).expect("should lift back");

    assert_eq!(lifted.body.blocks.len(), 2, "expected 2 blocks after round-trip");
    // Check block IDs cover 0 and 1.
    let block_ids: Vec<usize> = lifted.body.blocks.iter().map(|bb| bb.id.0).collect();
    assert!(block_ids.contains(&0), "should have block 0");
    assert!(block_ids.contains(&1), "should have block 1");
    // One block should have Goto, the other Return.
    let has_goto = lifted.body.blocks.iter().any(|bb| matches!(bb.terminator, Terminator::Goto(_)));
    let has_return =
        lifted.body.blocks.iter().any(|bb| matches!(bb.terminator, Terminator::Return));
    assert!(has_goto, "round-trip should preserve Goto terminator");
    assert!(has_return, "round-trip should preserve Return terminator");
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

// -- Tests for functions with many basic blocks (10+) --

/// Build a function with `n` blocks in a linear chain: bb0 -> bb1 -> ... -> return.
fn make_chain(n: usize) -> VerifiableFunction {
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::i32(), name: None }, // return
        LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
    ];
    for i in 0..n {
        locals.push(LocalDecl { index: 2 + i, ty: Ty::i32(), name: None });
    }

    let mut blocks = Vec::with_capacity(n);
    for i in 0..n {
        let assign_target = if i == n - 1 { 0 } else { 2 + i };
        let stmt = Statement::Assign {
            place: Place::local(assign_target),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::default(),
        };
        let term = if i == n - 1 { Terminator::Return } else { Terminator::Goto(BlockId(i + 1)) };
        blocks.push(TrustBlock { id: BlockId(i), stmts: vec![stmt], terminator: term });
    }

    VerifiableFunction {
        name: format!("chain_{n}"),
        def_path: format!("test::chain_{n}"),
        span: SourceSpan::default(),
        body: VerifiableBody { locals, blocks, arg_count: 1, return_ty: Ty::i32() },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_lower_chain_10_blocks() {
    let func = make_chain(10);
    let lir = lower_to_lir(&func).expect("should lower 10-block chain");
    assert!(lir.blocks.len() >= 10, "expected >= 10 blocks, got {}", lir.blocks.len());
    // Every block except the last should have a Jump terminator.
    for i in 0..9u32 {
        let bb = &lir.blocks[&Block(i)];
        let has_jump = bb
            .instructions
            .iter()
            .any(|inst| matches!(inst.opcode, Opcode::Jump { dest } if dest == Block(i + 1)));
        assert!(has_jump, "block {i} should jump to block {}", i + 1);
    }
}

#[test]
fn test_lower_chain_15_blocks() {
    let func = make_chain(15);
    let lir = lower_to_lir(&func).expect("should lower 15-block chain");
    assert!(lir.blocks.len() >= 15);
    // Last block should have a Return.
    let last = &lir.blocks[&Block(14)];
    assert!(
        last.instructions.iter().any(|i| matches!(i.opcode, Opcode::Return)),
        "last block should have Return"
    );
}

// -- Complex control flow: nested SwitchInt + loops --

#[test]
fn test_lower_switch_multi_way_produces_switch_opcode() {
    // match x { 0 => .., 1 => .., 2 => .., _ => .. }
    let func = VerifiableFunction {
        name: "multi_switch".to_string(),
        def_path: "test::multi_switch".to_string(),
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
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1)), (1, BlockId(2)), (2, BlockId(3))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(20))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(30))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                TrustBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
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
    };

    let lir = lower_to_lir(&func).expect("should lower multi-way switch");
    let entry = &lir.blocks[&lir.entry_block];
    // Multi-way SwitchInt (3 targets) produces an Opcode::Switch, not Brif.
    let has_switch = entry
        .instructions
        .iter()
        .any(|i| matches!(&i.opcode, Opcode::Switch { cases, .. } if cases.len() == 3));
    assert!(has_switch, "expected Switch opcode with 3 cases in entry block");
}

#[test]
fn test_lower_loop_back_edge() {
    // bb0: switchint x == 0 -> bb2, else bb1
    // bb1: x = x - 1; goto bb0  (back-edge)
    // bb2: return x
    let func = VerifiableFunction {
        name: "loop_back".to_string(),
        def_path: "test::loop_back".to_string(),
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
                TrustBlock {
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
    };

    let lir = lower_to_lir(&func).expect("should lower loop with back-edge");
    assert!(lir.blocks.len() >= 3);

    // Block 1 should jump back to block 0 (back-edge).
    let bb1 = &lir.blocks[&Block(1)];
    let has_back_jump = bb1
        .instructions
        .iter()
        .any(|i| matches!(i.opcode, Opcode::Jump { dest } if dest == Block(0)));
    assert!(has_back_jump, "bb1 should have a jump back to bb0 (back-edge)");
}

// -- Error cases --

#[test]
fn test_lower_unsupported_type_error() {
    // Use Bv(7) which is unsupported.
    let func = VerifiableFunction {
        name: "bad_type".to_string(),
        def_path: "test::bad_type".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Bv(7), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Bv(7),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_lir(&func).unwrap_err();
    assert!(matches!(err, BridgeError::UnsupportedType(_)));
    assert!(err.to_string().contains("Bv(7)"));
}

#[test]
fn test_lower_empty_function_zero_args() {
    // fn empty() -> () { }
    let func = VerifiableFunction {
        name: "empty".to_string(),
        def_path: "test::empty".to_string(),
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

    let lir = lower_to_lir(&func).expect("should lower empty function");
    assert_eq!(lir.name, "empty");
    assert_eq!(lir.signature.params.len(), 0);
    assert_eq!(lir.blocks.len(), 1);
    // Entry block should have at least a Return instruction.
    let entry = &lir.blocks[&lir.entry_block];
    assert!(
        entry.instructions.iter().any(|i| matches!(i.opcode, Opcode::Return)),
        "empty function should have Return"
    );
}

#[test]
fn test_lower_unreachable_terminator() {
    // fn diverge() -> ! { unreachable }
    let func = VerifiableFunction {
        name: "diverge".to_string(),
        def_path: "test::diverge".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Unreachable,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("should lower unreachable");
    let entry = &lir.blocks[&lir.entry_block];
    assert!(
        entry
            .instructions
            .iter()
            .any(|i| matches!(&i.opcode, Opcode::Call { name } if name == "abort")),
        "Unreachable should lower to an abort call"
    );
    assert!(
        !entry.instructions.iter().any(|i| matches!(i.opcode, Opcode::Return)),
        "Unreachable should not fabricate a Return"
    );
}

#[test]
fn test_lower_non_void_unreachable_lowers_to_abort_call() {
    let func = VerifiableFunction {
        name: "diverge_i32".to_string(),
        def_path: "test::diverge_i32".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Unreachable,
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("non-void unreachable should lower");
    let entry = &lir.blocks[&lir.entry_block];
    let abort_inst = entry.instructions.last().expect("unreachable block should end in abort");
    assert!(matches!(&abort_inst.opcode, Opcode::Call { name } if name == "abort"));
    assert!(
        abort_inst.args.is_empty() && abort_inst.results.is_empty(),
        "abort call should not carry fake return operands or results"
    );
    assert!(
        !entry.instructions.iter().any(|i| matches!(i.opcode, Opcode::Return)),
        "non-void unreachable should not fabricate a Return"
    );
}

// -- Round-trip tests for complex CFGs --

#[test]
fn test_roundtrip_multi_way_switch() {
    // Build a 4-arm switch and verify roundtrip preserves block count.
    let func = VerifiableFunction {
        name: "switch_rt".to_string(),
        def_path: "test::switch_rt".to_string(),
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
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(20))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(30))),
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
    };

    let lir = lower_to_lir(&func).expect("should lower");
    let lifted = lift_from_lir(&lir).expect("should lift back");

    // Should preserve at least the original 4 blocks.
    assert!(
        lifted.body.blocks.len() >= 4,
        "expected >= 4 blocks after roundtrip, got {}",
        lifted.body.blocks.len()
    );
    // At least one block should have a SwitchInt with 2+ targets.
    let has_multi_switch = lifted.body.blocks.iter().any(
        |bb| matches!(&bb.terminator, Terminator::SwitchInt { targets, .. } if targets.len() >= 2),
    );
    assert!(has_multi_switch, "roundtrip should preserve multi-way SwitchInt");
}

#[test]
fn test_roundtrip_chain_function() {
    let func = make_chain(5);
    let lir = lower_to_lir(&func).expect("should lower 5-block chain");
    let lifted = lift_from_lir(&lir).expect("should lift back");

    assert!(
        lifted.body.blocks.len() >= 5,
        "expected >= 5 blocks after roundtrip, got {}",
        lifted.body.blocks.len()
    );
    // Should have at least 4 Goto terminators (bb0->bb1, ..., bb3->bb4).
    let goto_count =
        lifted.body.blocks.iter().filter(|bb| matches!(bb.terminator, Terminator::Goto(_))).count();
    assert!(goto_count >= 4, "expected >= 4 Goto terminators in 5-block chain, got {}", goto_count);
}

// -- #828: Discriminant lowering tests --

#[test]
fn test_lower_discriminant_produces_struct_gep_load() {
    // Trust: Discriminant extracts the tag (field 0) from an ADT.
    let func = VerifiableFunction {
        name: "get_discr".to_string(),
        def_path: "test::get_discr".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Adt { adt_kind: None, layout: None,
                        variants: Vec::new(),
                        name: "Option".into(),
                        fields: vec![("tag".into(), Ty::i64()), ("value".into(), Ty::i32())],
                        disc_index_safe: false,
                     faithful_enum_repr: None, enum_layout: None, },
                    name: Some("opt".into()),
                },
                LocalDecl { index: 2, ty: Ty::i64(), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
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

    let lir = lower_to_lir(&func).expect("Discriminant should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should have StructGep(field_index: 0) + Load(I64).
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::StructGep { field_index: 0, .. })),
        "Discriminant should emit StructGep(0)"
    );
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Load { ty: LirType::I64, .. })),
        "Discriminant should emit Load(I64)"
    );
}

#[test]
fn test_lower_discriminant_fieldless_option_fails_closed() {
    let option_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "core::option::Option<i32>".into(),
        fields: vec![],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "get_fieldless_discr".to_string(),
        def_path: "test::get_fieldless_discr".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: option_ty, name: Some("opt".into()) },
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
            return_ty: Ty::i64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_lir(&func).expect_err("fieldless Option layout must fail closed");
    assert!(matches!(err, BridgeError::UnsupportedType(msg) if msg.contains("fieldless ADT")));
}

#[test]
fn test_lower_set_discriminant_explicit_tag_writes_tag_field() {
    let enum_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "Tagged".into(),
        fields: vec![("payload".into(), Ty::i32()), ("__discriminant".into(), Ty::u8())],
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
                    variant_index: 2,
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

    let lir = lower_to_lir(&func).expect("explicit-tag SetDiscriminant should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::StructGep { field_index: 1, .. })),
        "SetDiscriminant should address the explicit tag field"
    );
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::I8, imm: 2 })),
        "SetDiscriminant should materialize the variant index with the tag field type"
    );
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Store { .. })),
        "SetDiscriminant should store the tag value"
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

    let err = lower_to_lir(&func).expect_err("untagged SetDiscriminant must fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedOp(msg) if msg.contains("no explicit discriminant/tag field"))
    );
}

// -- #828: Repeat lowering tests --

#[test]
fn test_lower_repeat_array() {
    // Trust: [0i32; 3] should allocate a stack slot and store 3 copies.
    let func = VerifiableFunction {
        name: "repeat_arr".to_string(),
        def_path: "test::repeat_arr".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::Array { elem: Box::new(Ty::i32()), len: 3 },
                    name: None,
                },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::i32()), len: 3 },
                    name: None,
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Repeat(Operand::Constant(ConstValue::Int(0)), 3),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Array { elem: Box::new(Ty::i32()), len: 3 },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("Repeat should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should have StackAddr + 3 Store instructions (one per element).
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::StackAddr { .. })),
        "Repeat should allocate stack slot"
    );
    let store_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Store { .. })).count();
    assert_eq!(store_count, 3, "Repeat [_; 3] should emit 3 Store instructions");
}

// -- #828: CopyForDeref lowering tests --

#[test]
fn test_lower_copy_for_deref() {
    // Trust: CopyForDeref is semantically equivalent to Use(Copy(place)).
    let func = VerifiableFunction {
        name: "copy_deref".to_string(),
        def_path: "test::copy_deref".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::CopyForDeref(Place::local(1)),
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

    let lir = lower_to_lir(&func).expect("CopyForDeref should lower");
    // Should succeed without error — CopyForDeref is a simple value copy.
    let bb0 = &lir.blocks[&Block(0)];
    assert!(matches!(bb0.instructions.last().unwrap().opcode, Opcode::Return));
}

// -- #828: Diverging call (target=None) --

#[test]
fn test_lower_diverging_call_no_target() {
    // Trust: A call with target=None (e.g., calling panic!) should not emit a Jump.
    let func = VerifiableFunction {
        name: "diverge".to_string(),
        def_path: "test::diverge".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Never, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "panic".to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                },
            }],
            arg_count: 0,
            return_ty: Ty::Never,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("diverging call should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should have Call but no Jump after it.
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Call { .. })),
        "should have Call instruction"
    );
    assert!(
        !bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Jump { .. })),
        "diverging call should NOT emit Jump"
    );
}

// -- #828: Len on slice --

#[test]
fn test_lower_len_slice_produces_struct_gep_load() {
    // Trust: Len on a slice loads field 1 of the fat pointer { ptr, len }.
    let func = VerifiableFunction {
        name: "slice_len".to_string(),
        def_path: "test::slice_len".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Slice { elem: Box::new(Ty::i32()) },
                    name: Some("s".into()),
                },
                LocalDecl { index: 2, ty: Ty::u64(), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Len(Place::local(1)),
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

    let lir = lower_to_lir(&func).expect("Len on slice should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should produce StructGep(field_index: 1) to access the length field.
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::StructGep { field_index: 1, .. })),
        "Len on slice should emit StructGep(1) for length field"
    );
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Load { ty: LirType::I64, .. })),
        "Len on slice should emit Load(I64)"
    );
}

// -- #828: Aggregate::Array --

#[test]
fn test_lower_aggregate_array() {
    // Trust: Aggregate::Array stores each element via StructGep + Store.
    let func = VerifiableFunction {
        name: "make_array".to_string(),
        def_path: "test::make_array".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::Array { elem: Box::new(Ty::i32()), len: 3 },
                    name: None,
                },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: Some("c".into()) },
                LocalDecl {
                    index: 4,
                    ty: Ty::Array { elem: Box::new(Ty::i32()), len: 3 },
                    name: None,
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(4),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Array,
                        vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(3)),
                        ],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 3,
            return_ty: Ty::Array { elem: Box::new(Ty::i32()), len: 3 },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("Array aggregate should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::StackAddr { .. })),
        "Array should allocate stack slot"
    );
    let store_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Store { .. })).count();
    assert_eq!(store_count, 3, "Array [a, b, c] should emit 3 Store instructions");
}

// -- #828: Assert terminator --

#[test]
fn test_lower_assert_terminator_expected_true() {
    // Trust: Assert with expected=true branches to target on success, panic on failure.
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

    let lir = lower_to_lir(&func).expect("Assert should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should emit Brif with then_dest = Block(1) (target).
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Brif { then_dest: Block(1), .. })),
        "Assert expected=true should branch to target on true"
    );
    // Should have allocated a panic block.
    assert!(
        lir.blocks.len() >= 3,
        "Assert should create a panic block (expected >= 3 blocks, got {})",
        lir.blocks.len()
    );
}

#[test]
fn test_lower_assert_terminator_expected_false() {
    // Trust: Assert with expected=false branches to panic on true, target on false.
    use trust_types::AssertMessage;
    let func = VerifiableFunction {
        name: "assert_neg_fn".to_string(),
        def_path: "test::assert_neg_fn".to_string(),
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
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
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

    let lir = lower_to_lir(&func).expect("Assert expected=false should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should emit Brif with else_dest = Block(1) (target on false).
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Brif { else_dest: Block(1), .. })),
        "Assert expected=false should branch to target on false"
    );
}

#[test]
fn test_lower_non_void_assert_panic_block_lowers_to_abort_call() {
    use trust_types::AssertMessage;

    let func = VerifiableFunction {
        name: "assert_i32_fn".to_string(),
        def_path: "test::assert_i32_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("cond".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("x".into()) },
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
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("non-void assert should lower");
    let panic_block = lir
        .blocks
        .iter()
        .find(|(block, _)| **block != Block(0) && **block != Block(1))
        .map(|(_, block)| block)
        .expect("assert lowering should synthesize a panic block");
    let abort_inst =
        panic_block.instructions.last().expect("panic block should contain an abort call");

    assert!(matches!(&abort_inst.opcode, Opcode::Call { name } if name == "abort"));
    assert!(
        abort_inst.args.is_empty() && abort_inst.results.is_empty(),
        "panic block abort call should not carry fake return operands or results"
    );
    assert!(
        !panic_block.instructions.iter().any(|i| matches!(i.opcode, Opcode::Return)),
        "non-void panic block should not fabricate a Return"
    );
}

// -- #828: Drop terminator --

#[test]
fn test_lower_drop_terminator() {
    // Trust: Drop is a no-op (for scalar types), just jumps to target.
    let func = VerifiableFunction {
        name: "drop_fn".to_string(),
        def_path: "test::drop_fn".to_string(),
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
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(1),
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

    let lir = lower_to_lir(&func).expect("Drop should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Drop emits a Jump to the target block.
    assert!(matches!(bb0.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(1) }));
}

// -- #828: Call with arguments --

#[test]
fn test_lower_call_with_args_and_continuation() {
    // Trust: Call with arguments and a continuation block.
    let func = VerifiableFunction {
        name: "call_with_args".to_string(),
        def_path: "test::call_with_args".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: None },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "add".to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
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
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("Call with args should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should have Call with 2 args and a Jump to Block(1).
    let call_inst = bb0
        .instructions
        .iter()
        .find(|i| matches!(i.opcode, Opcode::Call { .. }))
        .expect("should have Call instruction");
    assert_eq!(call_inst.args.len(), 2, "Call should have 2 args");
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Jump { dest: Block(1) })),
        "Call with continuation should emit Jump to Block(1)"
    );
}

// -- #828: Unary Neg --

#[test]
fn test_lower_unary_neg() {
    // Trust: UnaryOp(Neg, x) -> Ineg instruction.
    let func = VerifiableFunction {
        name: "neg_fn".to_string(),
        def_path: "test::neg_fn".to_string(),
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
                    rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
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

    let lir = lower_to_lir(&func).expect("Neg should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Ineg)),
        "UnaryOp(Neg) should produce Ineg instruction"
    );
}

// =========================================================================
// #828: Edge case tests — error handling and malformed MIR
// =========================================================================

#[test]
fn test_lower_empty_body_returns_error() {
    // Trust: A function with zero basic blocks is malformed MIR.
    let func = VerifiableFunction {
        name: "empty_fn".to_string(),
        def_path: "test::empty_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_lir(&func).unwrap_err();
    assert!(
        matches!(err, BridgeError::EmptyBody),
        "Empty body should produce EmptyBody error, got: {err:?}"
    );
}

#[test]
fn test_lower_return_only_function() {
    // Trust: Minimal valid function — single block with only a Return.
    let func = VerifiableFunction {
        name: "return_only".to_string(),
        def_path: "test::return_only".to_string(),
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

    let lir = lower_to_lir(&func).expect("Return-only fn should lower");
    assert_eq!(lir.blocks.len(), 1);
    assert_eq!(lir.entry_block, Block(0));
    let bb0 = &lir.blocks[&Block(0)];
    assert_eq!(bb0.instructions.len(), 1);
    assert!(matches!(bb0.instructions[0].opcode, Opcode::Return));
}

#[test]
fn test_lower_duplicate_block_ids_returns_error() {
    // Trust: Duplicate block IDs in a function body are invalid MIR.
    let func = VerifiableFunction {
        name: "dup_blocks".to_string(),
        def_path: "test::dup_blocks".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                TrustBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return },
                TrustBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_lir(&func).unwrap_err();
    assert!(
        matches!(err, BridgeError::InvalidMir(_)),
        "Duplicate block IDs should produce InvalidMir error, got: {err:?}"
    );
}

#[test]
fn test_lower_switch_multiple_targets_same_destination() {
    // Trust: SwitchInt where multiple values route to the same block.
    let func = VerifiableFunction {
        name: "switch_same_dest".to_string(),
        def_path: "test::switch_same_dest".to_string(),
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
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1)), (2, BlockId(1)), (3, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
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
    };

    let lir = lower_to_lir(&func).expect("Switch with same dest should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Multi-way switch: should emit a Switch instruction (not Brif).
    let switch_inst = bb0
        .instructions
        .iter()
        .find(|i| matches!(i.opcode, Opcode::Switch { .. }))
        .expect("should have Switch instruction for multi-target");
    if let Opcode::Switch { cases, default } = &switch_inst.opcode {
        assert_eq!(cases.len(), 3, "Switch should have 3 cases");
        // All cases go to Block(1)
        for (_, dest) in cases {
            assert_eq!(*dest, Block(1));
        }
        assert_eq!(*default, Block(2));
    } else {
        panic!("Expected Switch opcode");
    }
}

#[test]
fn test_lower_nested_aggregate_struct_containing_tuple() {
    // Trust: Nested aggregate — ADT containing a Tuple field.
    use trust_types::AggregateKind;

    let inner_tuple_ty = Ty::Tuple(vec![Ty::i32(), Ty::Bool]);
    let outer_adt_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "Wrapper".to_string(),
        fields: vec![
            ("inner".to_string(), inner_tuple_ty.clone()),
            ("extra".to_string(), Ty::i64()),
        ],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };

    let func = VerifiableFunction {
        name: "nested_agg".to_string(),
        def_path: "test::nested_agg".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: outer_adt_ty.clone(), name: None },
                LocalDecl { index: 1, ty: inner_tuple_ty.clone(), name: Some("t".into()) },
                LocalDecl { index: 2, ty: Ty::i64(), name: Some("e".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "Wrapper".to_string(),
                            variant: 0,
                            active_field: None,
                        },
                        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: outer_adt_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("Nested aggregate should lower");
    assert_eq!(lir.blocks.len(), 1);
    // Verify the return type is a nested struct.
    assert_eq!(
        lir.signature.returns,
        vec![LirType::Struct(
            vec![LirType::Struct(vec![LirType::I32, LirType::B1]), LirType::I64,]
        )]
    );
}

#[test]
fn test_lower_large_signed_constants_fail_instead_of_truncating() {
    // Trust: Large constant values (u128 max, i128 extremes).
    let func = VerifiableFunction {
        name: "large_consts".to_string(),
        def_path: "test::large_consts".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: None },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(i128::MAX))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(i128::MIN))),
                        span: SourceSpan::default(),
                    },
                ],
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

    let error = lower_to_lir(&func)
        .expect_err("i128 values outside the LIR immediate domain must not be truncated");
    assert!(error.to_string().contains("exceeds the exact 64-bit Iconst domain"));
}

#[test]
fn test_lower_function_with_many_locals_stress() {
    // Trust: Stress test — function with 100 locals.
    let num_locals = 100;
    let mut locals = Vec::with_capacity(num_locals);
    // Local 0 = return slot
    locals.push(LocalDecl { index: 0, ty: Ty::i32(), name: None });
    // Local 1 = argument
    locals.push(LocalDecl { index: 1, ty: Ty::i32(), name: Some("arg".into()) });
    // Locals 2..100 = temps
    for i in 2..num_locals {
        locals.push(LocalDecl { index: i, ty: Ty::i32(), name: Some(format!("tmp_{i}")) });
    }

    // Build a chain: _2 = _1 + _1, _3 = _2 + _2, ..., _0 = _99 + _99
    let mut stmts = Vec::with_capacity(num_locals - 1);
    for i in 2..(num_locals - 1) {
        stmts.push(Statement::Assign {
            place: Place::local(i),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(i - 1)),
                Operand::Copy(Place::local(i - 1)),
            ),
            span: SourceSpan::default(),
        });
    }
    stmts.push(Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(num_locals - 2)),
            Operand::Copy(Place::local(num_locals - 2)),
        ),
        span: SourceSpan::default(),
    });

    let func = VerifiableFunction {
        name: "many_locals".to_string(),
        def_path: "test::many_locals".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![TrustBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("Many-locals function should lower");
    assert_eq!(lir.blocks.len(), 1);
    let bb0 = &lir.blocks[&Block(0)];
    // Each BinaryOp generates an Iadd instruction.
    let iadd_count = bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Iadd)).count();
    assert_eq!(
        iadd_count,
        num_locals - 2,
        "Should have {expected} Iadd instructions for {n} temp locals",
        expected = num_locals - 2,
        n = num_locals - 2
    );
}

#[test]
fn test_lower_missing_arg_local_returns_error() {
    // Trust: If arg_count says 2 but local index 2 is missing, error.
    let func = VerifiableFunction {
        name: "missing_arg".to_string(),
        def_path: "test::missing_arg".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                // Missing local index 2!
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_lir(&func).unwrap_err();
    assert!(
        matches!(err, BridgeError::MissingLocal(2)),
        "Missing arg local should produce MissingLocal(2), got: {err:?}"
    );
}

#[test]
fn test_lower_switch_single_target_emits_brif() {
    // Trust: SwitchInt with single target should emit Brif (binary branch),
    // not Switch.
    let func = VerifiableFunction {
        name: "switch_single".to_string(),
        def_path: "test::switch_single".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
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
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
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
    };

    let lir = lower_to_lir(&func).expect("Single-target switch should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should use Brif, not Switch.
    assert!(
        bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Brif { .. })),
        "Single-target SwitchInt should emit Brif"
    );
    assert!(
        !bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Switch { .. })),
        "Single-target SwitchInt should NOT emit Switch"
    );
}

#[test]
fn test_lower_u128_constant_fails_instead_of_truncating() {
    // Trust: LIR Iconst has only a signed 64-bit immediate. A u128 value cannot
    // be represented by silently retaining its low bits.
    let func = VerifiableFunction {
        name: "uint_const".to_string(),
        def_path: "test::uint_const".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::u64(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(u128::MAX, 128))),
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

    let error = lower_to_lir(&func)
        .expect_err("u128 constants outside the LIR immediate domain must not be truncated");
    assert!(error.to_string().contains("u128 constants cannot be represented"));
}

#[test]
fn test_lower_nop_statements_ignored() {
    // Trust: Nop statements should produce no instructions.
    let func = VerifiableFunction {
        name: "nop_fn".to_string(),
        def_path: "test::nop_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Nop, Statement::Nop, Statement::Nop],
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

    let lir = lower_to_lir(&func).expect("Nop fn should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Only the Return instruction should be present.
    assert_eq!(bb0.instructions.len(), 1, "Nop statements should not produce instructions");
    assert!(matches!(bb0.instructions[0].opcode, Opcode::Return));
}

#[test]
fn test_map_type_nested_ref_to_tuple() {
    // Trust: Reference to a tuple should still be I64 (pointer-sized).
    let ty = Ty::Ref { mutable: false, inner: Box::new(Ty::Tuple(vec![Ty::i32(), Ty::i64()])) };
    assert_eq!(map_type(&ty).unwrap(), LirType::I64);
}

#[test]
fn test_map_type_deeply_nested_adt() {
    // Trust: ADT containing another ADT should produce nested Struct.
    let inner = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "Inner".to_string(),
        fields: vec![("x".to_string(), Ty::i32())],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let outer = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "Outer".to_string(),
        fields: vec![("a".to_string(), inner), ("b".to_string(), Ty::Bool)],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let mapped = map_type(&outer).unwrap();
    assert_eq!(mapped, LirType::Struct(vec![LirType::Struct(vec![LirType::I32]), LirType::B1,]));
}

#[test]
fn test_lower_non_sequential_block_ids() {
    // Trust: Block IDs do not need to be sequential (e.g., bb0, bb5, bb10).
    let func = VerifiableFunction {
        name: "sparse_blocks".to_string(),
        def_path: "test::sparse_blocks".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                TrustBlock {
                    id: BlockId(5),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(10)),
                },
                TrustBlock { id: BlockId(10), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("Sparse block IDs should lower");
    assert_eq!(lir.blocks.len(), 3);
    assert!(lir.blocks.contains_key(&Block(0)));
    assert!(lir.blocks.contains_key(&Block(5)));
    assert!(lir.blocks.contains_key(&Block(10)));
    assert_eq!(lir.entry_block, Block(0));
}

// =========================================================================
// Stress tests: large/complex MIR inputs
// =========================================================================

#[test]
fn test_stress_large_basic_block_50_statements() {
    // A block with 50+ assignment statements should lower correctly.
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::i32(), name: None }, // return slot
        LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) }, // arg
    ];
    let mut stmts = Vec::with_capacity(60);
    // Chain: tmp_i = tmp_(i-1) + 1  for i = 2..62
    for i in 2..62 {
        locals.push(LocalDecl { index: i, ty: Ty::i32(), name: None });
        stmts.push(Statement::Assign {
            place: Place::local(i),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(i - 1)),
                Operand::Constant(ConstValue::Int(1)),
            ),
            span: SourceSpan::default(),
        });
    }
    // Final assign to return slot
    stmts.push(Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(61))),
        span: SourceSpan::default(),
    });

    let func = VerifiableFunction {
        name: "big_block".to_string(),
        def_path: "test::big_block".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![TrustBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("large basic block should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // 60 adds + 60 iconst(1) + 1 assign (Use) + 1 Return = many instructions
    // At minimum we expect at least 62 instructions (60 adds + assign + return)
    assert!(
        bb0.instructions.len() >= 62,
        "expected >= 62 instructions, got {}",
        bb0.instructions.len()
    );
    assert!(matches!(bb0.instructions.last().unwrap().opcode, Opcode::Return));
}

#[test]
fn test_stress_deeply_nested_aggregate_types() {
    // Struct(Struct(Struct(i32))) — 4 levels deep
    let level0 = Ty::i32();
    let level1 = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "L1".to_string(),
        fields: vec![("val".to_string(), level0)],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let level2 = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "L2".to_string(),
        fields: vec![("inner".to_string(), level1.clone())],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let level3 = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "L3".to_string(),
        fields: vec![("deep".to_string(), level2.clone()), ("tag".to_string(), Ty::Bool)],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let level4 = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "L4".to_string(),
        fields: vec![("nested".to_string(), level3), ("count".to_string(), Ty::i64())],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };

    // Verify type mapping produces the right nested structure.
    let lir_ty = map_type(&level4).unwrap();
    let expected = LirType::Struct(vec![
        LirType::Struct(vec![
            LirType::Struct(vec![LirType::Struct(vec![LirType::I32])]),
            LirType::B1,
        ]),
        LirType::I64,
    ]);
    assert_eq!(lir_ty, expected);

    // Also test that a function with this return type can be lowered.
    let func = VerifiableFunction {
        name: "deep_nested".to_string(),
        def_path: "test::deep_nested".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: level4.clone(), name: None },
                LocalDecl { index: 1, ty: level2, name: Some("arg".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: level4,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("deeply nested types should lower");
    assert_eq!(lir.signature.params.len(), 1);
}

#[test]
fn test_stress_function_with_many_parameters() {
    // Function with 25 parameters.
    let mut locals = vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }]; // return
    for i in 1..=25 {
        locals.push(LocalDecl { index: i, ty: Ty::i32(), name: Some(format!("p{i}")) });
    }
    // Sum all params into return slot (chain of adds).
    let mut stmts = Vec::new();
    // tmp26 = p1 + p2
    locals.push(LocalDecl { index: 26, ty: Ty::i32(), name: None });
    stmts.push(Statement::Assign {
        place: Place::local(26),
        rvalue: Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
        span: SourceSpan::default(),
    });
    // tmp_i = tmp_(i-1) + p_(i-24)
    for i in 27..=49 {
        locals.push(LocalDecl { index: i, ty: Ty::i32(), name: None });
        stmts.push(Statement::Assign {
            place: Place::local(i),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(i - 1)),
                Operand::Copy(Place::local(i - 24)),
            ),
            span: SourceSpan::default(),
        });
    }
    stmts.push(Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(49))),
        span: SourceSpan::default(),
    });

    let func = VerifiableFunction {
        name: "many_params".to_string(),
        def_path: "test::many_params".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![TrustBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 25,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("25-param function should lower");
    assert_eq!(lir.signature.params.len(), 25);
    for p in &lir.signature.params {
        assert_eq!(*p, LirType::I32);
    }
}

#[test]
fn test_stress_diamond_control_flow() {
    // Diamond CFG: bb0 branches to bb1/bb2, both jump to bb3.
    let func = VerifiableFunction {
        name: "diamond".to_string(),
        def_path: "test::diamond".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("cond".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: None },
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
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(20))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
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
    };

    let lir = lower_to_lir(&func).expect("diamond CFG should lower");
    assert_eq!(lir.blocks.len(), 4);
    // bb1 and bb2 should both jump to bb3.
    let bb1 = &lir.blocks[&Block(1)];
    assert!(matches!(bb1.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(3) }));
    let bb2 = &lir.blocks[&Block(2)];
    assert!(matches!(bb2.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(3) }));
}

#[test]
fn test_stress_loop_with_multiple_exits() {
    // Loop: bb0 -> bb1 (loop header, branches to bb2 or bb3), bb2 loops back,
    // bb3 is the exit.
    let func = VerifiableFunction {
        name: "multi_exit_loop".to_string(),
        def_path: "test::multi_exit_loop".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: None }, // counter
                LocalDecl { index: 3, ty: Ty::Bool, name: None },  // cond
            ],
            blocks: vec![
                // bb0: entry, init counter = 0, goto loop header
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                // bb1: loop header, check counter < n
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(1, BlockId(2))], // true -> body
                        otherwise: BlockId(3),          // false -> exit
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb2: loop body, increment counter, back to header
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Int(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)), // back-edge
                },
                // bb3: exit, return counter
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
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
    };

    let lir = lower_to_lir(&func).expect("loop with exits should lower");
    assert_eq!(lir.blocks.len(), 4);
    // bb2 should jump back to bb1 (back-edge).
    let bb2 = &lir.blocks[&Block(2)];
    assert!(matches!(bb2.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(1) }));
}

#[test]
fn test_lower_loop_header_uses_block_param_for_goto_back_edge() {
    let func = VerifiableFunction {
        name: "loop_header_param".to_string(),
        def_path: "test::loop_header_param".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: None }, // counter
                LocalDecl { index: 3, ty: Ty::Bool, name: None },  // cond
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Int(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
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
    };

    let lir = lower_to_lir(&func).expect("loop header param should lower");
    let header = &lir.blocks[&Block(1)];
    assert_eq!(header.params.len(), 1, "loop header should get one block param for counter");
    let (header_param, header_param_ty) = &header.params[0];
    let header_param = *header_param;
    assert_eq!(*header_param_ty, LirType::I32);

    let entry = &lir.blocks[&Block(0)];
    let entry_copy = entry
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Copy) && inst.results == vec![header_param])
        .expect("entry edge should copy initial counter into loop header param");
    assert_eq!(entry_copy.args.len(), 1);
    assert!(
        matches!(entry.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(1) }),
        "entry block should still jump to the loop header"
    );

    let body = &lir.blocks[&Block(2)];
    let backedge_copy = body
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Copy) && inst.results == vec![header_param])
        .expect("back-edge should copy the incremented counter into the loop header param");
    assert_eq!(backedge_copy.args.len(), 1);
    assert_ne!(
        backedge_copy.args[0], header_param,
        "back-edge should feed a new value into the loop header param"
    );
    assert!(
        matches!(body.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(1) }),
        "loop body should still jump back to the header"
    );

    let exit = &lir.blocks[&Block(3)];
    let ret = exit.instructions.last().expect("exit block should return");
    assert!(matches!(ret.opcode, Opcode::Return));
    assert_eq!(
        ret.args,
        vec![header_param],
        "exit path should read the loop header param, not a body-local stale value"
    );
}

#[test]
fn test_lower_switch_join_uses_edge_copy_block_for_block_param() {
    let func = VerifiableFunction {
        name: "switch_join_param".to_string(),
        def_path: "test::switch_join_param".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("cond".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: None }, // joined value
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: SourceSpan::default(),
                    }],
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
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
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
    };

    let lir = lower_to_lir(&func).expect("single-target switch join should lower");
    assert_eq!(lir.blocks.len(), 4, "join should add one synthetic edge copy block");

    let join = &lir.blocks[&Block(2)];
    assert_eq!(join.params.len(), 1, "join block should get one block param for the joined local");
    let (join_param, join_param_ty) = &join.params[0];
    let join_param = *join_param;
    assert_eq!(*join_param_ty, LirType::I32);

    let entry = &lir.blocks[&Block(0)];
    let (_, else_dest) = entry
        .instructions
        .iter()
        .find_map(|inst| match &inst.opcode {
            Opcode::Brif { then_dest, else_dest, .. } => Some((*then_dest, *else_dest)),
            _ => None,
        })
        .expect("single-target switch should still lower to Brif");
    assert_ne!(
        else_dest,
        Block(2),
        "conditional join edge should route through a synthetic copy block"
    );

    let edge_copy_block = &lir.blocks[&else_dest];
    let edge_copy = edge_copy_block
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Copy) && inst.results == vec![join_param])
        .expect("conditional edge copy block should feed the join param");
    assert_eq!(edge_copy.args.len(), 1);
    assert_ne!(
        edge_copy.args[0], join_param,
        "conditional edge should copy the predecessor value into the join param"
    );
    assert!(
        matches!(
            edge_copy_block.instructions.last().unwrap().opcode,
            Opcode::Jump { dest: Block(2) }
        ),
        "synthetic edge block should jump into the join block"
    );

    let then_block = &lir.blocks[&Block(1)];
    let goto_copy = then_block
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Copy) && inst.results == vec![join_param])
        .expect("goto predecessor should still copy into the join param directly");
    assert_eq!(goto_copy.args.len(), 1);
    assert!(
        matches!(then_block.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(2) }),
        "goto predecessor should still jump directly to the join block"
    );

    let ret = join.instructions.last().expect("join block should return");
    assert!(matches!(ret.opcode, Opcode::Return));
    assert_eq!(
        ret.args,
        vec![join_param],
        "join block should read the block param rather than a stale predecessor-local value"
    );
}

#[test]
fn test_lower_assert_join_uses_edge_copy_block_for_block_param() {
    use trust_types::AssertMessage;

    let func = VerifiableFunction {
        name: "assert_join_param".to_string(),
        def_path: "test::assert_join_param".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("branch".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("checked".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: None }, // joined value
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: SourceSpan::default(),
                    }],
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
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::local(2)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
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

    let lir = lower_to_lir(&func).expect("assert join should lower");
    assert!(lir.blocks.len() >= 6, "assert join should add a panic block and an edge copy block");

    let join = &lir.blocks[&Block(3)];
    assert_eq!(join.params.len(), 1, "join block should get one block param for the joined local");
    let (join_param, join_param_ty) = &join.params[0];
    let join_param = *join_param;
    assert_eq!(*join_param_ty, LirType::I32);

    let assert_block = &lir.blocks[&Block(1)];
    let (then_dest, else_dest) = assert_block
        .instructions
        .iter()
        .find_map(|inst| match &inst.opcode {
            Opcode::Brif { then_dest, else_dest, .. } => Some((*then_dest, *else_dest)),
            _ => None,
        })
        .expect("assert should lower to Brif");
    assert_ne!(
        then_dest,
        Block(3),
        "assert success edge should route through a synthetic copy block when joining"
    );
    assert_ne!(
        else_dest,
        Block(3),
        "assert failure edge should still target panic, not the join block"
    );

    let assert_edge_block = &lir.blocks[&then_dest];
    let assert_edge_copy = assert_edge_block
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Copy) && inst.results == vec![join_param])
        .expect("assert success edge copy block should feed the join param");
    assert_eq!(assert_edge_copy.args.len(), 1);
    assert_ne!(
        assert_edge_copy.args[0], join_param,
        "assert success edge should copy the predecessor value into the join param"
    );
    assert!(
        matches!(
            assert_edge_block.instructions.last().unwrap().opcode,
            Opcode::Jump { dest: Block(3) }
        ),
        "assert success edge block should jump into the join block"
    );

    let goto_block = &lir.blocks[&Block(2)];
    let goto_copy = goto_block
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Copy) && inst.results == vec![join_param])
        .expect("goto predecessor should still copy into the join param directly");
    assert_eq!(goto_copy.args.len(), 1);
    assert!(
        matches!(goto_block.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(3) }),
        "goto predecessor should still jump directly to the join block"
    );

    let ret = join.instructions.last().expect("join block should return");
    assert!(matches!(ret.opcode, Opcode::Return));
    assert_eq!(
        ret.args,
        vec![join_param],
        "join block should read the block param rather than a stale predecessor-local value"
    );
}

#[test]
fn test_lower_multi_switch_join_uses_edge_copy_block_for_block_param() {
    let func = VerifiableFunction {
        name: "multi_switch_join_param".to_string(),
        def_path: "test::multi_switch_join_param".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("branch".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: None }, // joined value
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(3)), (1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
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
    };

    let lir = lower_to_lir(&func).expect("multi-way switch join should lower");
    assert_eq!(lir.blocks.len(), 5, "join should add one synthetic edge copy block");

    let join = &lir.blocks[&Block(3)];
    assert_eq!(join.params.len(), 1, "join block should get one block param for the joined local");
    let (join_param, join_param_ty) = &join.params[0];
    let join_param = *join_param;
    assert_eq!(*join_param_ty, LirType::I32);

    let entry = &lir.blocks[&Block(0)];
    let (cases, default) = entry
        .instructions
        .iter()
        .find_map(|inst| match &inst.opcode {
            Opcode::Switch { cases, default } => Some((cases.clone(), *default)),
            _ => None,
        })
        .expect("multi-target switch should still lower to Switch");
    assert_eq!(cases.len(), 2, "multi-way switch should keep both explicit cases");
    let join_case_dest = cases
        .iter()
        .find_map(|(value, dest)| (*value == 0).then_some(*dest))
        .expect("case 0 should be present");
    assert_ne!(
        join_case_dest,
        Block(3),
        "direct join case should route through a synthetic copy block"
    );
    assert_eq!(default, Block(2), "non-joining default edge should stay direct");

    let switch_edge_block = &lir.blocks[&join_case_dest];
    let switch_edge_copy = switch_edge_block
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Copy) && inst.results == vec![join_param])
        .expect("switch edge copy block should feed the join param");
    assert_eq!(switch_edge_copy.args.len(), 1);
    assert_ne!(
        switch_edge_copy.args[0], join_param,
        "switch edge should copy the predecessor value into the join param"
    );
    assert!(
        matches!(
            switch_edge_block.instructions.last().unwrap().opcode,
            Opcode::Jump { dest: Block(3) }
        ),
        "synthetic switch edge block should jump into the join block"
    );

    let case_block = &lir.blocks[&Block(1)];
    let case_copy = case_block
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Copy) && inst.results == vec![join_param])
        .expect("goto predecessor should still copy into the join param directly");
    assert_eq!(case_copy.args.len(), 1);

    let default_block = &lir.blocks[&Block(2)];
    let default_copy = default_block
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Copy) && inst.results == vec![join_param])
        .expect("default goto predecessor should still copy into the join param directly");
    assert_eq!(default_copy.args.len(), 1);

    let ret = join.instructions.last().expect("join block should return");
    assert!(matches!(ret.opcode, Opcode::Return));
    assert_eq!(
        ret.args,
        vec![join_param],
        "join block should read the block param rather than a stale predecessor-local value"
    );
}

#[test]
fn test_lower_mixed_join_preserves_two_live_locals_across_switch_goto_and_assert() {
    use trust_types::AssertMessage;

    let func = VerifiableFunction {
        name: "mixed_multi_live_join".to_string(),
        def_path: "test::mixed_multi_live_join".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("branch".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("checked".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: None }, // x
                LocalDecl { index: 4, ty: Ty::i32(), name: None }, // y
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(20))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(3)), (1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(30))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(40))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(50))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(60))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::local(2)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(4)),
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
    };

    let lir = lower_to_lir(&func).expect("mixed multi-live join should lower");
    assert!(
        lir.blocks.len() >= 7,
        "mixed join should include synthetic switch/assert edge blocks and a panic block"
    );

    let join = &lir.blocks[&Block(3)];
    assert_eq!(join.params.len(), 2, "join should get block params for both live locals");
    let join_params: Vec<Value> = join.params.iter().map(|(value, _)| *value).collect();
    assert_eq!(
        join.params.iter().map(|(_, ty)| ty.clone()).collect::<Vec<_>>(),
        vec![LirType::I32, LirType::I32]
    );

    let add = join
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Iadd))
        .expect("join should add the two live locals");
    assert_eq!(
        add.args, join_params,
        "join should read both forwarded block params rather than stale predecessor locals"
    );

    let entry = &lir.blocks[&Block(0)];
    let (switch_cases, _) = entry
        .instructions
        .iter()
        .find_map(|inst| match &inst.opcode {
            Opcode::Switch { cases, default } => Some((cases.clone(), *default)),
            _ => None,
        })
        .expect("entry should still lower to Switch");
    let switch_join_dest = switch_cases
        .iter()
        .find_map(|(value, dest)| (*value == 0).then_some(*dest))
        .expect("switch case to join should be present");
    assert_ne!(
        switch_join_dest,
        Block(3),
        "direct switch edge should route through a synthetic copy block"
    );
    let switch_edge_block = &lir.blocks[&switch_join_dest];
    let switch_edge_copies: Vec<_> = switch_edge_block
        .instructions
        .iter()
        .filter(|inst| {
            matches!(inst.opcode, Opcode::Copy)
                && inst.results.len() == 1
                && join_params.contains(&inst.results[0])
        })
        .collect();
    assert_eq!(
        switch_edge_copies.len(),
        2,
        "direct switch edge should copy both live locals into the join params"
    );

    let goto_block = &lir.blocks[&Block(1)];
    let goto_copies: Vec<_> = goto_block
        .instructions
        .iter()
        .filter(|inst| {
            matches!(inst.opcode, Opcode::Copy)
                && inst.results.len() == 1
                && join_params.contains(&inst.results[0])
        })
        .collect();
    assert_eq!(goto_copies.len(), 2, "goto predecessor should copy both live locals");

    let assert_block = &lir.blocks[&Block(2)];
    let assert_then_dest = assert_block
        .instructions
        .iter()
        .find_map(|inst| match &inst.opcode {
            Opcode::Brif { then_dest, .. } => Some(*then_dest),
            _ => None,
        })
        .expect("assert should lower to Brif");
    assert_ne!(
        assert_then_dest,
        Block(3),
        "assert success edge should route through a synthetic copy block"
    );
    let assert_edge_block = &lir.blocks[&assert_then_dest];
    let assert_edge_copies: Vec<_> = assert_edge_block
        .instructions
        .iter()
        .filter(|inst| {
            matches!(inst.opcode, Opcode::Copy)
                && inst.results.len() == 1
                && join_params.contains(&inst.results[0])
        })
        .collect();
    assert_eq!(
        assert_edge_copies.len(),
        2,
        "assert success edge should copy both live locals into the join params"
    );
}

#[test]
fn test_lower_forwarding_join_preserves_two_live_locals_across_switch_goto_and_assert() {
    use trust_types::AssertMessage;

    let func = VerifiableFunction {
        name: "forwarding_multi_live_join".to_string(),
        def_path: "test::forwarding_multi_live_join".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("branch".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("checked".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: None }, // x
                LocalDecl { index: 4, ty: Ty::i32(), name: None }, // y
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(20))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(3)), (1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(30))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(40))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(50))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(60))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::local(2)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                TrustBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(4)),
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
    };

    let lir = lower_to_lir(&func).expect("forwarding multi-live join should lower");
    assert!(
        lir.blocks.len() >= 8,
        "forwarding join should include synthetic switch/assert edge blocks and a panic block"
    );

    let forwarding = &lir.blocks[&Block(3)];
    assert_eq!(
        forwarding.params.len(),
        2,
        "forwarding merge should get block params for both live locals it must pass through"
    );
    let forwarding_params: Vec<Value> = forwarding.params.iter().map(|(value, _)| *value).collect();
    assert_eq!(
        forwarding.params.iter().map(|(_, ty)| ty.clone()).collect::<Vec<_>>(),
        vec![LirType::I32, LirType::I32]
    );
    assert!(
        matches!(forwarding.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(4) }),
        "forwarding block should still just jump to the consumer block"
    );

    let consumer = &lir.blocks[&Block(4)];
    let add = consumer
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Iadd))
        .expect("consumer block should add the forwarded locals");
    assert_eq!(
        add.args, forwarding_params,
        "consumer should read the forwarding block params rather than stale initial locals"
    );

    let entry = &lir.blocks[&Block(0)];
    let switch_join_dest = entry
        .instructions
        .iter()
        .find_map(|inst| match &inst.opcode {
            Opcode::Switch { cases, .. } => {
                cases.iter().find_map(|(value, dest)| (*value == 0).then_some(*dest))
            }
            _ => None,
        })
        .expect("switch case into forwarding block should be present");
    assert_ne!(
        switch_join_dest,
        Block(3),
        "direct switch edge should route through a synthetic copy block into the forwarding merge"
    );
    let switch_edge_copies: Vec<_> = lir.blocks[&switch_join_dest]
        .instructions
        .iter()
        .filter(|inst| {
            matches!(inst.opcode, Opcode::Copy)
                && inst.results.len() == 1
                && forwarding_params.contains(&inst.results[0])
        })
        .collect();
    assert_eq!(
        switch_edge_copies.len(),
        2,
        "direct switch edge should copy both live locals into the forwarding merge params"
    );

    let goto_copies: Vec<_> = lir.blocks[&Block(1)]
        .instructions
        .iter()
        .filter(|inst| {
            matches!(inst.opcode, Opcode::Copy)
                && inst.results.len() == 1
                && forwarding_params.contains(&inst.results[0])
        })
        .collect();
    assert_eq!(goto_copies.len(), 2, "goto predecessor should copy both live locals");

    let assert_then_dest = lir.blocks[&Block(2)]
        .instructions
        .iter()
        .find_map(|inst| match &inst.opcode {
            Opcode::Brif { then_dest, .. } => Some(*then_dest),
            _ => None,
        })
        .expect("assert should lower to Brif");
    assert_ne!(
        assert_then_dest,
        Block(3),
        "assert success edge should route through a synthetic copy block into the forwarding merge"
    );
    let assert_edge_copies: Vec<_> = lir.blocks[&assert_then_dest]
        .instructions
        .iter()
        .filter(|inst| {
            matches!(inst.opcode, Opcode::Copy)
                && inst.results.len() == 1
                && forwarding_params.contains(&inst.results[0])
        })
        .collect();
    assert_eq!(
        assert_edge_copies.len(),
        2,
        "assert success edge should copy both live locals into the forwarding merge params"
    );
}

#[test]
fn test_lower_loop_header_breaks_parallel_copy_cycle_for_cross_swapped_params() {
    let func = VerifiableFunction {
        name: "loop_header_parallel_copy_cycle".to_string(),
        def_path: "test::loop_header_parallel_copy_cycle".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: None }, // iter
                LocalDecl { index: 2, ty: Ty::i32(), name: None }, // x
                LocalDecl { index: 3, ty: Ty::i32(), name: None }, // y
                LocalDecl { index: 4, ty: Ty::i32(), name: None }, // tmp
                LocalDecl { index: 5, ty: Ty::Bool, name: None },  // cond
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(20))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Ne,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(0)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(3)),
                        ),
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
    };

    let lir = lower_to_lir(&func).expect("cross-swapped loop header should lower");
    let header = &lir.blocks[&Block(1)];
    assert_eq!(header.params.len(), 3, "loop header should get params for iter, x, and y");
    let header_params: Vec<Value> = header.params.iter().map(|(value, _)| *value).collect();

    let body = &lir.blocks[&Block(2)];
    let copy_insts: Vec<_> =
        body.instructions.iter().filter(|inst| matches!(inst.opcode, Opcode::Copy)).collect();
    assert_eq!(
        copy_insts.len(),
        header_params.len() + 1,
        "cross-swapped back-edge should need one extra temp copy to break the cycle"
    );

    let param_copies: Vec<_> = copy_insts
        .iter()
        .copied()
        .filter(|inst| inst.results.len() == 1 && header_params.contains(&inst.results[0]))
        .collect();
    assert_eq!(
        param_copies.len(),
        header_params.len(),
        "back-edge should still populate every loop-header param"
    );

    let temp_copy = copy_insts
        .iter()
        .copied()
        .find(|inst| inst.results.len() == 1 && !header_params.contains(&inst.results[0]))
        .expect("parallel-copy cycle should be broken with one temporary value");
    let temp_value = temp_copy.results[0];
    assert!(
        param_copies.iter().any(|inst| inst.args == vec![temp_value]),
        "one loop-header param copy should reload from the cycle-breaking temporary"
    );
    assert!(
        matches!(body.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(1) }),
        "loop body should still jump back to the loop header"
    );
}

#[test]
fn test_lower_call_continuation_join_uses_block_param_for_call_defined_local() {
    let func = VerifiableFunction {
        name: "call_cont_join_param".to_string(),
        def_path: "test::call_cont_join_param".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("branch".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: None }, // call-defined result
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
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "left_call".to_string(),
                        args: vec![],
                        dest: Place::local(2),
                        target: Some(BlockId(3)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "right_call".to_string(),
                        args: vec![],
                        dest: Place::local(2),
                        target: Some(BlockId(3)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
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
    };

    let lir = lower_to_lir(&func).expect("call continuation join should lower");
    let join = &lir.blocks[&Block(3)];
    assert_eq!(
        join.params.len(),
        1,
        "join block should get one block param for the local defined by the call continuations"
    );
    let join_param = join.params[0].0;

    for pred in [Block(1), Block(2)] {
        let pred_block = &lir.blocks[&pred];
        let call = pred_block
            .instructions
            .iter()
            .find(|inst| matches!(inst.opcode, Opcode::Call { .. }))
            .expect("call predecessor should still contain the call instruction");
        let copy = pred_block
            .instructions
            .iter()
            .find(|inst| matches!(inst.opcode, Opcode::Copy) && inst.results == vec![join_param])
            .expect("call continuation should copy the call-defined local into the join param");
        assert_eq!(
            copy.args, call.results,
            "call continuation copy should use the call result value as its source"
        );
        assert!(
            matches!(
                pred_block.instructions.last().unwrap().opcode,
                Opcode::Jump { dest: Block(3) }
            ),
            "call continuation should still jump to the join block"
        );
    }

    let ret = join.instructions.last().expect("join block should return");
    assert!(matches!(ret.opcode, Opcode::Return));
    assert_eq!(
        ret.args,
        vec![join_param],
        "join should return the block param rather than the stale initial local value"
    );
}

#[test]
fn test_lower_call_join_uses_block_param_for_projected_dest_index() {
    let func = VerifiableFunction {
        name: "call_projected_dest_join".to_string(),
        def_path: "test::call_projected_dest_join".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("branch".into()) },
                LocalDecl { index: 2, ty: Ty::i64(), name: None }, // index
                LocalDecl {
                    index: 3,
                    ty: Ty::Array { elem: Box::new(Ty::i32()), len: 2 },
                    name: None,
                },
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
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "index_write".to_string(),
                        args: vec![],
                        dest: Place { local: 3, projections: vec![Projection::Index(2)] },
                        target: Some(BlockId(4)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("call join with projected dest should lower");
    let join = &lir.blocks[&Block(3)];
    assert_eq!(
        join.params.len(),
        1,
        "call block should get one block param for the index used only by the call destination"
    );
    let index_param = join.params[0].0;
    assert_eq!(join.params[0].1, LirType::I64);

    let imul = join
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::Imul))
        .expect("projected call destination should compute an indexed element offset");
    assert_eq!(
        imul.args[0], index_param,
        "indexed call destination should use the forwarded join param as the element index"
    );
    assert!(
        join.instructions.iter().any(|inst| matches!(inst.opcode, Opcode::Call { .. })),
        "call block should still contain the call instruction"
    );

    for pred in [Block(1), Block(2)] {
        let pred_block = &lir.blocks[&pred];
        assert!(
            pred_block.instructions.iter().any(
                |inst| matches!(inst.opcode, Opcode::Copy) && inst.results == vec![index_param]
            ),
            "each predecessor should copy its chosen index into the call block param"
        );
        assert!(
            matches!(
                pred_block.instructions.last().unwrap().opcode,
                Opcode::Jump { dest: Block(3) }
            ),
            "each predecessor should still jump to the call block"
        );
    }
}

// =========================================================================
// Edge case: closures and function calls
// =========================================================================

#[test]
fn test_edge_case_closure_call() {
    // Closures in MIR are just Call terminators with a closure name.
    // This tests that a "closure call" (function pointer invocation) lowers.
    let func = VerifiableFunction {
        name: "call_closure".to_string(),
        def_path: "test::call_closure".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("captured".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: None }, // call result
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "closure$0::call".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
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
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("closure call should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should contain a Call instruction
    let call_instr = bb0.instructions.iter().find(|i| matches!(i.opcode, Opcode::Call { .. }));
    assert!(call_instr.is_some(), "expected Call instruction for closure");
    let call = call_instr.unwrap();
    if let Opcode::Call { name } = &call.opcode {
        assert_eq!(name, "closure$0::call");
    }
}

#[test]
fn test_edge_case_vtable_dispatch() {
    // Trait object dispatch: Call with a dynamic dispatch name.
    let func = VerifiableFunction {
        name: "vtable_call".to_string(),
        def_path: "test::vtable_call".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                // self: trait object as raw pointer
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { pointee: Box::new(Ty::Unit), mutable: false },
                    name: Some("self_ptr".into()),
                },
                LocalDecl { index: 2, ty: Ty::i32(), name: None }, // result
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "<dyn Trait>::method".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
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
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("vtable dispatch should lower");
    let bb0 = &lir.blocks[&Block(0)];
    let call_instr = bb0.instructions.iter().find(|i| matches!(i.opcode, Opcode::Call { .. }));
    assert!(call_instr.is_some());
    if let Opcode::Call { name } = &call_instr.unwrap().opcode {
        assert_eq!(name, "<dyn Trait>::method");
    }
}

#[test]
fn test_edge_case_match_multiway_switch() {
    // Complex match: SwitchInt with multiple targets (enum discriminant match).
    let func = VerifiableFunction {
        name: "enum_match".to_string(),
        def_path: "test::enum_match".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("discr".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1)), (1, BlockId(2)), (2, BlockId(3))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(100))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                TrustBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(200))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                TrustBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(300))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                TrustBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(-1))),
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
    };

    let lir = lower_to_lir(&func).expect("multiway switch should lower");
    assert_eq!(lir.blocks.len(), 5);
    // The entry block should have a Switch instruction (not Brif).
    let bb0 = &lir.blocks[&Block(0)];
    let switch_instr = bb0.instructions.iter().find(|i| matches!(i.opcode, Opcode::Switch { .. }));
    assert!(switch_instr.is_some(), "3+ targets should produce Switch opcode");
    if let Opcode::Switch { cases, default } = &switch_instr.unwrap().opcode {
        assert_eq!(cases.len(), 3);
        assert_eq!(*default, Block(4));
    }
}

#[test]
fn test_edge_case_aggregate_construction_tuple() {
    // Construct a tuple (i32, bool, i64) via Rvalue::Aggregate.
    let tuple_ty = Ty::Tuple(vec![Ty::i32(), Ty::Bool, Ty::i64()]);
    let func = VerifiableFunction {
        name: "make_tuple".to_string(),
        def_path: "test::make_tuple".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: tuple_ty.clone(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Tuple,
                        vec![
                            Operand::Constant(ConstValue::Int(42)),
                            Operand::Constant(ConstValue::Bool(true)),
                            Operand::Constant(ConstValue::Int(999)),
                        ],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: tuple_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("tuple aggregate should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should have StackAddr + 3x (Iconst/Bconst + StructGep + Store) + Return
    let store_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Store { .. })).count();
    assert_eq!(store_count, 3, "expected 3 stores for 3 tuple fields");
}

#[test]
fn test_edge_case_aggregate_construction_adt() {
    // Construct an ADT with variant.
    let adt_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "MyStruct".to_string(),
        fields: vec![("x".to_string(), Ty::i32()), ("y".to_string(), Ty::i32())],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "make_adt".to_string(),
        def_path: "test::make_adt".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: adt_ty.clone(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "MyStruct".to_string(),
                            variant: 0,
                            active_field: None,
                        },
                        vec![
                            Operand::Constant(ConstValue::Int(10)),
                            Operand::Constant(ConstValue::Int(20)),
                        ],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: adt_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("ADT aggregate should lower");
    let bb0 = &lir.blocks[&Block(0)];
    let store_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Store { .. })).count();
    assert_eq!(store_count, 2, "expected 2 stores for 2 ADT fields");
}

#[test]
fn test_edge_case_downcast_and_field_access() {
    // Simulate accessing a field through a downcast projection:
    // place = _1.downcast(0).field(0)
    let adt_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "MyEnum".to_string(),
        fields: vec![("data".to_string(), Ty::i32())],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "downcast_field".to_string(),
        def_path: "test::downcast_field".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: adt_ty, name: Some("e".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Downcast(0), Projection::Field(0)],
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

    let lir = lower_to_lir(&func).expect("downcast + field should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should have StructGep and Load instructions for field access.
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::StructGep { .. })));
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Load { .. })));
}

#[test]
fn test_edge_case_assert_terminator() {
    // Assert creates a panic block automatically.
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

    let lir = lower_to_lir(&func).expect("assert should lower");
    // Should have 3 blocks: bb0, bb1, and the panic block.
    assert_eq!(lir.blocks.len(), 3);
    // bb0 should have a Brif instruction.
    let bb0 = &lir.blocks[&Block(0)];
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Brif { .. })));
    let panic_block = lir
        .blocks
        .iter()
        .find(|(block, _)| **block != Block(0) && **block != Block(1))
        .map(|(_, block)| block)
        .expect("assert lowering should synthesize a panic block");
    assert!(
        panic_block
            .instructions
            .iter()
            .any(|i| matches!(&i.opcode, Opcode::Call { name } if name == "abort")),
        "panic block should lower to an abort call"
    );
    assert!(
        !panic_block.instructions.iter().any(|i| matches!(i.opcode, Opcode::Return)),
        "panic block should not fabricate a Return"
    );
}

#[test]
fn test_edge_case_assert_expected_false() {
    // Assert with expected=false flips then/else.
    use trust_types::AssertMessage;
    let func = VerifiableFunction {
        name: "assert_false".to_string(),
        def_path: "test::assert_false".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("overflow".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::local(1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
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

    let lir = lower_to_lir(&func).expect("assert expected=false should lower");
    // The Brif should branch to panic on true (since expected=false means
    // the condition being true is a failure).
    let bb0 = &lir.blocks[&Block(0)];
    let brif = bb0.instructions.iter().find(|i| matches!(i.opcode, Opcode::Brif { .. }));
    assert!(brif.is_some());
    if let Opcode::Brif { then_dest, else_dest, .. } = &brif.unwrap().opcode {
        // then_dest should be the panic block (not bb1), else_dest should be bb1.
        assert_eq!(*else_dest, Block(1));
        assert_ne!(*then_dest, Block(1)); // then_dest is the panic block
    }
}

// =========================================================================
// Negative tests: invalid MIR produces descriptive errors
// =========================================================================

#[test]
fn test_negative_empty_body_error() {
    let func = VerifiableFunction {
        name: "empty".to_string(),
        def_path: "test::empty".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_lir(&func).unwrap_err();
    assert!(matches!(err, BridgeError::EmptyBody));
}

#[test]
fn test_negative_duplicate_block_ids_error() {
    let func = VerifiableFunction {
        name: "dup_blocks".to_string(),
        def_path: "test::dup_blocks".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                TrustBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return },
                TrustBlock {
                    id: BlockId(0), // duplicate!
                    stmts: vec![],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let err = lower_to_lir(&func).unwrap_err();
    assert!(matches!(err, BridgeError::InvalidMir(_)));
    let msg = format!("{err}");
    assert!(msg.contains("duplicate block ID"), "error: {msg}");
}

#[test]
fn test_negative_unsupported_type_odd_bv() {
    let ty = Ty::Bv(13);
    let err = map_type(&ty).unwrap_err();
    assert!(matches!(err, BridgeError::UnsupportedType(_)));
    let msg = format!("{err}");
    assert!(msg.contains("Bv(13)"), "error: {msg}");
}

#[test]
fn test_symbolic_expression_fails_closed_instead_of_becoming_zero() {
    use trust_types::{Formula, Sort};
    let func = VerifiableFunction {
        name: "symbolic".to_string(),
        def_path: "test::symbolic".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Symbolic(Formula::Var(
                        "x".to_string(),
                        Sort::BitVec(32),
                    ))),
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

    let error = lower_to_lir(&func).expect_err("symbolic variables must not become constants");
    assert!(matches!(
        error,
        BridgeError::UnsupportedOp(message)
            if message.contains("symbolic operand requires target-semantic lowering")
                && message.contains("refusing to replace")
    ));
}

#[test]
fn test_negative_missing_local_in_operand() {
    // Reference a local that doesn't exist in the locals list.
    let func = VerifiableFunction {
        name: "missing_local".to_string(),
        def_path: "test::missing_local".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(99))),
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

    let err = lower_to_lir(&func).unwrap_err();
    assert!(matches!(err, BridgeError::MissingLocal(99)));
}

#[test]
fn test_negative_cmp_binop_unsupported() {
    // Three-way Cmp is explicitly unsupported.
    let err = map_binop(BinOp::Cmp, false).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("three-way Cmp"), "error: {msg}");
}

#[test]
// Trust: #828 — ConstantIndex from_end now lowers for arrays.
fn test_constant_index_from_end() {
    let func = VerifiableFunction {
        name: "const_idx_end".to_string(),
        def_path: "test::const_idx_end".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::i32()), len: 5 },
                    name: Some("arr".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::ConstantIndex {
                            offset: 1,
                            min_length: 2,
                            from_end: true,
                        }],
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

    lower_to_lir(&func).expect("constant index from end should lower");
}

#[test]
fn test_edge_case_drop_terminator() {
    // Drop is a no-op jump to target.
    let func = VerifiableFunction {
        name: "drop_fn".to_string(),
        def_path: "test::drop_fn".to_string(),
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
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(1),
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

    let lir = lower_to_lir(&func).expect("drop should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(matches!(bb0.instructions.last().unwrap().opcode, Opcode::Jump { dest: Block(1) }));
}

#[test]
fn test_edge_case_unreachable_terminator() {
    // Unreachable lowers to a diverging abort call.
    let func = VerifiableFunction {
        name: "unreach".to_string(),
        def_path: "test::unreach".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Unreachable,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("unreachable should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(matches!(
        &bb0.instructions.last().unwrap().opcode,
        Opcode::Call { name } if name == "abort"
    ));
    assert!(
        !bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Return)),
        "unreachable should not fabricate a Return"
    );
}

#[test]
fn test_edge_case_single_target_opaque_terminator_is_unsupported() {
    let func = VerifiableFunction {
        name: "opaque".to_string(),
        def_path: "test::opaque".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Opaque {
                        kind: "inline_asm".to_string(),
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

    let err = lower_to_lir(&func).expect_err("single-target opaque must not lower as Jump");
    assert!(matches!(err, BridgeError::UnsupportedOp(_)));
    assert!(
        err.to_string().contains("opaque MIR terminator `inline_asm` is unsupported"),
        "unexpected error: {err}"
    );
}

#[test]
fn test_edge_case_checked_add_overflow() {
    let checked_ty = Ty::Tuple(vec![Ty::i32(), Ty::Bool]);
    let func = VerifiableFunction {
        name: "checked_add".to_string(),
        def_path: "test::checked_add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: checked_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
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
            return_ty: checked_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("checked add should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Iadd)));
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Icmp { cond: IntCC::SignedLessThan })),
        "signed checked add should derive overflow from the payload type's sign bit"
    );
    assert!(
        !bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Isub)),
        "signed checked add must not use the old inverse-sub overflow check"
    );
    let store_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Store { .. })).count();
    assert_eq!(store_count, 2, "expected 2 stores for (result, overflow) tuple");
}

#[test]
fn test_edge_case_repeat_array_construction() {
    // [0i32; 5] should lower to 5 stores.
    let arr_ty = Ty::Array { elem: Box::new(Ty::i32()), len: 5 };
    let func = VerifiableFunction {
        name: "repeat_arr".to_string(),
        def_path: "test::repeat_arr".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: arr_ty.clone(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Repeat(Operand::Constant(ConstValue::Int(0)), 5),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: arr_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("array repeat should lower");
    let bb0 = &lir.blocks[&Block(0)];
    let store_count =
        bb0.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Store { .. })).count();
    assert_eq!(store_count, 5, "expected 5 stores for [0; 5]");
}

#[test]
fn test_edge_case_cast_int_widening() {
    // Cast i8 -> i32 should produce Sextend or Uextend.
    let func = VerifiableFunction {
        name: "widen".to_string(),
        def_path: "test::widen".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i8(), name: Some("x".into()) },
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

    let lir = lower_to_lir(&func).expect("int widening cast should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should have Sextend (i8 is signed).
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Sextend { .. })));
}

#[test]
fn test_edge_case_cast_int_narrowing() {
    // Cast i64 -> i8 should produce Trunc.
    let func = VerifiableFunction {
        name: "narrow".to_string(),
        def_path: "test::narrow".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i8(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::i8()),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i8(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("int narrowing cast should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Trunc { .. })));
}

#[test]
fn test_edge_case_nop_statements_ignored() {
    // Nop statements should produce no instructions.
    let func = VerifiableFunction {
        name: "nops".to_string(),
        def_path: "test::nops".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Nop, Statement::Nop, Statement::Nop],
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

    let lir = lower_to_lir(&func).expect("nops should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Only the Return instruction should be present.
    assert_eq!(bb0.instructions.len(), 1);
    assert!(matches!(bb0.instructions[0].opcode, Opcode::Return));
}

#[test]
fn test_edge_case_len_on_array() {
    // Len on array should produce an Iconst with the known length.
    let arr_ty = Ty::Array { elem: Box::new(Ty::i32()), len: 42 };
    let func = VerifiableFunction {
        name: "arr_len".to_string(),
        def_path: "test::arr_len".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: arr_ty, name: Some("arr".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Len(Place::local(1)),
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

    let lir = lower_to_lir(&func).expect("array len should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should have an Iconst with imm=42 for the length.
    let iconst =
        bb0.instructions.iter().find(|i| matches!(i.opcode, Opcode::Iconst { imm: 42, .. }));
    assert!(iconst.is_some(), "expected Iconst(42) for array length");
}

#[test]
fn test_edge_case_ref_rvalue() {
    // Rvalue::Ref should compute the address via StackAddr.
    let func = VerifiableFunction {
        name: "take_ref".to_string(),
        def_path: "test::take_ref".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) },
                    name: None,
                },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
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
            return_ty: Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("ref should lower");
    let bb0 = &lir.blocks[&Block(0)];
    // Should have StackAddr for taking the address.
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::StackAddr { .. })));
}

// Trust: #828 — MIR lowering coverage for three-way compare, pointer metadata,
// subslices, and drop elaboration.
#[test]
fn test_cmp_binop_three_way() {
    let func = VerifiableFunction {
        name: "cmp_three_way".to_string(),
        def_path: "test::cmp_three_way".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("lhs".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("rhs".into()) },
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
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("three-way cmp should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Icmp { cond: IntCC::SignedLessThan })),
        "signed Cmp should use signed less-than"
    );
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Icmp { cond: IntCC::SignedGreaterThan })),
        "signed Cmp should use signed greater-than"
    );
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Select { .. })));
}

#[test]
fn test_cmp_binop_unsigned_three_way_uses_unsigned_conditions() {
    let func = VerifiableFunction {
        name: "cmp_unsigned_three_way".to_string(),
        def_path: "test::cmp_unsigned_three_way".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("lhs".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("rhs".into()) },
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
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let lir = lower_to_lir(&func).expect("unsigned three-way cmp should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Icmp { cond: IntCC::UnsignedLessThan })),
        "unsigned Cmp should use unsigned less-than"
    );
    assert!(
        bb0.instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Icmp { cond: IntCC::UnsignedGreaterThan })),
        "unsigned Cmp should use unsigned greater-than"
    );
    assert!(
        !bb0.instructions.iter().any(|i| matches!(
            i.opcode,
            Opcode::Icmp { cond: IntCC::SignedLessThan | IntCC::SignedGreaterThan }
        )),
        "unsigned Cmp must not use signed integer comparisons"
    );
}

#[test]
fn test_ptr_metadata_slice() {
    let slice_ty = Ty::Slice { elem: Box::new(Ty::i32()) };
    let func = VerifiableFunction {
        name: "ptr_metadata_slice".to_string(),
        def_path: "test::ptr_metadata_slice".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: slice_ty.clone(), name: Some("slice".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1))),
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

    let lir = lower_to_lir(&func).expect("slice ptr metadata should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::StructGep { .. })));
    assert!(bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Load { .. })));
}

#[test]
fn test_subslice_projection() {
    let array_ty = Ty::Array { elem: Box::new(Ty::i32()), len: 5 };
    let slice_ty = Ty::Slice { elem: Box::new(Ty::i32()) };
    let func = VerifiableFunction {
        name: "subslice_projection".to_string(),
        def_path: "test::subslice_projection".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: slice_ty.clone(), name: None },
                LocalDecl { index: 1, ty: array_ty, name: Some("arr".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Subslice { from: 1, to: 3, from_end: false }],
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: slice_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    lower_to_lir(&func).expect("subslice projection should lower");
}

#[test]
fn test_drop_adt_fails_without_resolved_drop_glue() {
    let adt_ty = Ty::Adt { adt_kind: None, layout: None,
        variants: Vec::new(),
        name: "TestStruct".to_string(),
        fields: vec![("x".to_string(), Ty::i32())],
        disc_index_safe: false,
     faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "drop_adt".to_string(),
        def_path: "test::drop_adt".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: adt_ty, name: Some("value".into()) },
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
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let error =
        lower_to_lir(&func).expect_err("ADT drop glue cannot be inferred from Ty debug text");
    assert!(matches!(
        error,
        BridgeError::UnsupportedOp(message)
            if message.contains("exact monomorphized drop-glue symbol")
    ));
}

#[test]
fn test_drop_scalar_no_call() {
    let func = VerifiableFunction {
        name: "drop_scalar".to_string(),
        def_path: "test::drop_scalar".to_string(),
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
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(1),
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

    let lir = lower_to_lir(&func).expect("scalar drop should lower");
    let bb0 = &lir.blocks[&Block(0)];
    assert!(!bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Call { .. })));
}
