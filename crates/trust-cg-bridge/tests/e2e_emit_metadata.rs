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

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use trust_cg_bridge::codegen_backend::{
    CrateInfo, OngoingCodegen, OutputFilenames, RustcCodegenBackend, TrustCgCodegenBackend,
};
use trust_cg_bridge::validation::{ValidationError, validate_lir};
use trust_cg_lower::function::{BasicBlock as LirBasicBlock, Function as LirFunction, Signature};
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::types::Type as LirType;
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
        linkage: Vec::new(),
        statics: Vec::new(),
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

        // Every use must be defined on every path that reaches it.
        assert_defined_before_use_by_dominance(lir);

        // Run structural validation. `validate_lir` is block-local: it accepts
        // only values defined in the same block, the formals, or the block's
        // own parameters. `sum_loop` carries `n` in its loop header's block
        // parameter, which the loop body and the exit read from the dominating
        // header, so for it only those dominance-justified `UndefinedValue`
        // reports are tolerated (the check above proved each is defined).
        match validate_lir(lir) {
            Ok(()) => {}
            Err(errors) if lir.name == "sum_loop" => {
                let other: Vec<_> = errors
                    .iter()
                    .filter(|e| !matches!(e, ValidationError::UndefinedValue { .. }))
                    .collect();
                assert!(other.is_empty(), "LIR validation failed for `sum_loop`: {other:?}");
            }
            Err(errors) => panic!("LIR validation failed for `{}`: {:?}", lir.name, errors),
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
    assert_entry_loop_carries_n_through_header_param(sum_loop_lir);
}

/// `sum_loop`'s bb0 is re-entered by bb1's backedge after `n -= 1`, so bb0
/// must read `n` from a block parameter that both the function entry and the
/// latch assign (the bridge feeds block parameters with `Copy`s in each
/// predecessor). Reading the formal argument there, as the lowering used to,
/// loops forever for any `n != 0`.
fn assert_entry_loop_carries_n_through_header_param(lir: &LirFunction) {
    // The value a predecessor copies into `param` right before jumping.
    fn copied_into(bb: &LirBasicBlock, param: Value) -> Value {
        let copies: Vec<_> = bb
            .instructions
            .iter()
            .filter(|i| matches!(i.opcode, Opcode::Copy) && i.results == [param])
            .collect();
        assert_eq!(copies.len(), 1, "one copy into {param:?}: {:?}", bb.instructions);
        copies[0].args[0]
    }

    let entry = &lir.blocks[&lir.entry_block];
    assert!(entry.params.is_empty(), "the function entry takes no block parameters");
    let header = match entry.instructions.last().map(|i| &i.opcode) {
        Some(Opcode::Jump { dest }) => *dest,
        other => panic!("sum_loop entry should jump to the loop header, got {other:?}"),
    };
    assert_ne!(header, lir.entry_block, "the loop header is not the function entry");
    let header_params = &lir.blocks[&header].params;
    assert_eq!(header_params.len(), 1, "the header carries exactly `n`: {header_params:?}");
    let n = header_params[0].0;
    assert_eq!(copied_into(entry, n), Value(0), "the entry feeds the formal `n`");

    let latches: Vec<_> = lir
        .blocks
        .iter()
        .filter(|(block, bb)| **block != lir.entry_block && bb.successors().contains(&header))
        .collect();
    assert_eq!(latches.len(), 1, "exactly one backedge into the header");
    let (_, latch) = latches[0];
    let passed = copied_into(latch, n);
    assert!(
        latch.instructions.iter().any(|i| i.results.contains(&passed) && i.args.contains(&n)),
        "the backedge feeds a value computed in the latch from the header's `n`, \
         not the formal: {:?}",
        latch.instructions
    );
    assert_ne!(passed, Value(0));
    assert_ne!(passed, n);
}

/// Dominance-aware defined-before-use: every operand is a formal, a parameter
/// of its own block, an earlier result in its own block, or a result or
/// parameter of a block that strictly dominates it.
fn assert_defined_before_use_by_dominance(lir: &LirFunction) {
    let mut preds: HashMap<Block, Vec<Block>> = HashMap::new();
    let mut rpo = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![(lir.entry_block, false)];
    while let Some((block, done)) = stack.pop() {
        if done {
            rpo.push(block);
            continue;
        }
        if !seen.insert(block) {
            continue;
        }
        stack.push((block, true));
        for succ in lir.blocks[&block].successors() {
            preds.entry(succ).or_default().push(block);
            if !seen.contains(&succ) {
                stack.push((succ, false));
            }
        }
    }
    rpo.reverse();

    // Iterative dominator sets over the reachable blocks.
    let all: HashSet<Block> = rpo.iter().copied().collect();
    let mut dom: HashMap<Block, HashSet<Block>> = rpo.iter().map(|b| (*b, all.clone())).collect();
    dom.insert(lir.entry_block, HashSet::from([lir.entry_block]));
    let mut changed = true;
    while changed {
        changed = false;
        for &block in rpo.iter().filter(|b| **b != lir.entry_block) {
            let mut new: Option<HashSet<Block>> = None;
            for pred in preds.get(&block).into_iter().flatten().filter(|p| all.contains(p)) {
                new = Some(match new {
                    None => dom[pred].clone(),
                    Some(acc) => acc.intersection(&dom[pred]).copied().collect(),
                });
            }
            let mut new = new.unwrap_or_default();
            new.insert(block);
            if new != dom[&block] {
                dom.insert(block, new);
                changed = true;
            }
        }
    }

    let defs_of = |block: Block| -> HashSet<Value> {
        let bb = &lir.blocks[&block];
        bb.params
            .iter()
            .map(|(v, _)| *v)
            .chain(bb.instructions.iter().flat_map(|i| i.results.iter().copied()))
            .collect()
    };
    for &block in &rpo {
        let mut defined: HashSet<Value> =
            (0..lir.signature.params.len() as u32).map(Value).collect();
        for dominator in dom[&block].iter().filter(|d| **d != block) {
            defined.extend(defs_of(*dominator));
        }
        let bb = &lir.blocks[&block];
        defined.extend(bb.params.iter().map(|(v, _)| *v));
        for instr in &bb.instructions {
            let cond = match &instr.opcode {
                Opcode::Brif { cond, .. } => Some(*cond),
                _ => None,
            };
            for used in instr.args.iter().copied().chain(cond) {
                assert!(
                    defined.contains(&used),
                    "`{}`: {block:?} uses {used:?}, not defined on every path to it",
                    lir.name
                );
            }
            defined.extend(instr.results.iter().copied());
        }
    }
}

/// The dominance check itself: a diamond whose join returns a value defined
/// on one arm only is rejected; its twin returning the entry's value passes.
fn diamond_returning(join_reads_arm_value: bool) -> LirFunction {
    let inst =
        |opcode, args: Vec<Value>, results: Vec<Value>| Instruction { opcode, args, results };
    let block = |instructions| LirBasicBlock { params: vec![], instructions, source_locs: vec![] };
    let mut f = LirFunction::new(
        "diamond",
        Signature { params: vec![LirType::I32], returns: vec![LirType::I32] },
    );
    f.entry_block = Block(0);
    f.blocks.insert(
        Block(0),
        block(vec![inst(
            Opcode::Brif { cond: Value(0), then_dest: Block(1), else_dest: Block(2) },
            vec![],
            vec![],
        )]),
    );
    f.blocks.insert(
        Block(1),
        block(vec![
            inst(Opcode::Iconst { ty: LirType::I32, imm: 7 }, vec![], vec![Value(1)]),
            inst(Opcode::Jump { dest: Block(3) }, vec![], vec![]),
        ]),
    );
    f.blocks.insert(Block(2), block(vec![inst(Opcode::Jump { dest: Block(3) }, vec![], vec![])]));
    let returned = if join_reads_arm_value { Value(1) } else { Value(0) };
    f.blocks.insert(Block(3), block(vec![inst(Opcode::Return, vec![returned], vec![])]));
    f
}

#[test]
#[should_panic(expected = "not defined on every path")]
fn dominance_check_rejects_a_value_defined_on_one_arm_only() {
    assert_defined_before_use_by_dominance(&diamond_returning(true));
}

#[test]
fn dominance_check_accepts_a_value_from_the_dominating_entry() {
    assert_defined_before_use_by_dominance(&diamond_returning(false));
}

/// Verify that the backend can emit metadata for an empty crate (zero functions).
/// This is a valid edge case that --emit=metadata must handle gracefully.
#[test]
fn test_emit_metadata_empty_crate() {
    let backend = TrustCgCodegenBackend::host();
    let crate_info = CrateInfo {
        crate_name: "empty_crate".to_string(),
        functions: vec![],
        linkage: Vec::new(),
        statics: Vec::new(),
    };

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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };

    let crate_info = CrateInfo {
        crate_name: "float_crate".to_string(),
        functions: vec![float_add],
        linkage: Vec::new(),
        statics: Vec::new(),
    };

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
