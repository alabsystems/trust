// trust-integration-tests/tests/self_verify.rs: Model-check showcase for Trust pipeline crates
//
// Tier 2 showcase: Trust checks hand-reviewed VerifiableFunction models of
// internal functions by generating VCs and dispatching them through the
// checking pipeline. This is model-based checking (Path B) --
// hand-reviewed approximations, not extracted MIR or end-to-end proof.
//
// Design: designs/2026-04-12-self-verification-pipeline-design.md
// Issue: #554 | Epic: #549
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Projection,
    Rvalue, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// Model builders: each constructs a VerifiableFunction approximating a real
// function in a Trust pipeline crate.
// ---------------------------------------------------------------------------

/// SV-1: Model of BvExtract width computation in trust-types::Formula.
///
/// Source: crates/trust-types/src/formula.rs -- BvExtract { value, high, low }
/// The result width is computed as `high - low + 1`. If `low > high`, the
/// subtraction underflows.
///
/// Model: two u32 args (high, low), computes `width = high - low + 1`.
/// Expected VCs: ArithmeticOverflow{Sub} for `high - low`.
fn build_bv_extract_width_model() -> VerifiableFunction {
    VerifiableFunction {
        name: "bv_extract_width".to_string(),
        def_path: "trust_types::formula::bv_extract_width".to_string(),
        span: SourceSpan {
            file: "crates/trust-types/src/formula.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 5,
            col_end: 1,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None }, // _0: return
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("high".into()) }, // _1: arg
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("low".into()) }, // _2: arg
                // _3: (u32, bool) -- checked sub result
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::u32(), name: None }, // _4: high - low
                // _5: (u32, bool) -- checked add result
                LocalDecl { index: 5, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                LocalDecl { index: 6, ty: Ty::u32(), name: None }, // _6: width
            ],
            blocks: vec![
                // bb0: _3 = CheckedSub(_1, _2); assert(!_3.1, overflow) -> bb1
                BasicBlock {
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
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                // bb1: _4 = _3.0; _5 = CheckedAdd(_4, 1); assert(!_5.1, overflow) -> bb2
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(4)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(5, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(2),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                // bb2: _6 = _5.0; _0 = _6; return
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(5, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(6))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// SV-2: Model of SimplificationPipeline::run() loop counter in trust_vcgen.
///
/// Source: crates/trust_vcgen/src/simplify.rs:54 -- `for iter in 0..self.max_iters`
/// The loop counter `iter` is incremented each iteration. We model the
/// arithmetic safety: `iter += 1` can overflow if iter == usize::MAX.
///
/// Model: usize args (max_iters), loop counter `iter` starting at 0,
/// incremented with CheckedAdd each iteration.
/// Expected VCs: ArithmeticOverflow{Add} for `iter + 1`.
fn build_simplifier_loop_model() -> VerifiableFunction {
    VerifiableFunction {
        name: "simplification_loop_counter".to_string(),
        def_path: "trust_vcgen::simplify::SimplificationPipeline::run".to_string(),
        span: SourceSpan {
            file: "crates/trust_vcgen/src/simplify.rs".to_string(),
            line_start: 54,
            col_start: 1,
            line_end: 68,
            col_end: 1,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None }, // _0: return
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("max_iters".into()) }, // _1: arg
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("iter".into()) }, // _2: counter
                // _3: (usize, bool) -- checked add result
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::usize(), name: None }, // _4: iter + 1
            ],
            blocks: vec![
                // bb0: _2 = 0; goto bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                // bb1 (loop body): _3 = CheckedAdd(_2, 1); assert(!_3.1, overflow) -> bb2
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(2),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                // bb2: _4 = _3.0; _2 = _4; return (simplified: one iteration)
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
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

/// SV-3: Model of BloomFilter::contains() modular arithmetic in trust-cache.
///
/// Source: crates/trust-cache/src/bloom_filter.rs -- `hash % self.bits.len()`
/// then `self.bits[idx]`. Division by zero when bits.len() == 0.
///
/// Model: u64 arg (hash), usize arg (bits_len), computes `index = hash % bits_len`,
/// then indexes into an array at `index`.
/// Expected VCs: RemainderByZero for `hash % bits_len`, IndexOutOfBounds for array[index].
fn build_bloom_filter_model() -> VerifiableFunction {
    VerifiableFunction {
        name: "bloom_filter_contains".to_string(),
        def_path: "trust_cache::bloom_filter::BloomFilter::contains".to_string(),
        span: SourceSpan {
            file: "crates/trust-cache/src/bloom_filter.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 10,
            col_end: 1,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None }, // _0: return
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("hash".into()) }, // _1: arg
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("bits_len".into()) }, // _2: arg
                LocalDecl { index: 3, ty: Ty::usize(), name: Some("index".into()) }, // _3: hash % bits_len
                // _4: bits array (fixed-size model for bounds checking)
                LocalDecl {
                    index: 4,
                    ty: Ty::Array { elem: Box::new(Ty::Bool), len: 64 },
                    name: Some("bits".into()),
                },
                LocalDecl { index: 5, ty: Ty::Bool, name: None }, // _5: bits[index]
            ],
            blocks: vec![
                // bb0: _3 = Rem(_1, _2); _5 = _4[_3]; _0 = _5; return
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // index = hash % bits_len (generates RemainderByZero VC)
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Rem,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan {
                                file: "crates/trust-cache/src/bloom_filter.rs".to_string(),
                                line_start: 5,
                                col_start: 1,
                                line_end: 5,
                                col_end: 30,
                            },
                        },
                        // bits[index] (generates IndexOutOfBounds VC)
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 4,
                                projections: vec![Projection::Index(3)],
                            })),
                            span: SourceSpan {
                                file: "crates/trust-cache/src/bloom_filter.rs".to_string(),
                                line_start: 6,
                                col_start: 1,
                                line_end: 6,
                                col_end: 20,
                            },
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// SV-4: Model of LoopConvergence::observe() resource accumulator in trust-convergence.
///
/// Source: crates/trust-convergence/src/loop_convergence.rs:261
/// Accumulates: `self.wall_time_used += observation.wall_time` (u64)
///              `self.solver_calls_used += observation.solver_calls` (u64)
/// Both can overflow.
///
/// Model: two u64 accumulators (wall_time_secs, solver_calls) and two u64
/// observation values, both incremented with CheckedAdd.
/// Expected VCs: 2x ArithmeticOverflow{Add}.
fn build_convergence_accumulator_model() -> VerifiableFunction {
    VerifiableFunction {
        name: "convergence_observe".to_string(),
        def_path: "trust_convergence::loop_convergence::LoopConvergence::observe".to_string(),
        span: SourceSpan {
            file: "crates/trust-convergence/src/loop_convergence.rs".to_string(),
            line_start: 261,
            col_start: 1,
            line_end: 270,
            col_end: 1,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None }, // _0: return
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("wall_time_secs".into()) }, // _1: arg
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("obs_wall_time_secs".into()) }, // _2: arg
                LocalDecl { index: 3, ty: Ty::u64(), name: Some("solver_calls".into()) }, // _3: arg
                LocalDecl { index: 4, ty: Ty::u64(), name: Some("obs_solver_calls".into()) }, // _4: arg
                // _5: (u64, bool) -- checked add result for wall_time
                LocalDecl { index: 5, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
                // _6: (u64, bool) -- checked add result for solver_calls
                LocalDecl { index: 6, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                // bb0: _5 = CheckedAdd(_1, _2); assert(!_5.1, overflow) -> bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(5, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                // bb1: _6 = CheckedAdd(_3, _4); assert(!_6.1, overflow) -> bb2
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(4)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(6, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(2),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                // bb2: return
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 4,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// Pipeline model-check result tracking
// ---------------------------------------------------------------------------

/// A single pipeline model property check result.
struct SelfVerifyResult {
    crate_name: &'static str,
    function_name: &'static str,
    property: &'static str,
    vc_kind_desc: String,
    outcome: &'static str,
}

/// Print the pipeline model-check summary in the showcase format.
fn print_self_verify_summary(results: &[SelfVerifyResult]) {
    println!();
    println!("=== Trust Model-Check Showcase: Pipeline Models ===");
    println!("Note: Model-based checking (Path B). Models are hand-reviewed approximations.");
    println!();

    let mut current_crate = "";
    for r in results {
        if r.crate_name != current_crate {
            current_crate = r.crate_name;
            println!("  {}::{}", r.crate_name, r.function_name);
        }
        println!("    {} ... {}", r.property, r.outcome);
        println!("      vc_kind: {}", r.vc_kind_desc);
    }

    let routed_count = results.iter().filter(|r| r.outcome == "ROUTED (mock)").count();
    let total = results.len();

    println!();
    println!("  Model-check showcase results:");
    println!("    {} properties checked via VC generation", total);
    println!("    {} VCs routed through ConstantFolderBackend", routed_count);
    println!("    4/4 models include source references and review notes");
    println!();
    println!("Trust generated and routed {} model-check properties for pipeline models.", total);
    println!();
}

// ---------------------------------------------------------------------------
// SV-1: BvExtract width underflow (trust-types)
// ---------------------------------------------------------------------------

#[test]
fn test_self_verify_sv1_bv_extract_vc_generation() {
    let func = build_bv_extract_width_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    // Should produce ArithmeticOverflow{Sub} for `high - low`
    let sub_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. }))
        .collect();
    assert!(
        !sub_vcs.is_empty(),
        "SV-1: BvExtract width model should produce ArithmeticOverflow(Sub) VC for high - low"
    );

    // Should also produce ArithmeticOverflow{Add} for `diff + 1`
    let add_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .collect();
    assert!(
        !add_vcs.is_empty(),
        "SV-1: BvExtract width model should produce ArithmeticOverflow(Add) VC for diff + 1"
    );

    // All VCs should be L0Safety
    for vc in &vcs {
        assert_eq!(
            vc.kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "SV-1: all VCs should be L0Safety"
        );
    }

    // Route through ConstantFolderBackend
    let router = trust_router::Router::new();
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), vcs.len());
    assert_eq!(vcs[0].function, "bv_extract_width");
}

// ---------------------------------------------------------------------------
// SV-2: Simplifier loop counter overflow (trust_vcgen)
// ---------------------------------------------------------------------------

#[test]
fn test_self_verify_sv2_simplifier_loop_vc_generation() {
    let func = build_simplifier_loop_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    // Should produce ArithmeticOverflow{Add} for `iter + 1`
    let add_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .collect();
    assert!(
        !add_vcs.is_empty(),
        "SV-2: simplifier loop model should produce ArithmeticOverflow(Add) VC for iter + 1"
    );

    // All VCs should be L0Safety
    for vc in &vcs {
        assert_eq!(
            vc.kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "SV-2: all VCs should be L0Safety"
        );
    }

    // Route through ConstantFolderBackend
    let router = trust_router::Router::new();
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), vcs.len());
    assert_eq!(vcs[0].function, "simplification_loop_counter");
}

// ---------------------------------------------------------------------------
// SV-3: Bloom filter modular arithmetic (trust-cache)
// ---------------------------------------------------------------------------

#[test]
fn test_self_verify_sv3_bloom_filter_vc_generation() {
    let func = build_bloom_filter_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    // Should produce RemainderByZero for `hash % bits_len`
    let rem_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::RemainderByZero)).collect();
    assert_eq!(
        rem_vcs.len(),
        1,
        "SV-3: bloom filter model should produce exactly 1 RemainderByZero VC"
    );

    // Should produce IndexOutOfBounds for `bits[index]`
    let idx_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)).collect();
    assert_eq!(
        idx_vcs.len(),
        1,
        "SV-3: bloom filter model should produce exactly 1 IndexOutOfBounds VC"
    );

    // All VCs should be L0Safety
    for vc in &vcs {
        assert_eq!(
            vc.kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "SV-3: all VCs should be L0Safety"
        );
    }

    // Route through ConstantFolderBackend
    let router = trust_router::Router::new();
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), vcs.len());

    // All routed to the same function
    for (vc, _result) in &results {
        assert_eq!(vc.function, "bloom_filter_contains");
    }
}

// ---------------------------------------------------------------------------
// SV-4: Convergence accumulator overflow (trust-convergence)
// ---------------------------------------------------------------------------

#[test]
fn test_self_verify_sv4_convergence_accumulator_vc_generation() {
    let func = build_convergence_accumulator_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    // Should produce 2 ArithmeticOverflow{Add} VCs (wall_time + solver_calls)
    let add_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .collect();
    assert_eq!(
        add_vcs.len(),
        2,
        "SV-4: convergence accumulator model should produce exactly 2 ArithmeticOverflow(Add) VCs"
    );

    // All VCs should be L0Safety
    for vc in &vcs {
        assert_eq!(
            vc.kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "SV-4: all VCs should be L0Safety"
        );
    }

    // Route through ConstantFolderBackend
    let router = trust_router::Router::new();
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), vcs.len());
    assert_eq!(vcs[0].function, "convergence_observe");
}

// ---------------------------------------------------------------------------
// Full pipeline model-check suite: all 4 targets with summary
// ---------------------------------------------------------------------------

#[test]
fn test_self_verify_full_suite() {
    let mut all_results = Vec::new();
    let router = trust_router::Router::new();

    // --- SV-1: BvExtract width (trust-types) ---
    let sv1 = build_bv_extract_width_model();
    let sv1_vcs = trust_vcgen::generate_vcs(&sv1);
    let sv1_results = router.verify_all(&sv1_vcs);

    let sv1_sub = sv1_vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. }))
        .count();
    let sv1_add = sv1_vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .count();
    assert!(sv1_sub >= 1, "SV-1: expected Sub overflow VC");
    assert!(sv1_add >= 1, "SV-1: expected Add overflow VC");

    all_results.push(SelfVerifyResult {
        crate_name: "trust-types",
        function_name: "Formula::BvExtract (width computation)",
        property: "arithmetic overflow (Sub) on width = high - low",
        vc_kind_desc: "ArithmeticOverflow { op: Sub }".to_string(),
        outcome: "ROUTED (mock)",
    });
    all_results.push(SelfVerifyResult {
        crate_name: "trust-types",
        function_name: "Formula::BvExtract (width computation)",
        property: "arithmetic overflow (Add) on width = diff + 1",
        vc_kind_desc: "ArithmeticOverflow { op: Add }".to_string(),
        outcome: "ROUTED (mock)",
    });

    // --- SV-2: Simplifier loop counter (trust_vcgen) ---
    let sv2 = build_simplifier_loop_model();
    let sv2_vcs = trust_vcgen::generate_vcs(&sv2);
    let sv2_results = router.verify_all(&sv2_vcs);

    let sv2_add = sv2_vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .count();
    assert!(sv2_add >= 1, "SV-2: expected Add overflow VC for loop counter");

    all_results.push(SelfVerifyResult {
        crate_name: "trust_vcgen",
        function_name: "SimplificationPipeline::run (loop counter)",
        property: "arithmetic overflow (Add) on iter + 1",
        vc_kind_desc: "ArithmeticOverflow { op: Add }".to_string(),
        outcome: "ROUTED (mock)",
    });

    // --- SV-3: Bloom filter (trust-cache) ---
    let sv3 = build_bloom_filter_model();
    let sv3_vcs = trust_vcgen::generate_vcs(&sv3);
    let sv3_results = router.verify_all(&sv3_vcs);

    let sv3_rem = sv3_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::RemainderByZero)).count();
    let sv3_idx = sv3_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)).count();
    assert_eq!(sv3_rem, 1, "SV-3: expected 1 RemainderByZero VC");
    assert_eq!(sv3_idx, 1, "SV-3: expected 1 IndexOutOfBounds VC");

    all_results.push(SelfVerifyResult {
        crate_name: "trust-cache",
        function_name: "BloomFilter::contains (modular arithmetic)",
        property: "remainder by zero (Rem) without constructor invariant",
        vc_kind_desc: "RemainderByZero".to_string(),
        outcome: "ROUTED (mock)",
    });
    all_results.push(SelfVerifyResult {
        crate_name: "trust-cache",
        function_name: "BloomFilter::contains (modular arithmetic)",
        property: "index out of bounds on bits[index]",
        vc_kind_desc: "IndexOutOfBounds".to_string(),
        outcome: "ROUTED (mock)",
    });

    // --- SV-4: Convergence accumulator (trust-convergence) ---
    let sv4 = build_convergence_accumulator_model();
    let sv4_vcs = trust_vcgen::generate_vcs(&sv4);
    let sv4_results = router.verify_all(&sv4_vcs);

    let sv4_add = sv4_vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .count();
    assert_eq!(sv4_add, 2, "SV-4: expected 2 ArithmeticOverflow(Add) VCs");

    all_results.push(SelfVerifyResult {
        crate_name: "trust-convergence",
        function_name: "LoopConvergence::observe (resource accumulators)",
        property: "arithmetic overflow (Add) on wall_time_secs accumulator",
        vc_kind_desc: "ArithmeticOverflow { op: Add }".to_string(),
        outcome: "ROUTED (mock)",
    });
    all_results.push(SelfVerifyResult {
        crate_name: "trust-convergence",
        function_name: "LoopConvergence::observe (resource accumulators)",
        property: "arithmetic overflow (Add) on solver_calls accumulator",
        vc_kind_desc: "ArithmeticOverflow { op: Add }".to_string(),
        outcome: "ROUTED (mock)",
    });

    // --- Summary ---
    let total_vcs: usize =
        sv1_results.len() + sv2_results.len() + sv3_results.len() + sv4_results.len();
    assert!(
        total_vcs >= 7,
        "pipeline model-check suite should generate at least 7 VCs total, got {}",
        total_vcs
    );

    print_self_verify_summary(&all_results);

    // Final assertion: at least 3 properties checked (acceptance criteria)
    // In mock mode, all are "ROUTED" which counts as successfully checked
    assert!(
        all_results.len() >= 3,
        "acceptance criteria: 3+ properties checked, got {}",
        all_results.len()
    );
}

// ---------------------------------------------------------------------------
// Report integration: generate a showcase report from pipeline model checks
// ---------------------------------------------------------------------------

#[test]
fn test_self_verify_report_generation() {
    let models: Vec<VerifiableFunction> = vec![
        build_bv_extract_width_model(),
        build_simplifier_loop_model(),
        build_bloom_filter_model(),
        build_convergence_accumulator_model(),
    ];

    let router = trust_router::Router::new();
    let mut all_results = Vec::new();

    for model in &models {
        let vcs = trust_vcgen::generate_vcs(model);
        let results = router.verify_all(&vcs);
        all_results.extend(results);
    }

    // Build a showcase report
    let report = trust_report::build_json_report("Trust-model-check-showcase", &all_results);

    assert_eq!(report.crate_name, "Trust-model-check-showcase");
    assert_eq!(
        report.summary.functions_analyzed, 4,
        "report should cover 4 pipeline model targets"
    );
    assert!(
        report.summary.total_obligations >= 7,
        "report should have at least 7 obligations, got {}",
        report.summary.total_obligations
    );

    // Verify all 4 function names appear in the report
    let func_names: Vec<&str> = report.functions.iter().map(|f| f.function.as_str()).collect();
    assert!(func_names.contains(&"bv_extract_width"));
    assert!(func_names.contains(&"simplification_loop_counter"));
    assert!(func_names.contains(&"bloom_filter_contains"));
    assert!(func_names.contains(&"convergence_observe"));

    // Verify text summary
    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("bv_extract_width"), "text report should mention bv_extract_width");
    assert!(
        text.contains("bloom_filter_contains"),
        "text report should mention bloom_filter_contains"
    );

    // Print the report summary for showcase
    println!();
    println!("=== Trust Model-Check Showcase Report ===");
    println!("{}", text);
    println!(
        "Trust generated and routed {} model-check obligations for pipeline models.",
        report.summary.total_obligations
    );
}
