// trust-integration-tests/tests/pipeline_benchmark.rs: Verification pipeline profiling baseline
//
// Constructs a representative verification workload (200+ VCs from synthetic MIR)
// and measures VC generation per function and formula hashing, outputting results
// as JSON. Part of #670: Profile verification pipeline baseline before
// optimization.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::time::{Duration, Instant};

use trust_types::fx::FxHashSet;
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, Contract, ContractKind, Formula, LocalDecl, Operand,
    Place, Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, VerifiableBody,
    VerifiableFunction, VerificationCondition,
};

// ---------------------------------------------------------------------------
// Synthetic workload generators
// ---------------------------------------------------------------------------

/// Generate a function with a CheckedAdd that produces an ArithmeticOverflow VC.
fn make_overflow_function(name: &str, ty: Ty, _width: u32) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("bench::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![ty.clone(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: ty.clone(), name: None },
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
                        span: SourceSpan::default(),
                        unwind: trust_types::UnwindEdge::Unreachable,
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
            return_ty: ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Generate a function with a Div that produces a DivisionByZero VC.
fn make_division_function(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("bench::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
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
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Generate a function with an array index that produces an IndexOutOfBounds VC.
fn make_index_function(name: &str, array_len: usize) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("bench::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u32()), len: array_len as u64 },
                    name: Some("arr".into()),
                },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("idx".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Index(2)],
                        })),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Generate a function with a Rem that produces a RemainderByZero VC.
fn make_remainder_function(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("bench::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Rem,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Generate a function with a postcondition contract.
fn make_contract_function(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("bench::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
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
                        span: SourceSpan::default(),
                        unwind: trust_types::UnwindEdge::Unreachable,
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
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result <= 4294967295".to_string(),
        }],
        preconditions: vec![],
        postconditions: vec![Formula::Le(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(4_294_967_295)),
        )],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Generate a multi-block function with a CheckedMul producing multiple VCs.
fn make_multi_op_function(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("bench::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::u32(), name: None },
                LocalDecl { index: 5, ty: Ty::u32(), name: None },
            ],
            blocks: vec![
                BasicBlock {
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
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Mul),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
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
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(4)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
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
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Add a batch-unique precondition `Var("salt_<n>", Int) = <n>` to a function.
///
/// vcgen conjoins preconditions into every VC formula, so a per-batch
/// precondition keeps the SMT-LIB hash unique across otherwise-identical
/// functions and prevents the solver cache from collapsing them. The
/// constraint is a tautology in any reasonable model (no other formula
/// references `salt_<n>`), so it never changes verdict outcomes.
fn salt_preconditions(mut func: VerifiableFunction, salt: i128) -> VerifiableFunction {
    let salt_var = format!("__bench_salt_{salt}");
    func.preconditions.push(Formula::Eq(
        Box::new(Formula::Var(salt_var, Sort::Int)),
        Box::new(Formula::Int(salt)),
    ));
    func
}

// ---------------------------------------------------------------------------
// Benchmark workload construction
// ---------------------------------------------------------------------------

/// Representative benchmark scenario targeting 200+ VCs from 30+ functions.
///
/// Workload composition (mirrors realistic verification runs):
///   - 8 overflow functions (u8/u16/u32/u64 x Add/Mul) -> ~8 VCs
///   - 5 division-by-zero functions -> ~5 VCs
///   - 5 remainder-by-zero functions -> ~5 VCs
///   - 5 index-out-of-bounds functions (various array sizes) -> ~5 VCs
///   - 5 contract functions (with postconditions) -> ~10 VCs
///   - 5 multi-op functions (overflow + division) -> ~10 VCs
///
/// The workload is duplicated 5x with distinct names to reach 200+ VCs total,
/// simulating the VC count from verifying a medium-sized crate.
struct BenchmarkWorkload {
    functions: Vec<VerifiableFunction>,
}

impl BenchmarkWorkload {
    fn build() -> Self {
        let mut functions = Vec::new();

        // Generate diverse function variants across batches to reach the 200+
        // VC floor that the benchmark profiling assumes. Each batch produces
        // 10 functions × ~1.3 VCs/func ≈ 13 VCs, so 16 batches yields ~208
        // VCs. (Earlier vcgen revisions produced more VCs per function via
        // redundant overflow paths; that has since been pruned without
        // losing coverage, so the workload needs more functions to hit the
        // same density floor used for cache-hit-rate sampling.)
        //
        // Each function is also salted with a unique precondition so the VC
        // formulas differ across the workload (the hashing benchmark counts
        // distinct formula hashes).
        let mut salt: i128 = 0;
        let push = |functions: &mut Vec<VerifiableFunction>,
                    salt_ref: &mut i128,
                    func: VerifiableFunction| {
            functions.push(salt_preconditions(func, *salt_ref));
            *salt_ref += 1;
        };

        for batch in 0..16 {
            let prefix = format!("b{batch}");

            // Overflow: different integer widths
            push(
                &mut functions,
                &mut salt,
                make_overflow_function(&format!("{prefix}_add_u8"), Ty::u8(), 8),
            );
            push(
                &mut functions,
                &mut salt,
                make_overflow_function(&format!("{prefix}_add_u16"), Ty::u16(), 16),
            );
            push(
                &mut functions,
                &mut salt,
                make_overflow_function(&format!("{prefix}_add_u32"), Ty::u32(), 32),
            );
            push(
                &mut functions,
                &mut salt,
                make_overflow_function(&format!("{prefix}_add_u64"), Ty::usize(), 64),
            );

            // Division and remainder
            push(&mut functions, &mut salt, make_division_function(&format!("{prefix}_div")));
            push(&mut functions, &mut salt, make_remainder_function(&format!("{prefix}_rem")));

            // Array access with different sizes
            push(&mut functions, &mut salt, make_index_function(&format!("{prefix}_idx_10"), 10));
            push(&mut functions, &mut salt, make_index_function(&format!("{prefix}_idx_100"), 100));

            // Contracts (produce 2 VCs each: overflow + postcondition)
            push(&mut functions, &mut salt, make_contract_function(&format!("{prefix}_safe_add")));

            // Multi-op (produce 2 VCs each: overflow + div-by-zero)
            push(&mut functions, &mut salt, make_multi_op_function(&format!("{prefix}_mul_div")));
        }

        Self { functions }
    }

    fn function_count(&self) -> usize {
        self.functions.len()
    }
}

// ---------------------------------------------------------------------------
// Benchmark test
// ---------------------------------------------------------------------------

/// Profile per-function VC generation cost to identify outliers.
///
/// Measures VC generation time individually per function to answer
/// Open Question 1: "What is the typical VC count per function?"
#[test]
fn benchmark_per_function_vcgen() {
    let workload = BenchmarkWorkload::build();

    let mut vc_counts: Vec<(String, usize, Duration)> = Vec::new();

    for func in &workload.functions {
        let start = Instant::now();
        let vcs = trust_vcgen::generate_vcs(func);
        let duration = start.elapsed();
        vc_counts.push((func.name.clone(), vcs.len(), duration));
    }

    // Output per-function stats
    let entries: Vec<String> = vc_counts
        .iter()
        .map(|(name, count, dur)| {
            format!(
                r#"    {{ "function": "{}", "vc_count": {}, "duration_us": {} }}"#,
                name,
                count,
                dur.as_micros()
            )
        })
        .collect();

    let total_vcs: usize = vc_counts.iter().map(|(_, c, _)| c).sum();
    let total_dur: Duration = vc_counts.iter().map(|(_, _, d)| *d).sum();

    let json = format!(
        r#"{{
  "benchmark": "per_function_vcgen",
  "total_functions": {},
  "total_vcs": {},
  "total_duration_us": {},
  "avg_vcs_per_function": {:.1},
  "functions": [
{}
  ]
}}"#,
        workload.function_count(),
        total_vcs,
        total_dur.as_micros(),
        total_vcs as f64 / workload.function_count() as f64,
        entries.join(",\n"),
    );

    println!("\n{json}");

    // Verify VC count target
    assert!(total_vcs >= 200, "Should generate 200+ VCs, got {total_vcs}");

    eprintln!(
        "Per-function VCGen: {} functions, {} total VCs, avg {:.1} VCs/func",
        workload.function_count(),
        total_vcs,
        total_vcs as f64 / workload.function_count() as f64
    );
}

/// Measure formula hashing overhead (targeted at Optimization 3 baseline).
///
/// Measures the cost of the canonical query hash
/// (`trust_types::formula_hash::canonical_query_hash`) over every VC formula in
/// the workload, each the whole query of the in-process lane.
#[test]
fn benchmark_formula_hashing() {
    let workload = BenchmarkWorkload::build();

    let all_vcs: Vec<VerificationCondition> =
        workload.functions.iter().flat_map(trust_vcgen::generate_vcs).collect();

    let total_vcs = all_vcs.len();
    assert!(total_vcs >= 200);

    // Measure Debug-based formula hashing (current implementation)
    let hash_start = Instant::now();
    let mut hashes: Vec<String> = Vec::with_capacity(total_vcs);
    for vc in &all_vcs {
        hashes.push(
            trust_types::formula_hash::canonical_query_hash(&[&vc.formula])
                .expect("a generated VC formula serializes"),
        );
    }
    let hash_duration = hash_start.elapsed();

    // Measure SMT-LIB serialization cost (alternative hashing path)
    let smtlib_start = Instant::now();
    let mut smtlib_strs: Vec<String> = Vec::with_capacity(total_vcs);
    for vc in &all_vcs {
        smtlib_strs.push(vc.formula.to_smtlib());
    }
    let smtlib_duration = smtlib_start.elapsed();

    // Count unique hashes (to estimate cache collision potential)
    let unique_hashes: FxHashSet<&str> = hashes.iter().map(|s| s.as_str()).collect();

    let json = format!(
        r#"{{
  "benchmark": "formula_hashing",
  "total_vcs": {},
  "debug_hash": {{
    "total_us": {},
    "per_vc_us": {:.2}
  }},
  "smtlib_serialize": {{
    "total_us": {},
    "per_vc_us": {:.2}
  }},
  "unique_hashes": {},
  "collision_count": {}
}}"#,
        total_vcs,
        hash_duration.as_micros(),
        hash_duration.as_micros() as f64 / total_vcs as f64,
        smtlib_duration.as_micros(),
        smtlib_duration.as_micros() as f64 / total_vcs as f64,
        unique_hashes.len(),
        total_vcs - unique_hashes.len(),
    );

    println!("\n{json}");

    eprintln!("Formula hashing: {} VCs", total_vcs);
    eprintln!(
        "  Debug hash:    {}us total, {:.1}us/vc",
        hash_duration.as_micros(),
        hash_duration.as_micros() as f64 / total_vcs as f64
    );
    eprintln!(
        "  SMT-LIB ser:  {}us total, {:.1}us/vc",
        smtlib_duration.as_micros(),
        smtlib_duration.as_micros() as f64 / total_vcs as f64
    );
    eprintln!(
        "  Unique hashes: {} / {} ({}% unique)",
        unique_hashes.len(),
        total_vcs,
        (unique_hashes.len() as f64 / total_vcs as f64 * 100.0) as u32
    );
}
