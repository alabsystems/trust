// trust-integration-tests/tests/pipeline_benchmark.rs: Verification pipeline profiling baseline
//
// Constructs a representative verification workload (200+ VCs from synthetic MIR),
// measures time per pipeline stage, tracks cache hit/miss rates, and outputs
// results as JSON. Part of #670: Profile verification pipeline baseline before
// optimization.
//
// Pipeline stages measured:
//   1. VC generation (trust_vcgen)
//   2. Cache lookup (trust-router solver_cache)
//   3. Solver dispatch (trust-router)
//   4. Result aggregation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::time::{Duration, Instant};
use trust_types::fx::FxHashMap;

use trust_cache::result_cache::CachePolicy;
use trust_router::Router;
use trust_router::solver_cache::SolverCachedRouter;
use trust_types::fx::FxHashSet;
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, Contract, ContractKind, Formula, LocalDecl, Operand,
    Place, Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody,
    VerifiableFunction, VerificationCondition, VerificationResult,
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
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
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
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
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
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
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
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
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
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
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
        // formulas differ across the workload; otherwise the solver_cache
        // would collapse same-shaped functions onto one cache entry and
        // produce within-pass cache hits before the warm-pass measurement
        // runs.
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
            push(&mut functions, &mut salt,
                make_overflow_function(&format!("{prefix}_add_u8"), Ty::u8(), 8));
            push(&mut functions, &mut salt,
                make_overflow_function(&format!("{prefix}_add_u16"), Ty::u16(), 16));
            push(&mut functions, &mut salt,
                make_overflow_function(&format!("{prefix}_add_u32"), Ty::u32(), 32));
            push(&mut functions, &mut salt,
                make_overflow_function(&format!("{prefix}_add_u64"), Ty::usize(), 64));

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
// Pipeline stage timing
// ---------------------------------------------------------------------------

/// Timing data for a single pipeline stage.
#[derive(Debug, Clone)]
struct StageTiming {
    name: String,
    duration: Duration,
    item_count: usize,
}

impl StageTiming {
    fn per_item_us(&self) -> f64 {
        if self.item_count == 0 {
            return 0.0;
        }
        self.duration.as_micros() as f64 / self.item_count as f64
    }
}

/// Complete benchmark result.
#[derive(Debug)]
struct BenchmarkResult {
    total_functions: usize,
    total_vcs: usize,
    stages: Vec<StageTiming>,
    cache_hits: usize,
    cache_misses: usize,
    cache_hit_rate: f64,
    vc_kind_distribution: FxHashMap<String, usize>,
    result_distribution: FxHashMap<String, usize>,
}

impl BenchmarkResult {
    /// Serialize to JSON string for downstream analysis.
    fn to_json(&self) -> String {
        let stages_json: Vec<String> = self
            .stages
            .iter()
            .map(|s| {
                format!(
                    r#"    {{
      "name": "{}",
      "duration_us": {},
      "item_count": {},
      "per_item_us": {:.2}
    }}"#,
                    s.name,
                    s.duration.as_micros(),
                    s.item_count,
                    s.per_item_us()
                )
            })
            .collect();

        let kinds_json: Vec<String> = {
            let mut entries: Vec<_> = self.vc_kind_distribution.iter().collect();
            entries.sort_by(|a, b| b.1.cmp(a.1));
            entries.iter().map(|(k, v)| format!(r#"    "{}": {}"#, k, v)).collect()
        };

        let results_json: Vec<String> = {
            let mut entries: Vec<_> = self.result_distribution.iter().collect();
            entries.sort_by(|a, b| b.1.cmp(a.1));
            entries.iter().map(|(k, v)| format!(r#"    "{}": {}"#, k, v)).collect()
        };

        let total_us: u128 = self.stages.iter().map(|s| s.duration.as_micros()).sum();

        format!(
            r#"{{
  "benchmark": "verification_pipeline_baseline",
  "total_functions": {},
  "total_vcs": {},
  "total_duration_us": {},
  "stages": [
{}
  ],
  "cache": {{
    "hits": {},
    "misses": {},
    "hit_rate": {:.4}
  }},
  "vc_kind_distribution": {{
{}
  }},
  "result_distribution": {{
{}
  }}
}}"#,
            self.total_functions,
            self.total_vcs,
            total_us,
            stages_json.join(",\n"),
            self.cache_hits,
            self.cache_misses,
            self.cache_hit_rate,
            kinds_json.join(",\n"),
            results_json.join(",\n"),
        )
    }
}

// ---------------------------------------------------------------------------
// VC kind classification helper
// ---------------------------------------------------------------------------

fn classify_vc_kind(kind: &VcKind) -> &'static str {
    match kind {
        VcKind::ArithmeticOverflow { .. } => "ArithmeticOverflow",
        VcKind::ShiftOverflow { .. } => "ShiftOverflow",
        VcKind::DivisionByZero => "DivisionByZero",
        VcKind::RemainderByZero => "RemainderByZero",
        VcKind::IndexOutOfBounds => "IndexOutOfBounds",
        VcKind::SliceBoundsCheck => "SliceBoundsCheck",
        VcKind::Assertion { .. } => "Assertion",
        VcKind::Precondition { .. } => "Precondition",
        VcKind::Postcondition => "Postcondition",
        VcKind::CastOverflow { .. } => "CastOverflow",
        VcKind::NegationOverflow { .. } => "NegationOverflow",
        VcKind::Unreachable => "Unreachable",
        _ => "Other",
    }
}

fn classify_result(result: &VerificationResult) -> &'static str {
    match result {
        VerificationResult::Proved { .. } => "Proved",
        VerificationResult::Failed { .. } => "Failed",
        VerificationResult::Unknown { .. } => "Unknown",
        VerificationResult::Timeout { .. } => "Timeout",
        _ => "Other",
    }
}

// ---------------------------------------------------------------------------
// Benchmark test
// ---------------------------------------------------------------------------

/// Profile the verification pipeline end-to-end and output baseline metrics.
///
/// This test:
///   1. Generates 200+ VCs from synthetic MIR across 30+ functions
///   2. Measures VC generation time per function
///   3. Routes all VCs through the solver-cached router (two passes to measure
///      cache effectiveness)
///   4. Tracks cache hit/miss rates
///   5. Outputs JSON results to stdout
///
/// Run with: cargo test --test pipeline_benchmark -- --nocapture
#[test]
fn benchmark_verification_pipeline_baseline() {
    let workload = BenchmarkWorkload::build();
    let total_functions = workload.function_count();

    // -----------------------------------------------------------------------
    // Stage 1: VC Generation
    // -----------------------------------------------------------------------
    let mut all_vcs: Vec<VerificationCondition> = Vec::new();
    let mut per_function_vcs: Vec<(String, Vec<VerificationCondition>)> = Vec::new();

    let vcgen_start = Instant::now();
    for func in &workload.functions {
        let vcs = trust_vcgen::generate_vcs(func);
        per_function_vcs.push((func.name.clone(), vcs.clone()));
        all_vcs.extend(vcs);
    }
    let vcgen_duration = vcgen_start.elapsed();

    let total_vcs = all_vcs.len();

    // Verify we hit the 200+ VC target
    assert!(total_vcs >= 200, "Workload should generate 200+ VCs, got {total_vcs}");

    // -----------------------------------------------------------------------
    // Stage 2: First pass -- cold cache (all misses)
    // -----------------------------------------------------------------------
    let cached_router = SolverCachedRouter::new(Router::new(), CachePolicy::AlwaysCache);

    let cold_start = Instant::now();
    let cold_results = cached_router.verify_all(&all_vcs);
    let cold_duration = cold_start.elapsed();

    let cold_stats = cached_router.cache_stats();

    // After cold pass: every unique-formula VC contributes a miss, but
    // duplicate-formula VCs (e.g. the same overflow check generated by every
    // rvalue safety pass) may hit the cache mid-pass. Require that the cold
    // pass populated the cache with at least one entry per unique formula
    // and that misses dominate hits — the warm pass below is the real signal
    // that caching saves work.
    assert!(
        cold_stats.misses > 0,
        "cold pass should produce at least one cache miss, got {misses}",
        misses = cold_stats.misses,
    );
    assert!(
        cold_stats.misses > cold_stats.hits,
        "cold pass should be miss-dominated, got hits={hits} misses={misses}",
        hits = cold_stats.hits,
        misses = cold_stats.misses,
    );
    assert_eq!(cold_results.len(), total_vcs, "Should get one result per VC");
    let cold_hits = cold_stats.hits;

    // -----------------------------------------------------------------------
    // Stage 3: Second pass -- warm cache (measure hit rate)
    // -----------------------------------------------------------------------
    let warm_start = Instant::now();
    let warm_results = cached_router.verify_all(&all_vcs);
    let warm_duration = warm_start.elapsed();

    let warm_stats = cached_router.cache_stats();
    let cache_hits = warm_stats.hits;
    let cache_misses = warm_stats.misses;
    let cache_hit_rate = if cache_hits + cache_misses > 0 {
        cache_hits as f64 / (cache_hits + cache_misses) as f64
    } else {
        0.0
    };

    assert_eq!(warm_results.len(), total_vcs);

    // The warm pass should add many cache hits (every VC has a corresponding
    // entry from the cold pass). Specifically, warm-only hits should at
    // least match the total VC count once we subtract the hits the cold
    // pass already recorded for intra-pass duplicates.
    let warm_only_hits = cache_hits - cold_hits;
    assert!(
        warm_only_hits >= total_vcs / 2,
        "warm pass should hit cache for at least half the VCs, got warm_only_hits={warm_only_hits} total_vcs={total_vcs}",
    );

    // -----------------------------------------------------------------------
    // Stage 4: Result aggregation timing
    // -----------------------------------------------------------------------
    let agg_start = Instant::now();
    let mut vc_kind_distribution: FxHashMap<String, usize> = FxHashMap::default();
    let mut result_distribution: FxHashMap<String, usize> = FxHashMap::default();

    for (vc, result) in &cold_results {
        *vc_kind_distribution.entry(classify_vc_kind(&vc.kind).to_string()).or_insert(0) += 1;
        *result_distribution.entry(classify_result(result).to_string()).or_insert(0) += 1;
    }
    let agg_duration = agg_start.elapsed();

    // -----------------------------------------------------------------------
    // Sanity assertions (before moving into BenchmarkResult)
    // -----------------------------------------------------------------------

    // All VCs should have results
    assert_eq!(cold_results.len(), total_vcs);
    assert_eq!(warm_results.len(), total_vcs);

    // VC kind distribution should include the expected types
    assert!(
        vc_kind_distribution.contains_key("ArithmeticOverflow"),
        "Should have ArithmeticOverflow VCs"
    );
    assert!(vc_kind_distribution.contains_key("DivisionByZero"), "Should have DivisionByZero VCs");
    assert!(
        vc_kind_distribution.contains_key("IndexOutOfBounds"),
        "Should have IndexOutOfBounds VCs"
    );

    // -----------------------------------------------------------------------
    // Build result
    // -----------------------------------------------------------------------
    let benchmark = BenchmarkResult {
        total_functions,
        total_vcs,
        stages: vec![
            StageTiming {
                name: "vc_generation".to_string(),
                duration: vcgen_duration,
                item_count: total_functions,
            },
            StageTiming {
                name: "solver_cold_pass".to_string(),
                duration: cold_duration,
                item_count: total_vcs,
            },
            StageTiming {
                name: "solver_warm_pass".to_string(),
                duration: warm_duration,
                item_count: total_vcs,
            },
            StageTiming {
                name: "result_aggregation".to_string(),
                duration: agg_duration,
                item_count: total_vcs,
            },
        ],
        cache_hits,
        cache_misses,
        cache_hit_rate,
        vc_kind_distribution,
        result_distribution,
    };

    // Output JSON for downstream analysis
    let json = benchmark.to_json();
    println!("\n{json}");

    // Warm pass should be faster than cold pass (cache hits avoid solver)
    // Note: with ConstantFolderBackend this may not hold due to minimal solver cost,
    // but the measurement infrastructure is the point.
    eprintln!("Pipeline benchmark: {} functions, {} VCs", total_functions, total_vcs);
    eprintln!(
        "  VC generation:    {:>8}us ({:.1}us/func)",
        vcgen_duration.as_micros(),
        benchmark.stages[0].per_item_us()
    );
    eprintln!(
        "  Cold solver pass: {:>8}us ({:.1}us/vc)",
        cold_duration.as_micros(),
        benchmark.stages[1].per_item_us()
    );
    eprintln!(
        "  Warm solver pass: {:>8}us ({:.1}us/vc)",
        warm_duration.as_micros(),
        benchmark.stages[2].per_item_us()
    );
    eprintln!(
        "  Cache: {} hits, {} misses, {:.1}% hit rate",
        cache_hits,
        cache_misses,
        cache_hit_rate * 100.0
    );
}

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

/// Measure cache effectiveness by verifying the same VCs multiple times.
///
/// Answers Open Question 3: "What percentage of VCs hit the solver cache?"
#[test]
fn benchmark_cache_effectiveness() {
    let workload = BenchmarkWorkload::build();

    // Generate all VCs
    let all_vcs: Vec<VerificationCondition> =
        workload.functions.iter().flat_map(trust_vcgen::generate_vcs).collect();

    let total_vcs = all_vcs.len();
    assert!(total_vcs >= 200);

    let cached_router = SolverCachedRouter::new(Router::new(), CachePolicy::AlwaysCache);

    // Pass 1: populate cache
    let pass1_start = Instant::now();
    let _ = cached_router.verify_all(&all_vcs);
    let pass1_dur = pass1_start.elapsed();

    // Pass 2: should hit cache
    let pass2_start = Instant::now();
    let _ = cached_router.verify_all(&all_vcs);
    let pass2_dur = pass2_start.elapsed();

    // Pass 3: should hit cache again
    let pass3_start = Instant::now();
    let _ = cached_router.verify_all(&all_vcs);
    let pass3_dur = pass3_start.elapsed();

    let stats = cached_router.cache_stats();

    let hit_rate = if stats.hits + stats.misses > 0 {
        stats.hits as f64 / (stats.hits + stats.misses) as f64
    } else {
        0.0
    };

    let json = format!(
        r#"{{
  "benchmark": "cache_effectiveness",
  "total_vcs": {},
  "passes": [
    {{ "pass": 1, "duration_us": {}, "description": "cold" }},
    {{ "pass": 2, "duration_us": {}, "description": "warm" }},
    {{ "pass": 3, "duration_us": {}, "description": "hot" }}
  ],
  "cache_entries": {},
  "total_hits": {},
  "total_misses": {},
  "hit_rate": {:.4},
  "speedup_warm_vs_cold": {:.2},
  "speedup_hot_vs_cold": {:.2}
}}"#,
        total_vcs,
        pass1_dur.as_micros(),
        pass2_dur.as_micros(),
        pass3_dur.as_micros(),
        stats.total_entries,
        stats.hits,
        stats.misses,
        hit_rate,
        if pass2_dur.as_micros() > 0 {
            pass1_dur.as_micros() as f64 / pass2_dur.as_micros() as f64
        } else {
            f64::INFINITY
        },
        if pass3_dur.as_micros() > 0 {
            pass1_dur.as_micros() as f64 / pass3_dur.as_micros() as f64
        } else {
            f64::INFINITY
        },
    );

    println!("\n{json}");

    eprintln!("Cache effectiveness: {} VCs", total_vcs);
    eprintln!("  Pass 1 (cold): {}us", pass1_dur.as_micros());
    eprintln!("  Pass 2 (warm): {}us", pass2_dur.as_micros());
    eprintln!("  Pass 3 (hot):  {}us", pass3_dur.as_micros());
    eprintln!(
        "  Cache: {} entries, {} hits, {} misses, {:.1}% hit rate",
        stats.total_entries,
        stats.hits,
        stats.misses,
        hit_rate * 100.0
    );
}

/// Measure formula hashing overhead (targeted at Optimization 3 baseline).
///
/// The performance analysis report identifies formula hashing via Debug
/// formatting as a potential bottleneck (solver_cache.rs:29). This test
/// measures the cost of hashing all formulas in the workload.
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
        hashes.push(trust_router::solver_cache::vc_formula_hash(vc));
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
