// trust-integration-tests/tests/verification_time_overhead.rs: Verification time overhead benchmarks
//
// Measures verification time overhead across pipeline stages using MirRouter,
// build_v1_vcs, and trust_vcgen::generate_vcs. Part of #944: Benchmark
// verification time overhead on real Rust crates.
//
// Pipeline stages measured:
//   1. MIR classification (MirRouter::classify)
//   2. VC generation (build_v1_vcs + trust_vcgen::generate_vcs)
//   3. Full MirRouter verification (classify + dispatch)
//   4. Scaling analysis (1 to 60 functions)
//
// Run with: cargo test -p trust-integration-tests --test verification_time_overhead -- --nocapture
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::time::{Duration, Instant};
use trust_types::fx::FxHashMap;

use trust_router::{MirRouter, MirRouterConfig, MirStrategy, Router, build_v1_vcs};
use trust_types::VerifiableFunction;

// ---------------------------------------------------------------------------
// Workload construction
// ---------------------------------------------------------------------------

/// Build a workload of `count` functions by cycling through the 5 fixture functions.
fn build_workload(count: usize) -> Vec<VerifiableFunction> {
    let fixtures = [trust_integration_tests::midpoint_function(),
        trust_integration_tests::division_function(),
        trust_integration_tests::array_access_function(),
        trust_integration_tests::contract_function(),
        trust_integration_tests::noop_function()];
    let mut funcs = Vec::with_capacity(count);
    for i in 0..count {
        let mut f = fixtures[i % fixtures.len()].clone();
        f.name = format!("{}_batch_{}", f.name, i);
        f.def_path = format!("{}_batch_{}", f.def_path, i);
        funcs.push(f);
    }
    funcs
}

/// Create a MirRouter with benchmark-appropriate config (fast timeouts, no proofs).
fn benchmark_router() -> MirRouter {
    let config = MirRouterConfig {
        bmc_depth: 10,
        timeout_ms: 5_000,
        produce_proofs: false,
        shadow_mode: false,
        enable_portfolio_racing: false,
        infer_invariants: false,
    };
    MirRouter::new(Router::new(), config)
}

// ---------------------------------------------------------------------------
// Test 1: MirRouter classification overhead
// ---------------------------------------------------------------------------

/// Measure MirRouter::classify overhead at multiple workload sizes.
///
/// Classification is the first pipeline stage: it examines MIR properties
/// (contracts, unsafe blocks, loops, atomics, raw pointers, FFI) to select
/// a verification strategy. This should be microsecond-cheap per function.
#[test]
fn benchmark_mir_router_classification_overhead() {
    let router = benchmark_router();
    let scales = [1, 5, 10, 30, 60];
    let mut results: Vec<(usize, Duration, FxHashMap<String, usize>)> = Vec::new();

    for &count in &scales {
        let workload = build_workload(count);

        let start = Instant::now();
        let mut strategy_counts: FxHashMap<String, usize> = FxHashMap::default();
        for func in &workload {
            let strategy = router.classify(func);
            *strategy_counts.entry(format!("{strategy}")).or_insert(0) += 1;
        }
        let duration = start.elapsed();

        results.push((count, duration, strategy_counts));
    }

    // Output JSON
    let entries: Vec<String> = results
        .iter()
        .map(|(count, dur, strategies)| {
            let strategy_json: Vec<String> = {
                let mut entries: Vec<_> = strategies.iter().collect();
                entries.sort_by(|a, b| b.1.cmp(a.1));
                entries.iter().map(|(k, v)| format!(r#"        "{}": {}"#, k, v)).collect()
            };
            format!(
                r#"    {{
      "function_count": {},
      "total_us": {},
      "per_function_us": {:.2},
      "strategies": {{
{}
      }}
    }}"#,
                count,
                dur.as_micros(),
                dur.as_micros() as f64 / *count as f64,
                strategy_json.join(",\n"),
            )
        })
        .collect();

    let json = format!(
        r#"{{
  "benchmark": "mir_router_classification_overhead",
  "scales": [
{}
  ]
}}"#,
        entries.join(",\n"),
    );

    println!("\n{json}");

    // Human-readable
    eprintln!("MIR Router Classification Overhead:");
    for (count, dur, strategies) in &results {
        eprintln!(
            "  {} functions: {}us total, {:.1}us/func, strategies: {:?}",
            count,
            dur.as_micros(),
            dur.as_micros() as f64 / *count as f64,
            strategies,
        );
    }

    // Sanity: classification should be fast (< 1ms per function on any hardware)
    let (_, last_dur, _) = results.last().unwrap();
    let per_func_us = last_dur.as_micros() as f64 / 60.0;
    assert!(
        per_func_us < 1_000.0,
        "Classification should be < 1ms/function, got {per_func_us:.0}us"
    );
}

// ---------------------------------------------------------------------------
// Test 2: VC generation overhead comparison
// ---------------------------------------------------------------------------

/// Compare VC generation cost between build_v1_vcs and trust_vcgen::generate_vcs.
///
/// build_v1_vcs is a lightweight bridge in mir_router.rs that generates safety VCs
/// directly from MIR blocks. trust_vcgen::generate_vcs is the full VC generation
/// pipeline. This benchmark measures both paths on the same functions.
#[test]
fn benchmark_vc_generation_overhead() {
    let workload = build_workload(60);

    // Measure build_v1_vcs
    let v1_start = Instant::now();
    let mut v1_total_vcs = 0usize;
    let mut v1_per_func: Vec<(String, usize, Duration)> = Vec::new();
    for func in &workload {
        let func_start = Instant::now();
        let vcs = build_v1_vcs(func);
        let func_dur = func_start.elapsed();
        v1_per_func.push((func.name.clone(), vcs.len(), func_dur));
        v1_total_vcs += vcs.len();
    }
    let v1_duration = v1_start.elapsed();

    // Measure trust_vcgen::generate_vcs
    let vcgen_start = Instant::now();
    let mut vcgen_total_vcs = 0usize;
    let mut vcgen_per_func: Vec<(String, usize, Duration)> = Vec::new();
    for func in &workload {
        let func_start = Instant::now();
        let vcs = trust_vcgen::generate_vcs(func);
        let func_dur = func_start.elapsed();
        vcgen_per_func.push((func.name.clone(), vcs.len(), func_dur));
        vcgen_total_vcs += vcs.len();
    }
    let vcgen_duration = vcgen_start.elapsed();

    let json = format!(
        r#"{{
  "benchmark": "vc_generation_overhead",
  "function_count": {},
  "build_v1_vcs": {{
    "total_vcs": {},
    "total_us": {},
    "per_function_us": {:.2},
    "per_vc_us": {:.2}
  }},
  "generate_vcs": {{
    "total_vcs": {},
    "total_us": {},
    "per_function_us": {:.2},
    "per_vc_us": {:.2}
  }},
  "speedup_ratio": {:.2}
}}"#,
        workload.len(),
        v1_total_vcs,
        v1_duration.as_micros(),
        v1_duration.as_micros() as f64 / workload.len() as f64,
        if v1_total_vcs > 0 { v1_duration.as_micros() as f64 / v1_total_vcs as f64 } else { 0.0 },
        vcgen_total_vcs,
        vcgen_duration.as_micros(),
        vcgen_duration.as_micros() as f64 / workload.len() as f64,
        if vcgen_total_vcs > 0 {
            vcgen_duration.as_micros() as f64 / vcgen_total_vcs as f64
        } else {
            0.0
        },
        if vcgen_duration.as_micros() > 0 {
            v1_duration.as_micros() as f64 / vcgen_duration.as_micros() as f64
        } else {
            f64::INFINITY
        },
    );

    println!("\n{json}");

    eprintln!("VC Generation Overhead (60 functions):");
    eprintln!(
        "  build_v1_vcs:     {} VCs in {}us ({:.1}us/func)",
        v1_total_vcs,
        v1_duration.as_micros(),
        v1_duration.as_micros() as f64 / workload.len() as f64,
    );
    eprintln!(
        "  generate_vcs:     {} VCs in {}us ({:.1}us/func)",
        vcgen_total_vcs,
        vcgen_duration.as_micros(),
        vcgen_duration.as_micros() as f64 / workload.len() as f64,
    );
}

// ---------------------------------------------------------------------------
// Test 3: Full MirRouter pipeline with per-strategy breakdown
// ---------------------------------------------------------------------------

/// Measure end-to-end MirRouter verification with per-strategy time breakdown.
///
/// This exercises the full pipeline: classify -> dispatch -> verify for each
/// function. Time is broken down by strategy to identify which backends
/// dominate verification cost.
#[test]
fn benchmark_mir_router_full_pipeline() {
    let router = benchmark_router();
    let workload = build_workload(60);

    // Stage 1: Classification
    let classify_start = Instant::now();
    let classifications: Vec<(String, MirStrategy)> =
        workload.iter().map(|f| (f.name.clone(), router.classify(f))).collect();
    let classify_duration = classify_start.elapsed();

    // Stage 2: Full verification (classify + dispatch)
    let verify_start = Instant::now();
    let results = router.verify_all(&workload);
    let verify_duration = verify_start.elapsed();

    // Per-strategy timing: measure each strategy group separately
    let mut strategy_groups: FxHashMap<String, Vec<&VerifiableFunction>> = FxHashMap::default();
    for (func, (_, strategy)) in workload.iter().zip(classifications.iter()) {
        strategy_groups.entry(format!("{strategy}")).or_default().push(func);
    }

    let mut strategy_timings: Vec<(String, usize, Duration)> = Vec::new();
    for (strategy_name, funcs) in &strategy_groups {
        let start = Instant::now();
        for func in funcs {
            let _ = router.verify_function(func);
        }
        let duration = start.elapsed();
        strategy_timings.push((strategy_name.clone(), funcs.len(), duration));
    }
    strategy_timings.sort_by_key(|t| std::cmp::Reverse(t.2)); // duration descending

    // Count results by type
    let mut result_counts: FxHashMap<String, usize> = FxHashMap::default();
    for (_, _, result) in &results {
        let label = match result {
            trust_types::VerificationResult::Proved { .. } => "Proved",
            trust_types::VerificationResult::Failed { .. } => "Failed",
            trust_types::VerificationResult::Unknown { .. } => "Unknown",
            trust_types::VerificationResult::Timeout { .. } => "Timeout",
            _ => "Other",
        };
        *result_counts.entry(label.to_string()).or_insert(0) += 1;
    }

    // Output JSON
    let strategy_json: Vec<String> = strategy_timings
        .iter()
        .map(|(name, count, dur)| {
            format!(
                r#"    {{
      "strategy": "{}",
      "function_count": {},
      "total_us": {},
      "per_function_us": {:.2}
    }}"#,
                name,
                count,
                dur.as_micros(),
                if *count > 0 { dur.as_micros() as f64 / *count as f64 } else { 0.0 },
            )
        })
        .collect();

    let results_json: Vec<String> = {
        let mut entries: Vec<_> = result_counts.iter().collect();
        entries.sort_by(|a, b| b.1.cmp(a.1));
        entries.iter().map(|(k, v)| format!(r#"    "{}": {}"#, k, v)).collect()
    };

    let json = format!(
        r#"{{
  "benchmark": "mir_router_full_pipeline",
  "function_count": {},
  "stages": {{
    "classification": {{
      "total_us": {},
      "per_function_us": {:.2}
    }},
    "full_verification": {{
      "total_us": {},
      "per_function_us": {:.2}
    }}
  }},
  "per_strategy": [
{}
  ],
  "result_distribution": {{
{}
  }}
}}"#,
        workload.len(),
        classify_duration.as_micros(),
        classify_duration.as_micros() as f64 / workload.len() as f64,
        verify_duration.as_micros(),
        verify_duration.as_micros() as f64 / workload.len() as f64,
        strategy_json.join(",\n"),
        results_json.join(",\n"),
    );

    println!("\n{json}");

    // Human-readable
    eprintln!("MIR Router Full Pipeline (60 functions):");
    eprintln!(
        "  Classification: {}us ({:.1}us/func)",
        classify_duration.as_micros(),
        classify_duration.as_micros() as f64 / workload.len() as f64,
    );
    eprintln!(
        "  Full verify:    {}us ({:.1}us/func)",
        verify_duration.as_micros(),
        verify_duration.as_micros() as f64 / workload.len() as f64,
    );
    eprintln!("  Per-strategy breakdown:");
    for (name, count, dur) in &strategy_timings {
        eprintln!(
            "    {}: {} funcs, {}us total, {:.1}us/func",
            name,
            count,
            dur.as_micros(),
            if *count > 0 { dur.as_micros() as f64 / *count as f64 } else { 0.0 },
        );
    }
    eprintln!("  Results: {:?}", result_counts);

    // Sanity: should have results for all functions
    assert_eq!(results.len(), workload.len(), "Should get one result per function");
}

// ---------------------------------------------------------------------------
// Test 4: Scaling analysis
// ---------------------------------------------------------------------------

/// Measure how verification overhead scales with function count.
///
/// Runs the full pipeline at 1, 5, 10, 30, 60 function counts and measures:
/// - Total wall-clock time
/// - Per-function overhead
/// - Total VCs generated
/// - VCs per function
///
/// This data answers: does verification time scale linearly with function count,
/// or is there super-linear overhead from shared state?
#[test]
fn benchmark_scaling_analysis() {
    let router = benchmark_router();
    let scales = [1, 5, 10, 30, 60];

    struct ScaleResult {
        function_count: usize,
        total_vcs: usize,
        classify_us: u128,
        vcgen_us: u128,
        verify_us: u128,
        total_us: u128,
    }

    let mut scale_results: Vec<ScaleResult> = Vec::new();

    for &count in &scales {
        let workload = build_workload(count);

        // Classification
        let t0 = Instant::now();
        for func in &workload {
            let _ = router.classify(func);
        }
        let classify_us = t0.elapsed().as_micros();

        // VC generation
        let t1 = Instant::now();
        let mut total_vcs = 0usize;
        for func in &workload {
            let vcs = trust_vcgen::generate_vcs(func);
            total_vcs += vcs.len();
        }
        let vcgen_us = t1.elapsed().as_micros();

        // Full pipeline (includes classify + dispatch + verify)
        let t2 = Instant::now();
        let _ = router.verify_all(&workload);
        let verify_us = t2.elapsed().as_micros();

        let total_us = classify_us + vcgen_us + verify_us;

        scale_results.push(ScaleResult {
            function_count: count,
            total_vcs,
            classify_us,
            vcgen_us,
            verify_us,
            total_us,
        });
    }

    // Output JSON
    let entries: Vec<String> = scale_results
        .iter()
        .map(|r| {
            format!(
                r#"    {{
      "function_count": {},
      "total_vcs": {},
      "classify_us": {},
      "vcgen_us": {},
      "verify_us": {},
      "total_us": {},
      "per_function_us": {:.2},
      "per_vc_us": {:.2},
      "vcs_per_function": {:.1}
    }}"#,
                r.function_count,
                r.total_vcs,
                r.classify_us,
                r.vcgen_us,
                r.verify_us,
                r.total_us,
                r.total_us as f64 / r.function_count as f64,
                if r.total_vcs > 0 { r.total_us as f64 / r.total_vcs as f64 } else { 0.0 },
                r.total_vcs as f64 / r.function_count as f64,
            )
        })
        .collect();

    // Identify top-3 bottlenecks from the 60-function run
    let last = scale_results.last().unwrap();
    let mut bottlenecks: Vec<(&str, u128)> = vec![
        ("classification", last.classify_us),
        ("vc_generation", last.vcgen_us),
        ("verification_dispatch", last.verify_us),
    ];
    bottlenecks.sort_by_key(|t| std::cmp::Reverse(t.1));

    let bottleneck_json: Vec<String> = bottlenecks
        .iter()
        .enumerate()
        .map(|(i, (name, us))| {
            let pct = if last.total_us > 0 {
                *us as f64 / last.total_us as f64 * 100.0
            } else {
                0.0
            };
            let optimization = match *name {
                "verification_dispatch" => "Incremental solving (IncrementalAYSession) to reuse solver context across VCs",
                "vc_generation" => "Cache generated VCs; use build_v1_vcs lightweight path for simple safety checks",
                "classification" => "Already fast; cache classification results for unchanged functions",
                _ => "N/A",
            };
            format!(
                r#"    {{
      "rank": {},
      "stage": "{}",
      "time_us": {},
      "percentage": {:.1},
      "proposed_optimization": "{}"
    }}"#,
                i + 1,
                name,
                us,
                pct,
                optimization,
            )
        })
        .collect();

    let json = format!(
        r#"{{
  "benchmark": "scaling_analysis",
  "scales": [
{}
  ],
  "bottleneck_analysis_at_60_functions": [
{}
  ]
}}"#,
        entries.join(",\n"),
        bottleneck_json.join(",\n"),
    );

    println!("\n{json}");

    // Human-readable
    eprintln!("Scaling Analysis:");
    eprintln!(
        "  {:<6} {:<8} {:<12} {:<12} {:<12} {:<12} {:<12}",
        "Funcs", "VCs", "Classify", "VCGen", "Verify", "Total", "Per-Func"
    );
    for r in &scale_results {
        eprintln!(
            "  {:<6} {:<8} {:<12} {:<12} {:<12} {:<12} {:<12.1}",
            r.function_count,
            r.total_vcs,
            format!("{}us", r.classify_us),
            format!("{}us", r.vcgen_us),
            format!("{}us", r.verify_us),
            format!("{}us", r.total_us),
            r.total_us as f64 / r.function_count as f64,
        );
    }
    eprintln!("\n  Top-3 Bottlenecks (at 60 functions):");
    for (i, (name, us)) in bottlenecks.iter().enumerate() {
        eprintln!(
            "    {}. {} — {}us ({:.0}%)",
            i + 1,
            name,
            us,
            if last.total_us > 0 { *us as f64 / last.total_us as f64 * 100.0 } else { 0.0 },
        );
    }

    // Sanity: scaling should be roughly linear (not quadratic)
    // Compare 60-func per-func cost to 1-func per-func cost
    let single = &scale_results[0];
    let full = scale_results.last().unwrap();
    let single_per = single.total_us as f64 / single.function_count as f64;
    let full_per = full.total_us as f64 / full.function_count as f64;
    // Per-function cost at 60x should not be more than 10x the single-function cost
    // (allows for some overhead from batch effects but catches quadratic scaling)
    if single_per > 0.0 {
        let overhead_ratio = full_per / single_per;
        eprintln!(
            "\n  Scaling overhead: {:.1}x (single={:.0}us, batch={:.0}us per-func)",
            overhead_ratio, single_per, full_per,
        );
        assert!(
            overhead_ratio < 10.0,
            "Scaling overhead should be < 10x, got {overhead_ratio:.1}x — possible super-linear scaling"
        );
    }
}
