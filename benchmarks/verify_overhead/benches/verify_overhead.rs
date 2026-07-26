// trust-benchmarks/benches/verify_overhead.rs
//
// Criterion benchmarks for verification pipeline overhead measurement.
//
// Loads real compiler-extracted MIR fixtures and benchmarks:
// - VC generation (trust_vcgen::generate_vcs)
// - MIR classification (MirRouter::classify)
// - Full function verification (MirRouter::verify_function)
//
// Run: cargo bench -p trust-benchmarks
// Results: target/criterion/ (HTML reports with statistical analysis)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use trust_router::MirRouter;
use trust_types::VerifiableFunction;
use trust_vcgen::generate_vcs;

/// Path to the real MIR fixtures directory.
fn fixtures_dir() -> PathBuf {
    // Resolve relative to the workspace root, not the benchmark crate.
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest_dir)
        .join("..")
        .join("..")
        .join("crates")
        .join("trust-integration-tests")
        .join("fixtures")
        .join("real_mir")
}

/// Load all JSON fixtures from the real_mir directory.
fn load_all_fixtures() -> Vec<(String, VerifiableFunction)> {
    let dir = fixtures_dir();
    if !dir.exists() {
        eprintln!(
            "WARNING: No fixtures at {}. Generate with: ./scripts/generate_mir_fixtures.sh",
            dir.display()
        );
        return vec![];
    }
    let mut fixtures = Vec::new();
    for entry in std::fs::read_dir(&dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().map_or(true, |ext| ext != "json") {
            continue;
        }
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        let json = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
        match serde_json::from_str::<VerifiableFunction>(&json) {
            Ok(func) => fixtures.push((name, func)),
            Err(e) => {
                eprintln!("WARNING: skipping invalid fixture {}: {e}", path.display());
            }
        }
    }
    fixtures.sort_by(|a, b| a.0.cmp(&b.0));
    fixtures
}

/// Benchmark: VC generation per fixture.
///
/// Measures trust_vcgen::generate_vcs() -- the core VC generation pass that
/// transforms MIR basic blocks into verification conditions.
fn bench_vcgen(c: &mut Criterion) {
    let fixtures = load_all_fixtures();
    if fixtures.is_empty() {
        return;
    }

    let mut group = c.benchmark_group("vcgen");
    for (name, func) in &fixtures {
        let block_count = func.body.blocks.len();
        group.bench_with_input(
            BenchmarkId::new("generate_vcs", format!("{name} ({block_count} blocks)")),
            func,
            |b, func| {
                b.iter(|| generate_vcs(func));
            },
        );
    }
    group.finish();
}

/// Benchmark: MIR-level function classification.
///
/// Measures MirRouter::classify() -- the strategy selection pass that
/// determines which backend (trust-mc, trust-wp, v1, etc.) handles each function.
fn bench_classify(c: &mut Criterion) {
    let fixtures = load_all_fixtures();
    if fixtures.is_empty() {
        return;
    }

    let router = MirRouter::with_defaults();
    let mut group = c.benchmark_group("classify");
    for (name, func) in &fixtures {
        group.bench_with_input(
            BenchmarkId::new("mir_classify", name),
            func,
            |b, func| {
                b.iter(|| router.classify(func));
            },
        );
    }
    group.finish();
}

/// Benchmark: Full function verification (without real solver backends).
///
/// Measures MirRouter::verify_function() -- the complete pipeline from
/// classification through VC generation and mock solver dispatch. Real ay/trust-mc
/// backends are not connected; this measures framework overhead only.
fn bench_verify_function(c: &mut Criterion) {
    let fixtures = load_all_fixtures();
    if fixtures.is_empty() {
        return;
    }

    let router = MirRouter::with_defaults();
    let mut group = c.benchmark_group("verify_function");
    for (name, func) in &fixtures {
        let block_count = func.body.blocks.len();
        group.bench_with_input(
            BenchmarkId::new(
                "verify_function",
                format!("{name} ({block_count} blocks)"),
            ),
            func,
            |b, func| {
                b.iter(|| router.verify_function(func));
            },
        );
    }
    group.finish();
}

/// Summary benchmark: aggregate over all fixtures.
///
/// Runs the entire pipeline on all fixtures in sequence, measuring total
/// throughput for the fixture suite as a batch.
fn bench_all_fixtures_batch(c: &mut Criterion) {
    let fixtures = load_all_fixtures();
    if fixtures.is_empty() {
        return;
    }

    let router = MirRouter::with_defaults();
    let total_blocks: usize = fixtures.iter().map(|(_, f)| f.body.blocks.len()).sum();

    let mut group = c.benchmark_group("batch");

    group.bench_function(
        BenchmarkId::new(
            "vcgen_all",
            format!("{} funcs, {} blocks", fixtures.len(), total_blocks),
        ),
        |b| {
            b.iter(|| {
                for (_, func) in &fixtures {
                    let _ = generate_vcs(func);
                }
            });
        },
    );

    group.bench_function(
        BenchmarkId::new(
            "verify_all",
            format!("{} funcs, {} blocks", fixtures.len(), total_blocks),
        ),
        |b| {
            b.iter(|| {
                for (_, func) in &fixtures {
                    let _ = router.verify_function(func);
                }
            });
        },
    );

    group.finish();
}

criterion_group!(
    benches,
    bench_vcgen,
    bench_classify,
    bench_verify_function,
    bench_all_fixtures_batch,
);
criterion_main!(benches);
