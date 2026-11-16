//! Wall-clock measurement of `generate_vcs` over real extracted-MIR fixtures, the
//! timing companion of `vc_row_parity_probe` (which checks that a change leaves
//! every row byte-identical). Measurement aid, not a gate.
//!
//! For every `*.json` file under the given roots that parses as a
//! `VerifiableFunction`, it runs `generate_vcs` `--iters` times (default 20) after
//! one warm-up pass and prints, slowest first, the median per-call time of each
//! fixture, then the total of the medians and the total row count (the latter a
//! cheap sanity check that two trees generated the same number of rows). A
//! fixture that panics is reported and skipped. It reads no environment variable.
//!
//! Usage: `vcgen_fixture_bench [--iters N] [--top K] <fixture root>...`
//!
//! Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use trust_types::VerifiableFunction;
use trust_vcgen::generate_vcs;

fn json_files(root: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(root) else { return };
    for entry in entries.filter_map(Result::ok) {
        let path = entry.path();
        if path.is_dir() {
            json_files(&path, out);
        } else if path.extension().is_some_and(|x| x == "json") {
            out.push(path);
        }
    }
}

fn main() {
    let mut iters = 20usize;
    let mut top = 25usize;
    let mut roots = Vec::new();
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--iters" => iters = args.next().and_then(|v| v.parse().ok()).unwrap_or(iters),
            "--top" => top = args.next().and_then(|v| v.parse().ok()).unwrap_or(top),
            _ => roots.push(PathBuf::from(arg)),
        }
    }
    let iters = iters.max(1);
    let mut files = Vec::new();
    for root in &roots {
        json_files(root, &mut files);
    }
    files.sort();

    let mut results: Vec<(Duration, usize, PathBuf)> = Vec::new();
    for path in files {
        let Ok(text) = std::fs::read_to_string(&path) else { continue };
        let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) else { continue };
        let Ok(rows) = catch_unwind(AssertUnwindSafe(|| generate_vcs(&func).len())) else {
            println!("panicked {}", path.display());
            continue;
        };
        let mut samples = Vec::with_capacity(iters);
        for _ in 0..iters {
            let start = Instant::now();
            let n = generate_vcs(&func).len();
            samples.push(start.elapsed());
            std::hint::black_box(n);
        }
        samples.sort();
        results.push((samples[samples.len() / 2], rows, path));
    }
    results.sort_by(|a, b| b.0.cmp(&a.0));
    for (median, rows, path) in results.iter().take(top) {
        println!("{:>10.3} ms  rows={rows:<5} {}", median.as_secs_f64() * 1e3, path.display());
    }
    let total: Duration = results.iter().map(|r| r.0).sum();
    let rows: usize = results.iter().map(|r| r.1).sum();
    println!(
        "TOTAL median-sum {:.3} ms over {} fixtures, {rows} rows, {iters} iters",
        total.as_secs_f64() * 1e3,
        results.len()
    );
}
