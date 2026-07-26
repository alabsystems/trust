// corpus-census-2026-07-24: the CORPUS-WIDE measurement artifact.
//
// WHY THIS EXISTS. The standing goal is "prove all of Rust" — every Rust function
// carrying a Clean-kernel certificate with axiom residue ⊆ the 3 foundational axioms
// and `kernel_rejected == 0`. You cannot drive that goal without a REPRODUCIBLE
// measurement of what is proven TODAY, and the 2026-07-24 toolchain audit found that
// the headline number in circulation (`464 harness tests`) appears in exactly one file
// — CLAUDE.md — with no artifact behind it, and ruled: "Either produce the artifact or
// retract the number."
//
// This binary produces the artifact for the CLEAN-KERNEL lane over the COMMITTED dump
// corpus. It needs NO `trustc` and no stage2 build: every committed dump is already a
// serialized `VerifiableFunction`, and the per-function proof is pure computation
// (recognizer match → kernel check), so the census is reproducible from a source
// checkout alone. That is deliberately a NARROWER claim than a full crate survey
// (`targo trust survey`, which does need a HEAD-matched `trustc`) — see HONEST SCOPE.
//
// SCRATCH/MEASUREMENT TOOL — additive (a new file; touches no pipeline source) and
// read-only with respect to the corpus. Uses ONLY the public API
// `trust_clean::prove_dump_dir_with_budget`.
//
// HONEST SCOPE — what a number from this tool does and does NOT mean:
//   * It counts functions in the COMMITTED FIXTURE CORPUS, which is a curated
//     regression corpus, NOT a uniform sample of Rust. It is emphatically NOT a
//     "fraction of Rust proven" figure and must never be reported as one.
//   * `inhabited` = the contract type grounded AND an inhabitant was kernel-checked
//     modulo 3. Functions with no contract are counted in `total` and are not
//     `inhabited`; a high not-inhabited count is therefore expected and is not a
//     failure.
//   * `kernel_rejected` MUST be 0. Any nonzero value is a SOUNDNESS BUG, and this tool
//     exits non-zero on it — that is the assertion worth having in the artifact.
//   * A per-function wall-clock budget DECLINES slow functions. A decline contributes
//     NOTHING to any proven tally (strictly fail-closed), but it does mean a budgeted
//     run UNDERSTATES `inhabited`. The budget used is printed in the header so a
//     number is never quotable without it.
//
// Usage:
//   corpus-census-2026-07-24 [--budget SECS] [--jobs N] [root-dir ...]
// Default root is `crates/trust-clean/fixtures`. Output: a TSV of per-directory
// scorecards to stdout, then an aggregate summary to stderr.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use trust_clean::{ProveScorecard, prove_dump_dir_with_budget};

/// Every directory at or under `root` that DIRECTLY contains ≥1 `*.json`.
/// `prove_dump_dir` reads one directory (non-recursively), and composition is
/// per-directory, so the directory is the natural unit.
fn dump_dirs(root: &Path, out: &mut BTreeSet<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(root) else { return };
    let mut has_json = false;
    let mut subdirs = Vec::new();
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            subdirs.push(path);
        } else if path.extension().and_then(|e| e.to_str()) == Some("json") {
            has_json = true;
        }
    }
    if has_json {
        out.insert(root.to_path_buf());
    }
    for sub in subdirs {
        dump_dirs(&sub, out);
    }
}

/// Field-by-field accumulate (the scorecard has no `AddAssign`).
fn accumulate(total: &mut ProveScorecard, one: &ProveScorecard) {
    total.total += one.total;
    total.inhabited += one.inhabited;
    total.type_grounded_not_inhabited += one.type_grounded_not_inhabited;
    total.not_grounded += one.not_grounded;
    total.kernel_rejected += one.kernel_rejected;
    total.total_obligations += one.total_obligations;
    total.postcondition_obligations += one.postcondition_obligations;
    total.safety_obligations += one.safety_obligations;
    total.safety_discharged += one.safety_discharged;
    // Trust: R4 MIGRATION METRIC (2026-07-25). `fully_faithful == via_trustir +
    // mirsem_fallback` is a pinned invariant, and the MirSem teardown's stated exit
    // criterion is `mirsem_fallback == 0` across every measured corpus. TrustIr is the
    // TARGET universal IR; the MirSem lane is an authenticated COMPATIBILITY lane being
    // migrated off. Without this split a census cannot say how far R4 actually is.
    total.fully_faithful += one.fully_faithful;
    total.fully_faithful_via_trustir += one.fully_faithful_via_trustir;
    total.fully_faithful_mirsem_fallback += one.fully_faithful_mirsem_fallback;
    total.proven.extend(one.proven.iter().cloned());
    total.rejections.extend(one.rejections.iter().cloned());
}

fn main() {
    let mut budget_secs: u64 = 5;
    let mut jobs: usize = std::thread::available_parallelism().map_or(4, |n| n.get());
    let mut roots: Vec<PathBuf> = Vec::new();

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--budget" => {
                budget_secs = args.next().and_then(|v| v.parse().ok()).unwrap_or(5);
            }
            "--jobs" => {
                jobs = args.next().and_then(|v| v.parse().ok()).unwrap_or(4).max(1);
            }
            other => roots.push(PathBuf::from(other)),
        }
    }
    if roots.is_empty() {
        roots.push(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures"));
    }

    let mut dirs = BTreeSet::new();
    for root in &roots {
        dump_dirs(root, &mut dirs);
    }
    let dirs: Vec<PathBuf> = dirs.into_iter().collect();

    println!("# corpus-census-2026-07-24");
    println!("# budget_secs\t{budget_secs}");
    println!("# jobs\t{jobs}");
    println!("# dump_dirs\t{}", dirs.len());
    println!("dir\ttotal\tinhabited\ttype_grounded_not_inhabited\tnot_grounded\tkernel_rejected\ttotal_obligations\tsafety_obligations\tsafety_discharged\tfully_faithful\tvia_trustir\tmirsem_fallback");

    let next = Arc::new(Mutex::new(0usize));
    let results: Arc<Mutex<Vec<(PathBuf, ProveScorecard)>>> = Arc::new(Mutex::new(Vec::new()));
    let dirs = Arc::new(dirs);

    std::thread::scope(|scope| {
        for _ in 0..jobs {
            let next = Arc::clone(&next);
            let results = Arc::clone(&results);
            let dirs = Arc::clone(&dirs);
            scope.spawn(move || {
                loop {
                    let index = {
                        let mut guard = next.lock().unwrap();
                        let i = *guard;
                        if i >= dirs.len() {
                            return;
                        }
                        *guard += 1;
                        i
                    };
                    let dir = &dirs[index];
                    // A directory that fails to read is recorded as an EMPTY scorecard
                    // rather than skipped silently — a census that hides its own gaps
                    // is not evidence.
                    let sc = prove_dump_dir_with_budget(dir, budget_secs)
                        .unwrap_or_else(|_| ProveScorecard::default());
                    results.lock().unwrap().push((dir.clone(), sc));
                }
            });
        }
    });

    let mut results = Arc::try_unwrap(results).unwrap().into_inner().unwrap();
    results.sort_by(|a, b| a.0.cmp(&b.0));

    let mut agg = ProveScorecard::default();
    for (dir, sc) in &results {
        let name = dir.strip_prefix(env!("CARGO_MANIFEST_DIR")).unwrap_or(dir);
        println!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            name.display(),
            sc.total,
            sc.inhabited,
            sc.type_grounded_not_inhabited,
            sc.not_grounded,
            sc.kernel_rejected,
            sc.total_obligations,
            sc.safety_obligations,
            sc.safety_discharged,
            sc.fully_faithful,
            sc.fully_faithful_via_trustir,
            sc.fully_faithful_mirsem_fallback,
        );
        accumulate(&mut agg, sc);
    }

    let distinct_proven: BTreeSet<&String> = agg.proven.iter().collect();
    eprintln!("\n=== AGGREGATE (budget {budget_secs}s/fn — a budgeted run UNDERSTATES inhabited) ===");
    eprintln!("dump_dirs                    {}", results.len());
    eprintln!("functions (total)            {}", agg.total);
    eprintln!("inhabited (kernel-proven)    {}", agg.inhabited);
    eprintln!("  distinct def_paths         {}", distinct_proven.len());
    eprintln!("type_grounded_not_inhabited  {}", agg.type_grounded_not_inhabited);
    eprintln!("not_grounded                 {}", agg.not_grounded);
    eprintln!("total_obligations            {}", agg.total_obligations);
    eprintln!("safety_obligations           {}", agg.safety_obligations);
    eprintln!("safety_discharged            {}", agg.safety_discharged);
    eprintln!("KERNEL_REJECTED              {}  (MUST be 0)", agg.kernel_rejected);
    eprintln!();
    eprintln!("--- R4 MIGRATION (TrustIr is the TARGET IR; MirSem is a compatibility lane) ---");
    eprintln!("fully_faithful               {}", agg.fully_faithful);
    eprintln!("  via_trustir                {}", agg.fully_faithful_via_trustir);
    eprintln!("  mirsem_fallback            {}  (teardown exit criterion: 0)", agg.fully_faithful_mirsem_fallback);
    if agg.fully_faithful
        != agg.fully_faithful_via_trustir + agg.fully_faithful_mirsem_fallback
    {
        eprintln!(
            "INVARIANT VIOLATED: fully_faithful != via_trustir + mirsem_fallback \
             (this equality is pinned by the switchover test)"
        );
        std::process::exit(2);
    }
    if agg.kernel_rejected != 0 {
        for r in &agg.rejections {
            eprintln!("  REJECTION: {r}");
        }
        eprintln!("\nSOUNDNESS BUG: kernel_rejected != 0");
        std::process::exit(1);
    }
}
